import StrataVerify
import Strata.DL.Imperative.Stmt

import CaseStudies.Velvet.Syntax

namespace Elab

open Lean Elab Command Term
open Strata HasInputContext
open Lean.Parser.Category

structure State where
  vars : List Boogie.BoogieIdent := []

abbrev TranslateTermM := StateT State TermElabM

def containsVar (id : Boogie.BoogieIdent) : TranslateTermM Bool := do
  let state ← get
  return id ∈ state.vars

def toVelvetMonoType (ty : Lambda.LMonoTy) : TranslateTermM (TSyntax `term) := do
  match ty with
  | .int  => `($(mkIdent ``Int))
  | .bool => `($(mkIdent ``Bool))
  | _ => throwError "Unsupported type {ty}"

def toVelvetType (ty : Boogie.Expression.Ty) : TranslateTermM (TSyntax `term) := do
  match ty with
  | .forAll [] mt => toVelvetMonoType mt
  | _             => throwError "Unsupported type {ty}"

def toVelvetExpr (t : Boogie.Expression.Expr) : TranslateTermM (TSyntax `term) := do
  match t with
  | .const c (.some ty) =>
    match ty with
    | .int =>
      let .some c := c.toNat? | throwError "Expected '{c}' to be a natural number"
      `(term| $(Syntax.mkNatLit c))
    | .bool => if c == "true" then `($(mkIdent ``true)) else `($(mkIdent ``false))
    | _ => throwError "Unsupported constant type"
  | .fvar id ty =>
    if ← containsVar id then
      `($(mkIdent id.snd.toName))
    else if let .some ty := ty then
      let t ← toVelvetMonoType ty
      `(@$(mkIdent ``Classical.choice) $t $(mkIdent ``inferInstance))
    else
      throwError "Unsupported fvar {t}"
  | .ite c t e =>
    let c ← toVelvetExpr c
    let t ← toVelvetExpr t
    let e ← toVelvetExpr e
    `(@$(mkIdent ``ite) $c $t $e)
  | .app (.app (.op "Bool.And" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ ∧ $e₂)
  | .app (.app (.op "Int.Add" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ + $e₂)
  | .app (.app (.op "Int.Sub" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ - $e₂)
  | .app (.app (.op "Int.Mul" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ * $e₂)
  | .app (.app (.op "Int.Div" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ / $e₂)
  | .app (.app (.op "Int.Lt" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ < $e₂)
  | .app (.app (.op "Int.Le" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ ≤ $e₂)
  | .app (.app (.op "Int.Ge" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ ≥ $e₂)
  | .app (.app (.op "Int.Gt" _) e₁) e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ > $e₂)
  | .eq e₁ e₂ =>
    let e₁ ← toVelvetExpr e₁
    let e₂ ← toVelvetExpr e₂
    `($e₁ = $e₂)
  | _ => throwError "Unsupported expr {t}"

open Lambda.LExpr.Syntax
open Lambda.LExpr.SyntaxMono

abbrev VelvetHeader := TSyntax `ident × TSyntaxArray `leafny_binder × TSyntax `ident × TSyntax `term

def toVelvetProcedureHeader (h : Boogie.Procedure.Header) : TranslateTermM VelvetHeader := do
  let name ← `(ident| $(mkIdent (`Boogie ++ h.name.snd.toName)))
  let params : Array (TSyntax `leafny_binder) ← h.inputs.toArray.mapM toVelvetParam
  let [(id, ty)] := h.outputs | throwError "Expected exactly one output"
  let outName ← `(ident| $(mkIdent id.snd.toName))
  let outType ← toVelvetMonoType ty
  return (name, params, outName, outType)
where
  toVelvetParam (id : Boogie.BoogieIdent × Lambda.LMonoTy) : TranslateTermM (TSyntax `leafny_binder) := do
    let (name, ty) := id
    modify fun s => { s with vars := name :: s.vars }
    let name ← `(ident| $(mkIdent name.snd.toName))
    let type ← toVelvetMonoType ty
    `(leafny_binder| (mut $name : $type))

abbrev VelvetSpec := TSyntaxArray `term × TSyntaxArray `term

def toVelvetSpec (s : Boogie.Procedure.Spec) : TranslateTermM VelvetSpec := do
  let reqs ← s.preconditions.toArray.mapM toVelvetCheck
  let enss ← s.postconditions.toArray.mapM toVelvetCheck
  return (reqs, enss)
where
  toVelvetCheck (c : Boogie.BoogieLabel × Boogie.Procedure.Check) :=
    toVelvetExpr c.snd.expr

mutual

def toVelvetStatement (out : Boogie.BoogieIdent) (s : Boogie.Statement) : TranslateTermM (TSyntax `doElem) := do
  match s with
  | .init id ty v =>
    let name ← `(ident| $(mkIdent id.snd.toName))
    modify fun s => { s with vars := id :: s.vars }
    let type ← toVelvetType ty
    let e ← if let .fvar id _ := v then
              if ← containsVar id then
                `($(mkIdent id.snd.toName))
              else
                -- Case: `var x : T := init_*`
                -- TODO: `init_*` should probably be declared as a global variable
                `(@Classical.choice $type inferInstance)
            else
              toVelvetExpr v
    `(doElem| let mut $name : $type := $e)
  | .set id v =>
    let e ← toVelvetExpr v
    if id = out then
      `(doElem| return $e)
    else
      let name ← `(ident| $(mkIdent id.snd.toName))
      if ← containsVar id then
        let reassign ← `(Lean.Parser.Term.doReassign| $name := $e)
        return ⟨reassign⟩
      else
        throwError "Unknown variable {id}"
  | .ite c t e md =>
    have : sizeOf t.ss < sizeOf (Imperative.Stmt.ite c t e md) := by simp +arith [sizeOf]
    have : sizeOf e.ss < sizeOf (Imperative.Stmt.ite c t e md) := by simp [sizeOf]
    let c ← toVelvetExpr c
    let t ← toVelvetBlock out t.ss
    let e ← toVelvetBlock out e.ss
    `(doElem| if $c then $[$t:doElem]* else $[$e:doElem]*)
  | .loop c m i b md =>
    have : sizeOf b.ss < sizeOf (Imperative.Stmt.loop c m i b md) := by simp [sizeOf]
    let c ← toVelvetExpr c
    let m ← m.mapM toVelvetExpr
    let i ← i.toArray.mapM toVelvetExpr
    let b ← toVelvetBlock out b.ss
    `(doElem| while $c
      $[invariant $i]*
      $[decreasing $m]?
      do
        $[$b:doElem]*)
  | _ => throwError s!"Unsupported statement"

def toVelvetBlock (out : Boogie.BoogieIdent) (ss : Boogie.Statements) : TranslateTermM (TSyntaxArray `doElem) := do
  let ss ← ss.attach.mapM fun ⟨s, h⟩ =>
    have : sizeOf s < sizeOf ss := by simp [Imperative.Stmts.sizeOf_lt_of_mem h]
    toVelvetStatement out s
  return ss.toArray

end

def toVelvetBody (out : Boogie.BoogieIdent) (ss : Boogie.Statements) : TranslateTermM doSeq := do
  let ss ← ss.toArray.mapM (toVelvetStatement out)
  `(doSeq| $[$ss:doElem]*)

abbrev TranslateCmdM := StateT State CommandElabM

def liftTranslateTermM {α} (x : TranslateTermM α) : TranslateCmdM α := do
  let s ← get
  let (a, s') ← liftTermElabM (StateT.run x s)
  set s'
  return a

def toVelvetProcedure (p : Boogie.Procedure) : TranslateCmdM (TSyntax `command) := do
  let state ← get
  let [(out, _)] := p.header.outputs | throwError "Expected exactly one output"
  let (name, params, outName, outType) ← liftTranslateTermM (toVelvetProcedureHeader p.header)
  let (reqs, enss) ← liftTranslateTermM (toVelvetSpec p.spec)
  let body ← liftTranslateTermM (toVelvetBody out p.body)
  set { state with vars := p.header.name :: state.vars }
  `(method $name $params* return ($outName : $outType)
    $[require $reqs]*
    $[ensures $enss]*
    do
      $body)

def toVelvetDecl (d : Boogie.Decl) : TranslateCmdM (TSyntax `command) := do
  match d with
  | .proc d _ => toVelvetProcedure d
  | _ => throwError s!"Unexpected declaration: {d.name}"

def toVelvetBoogie (p : Boogie.Program) : TranslateCmdM (TSyntaxArray `command) := do
  p.decls.toArray.mapM toVelvetDecl

def toVelvet (program : Strata.Program) : CommandElabM Unit := do
  let cmds ← match program.dialect with
    | "Boogie" =>
      let (program, errors) := Strata.TransM.run (Strata.translateProgram program)
      let #[] := errors | throwError s!"DDM Transform Error: {errors}"
      logInfo f!"AST: {program}"
      (toVelvetBoogie program).run' {}
    | _ => throwError s!"Unknown dialect: {program.dialect}"
  cmds.forM (logInfo m!"{·}")
  cmds.forM elabCommand

declare_tagged_region command strataVelvetProgram "#strataVelvet" "#end"

@[command_elab strataVelvetProgram]
def strataVelvetProgramImpl : CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← getInputContext
  let loader := (dialectExt.getState (←Lean.getEnv)).loaded
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram loader leanEnv inputCtx p e with
  | .ok pgm =>
    toVelvet pgm
  | .error errors =>
    for (stx, e) in errors do
      logMessage e

end Elab

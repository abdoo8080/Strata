/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.Boole
import Strata.Languages.Boole.DDMTransform.Parse
import Strata.Languages.Boole.DDMTransform.Translate
import Strata.Languages.Boogie.Verifier
import Strata.DL.Imperative.Stmt

def Lambda.LExpr.replaceExpr (e : Lambda.LExpr T) (f : Lambda.LExpr T → Option (Lambda.LExpr T))
  : Lambda.LExpr T :=
  match f e with
  | some e => e
  | none =>
    match e with
    | .const m c => .const m c
    | .op m o ty => .op m o ty
    | .bvar m n => .bvar m n
    | .fvar m n ty => .fvar m n ty
    | .abs m ty e' => .abs m ty (replaceExpr e' f)
    | .quant m k ty tr e' => .quant m k ty (replaceExpr tr f) (replaceExpr e' f)
    | .app m fn arg => .app m (replaceExpr fn f) (replaceExpr arg f)
    | .ite m c t e' => .ite m (replaceExpr c f) (replaceExpr t f) (replaceExpr e' f)
    | .eq m e1 e2 => .eq m (replaceExpr e1 f) (replaceExpr e2 f)

namespace Boogie

def Command.replaceExpr (c : Boogie.Command) (f : Expression.Expr → Option Expression.Expr) : Boogie.Command :=
  match c with
  | .cmd (.init name ty e md) => .cmd (.init name ty (e.replaceExpr f) md)
  | .cmd (.set name e md) => .cmd (.set name (e.replaceExpr f) md)
  | .cmd (.havoc name md) => .cmd (.havoc name md)
  | .cmd (.assert label b md) => .cmd (.assert label (b.replaceExpr f) md)
  | .cmd (.assume label b md) => .cmd (.assume label (b.replaceExpr f) md)
  | .call lhs name args md => .call lhs name (args.map (·.replaceExpr f)) md

mutual

def Imperative.Stmt.replaceExpr (s : Imperative.Stmt Boogie.Expression Boogie.Command) (f : Expression.Expr → Option Expression.Expr) : Imperative.Stmt Boogie.Expression Boogie.Command :=
  match s with
  | .cmd c => .cmd (Command.replaceExpr c f)
  | .block l b md => .block l (Imperative.Block.replaceExpr b f) md
  | .ite cond thenb elseb md => .ite (cond.replaceExpr f) (Imperative.Block.replaceExpr thenb f) (Imperative.Block.replaceExpr elseb f) md
  | .loop guard measure invariant body md =>
    .loop (guard.replaceExpr f) (measure.map (·.replaceExpr f)) (invariant.map (·.replaceExpr f)) (Imperative.Block.replaceExpr body f) md
  | .goto label md => .goto label md

def Imperative.Block.replaceExpr (bss : Imperative.Block Boogie.Expression Boogie.Command) (f : Expression.Expr → Option Expression.Expr) : Imperative.Block Boogie.Expression Boogie.Command :=
  let ss : List (Imperative.Stmt Boogie.Expression Boogie.Command) := bss.map fun s =>
    Imperative.Stmt.replaceExpr s f
  ss

end

end Boogie

namespace Strata.Boole

def toBoogieExpr (e : Boole.Expression.Expr) : Boogie.Expression.Expr :=
  match e with
  | .const c ty => .const c ty
  | .op m o ty => .op m ⟨o.name, .unres⟩ ty
  | .bvar m n => .bvar m n
  | .fvar m n ty => .fvar m ⟨n.name, .unres⟩ ty
  | .abs m ty e => .abs m ty (toBoogieExpr e)
  | .quant m k ty tr e => .quant m k ty (toBoogieExpr tr) (toBoogieExpr e)
  | .app m fn e => .app m (toBoogieExpr fn) (toBoogieExpr e)
  | .ite m c t e => .ite m (toBoogieExpr c) (toBoogieExpr t) (toBoogieExpr e)
  | .eq m e1 e2 => .eq m (toBoogieExpr e1) (toBoogieExpr e2)

def ofBoogieExpr (e : Boogie.Expression.Expr) : Boole.Expression.Expr :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m ⟨o.name, .unres⟩ ty
  | .bvar m n => .bvar m n
  | .fvar m n ty => .fvar m ⟨n.name, .unres⟩ ty
  | .abs m ty e => .abs m ty (ofBoogieExpr e)
  | .quant m k ty tr e => .quant m k ty (ofBoogieExpr tr) (ofBoogieExpr e)
  | .app m fn e => .app m (ofBoogieExpr fn) (ofBoogieExpr e)
  | .ite m c t e => .ite m (ofBoogieExpr c) (ofBoogieExpr t) (ofBoogieExpr e)
  | .eq m e1 e2 => .eq m (ofBoogieExpr e1) (ofBoogieExpr e2)

def toBoogieVisibility (v : Boole.Visibility) : Boogie.Visibility :=
  match v with
  | .unres => .unres
  | .glob => .glob
  | .locl => .locl
  | .temp => .temp

def toBoogieIdent (id : Expression.Ident) : Boogie.Expression.Ident :=
  ⟨id.name, toBoogieVisibility id.metadata⟩

def toBoogieField (f : Imperative.MetaDataElem.Field Boole.Expression) : Imperative.MetaDataElem.Field Boogie.Expression :=
  match f with
  | .var v => .var (toBoogieIdent v)
  | .label l => .label l

def toBoogieValue (v : Imperative.MetaDataElem.Value Boole.Expression) : Imperative.MetaDataElem.Value Boogie.Expression :=
  match v with
  | .expr e => .expr (toBoogieExpr e)
  | .msg s => .msg s

def toBoogieMetaDataElem (md : Imperative.MetaDataElem Boole.Expression) : Imperative.MetaDataElem Boogie.Expression :=
  { fld := toBoogieField md.fld, value := toBoogieValue md.value }

def toBoogieMetaData (md : Imperative.MetaData Boole.Expression) : Imperative.MetaData Boogie.Expression :=
  md.map toBoogieMetaDataElem

def toBoogieCmd (c : Boole.Command) : Boogie.Command :=
  match c with
  | .cmd (.init name ty e md) => .cmd (.init (toBoogieIdent name) ty (toBoogieExpr e) (toBoogieMetaData md))
  | .cmd (.set name e md) => .cmd (.set (toBoogieIdent name) (toBoogieExpr e) (toBoogieMetaData md))
  | .cmd (.havoc name md) => .cmd (.havoc (toBoogieIdent name) (toBoogieMetaData md))
  | .cmd (.assert label b md) => .cmd (.assert label (toBoogieExpr b) (toBoogieMetaData md))
  | .cmd (.assume label b md) => .cmd (.assume label (toBoogieExpr b) (toBoogieMetaData md))
  | .call lhs name args md => .call (lhs.map toBoogieIdent) name (args.map toBoogieExpr) (toBoogieMetaData md)

mutual

def toBoogieStmt (s : Boole.Statement) : Boogie.Statement :=
  match s with
  | .cmd c => .cmd (toBoogieCmd c)
  | .block l b md => .block l (toBoogieBlock b) (toBoogieMetaData md)
  | .ite cond thenb elseb md => .ite (toBoogieExpr cond) (toBoogieBlock thenb) (toBoogieBlock elseb) (toBoogieMetaData md)
  | .loop guard measure invariant body md => .loop (toBoogieExpr guard) (measure.map toBoogieExpr) (invariant.map toBoogieExpr) (toBoogieBlock body) (toBoogieMetaData md)
  | .goto label md => .goto label (toBoogieMetaData md)
  | .for var ty init guard step measure invariant body md =>
    let init := .cmd (.cmd (.init (toBoogieIdent var) ty (toBoogieExpr init)))
    let step := .cmd (.cmd (.set (toBoogieIdent var) (toBoogieExpr step)))
    let body := (toBoogieBlock body) ++ [step]
    let loop := .loop (toBoogieExpr guard) (measure.map toBoogieExpr) (invariant.map toBoogieExpr) body
    .block "for" [init, loop] (toBoogieMetaData md)

def toBoogieBlock (bss : Boole.Block Boole.Expression Boole.Command) : Imperative.Block Boogie.Expression Boogie.Command :=
  let ss : List (Boogie.Statement) := bss.map fun s =>
    toBoogieStmt s
  ss

end

def toBoogieFunction (f : Boole.Function) : Boogie.Function :=
  { name     := toBoogieIdent f.name
    typeArgs := f.typeArgs
    inputs   := f.inputs.map (fun (k, v) => (toBoogieIdent k, v))
    output   := f.output
    body     := f.body.map toBoogieExpr
    attr     := f.attr
    concreteEval := f.concreteEval.map (fun f e es => toBoogieExpr (f (ofBoogieExpr e) (es.map ofBoogieExpr)))
    axioms   := f.axioms.map toBoogieExpr }

def toBoogieProcedureHeader (p : Boole.Procedure.Header) : Boogie.Procedure.Header :=
  { name     := toBoogieIdent p.name
    typeArgs := p.typeArgs
    inputs   := p.inputs.map (fun (k, v) => (toBoogieIdent k, v))
    outputs  := p.outputs.map (fun (k, v) => (toBoogieIdent k, v)) }

def toBoogieProcedureCheckAttr (a : Boole.Procedure.CheckAttr) : Boogie.Procedure.CheckAttr :=
  match a with
  | .Free => .Free
  | .Default => .Default

def toBoogieProcedureCheck (c : Boole.Procedure.Check) : Boogie.Procedure.Check :=
  { expr := toBoogieExpr c.expr
    attr := toBoogieProcedureCheckAttr c.attr }

def toBoogieLabel (l : Boole.BooleLabel) : Boogie.BoogieLabel :=
  l

def toBoogieProcedureSpec (spec : Boole.Procedure.Spec) : Boogie.Procedure.Spec :=
  { modifies      := spec.modifies.map toBoogieIdent
    preconditions  := spec.preconditions.map (fun (l, e) => (toBoogieLabel l, toBoogieProcedureCheck e))
    postconditions := spec.postconditions.map (fun (l, e) => (toBoogieLabel l, toBoogieProcedureCheck e)) }

def toBoogieProcedure (p : Boole.Procedure) : Boogie.Procedure :=
  { header := toBoogieProcedureHeader p.header
    spec   := toBoogieProcedureSpec p.spec
    body   := p.body.map toBoogieStmt }

def toBoogieBoundedness (b : Boole.Boundedness) : Boogie.Boundedness :=
  match b with
  | .Finite => .Finite
  | .Infinite => .Infinite

def toBoogieTypeConstructor (tc : Boole.TypeConstructor) : Boogie.TypeConstructor :=
  { bound := toBoogieBoundedness tc.bound
    name  := tc.name
    numargs  := tc.numargs }

def toBoogieTypeSynonym (ts : Boole.TypeSynonym) : Boogie.TypeSynonym :=
  { name := ts.name
    typeArgs := ts.typeArgs
    type := ts.type }

def toBoogieTypeDecl (td : Boole.TypeDecl) : Boogie.TypeDecl :=
  match td with
  | .con tc => .con (toBoogieTypeConstructor tc)
  | .syn ts => .syn (toBoogieTypeSynonym ts)

def toBoogieAxiom (a : Boole.Axiom) : Boogie.Axiom :=
  { name := a.name
    e := toBoogieExpr a.e }

def toBoogieDecl (d : Boole.Decl) : Boogie.Decl :=
  match d with
  | .var name ty e md => .var (toBoogieIdent name) ty (toBoogieExpr e) (toBoogieMetaData md)
  | .type t md => .type (toBoogieTypeDecl t) (toBoogieMetaData md)
  | .ax a md => .ax (toBoogieAxiom a) (toBoogieMetaData md)
  | .distinct l es md => .distinct (toBoogieIdent l) (es.map toBoogieExpr) (toBoogieMetaData md)
  | .proc p md => .proc (toBoogieProcedure p) (toBoogieMetaData md)
  | .func f md => .func (toBoogieFunction f) (toBoogieMetaData md)

def toBoogieDecls (ds : Boole.Decls) : Boogie.Decls :=
  ds.map toBoogieDecl

def toBoogieProgram (program : Boole.Program) : Boogie.Program :=
  { decls := toBoogieDecls program.decls }

def getProgram (p : Strata.Program) : Boole.Program :=
  (TransM.run default (translateProgram p)).fst

def typeCheck (p : Strata.Program) (options : Options := Options.default):
  Except Std.Format Boogie.Program := do
  let program := getProgram p
  Boogie.typeCheck options (toBoogieProgram program)

def verify (smtsolver : String) (p : Strata.Program) (options : Options := Options.default):
  IO Boogie.VCResults := do
  let program := getProgram p
  EIO.toIO (fun f => IO.Error.userError (toString f))
    (Boogie.verify smtsolver (toBoogieProgram program) options)

end Strata.Boole

import Lean
import Strata.Languages.Boogie.SMTEncoder

open Lean
open Strata SMT

structure Translate.State where
  /-- Current de Bruijn level. -/
  level : Nat := 0
  /-- A mapping from variable names to their corresponding type and de Bruijn
      level (not index). So, the variables are indexed from the bottom of the
      stack rather than from the top (i.e., the order in which the symbols are
      introduced in the SMT-LIB file). To compute the de Bruijn index, we
      subtract the variable's level from the current level. Note that the type
      is stored using de Bruijn indices computed at the variable's level `vl`.
      To convert the type to use de Bruijn indices at the current level, we need
      to "sanitize" it by calling `sanitizeExpr` with the current level. -/
  bvars : Std.HashMap Name (Expr × Nat) := {}
deriving Repr

abbrev TranslateM := StateT Translate.State (Except MessageData)

namespace Translate

def sanitizeExpr (e : Expr) (offset : Nat) : Expr :=
  go e offset 0
where
  go (e : Expr) (offset currDepth : Nat) : Expr :=
    match e with
    | .bvar i =>
      .bvar (if i < currDepth then i else i + offset)
    | .forallE _ ty b _ =>
      let ty := go ty offset currDepth
      let b := go b offset (currDepth + 1)
      e.updateForallE! ty b
    | .lam _ ty b _ =>
      let ty := go ty offset currDepth
      let b := go b offset (currDepth + 1)
      e.updateLambdaE! ty b
    | .mdata _ b =>
      let b := go b offset currDepth
      e.updateMData! b
    | .letE _ t v b _ =>
      let t := go t offset currDepth
      let v := go v offset currDepth
      let b := go b offset (currDepth + 1)
      e.updateLetE! t v b
    | .app f a =>
      let f := go f offset currDepth
      let a := go a offset currDepth
      e.updateApp! f a
    | .proj _ _ b =>
      let b := go b offset currDepth
      e.updateProj! b
    | e => e

def findName (n : Name) : TranslateM (Expr × Expr) := do
  let state ← get
  match state.bvars[n]? with
  | some (t, i) =>
    return (sanitizeExpr t (state.level - i), .bvar (state.level - i - 1))
  | none => throw m!"Error: variable '{n}' not found in context"

private def mkArrow (α β : Expr) : Expr :=
  Lean.mkForall .anonymous BinderInfo.default α β

private def mkProp : Expr :=
  .sort 0

private def mkInt : Expr :=
  .const ``Int []

private def mkBitVec (w : Nat) : Expr :=
  .app (.const ``BitVec []) (mkNatLit w)

private def getBitVecWidth (α : Expr) : TranslateM Nat :=
  match_expr α with
  | BitVec w => match w.nat? with
    | some w => return w
    | none => throw m!"Error: expected natural number for BitVec width, got '{w}'"
  | _ => throw m!"Error: expected BitVec type, got '{α}'"

private def mkString : Expr :=
  .const ``String []

private def mkIntNeg : Expr :=
  mkApp2 (.const ``Neg.neg [0]) mkInt (.const ``Int.instNegInt [])

private def mkIntSub : Expr :=
  mkApp4 (.const ``HSub.hSub [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHSub [0]) mkInt
                 (.const ``Int.instSub []))

private def mkIntAdd : Expr :=
  mkApp4 (.const ``HAdd.hAdd [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHAdd [0]) mkInt
                 (.const ``Int.instAdd []))

private def mkIntMul : Expr :=
  mkApp4 (.const ``HMul.hMul [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHMul [0]) mkInt
                 (.const ``Int.instMul []))

private def mkIntDiv : Expr :=
  mkApp4 (.const ``HDiv.hDiv [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHDiv [0]) mkInt
                 (.const ``Int.instDiv []))

private def mkIntMod : Expr :=
  mkApp4 (.const ``HMod.hMod [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHMod [0]) mkInt
                 (.const ``Int.instMod []))

private def mkIntLE : Expr :=
  mkApp2 (.const ``LE.le [0]) mkInt (.const ``Int.instLEInt [])

private def mkIntLT : Expr :=
  mkApp2 (.const ``LT.lt [0]) mkInt (.const ``Int.instLTInt [])

private def mkIntGE : Expr :=
  mkApp2 (.const ``GE.ge [0]) mkInt (.const ``Int.instLEInt [])

private def mkIntGT : Expr :=
  mkApp2 (.const ``GT.gt [0]) mkInt (.const ``Int.instLTInt [])

private def mkBitVecNeg (w : Nat) : Expr :=
  mkApp2 (.const ``Neg.neg [0])
         (mkBitVec w)
         (.app (.const ``BitVec.instNeg []) (mkNatLit w))

private def mkBitVecSub (w : Nat) : Expr :=
  mkApp4 (.const ``HSub.hSub [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHSub [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instSub []) (mkNatLit w)))

def symbolToName (s : String) : Name :=
  -- Quote the string if a natural translation to Name fails
  if s.toName == .anonymous then
    Name.mkSimple s
  else
    s.toName

def translateSort (ty : TermType) : TranslateM Expr := do
  match ty with
  | .prim .bool =>
    return mkProp
  | .prim .int =>
    return mkInt
  | .prim .real =>
    throw m!"Error: unsupported sort '{repr ty}'"
  | .prim (.bitvec w) =>
    return (mkBitVec w)
  | .prim .string =>
    return mkString
  | .prim .regex =>
    throw m!"Error: regexes are not supported"
  | .prim .trigger =>
    throw m!"Error: triggers are not supported"
  | .option ty => do
    let ty ← translateSort ty
    return .app (.const ``Option [0]) ty
  | .constr n as =>
    let (_, t) ← findName (symbolToName n)
    let as ← as.mapM translateSort
    return mkAppN t as.toArray

def translateTerm (t : SMT.Term) : TranslateM (Expr × Expr) := do
  match t with
  | .var v =>
    findName (symbolToName v.id)
  | .app (.uf uf) as ty =>
    let (_, f) ← findName (symbolToName uf.id)
    let as ← as.mapM (translateTerm · >>= pure ∘ Prod.snd)
    return (← translateSort ty, mkAppN f as.toArray)
  | .quant q ns _ b =>
    let state ← get
    let translateBinder := fun ({ id := n, ty }) => do
      let n := symbolToName n
      let t ← translateSort ty
      modify fun s => { level := s.level + 1, bvars := s.bvars.insert n (t, s.level) }
      return (n, t)
    let ns ← ns.mapM translateBinder
    let (_, b) ← translateTerm b
    set state
    let mkQuant := match q with
      | .all => fun (n, ty) e => Expr.forallE n ty e .default
      | .exist => fun (n, ty) e => mkApp2 (.const ``Exists [1]) ty (.lam n ty e .default)
    return (mkProp, ns.foldr mkQuant b)
  | .prim (.bool b) =>
    return (mkProp, .const (if b then ``True else ``False) [])
  | .app .not [a] _ =>
    let (_, a) ← translateTerm a
    return (mkProp, .app (.const ``Not []) a)
  | .app .and as _ =>
    leftAssocOp (.const ``And []) as
  | .app .or as _ =>
    leftAssocOp (.const ``Or []) as
  | .app .eq [x, y] _ =>
    let (α, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp3 (.const ``Eq [1]) α x y)
  | .app .ite [c, x, y] _ =>
    let (_, c) ← translateTerm c
    let (α, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (α, mkApp5 (.const ``ite [1]) α c (.app (.const ``Classical.propDecidable []) c) x y)
  | .app .implies (a :: as) _ =>
    let level := (← get).level
    let (_, a) ← translateTerm a
    let as ← as.mapM fun a => do
      modify fun s => { s with level := s.level + 1 }
      let (_, a) ← translateTerm a
      return a
    modify fun s => { s with level := level }
    let (as, a) := ((a :: as).dropLast, (a :: as).getLast?.get rfl)
    return (mkProp, as.foldr mkArrow a)
  | .prim (.int x) =>
    return (mkProp, toExpr x)
  | .app .neg [a] _ =>
    let (_, a) ← translateTerm a
    return (mkInt, .app mkIntNeg a)
  | .app .sub as _ =>
    leftAssocOp mkIntSub as
  | .app .add as _ =>
    leftAssocOp mkIntAdd as
  | .app .mul as _ =>
    leftAssocOp mkIntMul as
  | .app .div as _ =>
    leftAssocOp mkIntDiv as
  | .app .mod as _ =>
    leftAssocOp mkIntMod as
  -- | .app .abs [a] _ =>
  --   let (_, a) ← translateTerm a
  --   return (mkInt, .app (.const ``Int.abs []) a)
  | .app .le [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntLE x y)
  | .app .lt [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntLT x y)
  | .app .ge [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntGE x y)
  | .app .gt [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntGT x y)
  | t => throw m!"Error: unsupported term '{repr t}'"
where
  leftAssocOp (op : Expr) (as : List SMT.Term) : TranslateM (Expr × Expr) := do
    let a :: as := as | throw m!"Error: expected at least two arguments for '{op}', got '{as.length}'"
    let (α, a) ← translateTerm a
    let as ← as.mapM (translateTerm · >>= pure ∘ Prod.snd)
    return (α, as.foldl (mkApp2 op) a)

def mkPropArrowN (as : Array SMT.Term) (a : SMT.Term) : TranslateM Expr := do
  let level := (← get).level
  let f as a := do
    let (_, a) ← translateTerm a
    modify fun s => { s with level := s.level + 1 }
    return (as.push a)
  let as ← as.foldlM f #[]
  let (_, a) ← translateTerm a
  modify fun s => { s with level := level + 1 }
  return as.foldr mkArrow a

def withTypeDecls (uss : Array Boogie.SMT.Sort) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let mut decls ← uss.mapM translateTypeDecl
  let b ← k
  set state
  return decls.flatten.foldr (fun (n, t, bi) b => .forallE n t b bi) b
where
  translateTypeDecl (us : Boogie.SMT.Sort) : TranslateM (Array (Name × Expr × BinderInfo)) := do
    let n := symbolToName us.name
    let t := us.arity.repeatTR (.forallE .anonymous (.sort 1) · .default) (.sort 1)
    modify fun s => { level := s.level + 1, bvars := s.bvars.insert n (t, s.level) }
    let hn := `inst
    let xs := (Array.range us.arity).map Expr.bvar
    let nonempty := .app (.const ``Nonempty [1]) (mkAppN (.bvar us.arity) xs.reverse)
    let ht := us.arity.repeatTR (.forallE `α (.sort 1) · .default) nonempty
    modify fun s => { level := s.level + 1, bvars := s.bvars.insert hn (ht, s.level) }
    return #[(n, t, .default), (hn, ht, .instImplicit)]

def withTypeDefs (iss : Map String TermType) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let defs ← iss.mapM translateTypeDef
  let b ← k
  set state
  -- Note: We set `nondep` to `false` for user-defined types to ensure
  -- type-checking works. Although this could be inefficient, it should be
  -- acceptable since user-defined types are rare.
  return defs.foldr (fun (n, t, v) b => .letE n t v b false) b
where
  translateTypeDef (is : String × TermType) : TranslateM (Name × Expr × Expr) := do
    let n := symbolToName is.fst
    let t := .sort 1
    let v ← translateSort is.snd
    modify fun s => { level := s.level + 1, bvars := s.bvars.insert n (t, s.level) }
    return (n, t, v)

def withFunDecls (ufs : Array UF) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let mut decls ← ufs.mapM translateFunDecl
  let b ← k
  set state
  return decls.foldr (fun (n, t) b => .forallE n t b .default) b
where
  translateFunDecl (uf : UF) : TranslateM (Name × Expr) := do
    let state ← get
    let n := symbolToName uf.id
    let ps ← uf.args.mapM translateParam
    let s ← translateSort uf.out
    let t := ps.foldr (fun (n, t) b => .forallE n t b .default) s
    set { level := state.level + 1, bvars := state.bvars.insert n (t, state.level) : Translate.State }
    return (n, t)
  translateParam (v : TermVar) : TranslateM (Name × Expr) := do
    let n := symbolToName v.id
    let t ← translateSort v.ty
    modify fun s => { level := s.level + 1, bvars := s.bvars.insert n (t, s.level) }
    return (n, t)

def withFunDefs (ifs : Array Boogie.SMT.IF) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  -- it's common for SMT-LIB queries to be "letified" using define-fun to
  -- minimize their size. We don't recurse on each definition to avoid stack
  -- overflows.
  let defs ← ifs.mapM translateFunDef
  let b ← k
  set state
  return defs.foldr (fun (n, t, v) b => .letE n t v b true) b
where
  translateFunDef (f : Boogie.SMT.IF) : TranslateM (Name × Expr × Expr) := do
    let state ← get
    let ps ← f.uf.args.mapM translateParam
    let s ← translateSort f.uf.out
    let (_, b) ← translateTerm f.body
    let n := symbolToName f.uf.id
    let t := ps.foldr (fun (n, t) b => .forallE n t b .default) s
    let v := ps.foldr (fun (n, t) b => .lam n t b .default) b
    set { level := state.level + 1, bvars := state.bvars.insert n (t, state.level) : Translate.State }
    return (n, t, v)
  translateParam (v : TermVar) : TranslateM (Name × Expr) := do
    let n := symbolToName v.id
    let t ← translateSort v.ty
    modify fun s => { level := s.level + 1, bvars := s.bvars.insert n (t, s.level) }
    return (n, t)

def withCtx (ctx : Boogie.SMT.Context) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let p ← withTypeDecls ctx.sorts <| withTypeDefs ctx.tySubst <|
          withFunDecls ctx.ufs <| withFunDefs ctx.ifs do
    let f as a := do
      let (_, a) ← translateTerm a
      modify fun s => { s with level := s.level + 1 }
      return (as.push a)
    let as ← ctx.axms.foldlM f #[]
    let a ← k
    return as.foldr mkArrow a
  set state
  return p

def translateQuery (ctx : Boogie.SMT.Context) (assums : Array SMT.Term) (conc : SMT.Term) : TranslateM Expr := do
  withCtx ctx (mkPropArrowN assums conc)

end Translate

def translateQuery (ctx : Boogie.SMT.Context) (assums : List SMT.Term) (conc : SMT.Term) : Except MessageData Expr :=
  (Translate.translateQuery ctx assums.toArray conc).run' {}

def translateQueryMeta (ctx : Boogie.SMT.Context) (assums : List SMT.Term) (conc : SMT.Term) : MetaM Expr := do
  Lean.ofExcept (translateQuery ctx assums conc)

open Elab Command in
def elabQuery (ctx : Boogie.SMT.Context) (assums : List SMT.Term) (conc : SMT.Term) : CommandElabM Unit := do
  runTermElabM fun _ => do
  let e ← translateQueryMeta ctx assums conc
  logInfo e

set_option trace.debug true

/-- info: ∀ (a : Int), 42 > a -/
#guard_msgs in
#eval
  let a := { id := "a", ty := .prim .int }
  (elabQuery {} [] (.quant .all [a] a (.app .gt [.prim (.int 42), a] (.prim .int))))

/--
info: ∀ (α : Type → Type → Type) [inst : ∀ (α_1 α_2 : Type), Nonempty (α α_1 α_2)] (β : Type) [inst : Nonempty β]
  (γ : Type → Type) [inst : ∀ (α : Type), Nonempty (γ α)] (a : α β Prop) (b : γ (α β Prop)) (f : α β Prop → β),
  a = a ∧ b = b
-/
#guard_msgs in
#eval
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let γ := { name := "γ", arity := 1 }
  let f := { id := "f", args := [{ id := "x", ty := .constr α.name [.constr β.name [], .prim .bool] }], out := .constr β.name [] }
  let a := { id := "a", args := [], out := .constr α.name [.constr β.name [], .prim .bool] }
  let b := { id := "b", args := [], out := .constr γ.name [.constr α.name [.constr β.name [], .prim .bool]] }
  elabQuery { sorts := #[α, β, γ], ufs := #[a, b, f] } [] (.app .and [(.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool)), (.app .eq [.app (.uf b) [] b.out, .app (.uf b) [] b.out] (.prim .bool))] (.prim .bool))

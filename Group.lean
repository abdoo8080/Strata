import Mathlib.Algebra.Group.Defs
import Smt
import Smt.Real

set_option trace.smt true in
set_option trace.smt.solve true in
set_option trace.smt.reconstruct.proof true in
set_option pp.instantiateMVars false in
-- Tactic pipeline: preprocess, translate, solve, reconstruct
example [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]

-- Counter-model example
example (x y z : Real) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0)
        (h3 : 12*y - z < 0) : False := by
  smt +model [h1, h2] -- , h3]

-- Group theory examples
variable [Group G]

theorem inverse : ∀ (a : G), a * a⁻¹ = 1 := by
  smt +mono [mul_assoc, one_mul, inv_mul_cancel]

theorem identity : ∀ (a : G), a * 1 = a := by
  smt +mono [mul_assoc, one_mul, inv_mul_cancel, inverse]

theorem unique_identity (e : G) : (∀ z, e * z = z) → e = 1 := by
  smt +mono [mul_assoc, one_mul, inv_mul_cancel]

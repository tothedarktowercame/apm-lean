import Mathlib
import ConstructionTargets.ManifoldRegularFiberGlobalAtlas

open scoped ContDiff Manifold
noncomputable section

namespace ConstructionTargets.RadialSquaredFiber

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev radialLevel {n : ℕ} (X : Set (E n)) (r : ℝ) :=
  {x : X // ‖x.1‖ = r}

abbrev squaredFiber {n : ℕ} (X : Set (E n)) (r : ℝ) :=
  {x : X // ‖x.1‖ ^ 2 = r ^ 2}

lemma norm_sq_eq_sq_iff {n : ℕ} {x : E n} {r : ℝ} (hr : 0 < r) :
    ‖x‖ ^ 2 = r ^ 2 ↔ ‖x‖ = r := by
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]

/-- At a positive radius, the squared-norm equality fiber and the literal
norm level are exactly equivalent by the identity on the ambient subtype. -/
def squaredFiberEquivRadialLevel {n : ℕ} (X : Set (E n)) (r : ℝ) (hr : 0 < r) :
    squaredFiber X r ≃ radialLevel X r where
  toFun x := ⟨x.1, (norm_sq_eq_sq_iff hr).mp x.2⟩
  invFun x := ⟨x.1, (norm_sq_eq_sq_iff hr).mpr x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

@[simp] theorem squaredFiberEquivRadialLevel_apply {n : ℕ} (X : Set (E n))
    (r : ℝ) (hr : 0 < r) (x : squaredFiber X r) :
    (squaredFiberEquivRadialLevel X r hr x).1 = x.1 := rfl

@[simp] theorem squaredFiberEquivRadialLevel_symm_apply {n : ℕ} (X : Set (E n))
    (r : ℝ) (hr : 0 < r) (x : radialLevel X r) :
    ((squaredFiberEquivRadialLevel X r hr).symm x).1 = x.1 := rfl

#print axioms norm_sq_eq_sq_iff
#print axioms squaredFiberEquivRadialLevel_apply
#print axioms squaredFiberEquivRadialLevel_symm_apply

end ConstructionTargets.RadialSquaredFiber

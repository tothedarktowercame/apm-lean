import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Uniqueness of an exponential endpoint winding integer

This is the arithmetic endpoint of circle path lifting.  It deliberately does
not assert that an arbitrary circle-valued path has a lift.
-/

namespace ConstructionTargets.CircleWindingUniqueness

/-- The endpoint displacement relation delivered by a lift through
`Circle.exp`. -/
def IsEndpointWinding (a b : ℝ) (n : ℤ) : Prop :=
  a = b + (n : ℝ) * (2 * Real.pi)

/-- An exponential endpoint displacement has at most one integral winding
integer. -/
theorem endpointWinding_unique {a b : ℝ} {m n : ℤ}
    (hm : IsEndpointWinding a b m) (hn : IsEndpointWinding a b n) :
    m = n := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (m : ℝ) = (n : ℝ) := by
    apply mul_right_cancel₀ hpi
    rw [← add_left_cancel_iff (a := b)]
    exact hm.symm.trans hn
  exact_mod_cast hcast

/-- Equality under the circle exponential is exactly existence of a unique
integral endpoint displacement.  This is the strongest existence statement
available without constructing a lift of a path. -/
theorem exp_eq_iff_existsUnique_endpointWinding (a b : ℝ) :
    Circle.exp a = Circle.exp b ↔ ∃! n : ℤ, IsEndpointWinding a b n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp h
    exact ⟨n, hn, fun m hm ↦ endpointWinding_unique hm hn⟩
  · rintro ⟨n, hn, -⟩
    exact Circle.exp_eq_exp.mpr ⟨n, hn⟩

#print axioms endpointWinding_unique
#print axioms exp_eq_iff_existsUnique_endpointWinding

end ConstructionTargets.CircleWindingUniqueness

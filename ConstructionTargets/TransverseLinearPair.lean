import Mathlib.LinearAlgebra.Prod

/-!
# Linear data of a transverse pair

This module packages the elementary linear-algebra translation used when two
smooth maps meet transversely.  The usual geometric statement says that the
sum of the two derivative ranges is the whole ambient tangent space; the
equivalent operational statement says that the coproduct of the derivatives
is surjective.
-/

namespace ConstructionTargets.TransverseLinearPair

/-- Two linear maps are transverse when their images jointly span the target. -/
def IsTransversePair {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] P) (g : N →ₗ[R] P) : Prop :=
  LinearMap.range f ⊔ LinearMap.range g = ⊤

/-- Transversality of a pair is exactly surjectivity of its tangent-sum map. -/
theorem isTransversePair_iff_surjective_coprod
    {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    IsTransversePair f g ↔ Function.Surjective (LinearMap.coprod f g) := by
  constructor
  · intro h y
    have hy : y ∈ LinearMap.range (LinearMap.coprod f g) := by
      rw [LinearMap.range_coprod, h]
      trivial
    exact LinearMap.mem_range.mp hy
  · intro h
    apply top_unique
    intro y _hy
    obtain ⟨x, hx⟩ := h y
    rw [← LinearMap.range_coprod]
    exact LinearMap.mem_range.mpr ⟨x, hx⟩

end ConstructionTargets.TransverseLinearPair

#print axioms ConstructionTargets.TransverseLinearPair.isTransversePair_iff_surjective_coprod

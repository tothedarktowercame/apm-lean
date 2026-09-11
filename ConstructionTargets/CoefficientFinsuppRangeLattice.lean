import ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeOrder
import Mathlib.LinearAlgebra.Finsupp.Supported

noncomputable section
namespace ConstructionTargets.CoefficientFinsuppRangeLattice

variable (R : Type) [Semiring R]
variable (M : Type) [AddCommMonoid M] [Module R M]
variable {α β γ : Type}

/-- The range of extension along a basis-index map consists exactly of the
finitely supported functions supported on the set-theoretic range. -/
theorem range_lmapDomain_eq_supported_range (f : α → β) :
    LinearMap.range (Finsupp.lmapDomain M R f) =
      Finsupp.supported M R (Set.range f) := by
  rw [LinearMap.range_eq_map, ← Finsupp.supported_univ (M := M) (R := R),
    Finsupp.lmapDomain_supported]
  congr
  exact Set.image_univ

theorem range_lmapDomain_inf (f : α → γ) (g : β → γ) :
    LinearMap.range (Finsupp.lmapDomain M R f) ⊓
        LinearMap.range (Finsupp.lmapDomain M R g) =
      Finsupp.supported M R (Set.range f ∩ Set.range g) := by
  rw [range_lmapDomain_eq_supported_range, range_lmapDomain_eq_supported_range,
    ← Finsupp.supported_inter]

theorem range_lmapDomain_sup (f : α → γ) (g : β → γ) :
    LinearMap.range (Finsupp.lmapDomain M R f) ⊔
        LinearMap.range (Finsupp.lmapDomain M R g) =
      Finsupp.supported M R (Set.range f ∪ Set.range g) := by
  rw [range_lmapDomain_eq_supported_range, range_lmapDomain_eq_supported_range,
    ← Finsupp.supported_union]

#print axioms range_lmapDomain_eq_supported_range
#print axioms range_lmapDomain_inf
#print axioms range_lmapDomain_sup
end ConstructionTargets.CoefficientFinsuppRangeLattice

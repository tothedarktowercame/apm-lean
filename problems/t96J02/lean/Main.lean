import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # t96J02: all finite-index subgroups of the Klein-bottle group

K is the concrete polygon quotient with word `aabb`. G is its actual
fundamental group, not a free group parameter carrying a desired presentation.
The statement gives the exhaustive isomorphism alternatives and asserts both
are realized. The classification proof is open.
-/

open ConstructionTargets.StatementSurfaceModels

abbrev T96J02Group := FundamentalGroup KleinBottle (surfacePoint false 2)
abbrev T96J02TorusGroup := Multiplicative (ℤ × ℤ)

theorem apm_t96j02 :
    (∀ H : Subgroup T96J02Group, H.FiniteIndex →
      Nonempty (H ≃* T96J02Group) ∨ Nonempty (H ≃* T96J02TorusGroup)) ∧
    (∃ H : Subgroup T96J02Group,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02Group)) ∧
    (∃ H : Subgroup T96J02Group,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02TorusGroup)) := by
  sorry

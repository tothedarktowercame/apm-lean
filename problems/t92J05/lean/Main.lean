import Mathlib
import Mathlib.GroupTheory.PresentedGroup

/-!
# APM t92J05

## Statement repairs

None.

## Encoding questions

`RP²`, `S²`, and `S¹` are encoded as their actual projectivization and
metric spheres. Mathlib has no packaged construction or genus classifier for
closed oriented surfaces, so that hypothesis is isolated as a typed predicate
on an actual topological space. The asserted genus-two fundamental group is
the actual presented group on four generators with relator
`[a₁,b₁][a₂,b₂]`.
-/

open Set
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t92J05_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t92J05_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t92J05_S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
abbrev apm_t92J05_S1 := Metric.sphere (0 : ℂ) 1

/-- The standard assertion that a space is a closed oriented genus-two surface. -/
opaque apm_t92J05_IsClosedOrientedGenusTwoSurface
    (S : Type*) [TopologicalSpace S] : Prop

/-- The commutator word on two generators of `FreeGroup (Fin 4)`. -/
def apm_t92J05_commutator (a b : Fin 4) : FreeGroup (Fin 4) :=
  FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹ * (FreeGroup.of b)⁻¹

/-- The genus-two surface relator `[a₁,b₁][a₂,b₂]`. -/
def apm_t92J05_genusTwoRelator : FreeGroup (Fin 4) :=
  apm_t92J05_commutator 0 1 * apm_t92J05_commutator 2 3

abbrev apm_t92J05_genusTwoGroup :=
  PresentedGroup ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))

theorem apm_t92j05 :
    (∀ x : apm_t92J05_RP2,
      Nonempty
        (FundamentalGroup apm_t92J05_RP2 x ≃* Multiplicative (ZMod 2))) ∧
    (∀ x : apm_t92J05_S2 × apm_t92J05_S1,
      Nonempty
        (FundamentalGroup (apm_t92J05_S2 × apm_t92J05_S1) x ≃*
          Multiplicative ℤ)) ∧
    ∀ (S : Type*) [TopologicalSpace S]
        (hS : apm_t92J05_IsClosedOrientedGenusTwoSurface S) (x : S),
      Nonempty
        (FundamentalGroup S x ≃* apm_t92J05_genusTwoGroup) := by
  sorry

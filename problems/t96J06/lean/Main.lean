import Mathlib

/-!
# APM t96J06 — the mod-two self-intersection obstruction

## Statement repairs

None.

## Encoding note

`ℝP²` is Mathlib's actual real projectivization. Its standard `ℝP¹` is the
projectivization of the coordinate plane `x₂ = 0`, so both the ambient product
and the embedded product are concrete. To bound means to be the intrinsic
boundary of an actual compact three-manifold-with-boundary embedded as a
subset of the ambient product. The mod-two self-intersection obstruction is
therefore proof content rather than a hypothesis.
-/

open Set
open scoped LinearAlgebra.Projectivization Manifold

noncomputable section

abbrev apm_t96j06_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t96j06_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

/-- The coordinate plane in `ℝ³` whose projectivization is the standard
embedded `ℝP¹ ⊂ ℝP²`. -/
def apm_t96j06_coordinatePlane : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x 2 = 0 at hx
    change y 2 = 0 at hy
    change x 2 + y 2 = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change x 2 = 0 at hx
    change c * x 2 = 0
    rw [hx, mul_zero]

def apm_t96j06_RP1InRP2 : Set apm_t96j06_RP2 :=
  apm_t96j06_coordinatePlane.projectivization

abbrev apm_t96j06_Ambient := apm_t96j06_RP2 × apm_t96j06_RP2

/-- The actual product `ℝP¹ × ℝP¹` inside `ℝP² × ℝP²`. -/
def apm_t96j06_ProductSubspace : Set apm_t96j06_Ambient :=
  {p | p.1 ∈ apm_t96j06_RP1InRP2 ∧ p.2 ∈ apm_t96j06_RP1InRP2}

/-- A compact embedded three-manifold in the ambient product whose intrinsic
manifold boundary is exactly `T`. -/
def apm_t96j06_BoundsThreeManifold
    (T : Set apm_t96j06_Ambient) : Prop :=
  ∃ W : Set apm_t96j06_Ambient,
    IsCompact W ∧
    ∃ charts : ChartedSpace (EuclideanHalfSpace 3) W,
      let _ := charts
      IsManifold (𝓡∂ 3) ⊤ W ∧
      Subtype.val '' ((𝓡∂ 3).boundary W) = T

theorem apm_t96j06 :
    ¬apm_t96j06_BoundsThreeManifold apm_t96j06_ProductSubspace := by
  sorry

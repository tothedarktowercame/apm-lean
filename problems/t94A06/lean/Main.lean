import Mathlib

/-!
# APM t94A06 — a two-parameter transverse perturbation

## Statement repairs

None.

## Encoding questions

Mathlib does not currently expose a general transversality predicate for maps
of manifolds to embedded submanifolds.  That single missing interface is kept
as a typed definition below.  The manifold, smooth map, z-axis, explicit
normal-plane translation family, and almost-everywhere quantifier are all
represented directly.
-/

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t94a06_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t94a06_E3 := EuclideanSpace ℝ (Fin 3)

def apm_t94a06_zAxis : Set apm_t94a06_E3 :=
  {y | y 0 = 0 ∧ y 1 = 0}

def apm_t94a06_normalTranslation (s : apm_t94a06_E2) : apm_t94a06_E3 :=
  WithLp.toLp 2 ![s 0, s 1, 0]

def apm_t94a06_family {X : Type*} (f : X → apm_t94a06_E3)
    (s : apm_t94a06_E2) (x : X) : apm_t94a06_E3 :=
  f x + apm_t94a06_normalTranslation s

def apm_t94a06_IsTransverseToZAxis
    {X : Type*} [TopologicalSpace X]
    (h : X → apm_t94a06_E3) : Prop := by
  sorry

theorem apm_t94a06
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f) :
    apm_t94a06_family f 0 = f ∧
      ∀ᵐ s : apm_t94a06_E2,
        apm_t94a06_IsTransverseToZAxis (apm_t94a06_family f s) := by
  sorry

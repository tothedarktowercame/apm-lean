import Mathlib

/-!
# APM t94A06 — a two-parameter transverse perturbation

## Statement repairs

The source uses the standard convention that a smooth manifold is second
countable. Mathlib's `IsManifold` class does not include this separation/countability
condition, so `SecondCountableTopology X` is stated explicitly; without it an
uncountable discrete zero-dimensional manifold makes the almost-everywhere
transversality conclusion false.

## Encoding questions

Transversality to the axis is expressed concretely using the actual manifold
derivative: at every inverse-image point, the derivative image together with
the tangent line `span(e₂)` of the z-axis fills `ℝ³`. The manifold, smooth map,
explicit normal-plane translation family, and almost-everywhere quantifier are
all represented directly.
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

/-- The perturbation family agrees with the original map at parameter zero. -/
lemma apm_t94a06_family_zero {X : Type*} (f : X → apm_t94a06_E3) :
    apm_t94a06_family f 0 = f := by
  funext x
  simp [apm_t94a06_family, apm_t94a06_normalTranslation]

/-- Translation in the normal plane preserves smoothness of every slice. -/
lemma apm_t94a06_family_contMDiff
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f)
    (s : apm_t94a06_E2) :
    ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ (apm_t94a06_family f s) := by
  simpa [apm_t94a06_family] using hf.add (contMDiff_const (c := apm_t94a06_normalTranslation s))

/-- A constant normal translation does not change the derivative in the
manifold variable. -/
lemma apm_t94a06_mfderiv_family
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f)
    (s : apm_t94a06_E2) (x : X) :
    mfderiv I 𝓘(ℝ, apm_t94a06_E3) (apm_t94a06_family f s) x =
      mfderiv I 𝓘(ℝ, apm_t94a06_E3) f x := by
  rw [show apm_t94a06_family f s = f + fun _ ↦ apm_t94a06_normalTranslation s by rfl]
  rw [mfderiv_add ((hf.mdifferentiable (by simp)) x) mdifferentiableAt_const]
  simp
  rfl

def apm_t94a06_IsTransverseToZAxis
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace X] [ChartedSpace H X]
    (h : X → apm_t94a06_E3) : Prop :=
  ∀ x : X, h x ∈ apm_t94a06_zAxis →
    LinearMap.range
        (mfderiv I 𝓘(ℝ, apm_t94a06_E3) h x).toLinearMap ⊔
      Submodule.span ℝ
        ({EuclideanSpace.single (2 : Fin 3) 1} : Set apm_t94a06_E3) = ⊤

theorem apm_t94a06
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f) :
    apm_t94a06_family f 0 = f ∧
      ∀ᵐ s : apm_t94a06_E2,
        apm_t94a06_IsTransverseToZAxis I (apm_t94a06_family f s) := by
  sorry

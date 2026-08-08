import Mathlib

/-!
# APM t94A06 — a two-parameter transverse perturbation

## Statement repairs

None.

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
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f) :
    apm_t94a06_family f 0 = f ∧
      ∀ᵐ s : apm_t94a06_E2,
        apm_t94a06_IsTransverseToZAxis I (apm_t94a06_family f s) := by
  /-
  Boundary (closer hop 2): `apm_t94a06_family_zero` now closes the first
  conjunct exactly. The second conjunct is parametric transversality for an
  arbitrary smooth manifold domain. Its standard proof applies Sard to the
  projection of the incidence manifold
  `{(x,s) | f x + normalTranslation s ∈ zAxis}` onto parameter space.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, the related
  artifacts `t02A07`, `t92J07`, `t93A04`, `t01A08`, Mathlib's fixed-vector-
  space Sard/Jacobian results, manifold `mfderiv`, regular-value, and subtype-
  chart APIs, and git history found no manifold Sard theorem, parametric
  transversality theorem, or incidence-submanifold/projection package. The
  available Sard lemmas concern maps between finite-dimensional normed vector
  spaces and do not directly accept this arbitrary charted domain. Building
  the incidence manifold chartwise and transporting null critical values is
  therefore the remaining bridge; the frozen statement is unchanged.
  -/
  sorry

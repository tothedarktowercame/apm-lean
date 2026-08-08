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

  CLOSER HOP 3 compiles the slice-level differential geometry consumed by
  that incidence argument. `apm_t94a06_family_contMDiff` proves every
  translated slice remains smooth, and `apm_t94a06_mfderiv_family` proves its
  manifold derivative in `x` is exactly `mfderiv f x`, since translation is
  constant. Thus no translation-derivative bookkeeping remains. The unresolved
  step is global and measure-theoretic: construct the incidence submanifold,
  identify bad parameters as critical values of its projection, and transport
  fixed-vector-space Sard null sets through manifold charts. Searches of Sard,
  regular-value, countable-atlas, and subtype-chart APIs found no packaged
  theorem performing that assembly. The frozen statement is unchanged.
  -/
  sorry

import Mathlib

/-!
# APM m02J06

## Statement repairs

The printed condition `|x| = 0 ⇒ f(x) = 0` only constrains one point and makes
the compactness conclusion false by translations. Following the intended
Kolmogorov–Riesz argument, it is repaired to the uniform support condition
`|x| ≥ 1 ⇒ f(x) = 0`. The translation estimate is quantified over `h > 0`.
The usual nonnegativity condition for a mollifier is made explicit; it is
needed for the stated constant-one approximation estimate.

## Encoding questions

Compactness is asserted after mapping the actual measurable representatives
into Mathlib's `L¹` space, so it is compactness in the `L¹` norm and not a
pointwise-function topology.
-/

open MeasureTheory Set

/-- The class `K` from the problem, with its intended common support. -/
def apm_m02J06_K : Set (ℝ → ℝ) :=
  {f | Integrable f volume ∧
    ∫ x, |f x| ∂volume ≤ 1 ∧
    (∀ h : ℝ, 0 < h → ∫ x, |f (x + h) - f x| ∂volume ≤ Real.sqrt h) ∧
    (∀ x : ℝ, 1 ≤ |x| → f x = 0)}

/-- The standard rescaling of a mollifier. -/
noncomputable def apm_m02J06_mollifier (φ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ε⁻¹ * φ (x / ε)

/-- Convolution of two scalar functions on `ℝ`. -/
noncomputable def apm_m02J06_convolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t, f (x - t) * g t ∂volume

/-- The canonical class of an integrable function in `L¹(ℝ)`. -/
noncomputable def apm_m02J06_toL1 (f : ℝ → ℝ) (hf : Integrable f volume) :
    Lp ℝ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.2 hf).toLp f

/-- `K` regarded as a subset of the normed space `L¹(ℝ)`. -/
def apm_m02J06_KL1 : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {u | ∃ (f : ℝ → ℝ) (hf : Integrable f volume),
    f ∈ apm_m02J06_K ∧ u = apm_m02J06_toL1 f hf}

theorem apm_m02j06 :
    ∀ (φ : ℝ → ℝ) (M : ℝ),
      ContDiff ℝ ⊤ φ →
      (∀ x, 0 ≤ φ x) →
      ∫ x, φ x ∂volume = 1 →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (∀ x, |φ x| ≤ M) →
      (∃ x, |φ x| = M) →
      (∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K,
        ∫ x, |f x - apm_m02J06_convolution f
          (apm_m02J06_mollifier φ ε) x| ∂volume ≤ Real.sqrt ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K, ∀ x y : ℝ,
        |apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x -
          apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) y| ≤
            (M / ε) * Real.sqrt |x - y|) ∧
      IsCompact apm_m02J06_KL1 := by
  /-
  SKIPPED (Kolmogorov–Riesz/L¹ quotient bridge). Mathlib searches found the
  general convolution integral API (`integral_convolution`) and abstract
  Arzelà–Ascoli theorems, but no Kolmogorov–Riesz compactness criterion for
  `Lp`, nor a compiled theorem transferring a uniformly supported,
  equicontinuous family of mollified representatives into total boundedness of
  their `L¹` equivalence classes.

  A local proof must first extend the one-sided translation estimate in
  `apm_m02J06_K` to every real shift, justify both Tonelli interchanges and the
  rescaled mollifier's normalization/support bounds, bundle the convolutions as
  continuous maps on a fixed compact interval for Arzelà–Ascoli, transfer the
  resulting sup-norm nets to `Lp`, and finally prove `apm_m02J06_KL1` closed
  while changing representatives modulo a.e. equality. `a96J02` was inspected
  for convolution identities but contains no compactness route, so its code was
  not reused. The frozen statement was left unchanged.
  -/
  sorry

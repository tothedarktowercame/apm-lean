import Mathlib

/-!
# APM m98J02

## Statement repairs

Part (d) assumes only `f ∈ C²(ℝ²)`, but the convolution construction in
parts (b)--(c) requires one factor to have compact support. Following the
informal solution, `f` is minimally assumed compactly supported. This is also
the hypothesis under which the stated `C²` convolution regularity is standard.

The garbled operator typography is read, as in the supplied solution, as
`T = 2 ∂²/∂x² - ∂/∂y + 3 ∂²/(∂x∂y)`.

## Encoding questions

Mathlib currently provides `Distribution` but not the general convolution of
a compactly supported distribution with an arbitrary distribution, nor
general distributional partial derivatives. Consequently these are encoded
by their defining test-function identities. `apm_m98J02_isConvolution` uses a
test-function cutoff equal to one on a compact support of the first factor;
`apm_m98J02_solvesT` uses the formal adjoint
`2∂ₓ² + ∂ᵧ + 3∂ₓ∂ᵧ` on test functions. No function-level surrogate
replaces the distributions.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

noncomputable section

abbrev apm_m98J02_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_m98J02_Test :=
  TestFunction (⊤ : Opens apm_m98J02_E) ℝ ⊤

abbrev apm_m98J02_Dist :=
  Distribution (⊤ : Opens apm_m98J02_E) ℝ ⊤

/-- A distribution vanishes on every test function supported off one compact set. -/
def apm_m98J02_hasCompactSupport (u : apm_m98J02_Dist) : Prop :=
  ∃ K : Set apm_m98J02_E, IsCompact K ∧
    ∀ φ : apm_m98J02_Test, Disjoint (tsupport (φ : apm_m98J02_E → ℝ)) K → u φ = 0

/-- The defining pairing for convolution when the first factor has compact support.

The cutoff `χ` lets the compactly supported distribution `u` act on the
generally non-compact smooth function `x ↦ v (y ↦ φ (x + y))`. -/
def apm_m98J02_isConvolution
    (u v w : apm_m98J02_Dist) : Prop :=
  ∀ φ : apm_m98J02_Test,
    ∃ (K : Set apm_m98J02_E) (χ Ψ : apm_m98J02_Test),
      IsCompact K ∧
      (∀ η : apm_m98J02_Test,
        Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K → u η = 0) ∧
      (∀ x ∈ K, χ x = 1) ∧
      (∀ x : apm_m98J02_E,
        ∃ τ : apm_m98J02_Test,
          (∀ y : apm_m98J02_E, τ y = φ (x + y)) ∧ Ψ x = χ x * v τ) ∧
      w φ = u Ψ

/-- Directional partial derivative in one of the two coordinate directions. -/
def apm_m98J02_partial (i : Fin 2) (f : apm_m98J02_E → ℝ)
    (x : apm_m98J02_E) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The formal adjoint of `2∂ₓ² - ∂ᵧ + 3∂ₓ∂ᵧ`. -/
def apm_m98J02_formalAdjoint (f : apm_m98J02_E → ℝ)
    (x : apm_m98J02_E) : ℝ :=
  2 * apm_m98J02_partial 0 (apm_m98J02_partial 0 f) x +
    apm_m98J02_partial 1 f x +
    3 * apm_m98J02_partial 0 (apm_m98J02_partial 1 f) x

/-- Distributional equation `T w = r`, expressed against test functions. -/
def apm_m98J02_solvesT
    (w : apm_m98J02_Dist) (r : apm_m98J02_Test → ℝ) : Prop :=
  ∀ φ : apm_m98J02_Test,
    ∃ ψ : apm_m98J02_Test,
      (∀ x : apm_m98J02_E,
        ψ x = apm_m98J02_formalAdjoint (φ : apm_m98J02_E → ℝ) x) ∧
      w ψ = r φ

/-- A distribution is the regular distribution induced by a function. -/
def apm_m98J02_representsFunction
    (u : apm_m98J02_Dist) (f : apm_m98J02_E → ℝ) : Prop :=
  ∀ φ : apm_m98J02_Test, u φ = ∫ x, f x * φ x

theorem apm_m98j02 :
    (∀ u : apm_m98J02_Dist,
      apm_m98J02_hasCompactSupport u ↔
        ∃ K : Set apm_m98J02_E, IsCompact K ∧
          ∀ φ : apm_m98J02_Test,
            Disjoint (tsupport (φ : apm_m98J02_E → ℝ)) K → u φ = 0) ∧
    (∀ u v : apm_m98J02_Dist,
      apm_m98J02_hasCompactSupport u →
        ∃ w : apm_m98J02_Dist, apm_m98J02_isConvolution u v w) ∧
    ∀ (f : apm_m98J02_E → ℝ) (w₀ : apm_m98J02_Dist),
      ContDiff ℝ 2 f → IsCompact (tsupport f) →
      apm_m98J02_solvesT w₀ (fun φ ↦ φ 0) →
      ∃ (u w w' : apm_m98J02_Dist) (g : apm_m98J02_E → ℝ),
        apm_m98J02_representsFunction u f ∧
        apm_m98J02_hasCompactSupport u ∧
        apm_m98J02_isConvolution u w₀ w ∧
        apm_m98J02_representsFunction w g ∧
        ContDiff ℝ 2 g ∧
        apm_m98J02_solvesT w (fun φ ↦ ∫ x, f x * φ x) ∧
        w' ≠ w ∧
        apm_m98J02_solvesT w' (fun φ ↦ ∫ x, f x * φ x) := by
  sorry

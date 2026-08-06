import Mathlib

/-!
# APM m98A05

## Statement repairs

Part (b) is false as printed: invertibility of `DF(x₀)` does not imply
invertibility of `DF(x₀) + ε₀ DG(x₀)` for an arbitrary `ε₀`.  The
parameter base point is minimally repaired to `ε₀ = 0`, the standard
perturbative statement and exactly the base point used in part (c).

## Encoding notes

The Banach-space implicit function theorem includes open neighborhoods, a
unique local `C¹` solution map, and invertibility as a continuous linear
equivalence.  Since Mathlib has no packaged Sobolev-space type, `H²(0,π)` is
encoded by a continuous representative, its continuous first derivative,
two `L²` weak-derivative identities, and the Dirichlet traces.
-/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

def apm_m98a05_IFTConclusion
    {X P Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (H : X × P → Z) (x₀ : X) (p₀ : P) : Prop :=
  ∃ (W : Set X) (V : Set P) (g : P → X),
    IsOpen W ∧ x₀ ∈ W ∧ IsOpen V ∧ p₀ ∈ V ∧
    ContDiffOn ℝ 1 g V ∧ g p₀ = x₀ ∧
    ∀ p ∈ V, g p ∈ W ∧ H (g p, p) = 0 ∧
      ∀ x ∈ W, H (x, p) = 0 → x = g p

def apm_m98a05_IsWeakDerivativeOn
    (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Function.support φ ⊆ s →
      ∫ x, u x * deriv φ x ∂(volume.restrict s) =
        -∫ x, du x * φ x ∂(volume.restrict s)

def apm_m98a05_InH2Dirichlet (w dw d2w : ℝ → ℝ) : Prop :=
  ContinuousOn w (Icc 0 Real.pi) ∧ ContinuousOn dw (Icc 0 Real.pi) ∧
  MemLp w 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  MemLp dw 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  MemLp d2w 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  apm_m98a05_IsWeakDerivativeOn (Ioo 0 Real.pi) w dw ∧
  apm_m98a05_IsWeakDerivativeOn (Ioo 0 Real.pi) dw d2w ∧
  w 0 = 0 ∧ w Real.pi = 0

theorem apm_m98a05 :
    (∀ (X P Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [CompleteSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
      [CompleteSpace P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      [CompleteSpace Z] (H : X × P → Z) (x₀ : X) (p₀ : P)
      (A : X →L[ℝ] Z),
      ContDiff ℝ 1 H → H (x₀, p₀) = 0 →
      HasFDerivAt (fun x ↦ H (x, p₀)) A x₀ →
      (∃ e : X ≃L[ℝ] Z, (e : X →L[ℝ] Z) = A) →
      apm_m98a05_IFTConclusion H x₀ p₀) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [CompleteSpace Y] (F G : X → Y) (x₀ : X) (A : X →L[ℝ] Y),
      ContDiff ℝ 1 F → ContDiff ℝ 1 G → F x₀ = 0 →
      HasFDerivAt F A x₀ →
      (∃ e : X ≃L[ℝ] Y, (e : X →L[ℝ] Y) = A) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ x : ℝ → X, x 0 = x₀ ∧
        ∀ ε : ℝ, |ε| < δ → F (x ε) + ε • G (x ε) = 0) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      ∃ w dw d2w : ℝ → ℝ,
        apm_m98a05_InH2Dirichlet w dw d2w ∧
        ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)),
          d2w x = w x + ε * (w x) ^ 2) := by
  constructor
  · /-
    Boundary: this clause is the full Banach-space implicit function theorem
    with parameters and local uniqueness. I searched Mathlib's
    `implicitFunction`, `HasStrictFDerivAt`, `ContinuousLinearEquiv`, and
    `ContDiff` APIs. The available packaged IFT is formulated through strict
    derivatives and local inverse data; I did not complete the conversion from
    the frozen hypotheses (`ContDiff` plus `HasFDerivAt`) to that interface.
    -/
    sorry
  constructor
  · /-
    Boundary: the perturbation clause follows by applying the preceding IFT to
    `(x, ε) ↦ F x + ε • G x`. Completing it requires the same strict-derivative
    bridge, together with a bundled product derivative for this map. I searched
    `HasFDerivAt.add`, scalar-multiplication derivative rules, and the local IFT
    API, but did not finish that assembly in this pass.
    -/
    sorry
  · refine ⟨1, by norm_num, ?_⟩
    intro ε _hε
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_⟩
    · unfold apm_m98a05_InH2Dirichlet
      refine ⟨continuous_const.continuousOn,
        continuous_const.continuousOn, ?_⟩
      simp [apm_m98a05_IsWeakDerivativeOn]
    · filter_upwards with x
      simp

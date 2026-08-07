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

lemma apm_m98a05_hasStrictFDerivAt_of_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (A : E →L[ℝ] F)
    (hf : ContDiff ℝ 1 f) (hA : HasFDerivAt f A x) :
    HasStrictFDerivAt f A x := by
  exact hf.contDiffAt.hasStrictFDerivAt' hA (by norm_num)

/-- The product-domain perturbation used in part (b) is `C¹`. -/
lemma apm_m98a05_contDiff_perturbation
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F G : X → Y) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (fun q : X × ℝ => F q.1 + q.2 • G q.1) := by
  exact (hF.comp contDiff_fst).add
    (contDiff_snd.smul (hG.comp contDiff_fst))

/-- Swapping the product puts the unknown in the second coordinate expected by
Mathlib's product-domain implicit function theorem without changing the
specified partial derivative. -/
lemma apm_m98a05_hasFDerivAt_swapped_partial
    {X P Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (H : X × P → Z) (x₀ : X) (p₀ : P) (A : X →L[ℝ] Z)
    (hA : HasFDerivAt (fun x ↦ H (x, p₀)) A x₀) :
    HasFDerivAt (fun x ↦ (fun q : P × X ↦ H (q.2, q.1)) (p₀, x)) A x₀ := by
  simpa using hA

/-- At parameter zero the perturbation has exactly the derivative of `F` in
the unknown direction. -/
lemma apm_m98a05_hasFDerivAt_perturbation_zero
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F G : X → Y) (x₀ : X) (A : X →L[ℝ] Y)
    (hA : HasFDerivAt F A x₀) :
    HasFDerivAt (fun x ↦ F x + (0 : ℝ) • G x) A x₀ := by
  simpa using hA

/-- The generic parameterized implicit-function bridge. -/
lemma apm_m98a05_ift
    (X P Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z] (H : X × P → Z) (x₀ : X) (p₀ : P)
    (A : X →L[ℝ] Z) (hH : ContDiff ℝ 1 H) (hzero : H (x₀, p₀) = 0)
    (hA : HasFDerivAt (fun x ↦ H (x, p₀)) A x₀)
    (he : ∃ e : X ≃L[ℝ] Z, (e : X →L[ℝ] Z) = A) :
    apm_m98a05_IFTConclusion H x₀ p₀ := by
  /-
  Final boundary: after swapping to `P × X`, Mathlib's implicit-function API
  supplies the local equation, uniqueness, and pointwise `ContDiffAt` facts.
  It remains to extract common open product neighborhoods from those eventual
  statements and upgrade pointwise differentiability to `ContDiffOn` on the
  chosen parameter neighborhood.  The strict-derivative and orientation
  prerequisites are compiled above.
  -/
  sorry

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
  refine ⟨(fun X P Z ↦ apm_m98a05_ift X P Z), ?_⟩
  constructor
  · intro X Y _ _ _ _ _ _ F G x₀ A hF hG hFx₀ hA he
    let H : X × ℝ → Y := fun q ↦ F q.1 + q.2 • G q.1
    obtain ⟨W, V, g, hWopen, hxW, hVopen, h0V, hgdiff, hg0, hg⟩ :=
      apm_m98a05_ift X ℝ Y H x₀ 0 A
        (apm_m98a05_contDiff_perturbation F G hF hG)
        (by simpa [H] using hFx₀)
        (apm_m98a05_hasFDerivAt_perturbation_zero F G x₀ A hA) he
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVopen 0 h0V
    refine ⟨δ, hδ, g, hg0, ?_⟩
    intro ε hε
    have hεV : ε ∈ V := hball (by simpa [Real.dist_eq] using hε)
    exact (hg ε hεV).2.1
  · /-
    PARTIAL boundary: the perturbation clause follows by applying the preceding
    IFT to `(x, ε) ↦ F x + ε • G x`. The strict-derivative bridge is now proved
    above, and closer hop 1 proves that this product-domain perturbation is `C¹`
    in `apm_m98a05_contDiff_perturbation`. What remains is identifying its
    partial derivative at `(x₀, 0)` with `A` and converting Mathlib's eventual
    local solution into the stated `δ`-interval witness. Searches of
    `HasFDerivAt.add`, scalar-multiplication
    derivative rules, all closed artifacts, `ConstructionTargets`, and
    `YoungL2.lean` found no compiled helper performing that assembly.

    Closer hop 2 also proves
    `apm_m98a05_hasFDerivAt_perturbation_zero`, closing identification of the
    unknown-direction derivative at `(x₀,0)`.  Consequently this clause now
    depends only on the preceding neighborhood-extraction bridge and the
    elementary choice of a symmetric interval inside the resulting real
    neighborhood.
    Closer hop 3 routes this clause through the first conjunct.  Applying
    `hIFT` to the compiled perturbation and derivative helpers produces an
    open real parameter neighborhood; `Metric.isOpen_iff` extracts a radius,
    and the local equation gives the required symmetric interval witness.
    -/
    refine ⟨1, by norm_num, ?_⟩
    intro ε _hε
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_⟩
    · unfold apm_m98a05_InH2Dirichlet
      refine ⟨continuous_const.continuousOn,
        continuous_const.continuousOn, ?_⟩
      simp [apm_m98a05_IsWeakDerivativeOn]
    · filter_upwards with x
      simp

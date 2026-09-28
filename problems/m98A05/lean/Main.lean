import Mathlib

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

lemma apm_m98a05_ift
    (X P Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z] (H : X × P → Z) (x₀ : X) (p₀ : P)
    (A : X →L[ℝ] Z) (hH : ContDiff ℝ 1 H) (hzero : H (x₀, p₀) = 0)
    (hA : HasFDerivAt (fun x ↦ H (x, p₀)) A x₀)
    (he : ∃ e : X ≃L[ℝ] Z, (e : X →L[ℝ] Z) = A) :
    apm_m98a05_IFTConclusion H x₀ p₀ := by
  let Q : P × X → Z := fun q ↦ H (q.2, q.1)
  have hQ : ContDiff ℝ 1 Q := by
    exact hH.comp (contDiff_snd.prodMk contDiff_fst)
  have hQR : HasFDerivAt (fun x : X ↦ Q (p₀, x))
      ((fderiv ℝ Q (p₀, x₀)).comp (ContinuousLinearMap.inr ℝ P X)) x₀ := by
    have hd := (hQ.differentiable (by norm_num) (p₀, x₀)).hasFDerivAt
    simpa [Function.comp_def] using hd.comp x₀ (hasFDerivAt_prodMk_right p₀ x₀)
  have hpart : (fderiv ℝ Q (p₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ P X) = A := by
    exact hQR.unique (by simpa [Q] using hA)
  obtain ⟨e, heA⟩ := he
  have hi : ((fderiv ℝ Q (p₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ P X)).IsInvertible := by
    rw [hpart, ← heA]
    exact ContinuousLinearMap.isInvertible_equiv
  have hc : ContDiffAt ℝ 1 Q (p₀, x₀) := hQ.contDiffAt
  let g : P → X := hc.implicitFunction (by norm_num) hi
  have hg0 : g p₀ = x₀ := hc.implicitFunction_apply_self (by norm_num) hi
  have heq : ∀ᶠ p in 𝓝 p₀, Q (p, g p) = Q (p₀, x₀) :=
    hc.eventually_apply_implicitFunction (by norm_num) hi
  have huniq : ∀ᶠ q in 𝓝 (p₀, x₀),
      Q q = Q (p₀, x₀) ↔ g q.1 = q.2 :=
    hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi
  have hg_at : ContDiffAt ℝ 1 g p₀ :=
    hc.contDiffAt_implicitFunction (by norm_num) hi
  obtain ⟨D, hDnhds, hgD⟩ := hg_at.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨U, hUnhds, T, hTnhds, hUT⟩ := mem_nhds_prod_iff.mp huniq
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hTnhds
  have hgW : ∀ᶠ p in 𝓝 p₀, g p ∈ W := by
    apply hg_at.continuousAt
    simpa [hg0] using hWopen.mem_nhds hxW
  have hp_good : {p | p ∈ D ∧ Q (p, g p) = Q (p₀, x₀) ∧ g p ∈ W} ∈ 𝓝 p₀ := by
    filter_upwards [hDnhds, heq, hgW] with p hpD hpeq hpgW
    exact ⟨hpD, hpeq, hpgW⟩
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp hp_good
  obtain ⟨V', hV'sub, hV'open, hpV'⟩ := mem_nhds_iff.mp hUnhds
  let Vfinal := V ∩ V'
  refine ⟨W, Vfinal, g, hWopen, hxW, hVopen.inter hV'open,
    ⟨hpV, hpV'⟩, ?_, hg0, ?_⟩
  · exact hgD.mono (fun p hp ↦ hVsub hp.1 |>.1)
  · intro p hp
    have hpD_eq := hVsub hp.1
    have hpU : p ∈ U := hV'sub hp.2
    refine ⟨hpD_eq.2.2, ?_, ?_⟩
    · simpa [Q, hzero] using hpD_eq.2.1
    · intro x hxW' hxzero
      have hpx : (p, x) ∈ U ×ˢ T := ⟨hpU, hWsub hxW'⟩
      have hiff := hUT hpx
      have hqeq : Q (p, x) = Q (p₀, x₀) := by
        simpa [Q, hzero] using hxzero
      exact (hiff.mp hqeq).symm

import Mathlib

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

noncomputable section

/-- The standard one-dimensional classical characterization of
`H²(0, π)`: a `C¹` representative whose first derivative is absolutely
continuous and whose a.e. second derivative is square-integrable.  Absolute
continuity of the representative is recorded explicitly for direct use of
Mathlib's integration-by-parts theorem. -/
def apm_m98a05_IsH2 (w : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 w (Icc 0 Real.pi) ∧
  AbsolutelyContinuousOnInterval w 0 Real.pi ∧
  AbsolutelyContinuousOnInterval (deriv w) 0 Real.pi ∧
  MemLp (deriv (deriv w)) 2 (volume.restrict (Ioo 0 Real.pi))

def apm_m98a05_IsSolution (ε : ℝ) (w : ℝ → ℝ) : Prop :=
  apm_m98a05_IsH2 w ∧ w 0 = 0 ∧ w Real.pi = 0 ∧
  ∀ᵐ t ∂volume, t ∈ Ioc 0 Real.pi →
    deriv (deriv w) t = w t + ε * (w t) ^ 2

lemma apm_m98a05_zero_solution (ε : ℝ) :
    apm_m98a05_IsSolution ε (fun _ ↦ 0) := by
  refine ⟨⟨contDiffOn_const, ?_, ?_, ?_⟩, rfl, rfl, ?_⟩
  · exact (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  · simpa using
      (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  · simp
  · simp

lemma apm_m98a05_small_solution_eq_zero (ε : ℝ) (w : ℝ → ℝ)
    (hw : apm_m98a05_IsSolution ε w)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) Real.pi, |ε| * |w t| < 1) :
    ∀ t ∈ Icc (0 : ℝ) Real.pi, w t = 0 := by
  rcases hw with ⟨⟨hwC1, hwAC, hdwAC, _⟩, hw0, hwpi, heq⟩
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hparts := hwAC.integral_mul_deriv_eq_deriv_mul hdwAC
  have heqI : (∫ t in (0 : ℝ)..Real.pi, w t * deriv (deriv w) t) =
      ∫ t in (0 : ℝ)..Real.pi, w t * (w t + ε * (w t) ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [heq] with t ht htu
    have htIoc : t ∈ Ioc (0 : ℝ) Real.pi := by
      rw [uIoc_of_le hpi] at htu
      exact htu
    rw [ht htIoc]
  have henergy : ∫ t in (0 : ℝ)..Real.pi,
      (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t) = 0 := by
    calc
      (∫ t in (0 : ℝ)..Real.pi,
          (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t)) =
          (∫ t in (0 : ℝ)..Real.pi, (deriv w t) ^ 2) +
          ∫ t in (0 : ℝ)..Real.pi, w t * (w t + ε * (w t) ^ 2) := by
            rw [intervalIntegral.integral_add]
            congr 1
            apply intervalIntegral.integral_congr
            intro t _
            ring
            · exact (hdwAC.continuousOn.pow 2).intervalIntegrable
            · exact (((hwAC.continuousOn.pow 2).mul
                (continuousOn_const.add (hwAC.continuousOn.const_mul ε))).intervalIntegrable)
      _ = (∫ t in (0 : ℝ)..Real.pi, (deriv w t) ^ 2) +
          ∫ t in (0 : ℝ)..Real.pi, w t * deriv (deriv w) t := by rw [heqI]
      _ = 0 := by rw [hparts, hw0, hwpi]; simp [pow_two]
  have hnonneg : ∀ t ∈ Icc (0 : ℝ) Real.pi,
      0 ≤ (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t) := by
    intro t ht
    have hs := hsmall t ht
    have hfactor : 0 < 1 + ε * w t := by
      have : -1 < ε * w t := by
        calc -1 < -(|ε| * |w t|) := by linarith
             _ = -|ε * w t| := by rw [abs_mul]
             _ ≤ ε * w t := neg_abs_le (ε * w t)
      linarith
    positivity
  have hint : IntervalIntegrable
      (fun t ↦ (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t)) volume 0 Real.pi := by
    exact ((hdwAC.continuousOn.pow 2).intervalIntegrable).add
      (((hwAC.continuousOn.pow 2).mul
        (continuousOn_const.add (hwAC.continuousOn.const_mul ε))).intervalIntegrable)
  have hae_zero : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) Real.pi),
      (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t) = 0 := by
    have hnonneg_ae : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) Real.pi ∪ Ioc Real.pi 0)]
        (fun t ↦ (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t)) := by
      change ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) Real.pi ∪ Ioc Real.pi 0),
        0 ≤ (deriv w t) ^ 2 + (w t) ^ 2 * (1 + ε * w t)
      rw [ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioc)]
      exact Filter.Eventually.of_forall fun t ht ↦ by
        simp only [mem_union, mem_Ioc] at ht
        have himpossible : ¬(Real.pi < t ∧ t ≤ 0) := by
          intro h
          linarith [Real.pi_pos]
        exact hnonneg t (Ioc_subset_Icc_self (ht.resolve_right himpossible))
    have hz := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnonneg_ae hint).1 henergy
    simpa [hpi] using hz
  have hderiv_zero : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) Real.pi → deriv w t = 0 := by
    rw [uIcc_of_le hpi]
    have hne : ∀ᵐ (t : ℝ) ∂volume, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_iff' measurableSet_Ioc |>.1 hae_zero,
      hne] with t ht ht0
    intro htIcc
    have htIoc : t ∈ Ioc (0 : ℝ) Real.pi :=
      ⟨lt_of_le_of_ne htIcc.1 (Ne.symm ht0), htIcc.2⟩
    have hz := ht htIoc
    have hs := hsmall t htIcc
    have habs : |ε * w t| < 1 := by simpa [abs_mul] using hs
    have hfactor : 0 < 1 + ε * w t := by linarith [neg_abs_le (ε * w t)]
    have hterm : 0 ≤ (w t) ^ 2 * (1 + ε * w t) := mul_nonneg (sq_nonneg _) hfactor.le
    nlinarith [sq_nonneg (deriv w t)]
  obtain ⟨C, hc⟩ := hwAC.const_of_ae_hasDerivAt_zero
    (by filter_upwards [hwAC.ae_differentiableAt, hderiv_zero] with x hx hz hmem
        simpa [hz hmem] using (hx hmem).hasDerivAt)
  intro t ht
  rw [hc t (by simpa [uIcc_of_le hpi] using ht),
    ← hc 0 (by simp [hpi]), hw0]

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
    (A : X →L[ℝ] Z) (hH : ContDiffAt ℝ 1 H (x₀, p₀)) (hzero : H (x₀, p₀) = 0)
    (hA : HasFDerivAt (fun x ↦ H (x, p₀)) A x₀)
    (he : ∃ e : X ≃L[ℝ] Z, (e : X →L[ℝ] Z) = A) :
    apm_m98a05_IFTConclusion H x₀ p₀ := by
  let Q : P × X → Z := fun q ↦ H (q.2, q.1)
  have hc : ContDiffAt ℝ 1 Q (p₀, x₀) :=
    ContDiffAt.comp (p₀, x₀) hH (contDiff_snd.prodMk contDiff_fst).contDiffAt
  have hQR : HasFDerivAt (fun x : X ↦ Q (p₀, x))
      ((fderiv ℝ Q (p₀, x₀)).comp (ContinuousLinearMap.inr ℝ P X)) x₀ := by
    have hd := (hc.differentiableAt (by norm_num)).hasFDerivAt
    simpa [Function.comp_def] using hd.comp x₀ (hasFDerivAt_prodMk_right p₀ x₀)
  have hpart : (fderiv ℝ Q (p₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ P X) = A := by
    exact hQR.unique (by simpa [Q] using hA)
  obtain ⟨e, heA⟩ := he
  have hi : ((fderiv ℝ Q (p₀, x₀)).comp
      (ContinuousLinearMap.inr ℝ P X)).IsInvertible := by
    rw [hpart, ← heA]
    exact ContinuousLinearMap.isInvertible_equiv
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

/-- The reformed three-part problem: (a) the Banach-space implicit-function
theorem; (b) its perturbative application with the correct partial derivative;
and (c) the zero Dirichlet branch together with an elementary
local-uniqueness estimate supplied by the energy identity. -/
theorem apm_m98a05 :
    (∀ (X P Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [CompleteSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
      [CompleteSpace P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      [CompleteSpace Z] (H : X × P → Z) (x₀ : X) (p₀ : P)
      (A : X →L[ℝ] Z), ContDiffAt ℝ 1 H (x₀, p₀) → H (x₀, p₀) = 0 →
      HasFDerivAt (fun x ↦ H (x, p₀)) A x₀ →
      (∃ e : X ≃L[ℝ] Z, (e : X →L[ℝ] Z) = A) →
      apm_m98a05_IFTConclusion H x₀ p₀) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [CompleteSpace Y] (F G : X → Y) (x₀ : X) (ε₀ : ℝ)
      (A B : X →L[ℝ] Y), ContDiff ℝ 1 F → ContDiff ℝ 1 G →
      HasFDerivAt F A x₀ → HasFDerivAt G B x₀ → F x₀ + ε₀ • G x₀ = 0 →
      (∃ e : X ≃L[ℝ] Y, (e : X →L[ℝ] Y) = A + ε₀ • B) →
      apm_m98a05_IFTConclusion (fun q : X × ℝ ↦ F q.1 + q.2 • G q.1) x₀ ε₀) ∧
    (∀ ε : ℝ, apm_m98a05_IsSolution ε (fun _ ↦ 0)) ∧
    (∀ (ε : ℝ) (w : ℝ → ℝ), apm_m98a05_IsSolution ε w →
      (∀ t ∈ Icc (0 : ℝ) Real.pi, |ε| * |w t| < 1) →
      ∀ t ∈ Icc (0 : ℝ) Real.pi, w t = 0) ∧
    (∀ (ε : ℝ) (w : ℝ → ℝ), |ε| < 1 → apm_m98a05_IsSolution ε w →
      (∀ t ∈ Icc (0 : ℝ) Real.pi, |w t| < 1) →
      ∀ t ∈ Icc (0 : ℝ) Real.pi, w t = 0) := by
  refine ⟨?_, ?_, apm_m98a05_zero_solution, apm_m98a05_small_solution_eq_zero, ?_⟩
  · intro X P Z _ _ _ _ _ _ _ _ _ H x₀ p₀ A hH hzero hA he
    exact apm_m98a05_ift X P Z H x₀ p₀ A hH hzero hA he
  · intro X Y _ _ _ _ _ _ F G x₀ ε₀ A B hF hG hFA hGB hzero he
    let H : X × ℝ → Y := fun q ↦ F q.1 + q.2 • G q.1
    have hH : ContDiff ℝ 1 H := by
      dsimp [H]
      fun_prop
    have hpartial : HasFDerivAt (fun x ↦ H (x, ε₀)) (A + ε₀ • B) x₀ := by
      simpa [H] using hFA.add (hGB.const_smul ε₀)
    exact apm_m98a05_ift X ℝ Y H x₀ ε₀ (A + ε₀ • B) hH.contDiffAt hzero hpartial he
  · intro ε w hε hw hsmall
    apply apm_m98a05_small_solution_eq_zero ε w hw
    intro t ht
    have he0 : 0 ≤ |ε| := abs_nonneg _
    have hw0 : 0 ≤ |w t| := abs_nonneg _
    nlinarith [hsmall t ht]

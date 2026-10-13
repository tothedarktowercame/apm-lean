import Mathlib

noncomputable section

open scoped Manifold

/-! The repaired definition requires genuine smoothness on each closed member
of a finite subdivision.  This rules out derivatives with non-integrable
oscillatory singularities at the break points. -/

def apm_t96a08_IsPiecewiseSmoothPath
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (γ : ℝ → M) : Prop :=
  Continuous γ ∧
    ∃ (n : ℕ) (cuts : Fin (n + 1) → ℝ),
      StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) γ
        (Set.Icc (cuts i.castSucc) (cuts i.succ))

def apm_t96a08_LineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (γ : ℝ → M) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    ω (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)

/-- The path operation needed by the fundamental theorem, separated from all
chart calculations. -/
def apm_t96A08_HasAdditiveConcatenation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ gamma delta : ℝ → M,
    apm_t96a08_IsPiecewiseSmoothPath I gamma →
    apm_t96a08_IsPiecewiseSmoothPath I delta →
    gamma 1 = delta 0 →
    ∃ eta : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I eta ∧
      eta 0 = gamma 0 ∧ eta 1 = delta 1 ∧
      apm_t96a08_LineIntegral I omega eta =
        apm_t96a08_LineIntegral I omega gamma +
          apm_t96a08_LineIntegral I omega delta

/-- The local output of the chart-linear-segment calculation.  Keeping this
as a proposition makes the analytic seat independent of path concatenation. -/
def apm_t96A08_HasLocalRadialPrimitives
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ g : M → ℝ,
      HasMFDerivAt I 𝓘(ℝ, ℝ) g x (omega x) ∧
      ∀ z ∈ U, ∃ delta : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I delta ∧
        delta 0 = x ∧ delta 1 = z ∧
        g z - g x = apm_t96a08_LineIntegral I omega delta

/-- Two-speed concatenation: `gamma (2 t)` for `t ≤ 1/2`, then `delta (2 t - 1)`. -/
def apm_t96A08_concat {M : Type*} (gamma delta : ℝ → M) : ℝ → M :=
  fun t => if t ≤ (1 / 2 : ℝ) then gamma (2 * t) else delta (2 * t - 1)

/-- Seat: the concatenation of two repaired piecewise-smooth paths with
`gamma 1 = delta 0` is one (continuity by the matching endpoint; cut points
`cutsγ i / 2` followed by `(1 + cutsδ j) / 2`, dropping the duplicated `1/2`;
on each piece the path is an affine reparametrisation of a smooth piece). -/
theorem apm_t96A08_concat_piecewiseSmooth
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (gamma delta : ℝ → M)
    (hgamma : apm_t96a08_IsPiecewiseSmoothPath I gamma)
    (hdelta : apm_t96a08_IsPiecewiseSmoothPath I delta)
    (hend : gamma 1 = delta 0) :
    apm_t96a08_IsPiecewiseSmoothPath I (apm_t96A08_concat gamma delta) := by
  rcases hgamma with ⟨hγc, nγ, cγ, hγmono, hγzero, hγone, hγsmooth⟩
  rcases hdelta with ⟨hδc, nδ, cδ, hδmono, hδzero, hδone, hδsmooth⟩
  have hnγ : 0 < nγ := by
    by_contra h
    have hn : nγ = 0 := by omega
    subst nγ
    have he : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    rw [he] at hγzero
    linarith
  have hnδ : 0 < nδ := by
    by_contra h
    have hn : nδ = 0 := by omega
    subst nδ
    have he : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    rw [he] at hδzero
    linarith
  let cuts : Fin (nγ + nδ + 1) → ℝ := fun i ↦
    if h : i.val ≤ nγ then cγ ⟨i.val, by omega⟩ / 2
    else (1 + cδ ⟨i.val - nγ, by omega⟩) / 2
  have hcont : Continuous (apm_t96A08_concat gamma delta) := by
    apply Continuous.if_le
    · exact hγc.comp (continuous_const.mul continuous_id)
    · exact hδc.comp ((continuous_const.mul continuous_id).sub continuous_const)
    · exact continuous_id
    · exact continuous_const
    · intro t ht
      have ht' : t = (1 / 2 : ℝ) := by linarith
      subst t
      simpa [hend]
  refine ⟨hcont, nγ + nδ, cuts, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val ≤ nγ
    · by_cases hj : j.val ≤ nγ
      · simp only [cuts, dif_pos hi, dif_pos hj]
        exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
          (hγmono hij)
      · simp only [cuts, dif_pos hi, dif_neg hj]
        have hleft : cγ ⟨i.val, by omega⟩ ≤ 1 := by
          rw [← hγone]
          apply hγmono.monotone
          simpa using hi
        have hright : 0 < cδ ⟨j.val - nγ, by omega⟩ := by
          rw [← hδzero]
          apply hδmono
          change 0 < j.val - nγ
          omega
        linarith
    · have hj : ¬j.val ≤ nγ := by omega
      simp only [cuts, dif_neg hi, dif_neg hj]
      have hv : i.val - nγ < j.val - nγ := by omega
      have hc : cδ ⟨i.val - nγ, by omega⟩ < cδ ⟨j.val - nγ, by omega⟩ :=
        hδmono hv
      linarith
  · simp [cuts, hγzero]
  · have he : (⟨nδ, by omega⟩ : Fin (nδ + 1)) = Fin.last nδ := by ext; simp
    simp [cuts, hnδ.ne', he, hδone]
  · intro i
    by_cases hi : i.val < nγ
    · have hics : (i.castSucc : Fin (nγ + nδ + 1)).val ≤ nγ := by simp; omega
      have his : (i.succ : Fin (nγ + nδ + 1)).val ≤ nγ := by simp; omega
      change i.val ≤ nγ at hics
      change i.val + 1 ≤ nγ at his
      have heq : Set.Icc (cuts i.castSucc) (cuts i.succ) ⊆
          (fun t : ℝ ↦ 2 * t) ⁻¹' Set.Icc (cγ ⟨i.val, by omega⟩)
            (cγ ⟨i.val + 1, by omega⟩) := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_Icc] at ht ⊢
        rw [show cuts i.castSucc = cγ ⟨i.val, by omega⟩ / 2 by simp [cuts, hics],
          show cuts i.succ = cγ ⟨i.val + 1, by omega⟩ / 2 by simp [cuts, his]] at ht
        constructor <;> linarith
      have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ ↦ 2 * t) := by
        exact contMDiff_const.mul contMDiff_id
      have hc := (hγsmooth ⟨i.val, hi⟩).comp haff.contMDiffOn heq
      apply hc.congr
      intro t ht
      have htle : t ≤ (2 : ℝ)⁻¹ := by
        have := ht.2
        rw [show cuts i.succ = cγ ⟨i.val + 1, by omega⟩ / 2 by simp [cuts, his]] at this
        have hcγ : cγ ⟨i.val + 1, by omega⟩ ≤ 1 := by
          rw [← hγone]
          apply hγmono.monotone
          change i.val + 1 ≤ nγ
          omega
        norm_num at this ⊢
        linarith
      have hp : t ≤ (1 / 2 : ℝ) := by norm_num [one_div] at htle ⊢; exact htle
      simp only [apm_t96A08_concat, if_pos hp, Function.comp_apply]
    · have his : ¬(i.succ : Fin (nγ + nδ + 1)).val ≤ nγ := by simp; omega
      change ¬i.val + 1 ≤ nγ at his
      have hil : i.val < nγ + nδ := i.isLt
      let k : Fin nδ := ⟨i.val - nγ, by omega⟩
      have hcutleft : cuts i.castSucc = (1 + cδ ⟨i.val - nγ, by omega⟩) / 2 := by
        by_cases he : i.val ≤ nγ
        · have hie : i.val = nγ := by omega
          have hefin : (⟨nγ, by omega⟩ : Fin (nγ + 1)) = Fin.last nγ := by ext; simp
          simp [cuts, he, hie, hefin, hγone, hδzero]
        · simp [cuts, he]
      have heq : Set.Icc (cuts i.castSucc) (cuts i.succ) ⊆
          (fun t : ℝ ↦ 2 * t - 1) ⁻¹' Set.Icc (cδ k.castSucc) (cδ k.succ) := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_Icc] at ht ⊢
        rw [hcutleft,
          show cuts i.succ = (1 + cδ ⟨i.val + 1 - nγ, by omega⟩) / 2 by
              simp [cuts, his]] at ht
        change cδ ⟨i.val - nγ, by omega⟩ ≤ 2 * t - 1 ∧
          2 * t - 1 ≤ cδ ⟨i.val - nγ + 1, by omega⟩
        have he : i.val + 1 - nγ = i.val - nγ + 1 := by omega
        simp [he] at ht
        constructor <;> linarith
      have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ ↦ 2 * t - 1) := by
        exact (contMDiff_const.mul contMDiff_id).sub contMDiff_const
      have hc := (hδsmooth k).comp haff.contMDiffOn heq
      apply hc.congr
      intro t ht
      by_cases hp : t ≤ (1 / 2 : ℝ)
      · have hlow := ht.1
        rw [hcutleft] at hlow
        have hcδ : 0 ≤ cδ ⟨i.val - nγ, by omega⟩ := by
          rw [← hδzero]
          apply hδmono.monotone
          change 0 ≤ i.val - nγ
          omega
        have hcz : cδ ⟨i.val - nγ, by omega⟩ = 0 := by linarith
        let z : Fin nδ := ⟨0, hnδ⟩
        have hidx : (⟨i.val - nγ, by omega⟩ : Fin (nδ + 1)) = 0 := by
          apply hδmono.injective
          simpa [hδzero] using hcz
        have kval : i.val - nγ = 0 := by
          simpa using congrArg Fin.val hidx
        have hkzero : k = z := by
          apply Fin.ext
          simp [k, z, kval]
        have htval : t = 1 / 2 := by linarith
        subst t
        norm_num [apm_t96A08_concat, hend]
      · simp only [apm_t96A08_concat, if_neg hp, Function.comp_apply]

lemma apm_t96A08_concat_lineIntegral_aux_left_substitution (f : ℝ → ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(1 / 2 : ℝ), (2 : ℝ) * f (2 * t)) =
      ∫ s : ℝ in (0 : ℝ)..1, f s := by
  rw [intervalIntegral.integral_const_mul]
  change (2 : ℝ) • (∫ t : ℝ in (0 : ℝ)..(1 / 2 : ℝ), f (2 * t)) = _
  rw [intervalIntegral.smul_integral_comp_mul_left]
  norm_num

lemma apm_t96A08_concat_lineIntegral_aux_right_substitution (f : ℝ → ℝ) :
    (∫ t : ℝ in (1 / 2 : ℝ)..1, (2 : ℝ) * f (2 * t - 1)) =
      ∫ s : ℝ in (0 : ℝ)..1, f s := by
  rw [intervalIntegral.integral_const_mul]
  change (2 : ℝ) • (∫ t : ℝ in (1 / 2 : ℝ)..1, f (2 * t - 1)) = _
  rw [intervalIntegral.smul_integral_comp_mul_left
    (f := fun s : ℝ ↦ f (s - 1))]
  rw [intervalIntegral.integral_comp_sub_right]
  norm_num

/-- Seat: the line-integral integrand of a repaired piecewise-smooth path is
interval integrable on `[0, 1]` (on each closed smooth piece the derivative
within the piece is continuous and agrees with `mfderiv` in the interior; the
cut points are null; `homega_smooth` makes the integrand continuous there). -/
theorem apm_t96A08_lineIntegrand_intervalIntegrable
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (gamma : ℝ → M) (hgamma : apm_t96a08_IsPiecewiseSmoothPath I gamma) :
    IntervalIntegrable
      (fun t : ℝ => omega (gamma t) ((mfderiv 𝓘(ℝ, ℝ) I gamma t) 1))
      MeasureTheory.volume 0 1 := by
  rcases hgamma with ⟨hγcont, n, cuts, hmono, hzero, hone, hsmooth⟩
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have he : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    rw [he] at hzero
    linarith
  let F : ℝ → ℝ := fun t ↦
    omega (gamma t) ((mfderiv 𝓘(ℝ, ℝ) I gamma t) 1)
  have hpiece : ∀ i : Fin n,
      MeasureTheory.IntegrableOn F
        (Set.Icc (cuts i.castSucc) (cuts i.succ)) := by
    intro i
    let s : Set ℝ := Set.Icc (cuts i.castSucc) (cuts i.succ)
    let V : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ := fun t ↦ ⟨t, 1⟩
    let G : ℝ → ℝ := fun t ↦
      (fun v : TangentBundle I M ↦ omega v.1 v.2)
        (tangentMapWithin 𝓘(ℝ, ℝ) I gamma s (V t))
    have hab : cuts i.castSucc < cuts i.succ := hmono (by simp)
    have hus : UniqueMDiffOn 𝓘(ℝ, ℝ) s :=
      (uniqueDiffOn_Icc hab).uniqueMDiffOn
    have hV : Continuous V := by
      change Continuous
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm ∘
          fun t : ℝ ↦ (t, (1 : ℝ)))
      exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ, ℝ) I gamma s)
        (Bundle.TotalSpace.proj ⁻¹' s) :=
      (hsmooth i).continuousOn_tangentMapWithin (by simp) hus
    have hGs : ContinuousOn G s := by
      apply homega_smooth.continuous.comp_continuousOn
      apply htan.comp hV.continuousOn
      intro t ht
      exact ht
    have hGint : MeasureTheory.IntegrableOn G s := by
      exact hGs.integrableOn_Icc
    apply hGint.congr
    change G =ᵐ[MeasureTheory.volume.restrict
      (Set.Icc (cuts i.castSucc) (cuts i.succ))] F
    change ∀ᵐ t ∂MeasureTheory.volume.restrict
      (Set.Icc (cuts i.castSucc) (cuts i.succ)), G t = F t
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.volume.ae_ne (cuts i.castSucc),
      MeasureTheory.volume.ae_ne (cuts i.succ)] with t htl htr
    intro ht
    have htio : t ∈ Set.Ioo (cuts i.castSucc) (cuts i.succ) :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
    have hnhds : s ∈ nhds t := Icc_mem_nhds htio.1 htio.2
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t :=
      ((hsmooth i t ht).contMDiffAt hnhds).mdifferentiableAt (by simp)
    simp only [F, G, V, tangentMapWithin_proj, tangentMapWithin_snd]
    rw [mfderivWithin_eq_mfderiv (hus t ht) hmd]
    rfl
  have hp : ∀ k : ℕ, ∀ hk : k ≤ n,
      IntervalIntegrable F MeasureTheory.volume (cuts 0) (cuts ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp [intervalIntegrable_iff]
    | succ k ih =>
        intro hk
        have hkn : k < n := by omega
        have hprev := ih (by omega)
        have hnext : IntervalIntegrable F MeasureTheory.volume
            (cuts ⟨k, by omega⟩) (cuts ⟨k + 1, by omega⟩) := by
          apply (intervalIntegrable_iff_integrableOn_Icc_of_le
            (hmono.monotone (by simp))).2
          simpa using hpiece ⟨k, hkn⟩
        exact hprev.trans hnext
  have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := by ext; simp
  simpa only [F, hzero, hlast, hone] using hp n le_rfl

/-- Seat: on `(0, 1/2)` the concatenation agrees with `gamma (2 ·)` near `t`,
so the chain rule doubles the velocity (both sides vanish where `gamma` is not
differentiable). -/
theorem apm_t96A08_concat_integrand_left
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (gamma delta : ℝ → M) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    omega (apm_t96A08_concat gamma delta t)
        ((mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t) 1) =
      2 * omega (gamma (2 * t)) ((mfderiv 𝓘(ℝ, ℝ) I gamma (2 * t)) 1) := by
  have ht12 : t < (1 / 2 : ℝ) := ht.2
  let s : ℝ → ℝ := fun u ↦ 2 * u
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s t := by
    rw [mdifferentiableAt_iff_differentiableAt]
    fun_prop
  have hsder : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s t) 1 =
      (2 : ℝ) • (1 : TangentSpace 𝓘(ℝ, ℝ) (s t)) := by
    rw [mfderiv_eq_fderiv]
    rw [HasFDerivAt.fderiv (hasDerivAt_const_mul (2 : ℝ) (x := t))]
    apply (NormedSpace.fromTangentSpace (s t)).injective
    unfold NormedSpace.fromTangentSpace TangentSpace
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  have hlocal : apm_t96A08_concat gamma delta =ᶠ[nhds t] gamma ∘ s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    simp only [apm_t96A08_concat, Function.comp_apply, s]
    rw [if_pos]
    linarith [hu.2]
  by_cases hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (s t)
  · have hcomp := mfderiv_comp t hgamma hs
    have hderiv : mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t =
        (mfderiv 𝓘(ℝ, ℝ) I gamma (s t)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s t) := by
      rw [hlocal.mfderiv_eq]
      exact hcomp
    rw [hderiv]
    change omega (apm_t96A08_concat gamma delta t)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma (s t))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s t) 1)) = _
    rw [hsder, map_smul]
    rw [show apm_t96A08_concat gamma delta t = gamma (2 * t) by
      simp only [apm_t96A08_concat, if_pos (le_of_lt ht12)]]
    simp [s, map_smul, smul_eq_mul]
  · have hgzero : mfderiv 𝓘(ℝ, ℝ) I gamma (s t) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hgamma
    have hconcat : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) I
        (apm_t96A08_concat gamma delta) t := by
      intro hc
      have hc' : MDifferentiableAt 𝓘(ℝ, ℝ) I (gamma ∘ s) t :=
        hlocal.mdifferentiableAt_iff.mp hc
      let r : ℝ → ℝ := fun u ↦ u / 2
      have hr : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) r (s t) := by
        rw [mdifferentiableAt_iff_differentiableAt]
        fun_prop
      have hback := hc'.comp_of_eq (s t) hr (by simp [s, r])
      have heq : (gamma ∘ s) ∘ r = gamma := by
        funext u
        simp [s, r]
        ring
      rw [heq] at hback
      exact hgamma hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hconcat, hgzero]
    simp only [ContinuousLinearMap.zero_apply, map_zero, mul_zero]

/-- Seat: on `(1/2, 1)` the concatenation agrees with `delta (2 · - 1)` near `t`. -/
theorem apm_t96A08_concat_integrand_right
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (gamma delta : ℝ → M) (t : ℝ) (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    omega (apm_t96A08_concat gamma delta t)
        ((mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t) 1) =
      2 * omega (delta (2 * t - 1)) ((mfderiv 𝓘(ℝ, ℝ) I delta (2 * t - 1)) 1) := by
  let phi : ℝ → ℝ := fun s ↦ 2 * s - 1
  have hphi : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) phi t := by
    have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) phi := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    exact hp.mdifferentiableAt (by simp)
  have hlocal : apm_t96A08_concat gamma delta =ᶠ[nhds t] delta ∘ phi := by
    filter_upwards [eventually_gt_nhds ht.1] with s hs
    simp only [apm_t96A08_concat, Function.comp_apply]
    rw [if_neg]
    linarith
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℝ) I delta (phi t)
  · have hderiv := hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    rw [show apm_t96A08_concat gamma delta t = delta (phi t) by
      rw [apm_t96A08_concat, if_neg (not_le.mpr ht.1)]]
    rw [hderiv, mfderiv_comp t hd hphi]
    have hphi_deriv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) phi t 1 = (2 : ℝ) := by
      rw [mfderiv_eq_fderiv]
      have hh : fderiv ℝ phi t = (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
        simpa [phi] using
          HasFDerivAt.fderiv (hasFDerivAt_id t |>.const_mul (2 : ℝ) |>.sub_const (1 : ℝ))
      simpa using congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hh
    rw [ContinuousLinearMap.comp_apply, hphi_deriv]
    have htwo : (mfderiv 𝓘(ℝ, ℝ) I delta (phi t)) (2 : ℝ) =
        (2 : ℝ) • (mfderiv 𝓘(ℝ, ℝ) I delta (phi t)) 1 := by
      conv_lhs => rw [show (2 : ℝ) = (2 : ℝ) • (1 : ℝ) by norm_num]
      exact (mfderiv 𝓘(ℝ, ℝ) I delta (phi t)).map_smul (2 : ℝ) (1 : ℝ)
    rw [htwo, map_smul]
    simp [phi]
  · have hcomp : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) I (delta ∘ phi) t := by
      intro hc
      let psi : ℝ → ℝ := fun s ↦ (s + 1) / 2
      have hpsi : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) psi (phi t) := by
        have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) psi := by
          rw [contMDiff_iff_contDiff]
          fun_prop
        exact hp.mdifferentiableAt (by simp)
      have hi : delta =ᶠ[nhds (phi t)] (delta ∘ phi) ∘ psi := by
        filter_upwards with s
        congr 1
        simp only [Function.comp_apply, phi, psi]
        ring
      have hpt : psi (phi t) = t := by simp [psi, phi]
      have hc' : MDifferentiableAt 𝓘(ℝ, ℝ) I (delta ∘ phi) (psi (phi t)) := by
        rwa [hpt]
      exact hd (hi.mdifferentiableAt_iff.mpr (hc'.comp (phi t) hpsi))
    have hc0 : mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t = 0 := by
      rw [hlocal.mfderiv_eq]
      exact mfderiv_zero_of_not_mdifferentiableAt hcomp
    have hd0 : mfderiv 𝓘(ℝ, ℝ) I delta (phi t) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hd
    rw [hc0, hd0]
    rw [show apm_t96A08_concat gamma delta t = delta (phi t) by
      rw [apm_t96A08_concat, if_neg (not_le.mpr ht.1)]]
    simp [phi]

/-- Seat (assembly from explicit hypotheses): split `∫₀¹` at `1/2`, replace the
integrand a.e. on each half (`intervalIntegral.integral_congr_ae`, endpoints
null), and apply the two substitution helpers above.  Integrability of each half
follows from `hγ`, `hδ` through the same a.e. identities. -/
theorem apm_t96A08_concat_lineIntegral_of_pieces
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (gamma delta : ℝ → M)
    (hγ : IntervalIntegrable
      (fun t : ℝ => omega (gamma t) ((mfderiv 𝓘(ℝ, ℝ) I gamma t) 1))
      MeasureTheory.volume 0 1)
    (hδ : IntervalIntegrable
      (fun t : ℝ => omega (delta t) ((mfderiv 𝓘(ℝ, ℝ) I delta t) 1))
      MeasureTheory.volume 0 1)
    (hleft : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2),
      omega (apm_t96A08_concat gamma delta t)
          ((mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t) 1) =
        2 * omega (gamma (2 * t)) ((mfderiv 𝓘(ℝ, ℝ) I gamma (2 * t)) 1))
    (hright : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 1,
      omega (apm_t96A08_concat gamma delta t)
          ((mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t) 1) =
        2 * omega (delta (2 * t - 1)) ((mfderiv 𝓘(ℝ, ℝ) I delta (2 * t - 1)) 1)) :
    apm_t96a08_LineIntegral I omega (apm_t96A08_concat gamma delta) =
      apm_t96a08_LineIntegral I omega gamma +
        apm_t96a08_LineIntegral I omega delta := by
  let F : ℝ → ℝ := fun t ↦
    omega (apm_t96A08_concat gamma delta t)
      ((mfderiv 𝓘(ℝ, ℝ) I (apm_t96A08_concat gamma delta) t) 1)
  let G : ℝ → ℝ := fun t ↦
    2 * omega (gamma (2 * t)) ((mfderiv 𝓘(ℝ, ℝ) I gamma (2 * t)) 1)
  let H : ℝ → ℝ := fun t ↦
    2 * omega (delta (2 * t - 1))
      ((mfderiv 𝓘(ℝ, ℝ) I delta (2 * t - 1)) 1)
  have hFG : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (0 : ℝ) (1 / 2) → F t = G t := by
    filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ),
      MeasureTheory.volume.ae_ne (1 / 2 : ℝ)] with t ht0 hthalf ht
    apply hleft t
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    exact ⟨ht.1, lt_of_le_of_ne ht.2 hthalf⟩
  have hFH : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (1 / 2 : ℝ) 1 → F t = H t := by
    filter_upwards [MeasureTheory.volume.ae_ne (1 / 2 : ℝ),
      MeasureTheory.volume.ae_ne (1 : ℝ)] with t hthalf ht1 ht
    apply hright t
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    exact ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  have hGint : IntervalIntegrable G MeasureTheory.volume 0 (1 / 2) := by
    apply IntervalIntegrable.const_mul
    simpa [G] using hγ.comp_mul_left (c := (2 : ℝ))
  have hHbase : IntervalIntegrable
      (fun t : ℝ ↦ omega (delta (t - 1))
        ((mfderiv 𝓘(ℝ, ℝ) I delta (t - 1)) 1))
      MeasureTheory.volume 1 2 := by
    convert hδ.comp_add_right (-1) using 1 <;> norm_num [sub_eq_add_neg]
  have hHint : IntervalIntegrable H MeasureTheory.volume (1 / 2) 1 := by
    apply IntervalIntegrable.const_mul
    simpa [H, mul_sub] using hHbase.comp_mul_left (c := (2 : ℝ))
  have hFleft : IntervalIntegrable F MeasureTheory.volume 0 (1 / 2) :=
    hGint.congr_ae ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2
      (hFG.mono fun _ ht hmem ↦ (ht hmem).symm))
  have hFright : IntervalIntegrable F MeasureTheory.volume (1 / 2) 1 :=
    hHint.congr_ae ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2
      (hFH.mono fun _ ht hmem ↦ (ht hmem).symm))
  change (∫ t : ℝ in (0 : ℝ)..1, F t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hFleft hFright,
    intervalIntegral.integral_congr_ae hFG,
    intervalIntegral.integral_congr_ae hFH]
  change (∫ t : ℝ in (0 : ℝ)..(1 / 2 : ℝ), G t) +
      (∫ t : ℝ in (1 / 2 : ℝ)..1, H t) = _
  rw [show (∫ t : ℝ in (0 : ℝ)..(1 / 2 : ℝ), G t) =
      ∫ t : ℝ in (0 : ℝ)..1,
        omega (gamma t) ((mfderiv 𝓘(ℝ, ℝ) I gamma t) 1) by
        simpa [G] using
          (apm_t96A08_concat_lineIntegral_aux_left_substitution
            (fun t : ℝ ↦ omega (gamma t) ((mfderiv 𝓘(ℝ, ℝ) I gamma t) 1)))]
  rw [show (∫ t : ℝ in (1 / 2 : ℝ)..1, H t) =
      ∫ t : ℝ in (0 : ℝ)..1,
        omega (delta t) ((mfderiv 𝓘(ℝ, ℝ) I delta t) 1) by
        simpa [H] using
          (apm_t96A08_concat_lineIntegral_aux_right_substitution
            (fun t : ℝ ↦ omega (delta t) ((mfderiv 𝓘(ℝ, ℝ) I delta t) 1)))]
  rfl

/-- The line integral is additive under concatenation (assembly). -/
theorem apm_t96A08_concat_lineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (gamma delta : ℝ → M)
    (hgamma : apm_t96a08_IsPiecewiseSmoothPath I gamma)
    (hdelta : apm_t96a08_IsPiecewiseSmoothPath I delta)
    (hend : gamma 1 = delta 0) :
    apm_t96a08_LineIntegral I omega (apm_t96A08_concat gamma delta) =
      apm_t96a08_LineIntegral I omega gamma +
        apm_t96a08_LineIntegral I omega delta :=
  apm_t96A08_concat_lineIntegral_of_pieces I omega gamma delta
    (apm_t96A08_lineIntegrand_intervalIntegrable I omega homega_smooth gamma hgamma)
    (apm_t96A08_lineIntegrand_intervalIntegrable I omega homega_smooth delta hdelta)
    (fun t ht => apm_t96A08_concat_integrand_left I omega gamma delta t ht)
    (fun t ht => apm_t96A08_concat_integrand_right I omega gamma delta t ht)

/-- Closed-piecewise-smooth paths can be concatenated, and the integral is
additive under the standard affine reparameterizations. -/
theorem apm_t96A08_piecewisePath_concat_additive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2)) :
    apm_t96A08_HasAdditiveConcatenation I omega := by
  intro gamma delta hgamma hdelta hend
  refine ⟨apm_t96A08_concat gamma delta,
    apm_t96A08_concat_piecewiseSmooth I gamma delta hgamma hdelta hend, ?_, ?_,
    apm_t96A08_concat_lineIntegral I omega homega_smooth gamma delta hgamma hdelta hend⟩
  · simp [apm_t96A08_concat]
  · norm_num [apm_t96A08_concat]

/-- In a sufficiently small convex chart, integration along the straight
coordinate segment gives a smooth local function whose derivative at the
centre is the prescribed one-form. -/
lemma apm_t96A08_chart_radial_primitive_aux_path_of_contMDiff
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) gamma) :
    apm_t96a08_IsPiecewiseSmoothPath I gamma := by
  refine ⟨hgamma.continuous, 1, fun i ↦ (i.val : ℝ), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · norm_num
  · norm_num
  · intro i
    exact hgamma.contMDiffOn

lemma apm_t96A08_chart_radial_primitive_aux_const_path
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (x : M) :
    apm_t96a08_IsPiecewiseSmoothPath I (fun _ : ℝ ↦ x) := by
  apply apm_t96A08_chart_radial_primitive_aux_path_of_contMDiff
  exact contMDiff_const

/-- A chart can be shrunk using an ambient convex set.  The intersection with
`range I` is essential at boundary points of a manifold with corners. -/
lemma apm_t96A08_chart_radial_primitive_chart_neighborhood
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] (x : M) :
    ∃ (U : Set M) (W : Set E), IsOpen U ∧ x ∈ U ∧ IsOpen W ∧
      Convex ℝ W ∧ (extChartAt I x x) ∈ W ∧
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target ∧
      U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W := by
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp
    (extChartAt_target_mem_nhdsWithin (I := I) x)
  let W : Set E := Metric.ball (extChartAt I x x) r
  let U : Set M :=
    (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W
  refine ⟨U, W, ?_, ?_, Metric.isOpen_ball, convex_ball _ _, ?_, ?_, rfl⟩
  · exact (continuousOn_extChartAt (I := I) x).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) x) Metric.isOpen_ball
  · exact ⟨mem_extChartAt_source (I := I) x, Metric.mem_ball_self hr⟩
  · exact Metric.mem_ball_self hr
  · exact hrsub

/-- Relative convexity in the chart produces the clamped radial paths.  This
seat only does chart and endpoint bookkeeping. -/
lemma apm_t96A08_chart_radial_primitive_radial_paths
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] (x : M) (U : Set M) (W : Set E)
    (hU : U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W)
    (hxW : extChartAt I x x ∈ W) (hWconv : Convex ℝ W)
    (hWtarget : W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target) :
    ∀ z ∈ U, ∃ delta : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I delta ∧ delta 0 = x ∧ delta 1 = z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        extChartAt I x (delta t) = extChartAt I x x +
          t • (extChartAt I x z - extChartAt I x x) := by
  intro z hzU
  have hxsource : x ∈ (extChartAt I x).source := by simp
  have hzsource : z ∈ (extChartAt I x).source := by
    rw [hU] at hzU
    exact hzU.1
  have hzW : extChartAt I x z ∈ W := by
    rw [hU] at hzU
    exact hzU.2
  have hxr : extChartAt I x x ∈ Set.range (I : E → E) :=
    (extChartAt_target_subset_range x) (PartialEquiv.map_source _ hxsource)
  have hzr : extChartAt I x z ∈ Set.range (I : E → E) :=
    (extChartAt_target_subset_range x) (PartialEquiv.map_source _ hzsource)
  let eta : ℝ → E := fun t ↦
    extChartAt I x x + t • (extChartAt I x z - extChartAt I x x)
  have heta_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      eta t ∈ W ∩ Set.range (I : E → E) := by
    intro t ht
    constructor
    · exact hWconv.add_smul_sub_mem hxW hzW ht
    · exact I.convex_range.add_smul_sub_mem hxr hzr ht
  have heta_target : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      eta t ∈ (extChartAt I x).target := fun t ht ↦ hWtarget (heta_mem t ht)
  let q : ℝ → E := fun t ↦ eta (Set.projIcc 0 1 zero_le_one t)
  have hq_target : ∀ t, q t ∈ (extChartAt I x).target := by
    intro t
    exact heta_target _ (Set.projIcc 0 1 zero_le_one t).property
  let delta : ℝ → M := fun t ↦ (extChartAt I x).symm (q t)
  have heta_cont : Continuous eta := by
    fun_prop
  have hq_cont : Continuous q :=
    heta_cont.comp (continuous_subtype_val.comp continuous_projIcc)
  have hdelta_cont : Continuous delta := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) x).continuousOn.comp_continuous
      hq_cont hq_target
  have heta_smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ E) ((⊤ : ℕ∞) : WithTop ℕ∞) eta := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hdelta_smooth : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) delta
      (Set.Icc (0 : ℝ) 1) := by
    have hg := (contMDiffOn_extChartAt_symm (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) x).comp
      heta_smooth.contMDiffOn (fun t ht ↦ heta_target t ht)
    apply hg.congr
    intro t ht
    simp [delta, q, Set.projIcc_of_mem zero_le_one ht]
  refine ⟨delta, ⟨hdelta_cont, 1, fun i ↦ (i.val : ℝ), ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · norm_num
  · norm_num
  · intro i
    simpa using hdelta_smooth
  · have hp : (Set.projIcc 0 1 zero_le_one (0 : ℝ) : ℝ) = 0 :=
      congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩)
    simpa only [delta, q, hp, eta, zero_smul, add_zero] using
      (extChartAt I x).left_inv hxsource
  · have hp : (Set.projIcc 0 1 zero_le_one (1 : ℝ) : ℝ) = 1 :=
      congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩)
    have he : eta 1 = extChartAt I x z := by
      simp only [eta, one_smul]
      abel
    simpa only [delta, q, hp, he] using
      (extChartAt I x).left_inv hzsource
  · intro t ht
    have := hq_target t
    simpa [delta] using PartialEquiv.map_target (extChartAt I x) this
  · intro t ht
    have hp : (Set.projIcc 0 1 zero_le_one t : ℝ) = t :=
      congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ht)
    simpa only [delta, q, hp, eta] using
      (extChartAt I x).right_inv (heta_target t ht)

/-- The coordinate expression of `omega` in the chart at `x`. -/
noncomputable def apm_t96A08_omegaCoord
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (x : M) : E → (E →L[ℝ] ℝ) :=
  fun y ↦ (omega ((extChartAt I x).symm y)).comp
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) y)

/-- Seat: the evaluation `(y, v) ↦ omegaCoord y v` is `C¹` on
`φ.target ×ˢ univ`: it is `homega_smooth` composed with the inverse of the
tangent-bundle chart at `x` (`(y, v) ↦ (φ.symm y, D φ.symm y v)`, smooth on the
chart target, cf. `contMDiffOn_extChartAt_symm`, tangent map of a smooth map). -/
theorem apm_t96A08_omegaCoord_eval_contDiffOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (x : M) :
    ContDiffOn ℝ 1 (fun p : E × E ↦ apm_t96A08_omegaCoord I omega x p.1 p.2)
      ((extChartAt I x).target ×ˢ Set.univ) := by
  let e : E × E → TangentBundle (modelWithCornersSelf ℝ E) E :=
    fun p ↦ ⟨p.1, p.2⟩
  let T : TangentBundle (modelWithCornersSelf ℝ E) E → TangentBundle I M :=
    tangentMapWithin (modelWithCornersSelf ℝ E) I (extChartAt I x).symm
      (extChartAt I x).target
  have hs : ContMDiffOn (modelWithCornersSelf ℝ E) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      (extChartAt I x).symm (extChartAt I x).target :=
    contMDiffOn_extChartAt_symm x
  have hT : ContMDiffOn (modelWithCornersSelf ℝ E).tangent I.tangent 1 T
      (Bundle.TotalSpace.proj ⁻¹' (extChartAt I x).target) :=
    hs.contMDiffOn_tangentMapWithin (by norm_cast)
      (uniqueDiffOn_extChartAt_target x).uniqueMDiffOn
  have he : ContMDiff (modelWithCornersSelf ℝ (E × E))
      (modelWithCornersSelf ℝ E).tangent ((⊤ : ℕ∞) : WithTop ℕ∞) e := by
    apply contMDiff_iff.2
    constructor
    · change Continuous
        ((tangentBundleModelSpaceHomeomorph (modelWithCornersSelf ℝ E)).symm ∘ id)
      exact (tangentBundleModelSpaceHomeomorph
        (modelWithCornersSelf ℝ E)).symm.continuous.comp continuous_id
    · intro p q
      apply contDiffOn_id.congr
      simp only [e, mfld_simps, Prod.mk.injEq]
  have hc : ContMDiffOn (modelWithCornersSelf ℝ (E × E))
      (modelWithCornersSelf ℝ ℝ) 1
      ((fun v : TangentBundle I M ↦ omega v.1 v.2) ∘ T ∘ e)
      ((extChartAt I x).target ×ˢ Set.univ) := by
    exact (homega_smooth.of_le (by simp)).comp_contMDiffOn
      (hT.comp (he.of_le (by simp)).contMDiffOn (fun p hp ↦ hp.1))
  rw [contMDiffOn_iff_contDiffOn] at hc
  apply hc.congr
  intro p hp
  simp only [Function.comp_apply, T, e, apm_t96A08_omegaCoord,
    tangentMapWithin_proj, tangentMapWithin_snd]
  rw [show mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I x).symm
      (Set.range I) p.1 = mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I x).symm (extChartAt I x).target p.1 by
    have hd := (hs p.1 hp.1).mdifferentiableWithinAt (by simp)
    exact hd.mfderivWithin_mono_of_mem_nhdsWithin
      (I.uniqueMDiffOn p.1 (extChartAt_target_subset_range x hp.1))
      (extChartAt_target_mem_nhdsWithin_of_mem hp.1)]
  rfl

/-- Seat (pure analysis): a family of continuous linear functionals whose
evaluation is jointly `C¹` on `S ×ˢ univ` is operator-norm continuous on `S`:
`L y` is the second partial derivative, i.e. `fderivWithin` of the evaluation at
`(y, 0)` composed with `inr`, and `fderivWithin` is continuous by
`ContDiffOn.continuousOn_fderivWithin` (needs `UniqueDiffOn (S ×ˢ univ)`). -/
theorem apm_t96A08_continuousOn_of_eval_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (L : E → (E →L[ℝ] ℝ)) (hS : UniqueDiffOn ℝ S)
    (hL : ContDiffOn ℝ 1 (fun p : E × E ↦ L p.1 p.2) (S ×ˢ Set.univ)) :
    ContinuousOn L S := by
  let F : E × E → ℝ := fun p ↦ L p.1 p.2
  let T : Set (E × E) := S ×ˢ Set.univ
  let j : E →L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E
  let D : E → (E →L[ℝ] ℝ) := fun y ↦
    (fderivWithin ℝ F T (y, 0)).comp j
  have hT : UniqueDiffOn ℝ T := hS.prod uniqueDiffOn_univ
  have hder : ContinuousOn (fderivWithin ℝ F T) T := by
    exact hL.continuousOn_fderivWithin hT (by norm_num)
  have hemb : ContinuousOn (fun y : E ↦ (y, (0 : E))) S :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hemb_maps : Set.MapsTo (fun y : E ↦ (y, (0 : E))) S T := by
    intro y hy
    exact ⟨hy, Set.mem_univ 0⟩
  have hD : ContinuousOn D S := by
    have hpre : ContinuousOn
        (fun y : E ↦ fderivWithin ℝ F T (y, 0)) S :=
      hder.comp hemb hemb_maps
    have hpost : Continuous
        (fun A : (E × E →L[ℝ] ℝ) ↦ A.comp j) := by
      fun_prop
    exact hpost.comp_continuousOn hpre
  apply hD.congr
  intro y hy
  apply ContinuousLinearMap.ext
  intro v
  have hdiff := (hL (y, 0) ⟨hy, Set.mem_univ 0⟩).differentiableWithinAt
    (by norm_num)
  have hj : HasFDerivAt (fun v : E ↦ (y, v)) j 0 := by
    simpa [j] using (hasFDerivAt_const (x := (0 : E)) y).prodMk
      (hasFDerivAt_id (x := (0 : E)))
  have hmap : Set.MapsTo (fun v : E ↦ (y, v)) Set.univ T := by
    intro v hv
    exact ⟨hy, Set.mem_univ v⟩
  have hc := hdiff.hasFDerivWithinAt.comp 0 hj.hasFDerivWithinAt hmap
  have hc' : HasFDerivWithinAt (fun v : E ↦ L y v)
      ((fderivWithin ℝ F T (y, 0)).comp j) Set.univ 0 := by
    simpa [F, Function.comp_def] using hc
  have hu : UniqueDiffOn ℝ (Set.univ : Set E) := uniqueDiffOn_univ
  have heq := hc'.fderivWithin (hu 0 (Set.mem_univ (0 : E)))
  have hlin : fderivWithin ℝ (fun v : E ↦ L y v) Set.univ 0 = L y := by
    simpa using (L y).hasFDerivAt.fderiv
  simpa [D] using congrArg (fun A : E →L[ℝ] ℝ ↦ A v)
    (heq.symm.trans hlin).symm

/-- Seat: the coordinate expression is continuous on `W ∩ range I` inside the
chart target (`homega_smooth` and smoothness of `(extChartAt I x).symm` within
`range I`; the tangent-bundle evaluation is continuous). -/
theorem apm_t96A08_omegaCoord_continuousOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (x : M) (W : Set E)
    (hWtarget : W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target) :
    ContinuousOn (apm_t96A08_omegaCoord I omega x) (W ∩ Set.range (I : E → E)) := by
  have hS : UniqueDiffOn ℝ (extChartAt I x).target := uniqueDiffOn_extChartAt_target x
  have hcont := apm_t96A08_continuousOn_of_eval_contDiffOn _ _ hS
    (apm_t96A08_omegaCoord_eval_contDiffOn I omega homega_smooth x)
  exact hcont.mono hWtarget

/-- Seat: the value at the centre (`(extChartAt I x).symm (extChartAt I x x) = x`). -/
theorem apm_t96A08_omegaCoord_centre
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (x : M) :
    apm_t96A08_omegaCoord I omega x (extChartAt I x x) = (omega x).comp
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
        (extChartAt I x x)) := by
  simp only [apm_t96A08_omegaCoord]
  rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  rfl

/-- Seat: along a chart-linear path the line integral is the coordinate
integral (chart chain rule on `(0, 1)`: `delta = φ.symm ∘ (affine)` there;
endpoints are null; `intervalIntegral.integral_congr_ae`). -/
theorem apm_t96A08_omegaCoord_lineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (x z : M) (delta : ℝ → M)
    (hdelta_source : ∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source)
    (hdelta_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) delta (Set.Icc (0 : ℝ) 1))
    (hdelta : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      extChartAt I x (delta t) = extChartAt I x x +
        t • (extChartAt I x z - extChartAt I x x)) :
    apm_t96a08_LineIntegral I omega delta =
      ∫ t : ℝ in (0 : ℝ)..1, apm_t96A08_omegaCoord I omega x
        (extChartAt I x x + t • (extChartAt I x z - extChartAt I x x))
        (extChartAt I x z - extChartAt I x x) := by
  let eta : ℝ → E := fun t ↦ extChartAt I x x +
    t • (extChartAt I x z - extChartAt I x x)
  have heta_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞) eta := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have heta_range : ∀ t ∈ Set.Icc (0 : ℝ) 1, eta t ∈ Set.range (I : E → E) := by
    intro t ht
    change (extChartAt I x x + t • (extChartAt I x z - extChartAt I x x)) ∈ _
    rw [← hdelta t ht]
    exact extChartAt_target_subset_range x
      (PartialEquiv.map_source _ (hdelta_source t ht))
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      omega (delta t) ((mfderiv 𝓘(ℝ, ℝ) I delta t) 1) =
        apm_t96A08_omegaCoord I omega x (eta t)
          (extChartAt I x z - extChartAt I x x) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hdt : delta t = (extChartAt I x).symm (eta t) := by
      calc
        delta t = (extChartAt I x).symm (extChartAt I x (delta t)) :=
          ((extChartAt I x).left_inv (hdelta_source t htIcc)).symm
        _ = (extChartAt I x).symm (eta t) := by
          rw [hdelta t htIcc]
    have hcomp : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        delta s = (extChartAt I x).symm (eta s) := by
      intro s hs
      calc
        delta s = (extChartAt I x).symm (extChartAt I x (delta s)) :=
          ((extChartAt I x).left_inv (hdelta_source s hs)).symm
        _ = (extChartAt I x).symm (eta s) := by rw [hdelta s hs]
    have hderivWithin :
        mfderivWithin 𝓘(ℝ, ℝ) I delta (Set.Icc 0 1) t =
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) (eta t)).comp
            (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) eta (Set.Icc 0 1) t) := by
      rw [mfderivWithin_congr hcomp hdt]
      apply mfderivWithin_comp
      · exact mdifferentiableWithinAt_extChartAt_symm (by
          change (extChartAt I x x + t • (extChartAt I x z - extChartAt I x x)) ∈ _
          rw [← hdelta t htIcc]
          exact PartialEquiv.map_source _ (hdelta_source t htIcc))
      · exact heta_smooth.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
      · exact heta_range
      · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffOn_Icc zero_lt_one t htIcc
    have hdelta_at : MDifferentiableAt 𝓘(ℝ, ℝ) I delta t :=
      (hdelta_smooth t htIcc).contMDiffAt hnhds |>.mdifferentiableAt (by simp)
    have heta_at : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) eta t :=
      heta_smooth.mdifferentiableAt (by simp)
    rw [← mfderivWithin_eq_mfderiv
      (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt];
          exact uniqueDiffOn_Icc zero_lt_one t htIcc) hdelta_at]
    rw [hderivWithin]
    rw [hdt]
    simp only [apm_t96A08_omegaCoord, ContinuousLinearMap.comp_apply]
    rw [mfderivWithin_eq_mfderiv
      (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt];
          exact uniqueDiffOn_Icc zero_lt_one t htIcc) heta_at]
    have hsmul : fderiv ℝ
        (fun y : ℝ ↦ y • (extChartAt I x z - extChartAt I x x)) t 1 =
          extChartAt I x z - extChartAt I x x := by
      have hd := ((hasFDerivAt_id (𝕜 := ℝ) t).smul_const
        (extChartAt I x z - extChartAt I x x)).fderiv
      have hd' := congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) hd
      simpa using hd'
    apply congrArg (fun v : E ↦
      omega ((extChartAt I x).symm (eta t))
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm
          (Set.range I) (eta t) v))
    rw [mfderiv_eq_fderiv]
    simpa only [eta, fderiv_const_add] using hsmul
  unfold apm_t96a08_LineIntegral
  apply intervalIntegral.integral_congr_ae
  have hae : ∀ᵐ t : ℝ, t ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton (1 : ℝ))
  filter_upwards [hae] with t htne htmem
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_uIoc] at htmem
    rcases htmem with htmem | htmem
    · exact ⟨htmem.1, lt_of_le_of_ne htmem.2 htne⟩
    · linarith
  simpa [eta] using hpoint t ht

/-- Pulling the one-form and the radial path into the extended chart gives
the ordinary coordinate interval integral. -/
lemma apm_t96A08_chart_radial_primitive_coordinate_formula
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (x : M) (W : Set E)
    (hWtarget : W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target) :
    ∃ omegaCoord : E → (E →L[ℝ] ℝ),
      ContinuousOn omegaCoord
        (W ∩ Set.range (I : E → E)) ∧
      omegaCoord (extChartAt I x x) = (omega x).comp
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
          (extChartAt I x x)) ∧
      ∀ (z : M) (delta : ℝ → M),
        (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) →
        ContMDiffOn 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) delta (Set.Icc (0 : ℝ) 1) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          extChartAt I x (delta t) = extChartAt I x x +
            t • (extChartAt I x z - extChartAt I x x)) →
        apm_t96a08_LineIntegral I omega delta =
          ∫ t : ℝ in (0 : ℝ)..1, omegaCoord
            (extChartAt I x x + t • (extChartAt I x z - extChartAt I x x))
            (extChartAt I x z - extChartAt I x x) := by
  exact ⟨apm_t96A08_omegaCoord I omega x,
    apm_t96A08_omegaCoord_continuousOn I omega homega_smooth x W hWtarget,
    apm_t96A08_omegaCoord_centre I omega x,
    fun z delta h1 h2 h3 ↦ apm_t96A08_omegaCoord_lineIntegral I omega x z delta h1 h2 h3⟩

/-- The parameter-integral calculation in a normed vector space: only the
derivative AT THE CENTRE is needed (claude-14 restructure: smoothness of the
potential now comes from `apm_t96A08_contMDiff_of_hasMFDerivAt`).
`G v = omegaCoord a (v - a) + o(‖v - a‖)` by continuity of `omegaCoord` at `a`. -/
lemma apm_t96A08_chart_radial_primitive_euclidean_calculus_aux_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ModelWithCorners ℝ E E) (W : Set E) (a v : E)
    (hWconv : Convex ℝ W) (ha : a ∈ W ∩ Set.range (I : E → E))
    (hv : v ∈ W ∩ Set.range (I : E → E)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    a + t • (v - a) ∈ W ∩ Set.range (I : E → E) := by
  exact (hWconv.inter I.convex_range).add_smul_sub_mem ha hv ht

lemma apm_t96A08_chart_radial_primitive_euclidean_calculus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (I : ModelWithCorners ℝ E E) (W : Set E) (a : E) (omegaCoord : E → (E →L[ℝ] ℝ))
    (hWopen : IsOpen W) (hWconv : Convex ℝ W) (haW : a ∈ W ∩ Set.range (I : E → E))
    (homega : ContinuousOn omegaCoord
      (W ∩ Set.range (I : E → E))) :
    let G : E → ℝ := fun v ↦ ∫ t : ℝ in (0 : ℝ)..1,
      omegaCoord (a + t • (v - a)) (v - a)
    HasFDerivWithinAt G (omegaCoord a) (W ∩ Set.range (I : E → E)) a := by
  dsimp only
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hcont := homega.continuousWithinAt haW
  have htend : Filter.Tendsto omegaCoord (nhdsWithin a (W ∩ Set.range (I : E → E)))
      (nhds (omegaCoord a)) := hcont
  rw [Metric.tendsto_nhdsWithin_nhds] at htend
  obtain ⟨d, hd, hdc⟩ := htend c hc
  have hev : ∀ᶠ v in nhds a, dist v a < d :=
    Metric.eventually_nhds_iff.2 ⟨d, hd, fun _ h => h⟩
  have hev' : ∀ᶠ v in nhdsWithin a (W ∩ Set.range (I : E → E)), dist v a < d :=
    hev.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hev'] with v hvS hva
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖omegaCoord (a + t • (v - a)) (v - a) - omegaCoord a (v - a)‖ ≤
        c * ‖v - a‖ := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hs := apm_t96A08_chart_radial_primitive_euclidean_calculus_aux_segment
      I W a v hWconv haW hvS ht'
    have hdist : dist (a + t • (v - a)) a < d := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht'.1]; exact ht'.2
      calc
        |t| * ‖v - a‖ ≤ 1 * ‖v - a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = dist v a := by simp [dist_eq_norm]
        _ < d := hva
    have hop : ‖omegaCoord (a + t • (v - a)) - omegaCoord a‖ < c :=
      by simpa [dist_eq_norm] using hdc hs hdist
    rw [← ContinuousLinearMap.sub_apply]
    calc
      ‖(omegaCoord (a + t • (v - a)) - omegaCoord a) (v - a)‖ ≤
          ‖omegaCoord (a + t • (v - a)) - omegaCoord a‖ * ‖v - a‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖v - a‖ := mul_le_mul_of_nonneg_right hop.le (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  norm_num at hi
  have hseg : Continuous (fun t : ℝ => a + t • (v - a)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hf : IntervalIntegrable
      (fun t : ℝ => omegaCoord (a + t • (v - a)) (v - a))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.clm_apply
    · apply homega.comp hseg.continuousOn
      intro t ht
      apply apm_t96A08_chart_radial_primitive_euclidean_calculus_aux_segment
        I W a v hWconv haW hvS
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    · exact continuousOn_const
  simp only [sub_self, smul_zero, add_zero, map_zero,
    intervalIntegral.integral_zero, sub_zero]
  have hcint : (∫ _ : ℝ in (0 : ℝ)..1, omegaCoord a (v - a)) =
      omegaCoord a (v - a) := by simp
  rw [← hcint, ← intervalIntegral.integral_sub hf intervalIntegrable_const]
  simpa only [map_sub, Real.norm_eq_abs] using hi

/-- Transfer the ambient parameter-integral result through the chart.  All
four preceding conclusions are explicit hypotheses, keeping this seat
independent of their proofs. -/
lemma apm_t96A08_chart_radial_primitive_transfer
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (hcharts : ∀ x : M, ∃ (U : Set M) (W : Set E), IsOpen U ∧ x ∈ U ∧
      IsOpen W ∧ Convex ℝ W ∧ extChartAt I x x ∈ W ∧
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target ∧
      U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W)
    (hpaths : ∀ (x : M) (U : Set M) (W : Set E),
      U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W →
      extChartAt I x x ∈ W → Convex ℝ W →
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target →
      ∀ z ∈ U, ∃ delta : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I delta ∧ delta 0 = x ∧ delta 1 = z ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, extChartAt I x (delta t) =
          extChartAt I x x + t • (extChartAt I x z - extChartAt I x x))
    (hcoord : ∀ (x : M) (W : Set E),
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target →
      ∃ omegaCoord : E → (E →L[ℝ] ℝ),
        ContinuousOn omegaCoord
          (W ∩ Set.range (I : E → E)) ∧
        omegaCoord (extChartAt I x x) = (omega x).comp
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
            (extChartAt I x x)) ∧
        ∀ (z : M) (delta : ℝ → M),
          (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) →
          ContMDiffOn 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞) delta (Set.Icc (0 : ℝ) 1) →
          (∀ t ∈ Set.Icc (0 : ℝ) 1, extChartAt I x (delta t) =
            extChartAt I x x + t • (extChartAt I x z - extChartAt I x x)) →
          apm_t96a08_LineIntegral I omega delta = ∫ t : ℝ in (0 : ℝ)..1,
            omegaCoord (extChartAt I x x + t •
              (extChartAt I x z - extChartAt I x x))
              (extChartAt I x z - extChartAt I x x))
    (heuclid : ∀ (W : Set E) (a : E) (omegaCoord : E → (E →L[ℝ] ℝ)),
      IsOpen W → Convex ℝ W → a ∈ W ∩ Set.range (I : E → E) →
      ContinuousOn omegaCoord
        (W ∩ Set.range (I : E → E)) →
      let G : E → ℝ := fun v ↦ ∫ t : ℝ in (0 : ℝ)..1,
        omegaCoord (a + t • (v - a)) (v - a)
      HasFDerivWithinAt G (omegaCoord a) (W ∩ Set.range (I : E → E)) a) :
    apm_t96A08_HasLocalRadialPrimitives I omega := by
  intro x
  rcases hcharts x with
    ⟨U, W, hUopen, hxU, hWopen, hWconv, hxW, hWtarget, hU⟩
  rcases hcoord x W hWtarget with
    ⟨omegaCoord, homegaCoord, homegaCoord_x, hcoord_formula⟩
  let a : E := extChartAt I x x
  let G : E → ℝ := fun v ↦ ∫ t : ℝ in (0 : ℝ)..1,
    omegaCoord (a + t • (v - a)) (v - a)
  have ha : a ∈ W ∩ Set.range (I : E → E) := by
    refine ⟨hxW, ?_⟩
    exact extChartAt_target_subset_range x
      ((extChartAt I x).map_source (mem_extChartAt_source x))
  have hG := heuclid W a omegaCoord hWopen hWconv ha homegaCoord
  change HasFDerivWithinAt G (omegaCoord a)
    (W ∩ Set.range (I : E → E)) a at hG
  let g : M → ℝ := fun y ↦ G (extChartAt I x y)
  have hchart_image : U ⊆ (extChartAt I x) ⁻¹' (W ∩ Set.range (I : E → E)) := by
    intro y hy
    rw [hU] at hy
    refine ⟨hy.2, ?_⟩
    exact extChartAt_target_subset_range x ((extChartAt I x).map_source hy.1)
  have hchart := hasMFDerivAt_extChartAt (I := I) (x := x) (y := x)
    (mem_chart_source E x)
  have hchart' := hchart.mdifferentiableAt.hasMFDerivAt
  have hg0 := hG.hasMFDerivWithinAt.comp x hchart'.hasMFDerivWithinAt hchart_image
  have hg1 := hg0.hasMFDerivAt (hUopen.mem_nhds hxU)
  have hcancel : (omegaCoord a).comp
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x) = omega x := by
    rw [homegaCoord_x]
    have hc := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (I := I) (x := x) (y := x) (mem_extChartAt_source x)
    simpa only [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_id] using
      congrArg (fun L ↦ (omega x).comp L) hc
  have hg : HasMFDerivAt I 𝓘(ℝ, ℝ) g x (omega x) := by
    simpa only [g] using hg1.congr_mfderiv hcancel
  refine ⟨U, hUopen, hxU, g, hg, ?_⟩
  intro z hz
  rcases hpaths x U W hU hxW hWconv hWtarget z hz with
    ⟨delta, hdelta, hd0, hd1, hdsource, hdchart⟩
  refine ⟨delta, hdelta, hd0, hd1, ?_⟩
  have hsmooth : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) delta (Set.Icc (0 : ℝ) 1) := by
    let q : ℝ → E := fun t ↦ extChartAt I x x +
      t • (extChartAt I x z - extChartAt I x x)
    have hq : ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ E) ((⊤ : ℕ∞) : WithTop ℕ∞) q := by
      exact contMDiff_const.add (contMDiff_id.smul contMDiff_const)
    have hqt : Set.Icc (0 : ℝ) 1 ⊆ q ⁻¹' (extChartAt I x).target := by
      intro t ht
      change q t ∈ (extChartAt I x).target
      rw [show q t = extChartAt I x (delta t) by exact (hdchart t ht).symm]
      exact (extChartAt I x).map_source (hdsource t ht)
    have hc := (contMDiffOn_extChartAt_symm x).comp hq.contMDiffOn hqt
    apply hc.congr
    intro t ht
    change delta t = (extChartAt I x).symm (q t)
    rw [show q t = extChartAt I x (delta t) by exact (hdchart t ht).symm]
    exact ((extChartAt I x).left_inv (hdsource t ht)).symm
  rw [hcoord_formula z delta hdsource hsmooth hdchart]
  change G (extChartAt I x z) - G (extChartAt I x x) = _
  simp [G, a]

theorem apm_t96A08_chart_radial_primitive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2)) :
    apm_t96A08_HasLocalRadialPrimitives I omega := by
  apply apm_t96A08_chart_radial_primitive_transfer I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive_chart_neighborhood I
  · exact apm_t96A08_chart_radial_primitive_radial_paths I
  · exact apm_t96A08_chart_radial_primitive_coordinate_formula I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive_euclidean_calculus I

/-- Seat: the evaluation `(y, v) ↦ omegaCoord y v` is smooth on
`φ.target ×ˢ univ` (as `apm_t96A08_omegaCoord_eval_contDiffOn`, all orders). -/
theorem apm_t96A08_omegaCoord_eval_contDiffOn_top
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (x : M) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × E ↦ apm_t96A08_omegaCoord I omega x p.1 p.2)
      ((extChartAt I x).target ×ˢ Set.univ) := by
  let e : E × E → TangentBundle (modelWithCornersSelf ℝ E) E :=
    fun p ↦ ⟨p.1, p.2⟩
  let T : TangentBundle (modelWithCornersSelf ℝ E) E → TangentBundle I M :=
    tangentMapWithin (modelWithCornersSelf ℝ E) I (extChartAt I x).symm
      (extChartAt I x).target
  have hs : ContMDiffOn (modelWithCornersSelf ℝ E) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      (extChartAt I x).symm (extChartAt I x).target :=
    contMDiffOn_extChartAt_symm x
  have hT : ContMDiffOn (modelWithCornersSelf ℝ E).tangent I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞) T
      (Bundle.TotalSpace.proj ⁻¹' (extChartAt I x).target) :=
    hs.contMDiffOn_tangentMapWithin (by norm_cast)
      (uniqueDiffOn_extChartAt_target x).uniqueMDiffOn
  have he : ContMDiff (modelWithCornersSelf ℝ (E × E))
      (modelWithCornersSelf ℝ E).tangent ((⊤ : ℕ∞) : WithTop ℕ∞) e := by
    apply contMDiff_iff.2
    constructor
    · change Continuous
        ((tangentBundleModelSpaceHomeomorph (modelWithCornersSelf ℝ E)).symm ∘ id)
      exact (tangentBundleModelSpaceHomeomorph
        (modelWithCornersSelf ℝ E)).symm.continuous.comp continuous_id
    · intro p q
      apply contDiffOn_id.congr
      simp only [e, mfld_simps, Prod.mk.injEq]
  have hc : ContMDiffOn (modelWithCornersSelf ℝ (E × E))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun v : TangentBundle I M ↦ omega v.1 v.2) ∘ T ∘ e)
      ((extChartAt I x).target ×ˢ Set.univ) := by
    exact (homega_smooth.of_le (by simp)).comp_contMDiffOn
      (hT.comp (he.of_le (by simp)).contMDiffOn (fun p hp ↦ hp.1))
  rw [contMDiffOn_iff_contDiffOn] at hc
  apply hc.congr
  intro p hp
  simp only [Function.comp_apply, T, e, apm_t96A08_omegaCoord,
    tangentMapWithin_proj, tangentMapWithin_snd]
  rw [show mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I x).symm
      (Set.range I) p.1 = mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I x).symm (extChartAt I x).target p.1 by
    have hd := (hs p.1 hp.1).mdifferentiableWithinAt (by simp)
    exact hd.mfderivWithin_mono_of_mem_nhdsWithin
      (I.uniqueMDiffOn p.1 (extChartAt_target_subset_range x hp.1))
      (extChartAt_target_mem_nhdsWithin_of_mem hp.1)]
  rfl

theorem apm_t96A08_contDiffOn_of_eval_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (L : E → (E →L[ℝ] ℝ)) (hS : UniqueDiffOn ℝ S)
    (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × E ↦ L p.1 p.2) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L S := by
  let F : E × E → ℝ := fun p ↦ L p.1 p.2
  let T : Set (E × E) := S ×ˢ Set.univ
  have hT : UniqueDiffOn ℝ T := hS.prod uniqueDiffOn_univ
  let D : E × E → ((E × E) →L[ℝ] ℝ) := fderivWithin ℝ F T
  have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D T := by
    exact hL.fderivWithin hT (by simp)
  let j : E → E × E := fun y ↦ (y, 0)
  let ι : E →L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E
  have hj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) j S := by
    fun_prop
  have hjT : Set.MapsTo j S T := by
    intro y hy
    exact ⟨hy, Set.mem_univ 0⟩
  have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y ↦ (D (j y)).comp ι) S := by
    exact (hD.comp hj hjT).clm_comp contDiffOn_const
  apply hsmooth.congr
  intro y hy
  have hFD : HasFDerivWithinAt F (D (j y)) T (j y) :=
    ((hL.differentiableOn (by simp)) (j y) ⟨hy, Set.mem_univ 0⟩).hasFDerivWithinAt
  have hji : HasFDerivAt (fun v : E ↦ (y, v)) ι 0 := by
    simpa [ι] using (ι.hasFDerivAt.const_add (y, (0 : E)))
  have hmap : Set.MapsTo (fun v : E ↦ (y, v)) Set.univ T := by
    intro v hv
    exact ⟨hy, Set.mem_univ v⟩
  have hc := hFD.comp 0 hji.hasFDerivWithinAt hmap
  have hc' : HasFDerivWithinAt (fun v : E ↦ L y v)
      ((D (j y)).comp ι) Set.univ 0 := by
    simpa [F, j] using hc
  have hlin : HasFDerivWithinAt (fun v : E ↦ L y v) (L y) Set.univ 0 :=
    (L y).hasFDerivAt.hasFDerivWithinAt
  exact (hlin.fderivWithin
    (uniqueDiffOn_univ.uniqueDiffWithinAt (Set.mem_univ 0))).symm.trans
      (hc'.fderivWithin
        (uniqueDiffOn_univ.uniqueDiffWithinAt (Set.mem_univ 0)))

/-- Seat: in the chart at `x`, `f ∘ φ.symm` has within-derivative
`omegaCoord y` at each `y ∈ φ.target` (chain rule:
`HasMFDerivAt f p (omega p)` with `p = φ.symm y`, composed with
`mfderivWithin φ.symm (range I) y`; `HasMFDerivAt.comp_hasMFDerivWithinAt`,
then `hasMFDerivWithinAt_iff_hasFDerivWithinAt` on the model space). -/
theorem apm_t96A08_chart_hasFDerivWithinAt
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (f : M → ℝ) (hf : ∀ p : M, HasMFDerivAt I 𝓘(ℝ, ℝ) f p (omega p)) (x : M) :
    ∀ y ∈ (extChartAt I x).target,
      HasFDerivWithinAt (f ∘ (extChartAt I x).symm)
        (apm_t96A08_omegaCoord I omega x y) (extChartAt I x).target y := by
  intro y hy
  have hinv := (mdifferentiableWithinAt_extChartAt_symm hy).hasMFDerivWithinAt
  have hcomp := HasMFDerivAt.comp_hasMFDerivWithinAt
    (f := (extChartAt I x).symm) y (hf ((extChartAt I x).symm y)) hinv
  have htarget := hcomp.mono (extChartAt_target_subset_range x)
  simpa only [apm_t96A08_omegaCoord] using htarget.hasFDerivWithinAt

/-- Seat (pure analysis): if `g` has within-derivative `L y` at every point of
a uniquely differentiable `S` and `L` is smooth on `S`, then `g` is smooth on
`S` (`contDiffOn_infty_iff_fderivWithin`, with `fderivWithin g S = L` on `S`). -/
theorem apm_t96A08_contDiffOn_of_hasFDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (g : E → ℝ) (L : E → (E →L[ℝ] ℝ)) (hS : UniqueDiffOn ℝ S)
    (hg : ∀ y ∈ S, HasFDerivWithinAt g (L y) S y)
    (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L S) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g S := by
  rw [contDiffOn_infty_iff_fderivWithin hS]
  refine ⟨fun y hy ↦ (hg y hy).differentiableWithinAt, ?_⟩
  exact hL.congr fun y hy ↦ (hg y hy).fderivWithin (hS y hy)

/-- Seat: a real function on `M` that is smooth in every chart
(`f ∘ (extChartAt I x).symm` smooth on `(extChartAt I x).target`) is smooth
(`contMDiffAt_iff_target`/`contMDiffOn_extChartAt_symm`, `contMDiff_iff`). -/
theorem apm_t96A08_contMDiff_of_chart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ)
    (hf : ∀ x : M, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (extChartAt I x).symm)
      (extChartAt I x).target) :
    ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  sorry

/-- Seat (claude-14 restructure): a function whose manifold derivative exists
everywhere and equals a smooth one-form is smooth.  In the chart at `p`,
`f ∘ φ.symm` has within-derivative `omegaCoord` on `φ.target ∩ range I`
(open ∩ convex, so unique differentiability), and `omegaCoord` is smooth there,
so `contDiffOn_succ_iff_fderivWithin` bootstraps to `C^((⊤ : ℕ∞) : WithTop ℕ∞)`. -/
theorem apm_t96A08_contMDiff_of_hasMFDerivAt
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (f : M → ℝ) (hf : ∀ p : M, HasMFDerivAt I 𝓘(ℝ, ℝ) f p (omega p)) :
    ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  apply apm_t96A08_contMDiff_of_chart I f
  intro x
  have hS : UniqueDiffOn ℝ (extChartAt I x).target := uniqueDiffOn_extChartAt_target x
  exact apm_t96A08_contDiffOn_of_hasFDerivWithinAt _ _ _ hS
    (apm_t96A08_chart_hasFDerivWithinAt I omega f hf x)
    (apm_t96A08_contDiffOn_of_eval_contDiffOn _ _ hS
      (apm_t96A08_omegaCoord_eval_contDiffOn_top I omega homega_smooth x))

/-- Seat (claude-14 restructure of the former proved glue): additive
concatenation and local primitives with the right derivative at their centre
give `HasMFDerivAt f x (omega x)` at every `x` (`f = g + (f x - g x)` near `x`,
as in the previous proof, then `HasMFDerivAt.congr_of_eventuallyEq`);
smoothness comes from `hboot`. -/
theorem apm_t96A08_potential_of_local_primitives
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (hconcat : apm_t96A08_HasAdditiveConcatenation I omega)
    (hlocal : apm_t96A08_HasLocalRadialPrimitives I omega)
    (hboot : ∀ f : M → ℝ, (∀ p : M, HasMFDerivAt I 𝓘(ℝ, ℝ) f p (omega p)) →
      ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreachable : ∀ p : M, ∃ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma ∧
        gamma 0 = base ∧ gamma 1 = p)
    (f : M → ℝ)
    (hf : ∀ p : M, ∀ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma →
      gamma 0 = base → gamma 1 = p →
      f p = apm_t96a08_LineIntegral I omega gamma) :
    ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = omega p := by
  have h_at : ∀ x : M, HasMFDerivAt I 𝓘(ℝ, ℝ) f x (omega x) := by
    intro x
    rcases hlocal x with ⟨U, hU, hxU, g, hgd, hradial⟩
    rcases hreachable x with ⟨gamma, hgamma, hgamma0, hgamma1⟩
    have heq : ∀ z ∈ U, f z = g z + (f x - g x) := by
      intro z hz
      rcases hradial z hz with ⟨delta, hdelta, hdelta0, hdelta1, hdelta_int⟩
      rcases hconcat gamma delta hgamma hdelta (hgamma1.trans hdelta0.symm) with
        ⟨eta, heta, heta0, heta1, heta_int⟩
      have hfz := hf z eta heta (heta0.trans hgamma0) (heta1.trans hdelta1)
      have hfx := hf x gamma hgamma hgamma0 hgamma1
      linarith
    have hfg : Filter.EventuallyEq (nhds x) f (fun y ↦ g y + (f x - g x)) :=
      Filter.mem_of_superset (hU.mem_nhds hxU) (fun z hz ↦ heq z hz)
    have hq : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y ↦ g y + (f x - g x)) x (omega x) := by
      have h2 := hgd.add (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (f x - g x) x)
      convert h2 using 1
      ext v
      change omega x v = omega x v + 0
      exact (add_zero _).symm
    exact hq.congr_of_eventuallyEq hfg
  exact ⟨hboot f h_at, fun x ↦ (h_at x).mfderiv⟩

/-- The fundamental theorem assembled from the three independent library
boundaries above. -/
theorem apm_t96A08_piecewise_lineIntegral_fundamental
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (hreachable : ∀ p : M, ∃ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma ∧
        gamma 0 = base ∧ gamma 1 = p)
    (f : M → ℝ)
    (hf : ∀ p : M, ∀ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma →
      gamma 0 = base → gamma 1 = p →
      f p = apm_t96a08_LineIntegral I omega gamma) :
    ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = omega p := by
  apply apm_t96A08_potential_of_local_primitives I omega base
  · exact apm_t96A08_piecewisePath_concat_additive I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive I omega homega_smooth
  · exact apm_t96A08_contMDiff_of_hasMFDerivAt I omega homega_smooth
  · exact hreachable
  · exact hf

theorem apm_t96a08
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (hωsmooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : TangentBundle I M => ω v.1 v.2))
    (hreachable : ∀ p : M, ∃ γ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I γ ∧ γ 0 = base ∧ γ 1 = p)
    (hindependent : ∀ γ₁ γ₂ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I γ₁ →
      apm_t96a08_IsPiecewiseSmoothPath I γ₂ →
      γ₁ 0 = γ₂ 0 → γ₁ 1 = γ₂ 1 →
      apm_t96a08_LineIntegral I ω γ₁ = apm_t96a08_LineIntegral I ω γ₂) :
    ∃ f : M → ℝ,
      (∀ p : M, ∀ γ : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I γ → γ 0 = base → γ 1 = p →
        f p = apm_t96a08_LineIntegral I ω γ) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = ω p := by
  classical
  have hreach := hreachable
  choose γ hγ using hreachable
  let f : M → ℝ := fun p ↦ apm_t96a08_LineIntegral I ω (γ p)
  have hf : ∀ p : M, ∀ δ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I δ → δ 0 = base → δ 1 = p →
      f p = apm_t96a08_LineIntegral I ω δ := by
    intro p δ hδ hδ0 hδ1
    exact hindependent (γ p) δ (hγ p).1 hδ
      (by rw [(hγ p).2.1, hδ0]) (by rw [(hγ p).2.2, hδ1])
  exact ⟨f, hf,
    apm_t96A08_piecewise_lineIntegral_fundamental I ω base hωsmooth
      hreach f hf⟩

#print axioms apm_t96a08

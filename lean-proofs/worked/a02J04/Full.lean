import Mathlib

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace A02J04Full

def triangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}

def triWeight : ℝ × ℝ → ℝ≥0∞ :=
  triangle.indicator (fun _ => (2 : ℝ≥0∞))

def μ : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity triWeight

def τ : Measure ℝ :=
  μ.fst

def tauDensity : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Icc (0 : ℝ) 1) (fun x => ENNReal.ofReal (2 * x))

def dmDtau : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1) (fun x => (ENNReal.ofReal (2 * x))⁻¹)

def mSingSet : Set ℝ :=
  Set.Iic (0 : ℝ) ∪ Set.Ioi (1 : ℝ)

lemma triangle_measurable : MeasurableSet triangle := by
  change MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}
  measurability

lemma triWeight_measurable : Measurable triWeight := by
  exact measurable_const.indicator triangle_measurable

lemma section_set_eq (x : ℝ) :
    {y : ℝ | (x, y) ∈ triangle} =
      if x ∈ Set.Icc (0 : ℝ) 1 then Set.Icc (0 : ℝ) x else ∅ := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · ext y
    simp [hx, triangle]
    exact fun _ _ => hx.2
  · ext y
    simp [hx]
    intro hy
    apply hx
    exact ⟨le_trans hy.1 hy.2.1, hy.2.2⟩

lemma section_integral (x : ℝ) :
    ∫⁻ y, triWeight (x, y) ∂volume = tauDensity x := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have hsec : {y : ℝ | (x, y) ∈ triangle} = Set.Icc (0 : ℝ) x := by
      simpa [hx] using section_set_eq x
    rw [tauDensity]
    simp [hx]
    have hfun : (fun y : ℝ => triWeight (x, y)) =
        (Set.Icc (0 : ℝ) x).indicator (fun _ => (2 : ℝ≥0∞)) := by
      ext y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) x
      · have htri : (x, y) ∈ triangle := by
          exact ⟨hy.1, hy.2, hx.2⟩
        simp [triWeight, hy, htri]
      · have htri : (x, y) ∉ triangle := by
          intro htri
          apply hy
          rw [← hsec]
          exact htri
        simp [triWeight, hy, htri]
    rw [hfun, lintegral_indicator measurableSet_Icc]
    have hvol : volume (Set.Icc (0 : ℝ) x) = ENNReal.ofReal x := by
      simpa [sub_zero] using (volume_Icc (a := (0 : ℝ)) (b := x))
    simp [hvol, mul_comm]
  · have hsec : {y : ℝ | (x, y) ∈ triangle} = (∅ : Set ℝ) := by
      simpa [hx] using section_set_eq x
    rw [tauDensity]
    simp [hx]
    have hfun : (fun y : ℝ => triWeight (x, y)) = 0 := by
      ext y
      have htri : (x, y) ∉ triangle := by
        intro htri
        have : y ∈ ({y | (x, y) ∈ triangle} : Set ℝ) := htri
        rw [hsec] at this
        simpa using this
      simp [triWeight, htri]
    rw [hfun]
    exact lintegral_zero

lemma fst_withDensity_eq_withDensity_lintegral {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (((volume.prod volume).withDensity f).fst) =
      volume.withDensity (fun x => ∫⁻ y, f (x, y) ∂volume) := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (measurable_fst hs)]
  rw [show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set ℝ) by ext z; simp]
  rw [MeasureTheory.setLIntegral_prod]
  · simpa [withDensity_apply, hs]
  · simpa using hf.aemeasurable.restrict

theorem tau_eq_withDensity :
    τ = volume.withDensity tauDensity := by
  rw [τ, μ]
  calc
    (((volume.prod volume).withDensity triWeight).fst)
        = volume.withDensity (fun x => ∫⁻ y, triWeight (x, y) ∂volume) :=
      fst_withDensity_eq_withDensity_lintegral triWeight_measurable
    _ = volume.withDensity tauDensity := by
      refine withDensity_congr_ae ?_
      filter_upwards with x
      exact section_integral x

lemma tauDensity_measurable : Measurable tauDensity := by
  exact ((measurable_const.mul measurable_id).ennreal_ofReal).indicator measurableSet_Icc

lemma dmDtau_measurable : Measurable dmDtau := by
  exact (((measurable_const.mul measurable_id).ennreal_ofReal).inv).indicator measurableSet_Ioc

lemma tauDensity_ne_zero_mem_Ioc {x : ℝ} (hx : tauDensity x ≠ 0) :
    x ∈ Set.Ioc (0 : ℝ) 1 := by
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hmem : x ∈ Set.Icc (0 : ℝ) 1
    · exact hmem
    · have : tauDensity x = 0 := by simp [tauDensity, hmem]
      exact (hx this).elim
  have hxpos : 0 < x := by
    by_contra hnot
    have hxzero : x = 0 := le_antisymm (not_lt.mp hnot) hxmem.1
    have : tauDensity x = 0 := by simp [tauDensity, hxzero]
    exact hx this
  exact ⟨hxpos, hxmem.2⟩

lemma tauDensity_mul_dmDtau :
    tauDensity * dmDtau = (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
  ext x
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
    have h2xne : 2 * x ≠ 0 := by nlinarith [hx.1]
    have h2xenn_ne : ENNReal.ofReal (2 * x) ≠ 0 := by
      exact ne_of_gt (by
        rw [ENNReal.ofReal_pos]
        nlinarith [hx.1])
    have hcalc : ENNReal.ofReal (2 * x) * (ENNReal.ofReal (2 * x))⁻¹ = 1 := by
      exact ENNReal.mul_inv_cancel h2xenn_ne ENNReal.ofReal_ne_top
    calc
      (tauDensity * dmDtau) x
          = ENNReal.ofReal (2 * x) * (ENNReal.ofReal (2 * x))⁻¹ := by
              simp [tauDensity, dmDtau, hx, hx']
      _ = 1 := hcalc
      _ = ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))) x := by
            simp [hx]
  · simp [dmDtau, hx]

lemma tau_withDensity_dmDtau_eq :
    τ.withDensity dmDtau = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
  rw [tau_eq_withDensity]
  calc
    (volume.withDensity tauDensity).withDensity dmDtau
        = volume.withDensity (tauDensity * dmDtau) := by
      symm
      exact withDensity_mul volume tauDensity_measurable dmDtau_measurable
    _ = volume.withDensity ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))) := by
      congr 1
      exact tauDensity_mul_dmDtau
    _ = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
      simpa using (withDensity_indicator_one (μ := volume) (s := Set.Ioc (0 : ℝ) 1))

lemma tau_mSingSet_zero : τ mSingSet = 0 := by
  rw [tau_eq_withDensity]
  exact (withDensity_apply_eq_zero tauDensity_measurable).2 (by
    apply measure_mono_null (t := (∅ : Set ℝ))
    · intro x hx
      exfalso
      rcases hx.2 with hxle | hxgt
      · exact (lt_irrefl (0 : ℝ)) (lt_of_lt_of_le (tauDensity_ne_zero_mem_Ioc hx.1).1 hxle)
      · exact (not_lt_of_ge (tauDensity_ne_zero_mem_Ioc hx.1).2) hxgt
    · simp)

lemma singular_witness : volume.restrict mSingSet ⟂ₘ τ := by
  refine Measure.MutuallySingular.mk (s := Set.Ioc (0 : ℝ) 1) (t := mSingSet) ?_ ?_ ?_
  · rw [Measure.restrict_apply]
    · have : Set.Ioc (0 : ℝ) 1 ∩ mSingSet = (∅ : Set ℝ) := by
        ext x
        simp [mSingSet]
      simp [this]
    · exact measurableSet_Ioc
  · exact tau_mSingSet_zero
  · intro x _
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · exact Or.inl hx
    · right
      by_cases hx0 : x ≤ 0
      · exact Or.inl hx0
      · have hx1 : 1 < x := by
          have : ¬ x ≤ 1 := by
            intro h1
            exact hx ⟨lt_of_not_ge hx0, h1⟩
          exact lt_of_not_ge this
        exact Or.inr hx1

lemma volume_decomposition :
    volume = volume.restrict mSingSet + τ.withDensity dmDtau := by
  calc
    volume = volume.restrict (Set.Ioc (0 : ℝ) 1)ᶜ + volume.restrict (Set.Ioc (0 : ℝ) 1) := by
      simpa using (Measure.restrict_compl_add_restrict (μ := volume) measurableSet_Ioc).symm
    _ = volume.restrict mSingSet + τ.withDensity dmDtau := by
      simp [mSingSet, compl_Ioc, tau_withDensity_dmDtau_eq]

lemma singular_part_explicit :
    volume.singularPart τ = volume.restrict mSingSet := by
  exact (Measure.eq_singularPart dmDtau_measurable singular_witness volume_decomposition).symm

lemma rnDeriv_explicit :
    dmDtau =ᵐ[τ] volume.rnDeriv τ := by
  letI : SigmaFinite τ := by
    rw [tau_eq_withDensity]
    exact SigmaFinite.withDensity_of_ne_top (ae_of_all _ (by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · simp [tauDensity, hx]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
      · simp [tauDensity, hx]))
  exact Measure.eq_rnDeriv dmDtau_measurable singular_witness volume_decomposition

theorem full_answer :
    volume.singularPart τ = volume.restrict mSingSet ∧
      dmDtau =ᵐ[τ] volume.rnDeriv τ := by
  exact ⟨singular_part_explicit, rnDeriv_explicit⟩

end A02J04Full

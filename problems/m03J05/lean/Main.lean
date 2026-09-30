import Mathlib

/-! # APM m03J05: linear and semilinear mixed boundary-value problems

## Statement repairs

The source writes `x \in R` in the antiderivative hypothesis; this is read as
the evident `x \in ℝ`.

## Encoding note

Mathlib does not currently bundle the Sobolev space `H¹(0,1)`.  In one
dimension it is canonically represented by a pair consisting of the value at
zero and an `L²(0,1)` weak derivative; `m03J05H1Value` reconstructs its absolutely
continuous representative.  Thus the central Sobolev object is retained rather
than replaced by a scalar surrogate.
-/

open MeasureTheory Set

noncomputable section

def m03J05UnitMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

/-- The restricted measure used by the custom Sobolev model really is a
probability measure. -/
@[simp] lemma m03J05UnitMeasure_apply_univ :
    m03J05UnitMeasure Set.univ = 1 := by
  simp [m03J05UnitMeasure, Real.volume_Ioo]

instance : IsProbabilityMeasure m03J05UnitMeasure where
  measure_univ := m03J05UnitMeasure_apply_univ

lemma m03J05UnitMeasure_eq_restrict_Ioc :
    m03J05UnitMeasure = volume.restrict (Ioc 0 1) := by
  unfold m03J05UnitMeasure
  exact Measure.restrict_congr_set Ioo_ae_eq_Ioc

/-- Every measurable subinterval used in reconstruction has mass at most
one under the restricted unit-interval measure. -/
lemma m03J05UnitMeasure_Ioc_le_one (x : ℝ) :
    m03J05UnitMeasure (Ioc 0 x) ≤ 1 := by
  rw [← m03J05UnitMeasure_apply_univ]
  exact measure_mono (subset_univ _)

/-- The `L²` indicator of any reconstruction subinterval has norm at most
one. -/
lemma m03J05_indicatorConstLp_norm_le_one (x : ℝ) :
    ‖indicatorConstLp (μ := m03J05UnitMeasure) 2 measurableSet_Ioc
        (measure_ne_top m03J05UnitMeasure (Ioc 0 x)) (1 : ℝ)‖ ≤ 1 := by
  refine (norm_indicatorConstLp_le (μ := m03J05UnitMeasure)
    (p := (2 : ENNReal)) (hs := measurableSet_Ioc)
    (hμs := measure_ne_top m03J05UnitMeasure (Ioc 0 x)) (c := (1 : ℝ))).trans ?_
  norm_num
  have hm : (m03J05UnitMeasure (Ioc 0 x)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simp) (m03J05UnitMeasure_Ioc_le_one x)
  exact Real.rpow_le_one (measureReal_nonneg) hm (by positivity)

abbrev m03J05H1 := ℝ × Lp ℝ 2 m03J05UnitMeasure

/-- Pairing an `L²` derivative with a subinterval indicator is bounded by the
derivative norm. -/
lemma m03J05_indicator_pairing_le (u : m03J05H1) (x : ℝ) :
    let g := indicatorConstLp (μ := m03J05UnitMeasure) 2 measurableSet_Ioc
      (measure_ne_top m03J05UnitMeasure (Ioc 0 x)) (1 : ℝ)
    |∫ t, u.2 t * g t ∂m03J05UnitMeasure| ≤ ‖u.2‖ := by
  dsimp only
  let g := indicatorConstLp (μ := m03J05UnitMeasure) 2 measurableSet_Ioc
    (measure_ne_top m03J05UnitMeasure (Ioc 0 x)) (1 : ℝ)
  have hcs := abs_real_inner_le_norm u.2 g
  rw [MeasureTheory.L2.inner_def] at hcs
  have hb := hcs.trans (mul_le_of_le_one_right (norm_nonneg u.2)
    (m03J05_indicatorConstLp_norm_le_one x))
  simpa [inner, mul_comm] using hb

/-- For points in the unit interval, the Hilbert pairing with the interval
indicator is exactly the oriented integral used by reconstruction. -/
lemma m03J05_indicator_pairing_eq_intervalIntegral (u : m03J05H1) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    let g := indicatorConstLp (μ := m03J05UnitMeasure) 2 measurableSet_Ioc
      (measure_ne_top m03J05UnitMeasure (Ioc 0 x)) (1 : ℝ)
    (∫ t, u.2 t * g t ∂m03J05UnitMeasure) = ∫ t in (0 : ℝ)..x, u.2 t := by
  dsimp only
  let g := indicatorConstLp (μ := m03J05UnitMeasure) 2 measurableSet_Ioc
    (measure_ne_top m03J05UnitMeasure (Ioc 0 x)) (1 : ℝ)
  have hg := indicatorConstLp_coeFn (μ := m03J05UnitMeasure) (p := (2 : ENNReal))
    (hs := measurableSet_Ioc) (hμs := measure_ne_top m03J05UnitMeasure (Ioc 0 x))
    (c := (1 : ℝ))
  have hpair : (∫ t, u.2 t * g t ∂m03J05UnitMeasure) =
      ∫ t in Ioc 0 x, u.2 t ∂m03J05UnitMeasure := by
    calc
      (∫ t, u.2 t * g t ∂m03J05UnitMeasure) =
          ∫ t, (Ioc 0 x).indicator (fun y => u.2 y) t ∂m03J05UnitMeasure := by
            apply integral_congr_ae
            filter_upwards [hg] with t ht
            rw [ht]
            by_cases htx : t ∈ Ioc 0 x <;> simp [htx]
      _ = ∫ t in Ioc 0 x, u.2 t ∂m03J05UnitMeasure :=
        integral_indicator measurableSet_Ioc
  rw [hpair, intervalIntegral.integral_of_le hx.1]
  change (∫ t, u.2 t ∂(m03J05UnitMeasure.restrict (Ioc 0 x))) =
    ∫ t, u.2 t ∂(volume.restrict (Ioc 0 x))
  congr 1
  unfold m03J05UnitMeasure
  rcases hx.2.eq_or_lt with hxeq | hxlt
  · subst x
    rw [Measure.restrict_restrict measurableSet_Ioc]
    apply Measure.restrict_congr_set
    filter_upwards [Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1)] with t ht
    change (Ioc 0 1 t ∧ Ioo 0 1 t) = Ioc 0 1 t
    rw [ht]
    simp
  · exact Measure.restrict_restrict_of_subset fun t ht =>
      ⟨ht.1, lt_of_le_of_lt ht.2 hxlt⟩

/-- Quantitative one-dimensional reconstruction estimate. -/
lemma m03J05_intervalIntegral_le_deriv_norm (u : m03J05H1) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |∫ t in (0 : ℝ)..x, u.2 t| ≤ ‖u.2‖ := by
  rw [← m03J05_indicator_pairing_eq_intervalIntegral u hx]
  exact m03J05_indicator_pairing_le u x

def m03J05H1Value (u : m03J05H1) (x : ℝ) : ℝ :=
  u.1 + ∫ t in (0 : ℝ)..x, u.2 t

lemma m03J05H1Value_abs_le (u : m03J05H1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |m03J05H1Value u x| ≤ |u.1| + ‖u.2‖ := by
  unfold m03J05H1Value
  calc
    |u.1 + ∫ t in (0 : ℝ)..x, u.2 t| ≤
        |u.1| + |∫ t in (0 : ℝ)..x, u.2 t| := abs_add_le _ _
    _ ≤ |u.1| + ‖u.2‖ := by
      gcongr
      exact m03J05_intervalIntegral_le_deriv_norm u hx

@[simp] lemma m03J05H1Value_zero (u : m03J05H1) :
    m03J05H1Value u 0 = u.1 := by
  simp [m03J05H1Value]

lemma m03J05H1Value_zero_of_trace_zero (u : m03J05H1) (hu : u.1 = 0) :
    m03J05H1Value u 0 = 0 := by
  simpa using congrArg id hu

/-- Every derivative component in the product realization is integrable on
the unit interval (the finite-measure `L² ⊆ L¹` inclusion). -/
lemma m03J05H1_deriv_intervalIntegrable (u : m03J05H1) :
    IntervalIntegrable (fun x : ℝ => u.2 x) volume 0 1 := by
  letI : IsFiniteMeasure m03J05UnitMeasure := by
    unfold m03J05UnitMeasure
    infer_instance
  rw [intervalIntegrable_iff]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change Integrable (fun x : ℝ => u.2 x) (volume.restrict (Ioc 0 1))
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have h := integrableOn_Lp_of_measure_ne_top u.2
    (by norm_num : (1 : ENNReal) ≤ 2)
    (measure_ne_top m03J05UnitMeasure Set.univ)
  simpa [m03J05UnitMeasure, IntegrableOn] using h

/-- Reconstruction is additive at every point of the unit interval. -/
lemma m03J05H1Value_add (u v : m03J05H1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    m03J05H1Value (u + v) x = m03J05H1Value u x + m03J05H1Value v x := by
  have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc_right hx.2
  have hu := IntervalIntegrable.mono_set (m03J05H1_deriv_intervalIntegrable u) hsub
  have hv := IntervalIntegrable.mono_set (m03J05H1_deriv_intervalIntegrable v) hsub
  have hadd : (fun t : ℝ => (u.2 + v.2) t) =ᵐ[volume.restrict (Ioc 0 1)]
      fun t => u.2 t + v.2 t := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact Lp.coeFn_add u.2 v.2
  have hadd' : ∀ᵐ t ∂volume.restrict (Ioc 0 1),
      (u.2 + v.2) t = u.2 t + v.2 t := hadd
  rw [ae_restrict_iff' measurableSet_Ioc] at hadd'
  have hint : (∫ t in (0 : ℝ)..x, (u.2 + v.2) t) =
      ∫ t in (0 : ℝ)..x, (u.2 t + v.2 t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hadd'] with t ht htx
    apply ht
    have htx' := hsub (uIoc_subset_uIcc htx)
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc] at htx'
    simp only [uIoc_of_le hx.1, mem_Ioc] at htx
    exact ⟨htx.1, htx'.2⟩
  simp only [m03J05H1Value, Prod.fst_add, Prod.snd_add]
  rw [hint]
  rw [intervalIntegral.integral_add hu hv]
  ring

/-- Reconstruction commutes with real scalar multiplication at every point
of the unit interval. -/
lemma m03J05H1Value_smul (c : ℝ) (u : m03J05H1) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    m03J05H1Value (c • u) x = c * m03J05H1Value u x := by
  have hsmul : (fun t : ℝ => (c • u.2) t) =ᵐ[volume.restrict (Ioc 0 1)]
      fun t => c * u.2 t := by
    have hb : (fun t : ℝ => (c • u.2) t) =ᵐ[m03J05UnitMeasure]
        fun t => c * u.2 t := by
      simpa [smul_eq_mul] using Lp.coeFn_smul c u.2
    change (fun t : ℝ => (c • u.2) t) =ᵐ[volume.restrict (Ioo 0 1)]
      fun t => c * u.2 t at hb
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hb
    exact hb
  have hsmul' : ∀ᵐ t ∂volume.restrict (Ioc 0 1),
      (c • u.2) t = c * u.2 t := hsmul
  rw [ae_restrict_iff' measurableSet_Ioc] at hsmul'
  have hint : (∫ t in (0 : ℝ)..x, (c • u.2) t) =
      ∫ t in (0 : ℝ)..x, c * u.2 t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hsmul'] with t ht htx
    apply ht
    simp only [uIoc_of_le hx.1, mem_Ioc] at htx
    exact ⟨htx.1, htx.2.trans hx.2⟩
  unfold m03J05H1Value
  change c * u.1 + (∫ t in (0 : ℝ)..x, (c • u.2) t) =
    c * (u.1 + ∫ t in (0 : ℝ)..x, u.2 t)
  rw [hint, intervalIntegral.integral_const_mul]
  ring

/-- Reconstruction commutes with subtraction on the unit interval. -/
lemma m03J05H1Value_sub (u v : m03J05H1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    m03J05H1Value (u - v) x = m03J05H1Value u x - m03J05H1Value v x := by
  rw [sub_eq_add_neg, m03J05H1Value_add _ _ hx]
  have hneg := m03J05H1Value_smul (-1 : ℝ) v hx
  simpa only [neg_smul, one_smul, neg_mul, one_mul, sub_eq_add_neg] using
    congrArg (fun z => m03J05H1Value u x + z) hneg

/-- Point evaluation of the reconstructed representative, bundled as a
continuous linear map for points in the unit interval. -/
noncomputable def m03J05H1EvalCLM (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    m03J05H1 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => m03J05H1Value u x
      map_add' := fun u v => m03J05H1Value_add u v hx
      map_smul' := fun c u => by
        simpa [smul_eq_mul] using m03J05H1Value_smul c u hx }
    2 (fun u => by
      rw [Real.norm_eq_abs]
      calc
        |m03J05H1Value u x| ≤ |u.1| + ‖u.2‖ := m03J05H1Value_abs_le u hx
        _ = ‖u.1‖ + ‖u.2‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖u‖ + ‖u‖ := add_le_add (norm_fst_le u) (norm_snd_le u)
        _ = 2 * ‖u‖ := by ring)

/-- Non-vacuity check for the bundled evaluation map. -/
lemma m03J05H1EvalCLM_one_zero (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    m03J05H1EvalCLM x hx ((1 : ℝ), 0) = 1 := by
  simp [m03J05H1EvalCLM, m03J05H1Value]

/-- The kinetic interval integral is exactly the squared `L²` norm of the
derivative component. -/
lemma m03J05_deriv_sq_integral_eq_norm_sq (u : m03J05H1) :
    (∫ x in (0 : ℝ)..1, (u.2 x) ^ 2) = ‖u.2‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← m03J05UnitMeasure_eq_restrict_Ioc]
  calc
    (∫ x, (u.2 x) ^ 2 ∂m03J05UnitMeasure) = inner ℝ u.2 u.2 := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [inner, pow_two]
    _ = ‖u.2‖ ^ 2 := real_inner_self_eq_norm_sq u.2

/-- The kinetic part of the frozen energy is a differentiable quadratic
functional on the product Sobolev realization. -/
lemma m03J05_kinetic_differentiable :
    Differentiable ℝ (fun u : m03J05H1 =>
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, (u.2 x) ^ 2) := by
  simp_rw [m03J05_deriv_sq_integral_eq_norm_sq]
  exact differentiable_const (c := (1 / 2 : ℝ)) |>.mul
    ((ContinuousLinearMap.snd ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)).differentiable.norm_sq ℝ)

lemma m03J05_deriv_sq_intervalIntegrable (u : m03J05H1) :
    IntervalIntegrable (fun x : ℝ => (u.2 x) ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change Integrable (fun x : ℝ => (u.2 x) ^ 2) (volume.restrict (Ioc 0 1))
  rw [← m03J05UnitMeasure_eq_restrict_Ioc]
  simpa [pow_two] using (Lp.memLp u.2).integrable_mul (Lp.memLp u.2)

lemma m03J05_deriv_pairing_eq_inner (u v : m03J05H1) :
    (∫ x in (0 : ℝ)..1, u.2 x * v.2 x) = inner ℝ u.2 v.2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← m03J05UnitMeasure_eq_restrict_Ioc, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [inner, mul_comm]

/-- The reconstructed representative is continuous on the unit interval. -/
lemma m03J05H1Value_continuousOn (u : m03J05H1) :
    ContinuousOn (m03J05H1Value u) (Icc (0 : ℝ) 1) := by
  have hp := intervalIntegral.continuousOn_primitive_interval'
    (m03J05H1_deriv_intervalIntegrable u) (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)
  simpa [m03J05H1Value, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    continuousOn_const.add hp

/-- The forcing integrand in the frozen energy is interval-integrable. -/
lemma m03J05_forcing_intervalIntegrable
    (F : Lp ℝ 2 m03J05UnitMeasure) (u : m03J05H1) :
    IntervalIntegrable (fun x : ℝ => F x * m03J05H1Value u x) volume 0 1 := by
  rw [intervalIntegrable_iff]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change Integrable (fun x : ℝ => F x * m03J05H1Value u x)
    (volume.restrict (Ioc 0 1))
  rw [← m03J05UnitMeasure_eq_restrict_Ioc]
  have hF : Integrable (fun x : ℝ => F x) m03J05UnitMeasure := by
    simpa [IntegrableOn] using integrableOn_Lp_of_measure_ne_top F
      (by norm_num : (1 : ENNReal) ≤ 2)
      (measure_ne_top m03J05UnitMeasure Set.univ)
  have hae : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Icc (0 : ℝ) 1 := by
    rw [m03J05UnitMeasure_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact ⟨hx.1.le, hx.2⟩
  apply hF.mul_bdd
  · rw [m03J05UnitMeasure_eq_restrict_Ioc]
    exact ((m03J05H1Value_continuousOn u).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    exact (m03J05H1Value_abs_le u hx).trans <| by
      rw [← Real.norm_eq_abs]

/-- Reconstruction defines an `L²` function, with the bound needed for the
forcing functional. -/
lemma m03J05H1Value_memLp (u : m03J05H1) :
    MemLp (m03J05H1Value u) 2 m03J05UnitMeasure := by
  have hmeas : AEStronglyMeasurable (m03J05H1Value u) m03J05UnitMeasure := by
    rw [m03J05UnitMeasure_eq_restrict_Ioc]
    exact ((m03J05H1Value_continuousOn u).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  apply MemLp.of_bound hmeas (2 * ‖u‖)
  have haeIoc : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Ioc (0 : ℝ) 1 := by
    unfold m03J05UnitMeasure
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨hx.1, hx.2.le⟩
  filter_upwards [haeIoc] with x hx
  rw [Real.norm_eq_abs]
  exact (m03J05H1Value_abs_le u ⟨hx.1.le, hx.2⟩).trans <| by
    rw [← Real.norm_eq_abs]
    calc
      ‖u.1‖ + ‖u.2‖ ≤ ‖u‖ + ‖u‖ :=
        add_le_add (norm_fst_le u) (norm_snd_le u)
      _ = 2 * ‖u‖ := by ring

/-- The canonical `L²` reconstruction has operator norm at most two. -/
lemma m03J05H1Value_toLp_norm_le (u : m03J05H1) :
    ‖(m03J05H1Value_memLp u).toLp (m03J05H1Value u)‖ ≤ 2 * ‖u‖ := by
  rw [Lp.norm_toLp]
  have hbound : ∀ᵐ x ∂m03J05UnitMeasure,
      ‖m03J05H1Value u x‖ ≤ 2 * ‖u‖ := by
    have haeIoc : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Ioc (0 : ℝ) 1 := by
      unfold m03J05UnitMeasure
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ⟨hx.1, hx.2.le⟩
    filter_upwards [haeIoc] with x hx
    rw [Real.norm_eq_abs]
    exact (m03J05H1Value_abs_le u ⟨hx.1.le, hx.2⟩).trans <| by
      rw [← Real.norm_eq_abs]
      calc
        ‖u.1‖ + ‖u.2‖ ≤ ‖u‖ + ‖u‖ :=
          add_le_add (norm_fst_le u) (norm_snd_le u)
        _ = 2 * ‖u‖ := by ring
  have h := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hbound
  simp only [measure_univ, ENNReal.one_rpow, one_mul] at h
  calc
      ENNReal.toReal (eLpNorm (m03J05H1Value u) 2 m03J05UnitMeasure) ≤
        ENNReal.toReal (ENNReal.ofReal (2 * ‖u‖)) :=
      ENNReal.toReal_mono (by finiteness) h
    _ = 2 * ‖u‖ := ENNReal.toReal_ofReal (by positivity)

/-- Reconstruction as a bounded linear map into `L²(0,1)`. -/
noncomputable def m03J05H1ValueCLM :
    m03J05H1 →L[ℝ] Lp ℝ 2 m03J05UnitMeasure :=
  LinearMap.mkContinuous
    { toFun := fun u => (m03J05H1Value_memLp u).toLp (m03J05H1Value u)
      map_add' := fun u v => by
        rw [Lp.ext_iff]
        have hmem : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Icc (0 : ℝ) 1 := by
          unfold m03J05UnitMeasure
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
          exact ⟨hx.1.le, hx.2.le⟩
        filter_upwards [(m03J05H1Value_memLp (u + v)).coeFn_toLp,
          (m03J05H1Value_memLp u).coeFn_toLp,
          (m03J05H1Value_memLp v).coeFn_toLp,
          Lp.coeFn_add ((m03J05H1Value_memLp u).toLp (m03J05H1Value u))
            ((m03J05H1Value_memLp v).toLp (m03J05H1Value v)), hmem]
          with x huv hu hv hadd hx
        rw [huv, hadd]
        simp only [Pi.add_apply]
        rw [hu, hv, m03J05H1Value_add u v hx]
      map_smul' := fun c u => by
        rw [Lp.ext_iff]
        have hmem : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Icc (0 : ℝ) 1 := by
          unfold m03J05UnitMeasure
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
          exact ⟨hx.1.le, hx.2.le⟩
        filter_upwards [(m03J05H1Value_memLp (c • u)).coeFn_toLp,
          (m03J05H1Value_memLp u).coeFn_toLp,
          Lp.coeFn_smul c ((m03J05H1Value_memLp u).toLp (m03J05H1Value u)), hmem]
          with x hcu hu hsmul hx
        rw [hcu]
        change m03J05H1Value (c • u) x =
          (c • (m03J05H1Value_memLp u).toLp (m03J05H1Value u)) x
        rw [hsmul]
        simp only [Pi.smul_apply, smul_eq_mul, hu, m03J05H1Value_smul c u hx] }
    2 m03J05H1Value_toLp_norm_le

/-- The linear forcing term, bundled through the real `L²` pairing. -/
noncomputable def m03J05ForcingCLM
    (F : Lp ℝ 2 m03J05UnitMeasure) : m03J05H1 →L[ℝ] ℝ :=
  (innerSL ℝ F).comp m03J05H1ValueCLM

lemma m03J05ForcingCLM_apply
    (F : Lp ℝ 2 m03J05UnitMeasure) (u : m03J05H1) :
    m03J05ForcingCLM F u =
      ∫ x in (0 : ℝ)..1, F x * m03J05H1Value u x := by
  unfold m03J05ForcingCLM
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, MeasureTheory.L2.inner_def,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← m03J05UnitMeasure_eq_restrict_Ioc]
  apply integral_congr_ae
  filter_upwards [(m03J05H1Value_memLp u).coeFn_toLp] with x hx
  change ((m03J05H1Value_memLp u).toLp (m03J05H1Value u)) x * F x =
    F x * m03J05H1Value u x
  rw [hx]
  ring

/-- Consequently the frozen forcing summand is differentiable. -/
lemma m03J05_forcing_differentiable
    (F : Lp ℝ 2 m03J05UnitMeasure) :
    Differentiable ℝ (fun u : m03J05H1 =>
      ∫ x in (0 : ℝ)..1, F x * m03J05H1Value u x) := by
  simpa only [← m03J05ForcingCLM_apply F] using (m03J05ForcingCLM F).differentiable

/-- A globally Lipschitz derivative gives the quadratic Taylor bound needed
for the Nemytskii energy. -/
lemma m03J05_scalar_taylor_remainder
    {G g : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (hg : ∀ z : ℝ, HasDerivAt g (G z) z) (x y : ℝ) :
    |g y - g x - G x * (y - x)| ≤ (L : ℝ) * |y - x| ^ 2 := by
  let d := y - x
  let r : ℝ → ℝ := fun t => g (x + t * d) - g x - t * (G x * d)
  have hr (t : ℝ) : HasDerivAt r ((G (x + t * d) - G x) * d) t := by
    have haff : HasDerivAt (fun s : ℝ => x + s * d) d t :=
      by simpa using ((hasDerivAt_id t).mul_const d).const_add x
    have hcomp := (hg (x + t * d)).comp t haff
    have hlin := (hasDerivAt_id t).mul_const (G x * d)
    dsimp only [r]
    convert (hcomp.sub_const (g x)).sub hlin using 1 <;> ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖(G (x + t * d) - G x) * d‖ ≤ (L : ℝ) * |d| ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hlip := hG.norm_sub_le (x + t * d) x
    rw [add_sub_cancel_left] at hlip
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0] at hlip
    rw [Real.norm_eq_abs, abs_mul]
    have habs : t * |d| ≤ |d| := by nlinarith [abs_nonneg d]
    calc
      |G (x + t * d) - G x| * |d| ≤
          ((L : ℝ) * (t * |d|)) * |d| :=
        mul_le_mul_of_nonneg_right hlip (abs_nonneg d)
      _ ≤ ((L : ℝ) * |d|) * |d| := by
        gcongr
      _ = (L : ℝ) * |d| ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hr t).hasDerivWithinAt) hderiv
  dsimp only [r] at hmv
  simp only [one_mul, zero_mul, add_zero, sub_zero, Real.norm_eq_abs] at hmv
  simpa [d] using hmv

/-- The potential summand is a genuine interval integral for every Sobolev
input; this rules out any reliance on the Bochner integral's nonintegrable
fallback value. -/
lemma m03J05_potential_intervalIntegrable
    {G g : ℝ → ℝ} (hg : ∀ z : ℝ, HasDerivAt g (G z) z)
    (u : m03J05H1) :
    IntervalIntegrable (fun x : ℝ => g (m03J05H1Value u x)) volume 0 1 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z => (hg z).continuousAt
  exact (hgc.comp_continuousOn (m03J05H1Value_continuousOn u)).intervalIntegrable_of_Icc
    (by norm_num)

/-- The squared reconstruction integral is exactly its `L²` norm square. -/
lemma m03J05H1Value_sq_integral_eq_norm_sq (u : m03J05H1) :
    (∫ x in (0 : ℝ)..1, (m03J05H1Value u x) ^ 2) =
      ‖m03J05H1ValueCLM u‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← m03J05UnitMeasure_eq_restrict_Ioc, ← real_inner_self_eq_norm_sq,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(m03J05H1Value_memLp u).coeFn_toLp] with x hx
  have heval : (m03J05H1ValueCLM u) x =
      ((m03J05H1Value_memLp u).toLp (m03J05H1Value u)) x := rfl
  rw [heval, hx]
  simp [inner, pow_two]

/-- The reconstruction square has the uniform quadratic bound used for the
integrated Taylor remainder. -/
lemma m03J05H1Value_sq_integral_le (u : m03J05H1) :
    (∫ x in (0 : ℝ)..1, (m03J05H1Value u x) ^ 2) ≤ 4 * ‖u‖ ^ 2 := by
  rw [m03J05H1Value_sq_integral_eq_norm_sq]
  have hb : ‖m03J05H1ValueCLM u‖ ≤ 2 * ‖u‖ := m03J05H1Value_toLp_norm_le u
  nlinarith [sq_nonneg (‖m03J05H1ValueCLM u‖ - 2 * ‖u‖),
    norm_nonneg (m03J05H1ValueCLM u), norm_nonneg u]

/-- Integrated quadratic Taylor estimate for the potential energy. -/
lemma m03J05_potential_remainder_le
    {G g : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (hg : ∀ z : ℝ, HasDerivAt g (G z) z) (u h : m03J05H1) :
    |∫ x in (0 : ℝ)..1,
        (g (m03J05H1Value (u + h) x) - g (m03J05H1Value u x) -
          G (m03J05H1Value u x) * m03J05H1Value h x)| ≤
      4 * (L : ℝ) * ‖h‖ ^ 2 := by
  have hsq : IntervalIntegrable
      (fun x : ℝ => (L : ℝ) * (m03J05H1Value h x) ^ 2) volume 0 1 := by
    apply IntervalIntegrable.const_mul
    exact ((m03J05H1Value_continuousOn h).pow 2).intervalIntegrable_of_Icc
      (by norm_num)
  have hpoint : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 →
      ‖g (m03J05H1Value (u + h) x) - g (m03J05H1Value u x) -
          G (m03J05H1Value u x) * m03J05H1Value h x‖ ≤
        (L : ℝ) * (m03J05H1Value h x) ^ 2 := by
    filter_upwards [] with x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    rw [m03J05H1Value_add u h hx']
    have ht := m03J05_scalar_taylor_remainder hG hg
      (m03J05H1Value u x) (m03J05H1Value u x + m03J05H1Value h x)
    rw [Real.norm_eq_abs]
    convert ht using 1 <;> ring_nf
    rw [sq_abs]
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun x : ℝ => g (m03J05H1Value (u + h) x) - g (m03J05H1Value u x) -
      G (m03J05H1Value u x) * m03J05H1Value h x)
    (g := fun x : ℝ => (L : ℝ) * (m03J05H1Value h x) ^ 2)
    (by norm_num : (0 : ℝ) ≤ 1) hpoint hsq
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    m03J05H1Value_sq_integral_eq_norm_sq] at hi
  calc
    _ ≤ (L : ℝ) * ‖m03J05H1ValueCLM h‖ ^ 2 := hi
    _ ≤ (L : ℝ) * (4 * ‖h‖ ^ 2) := by
      gcongr
      simpa only [m03J05H1Value_sq_integral_eq_norm_sq] using
        m03J05H1Value_sq_integral_le h
    _ = 4 * (L : ℝ) * ‖h‖ ^ 2 := by ring

/-- The Nemytskii coefficient at a fixed Sobolev input belongs to `L²`. -/
lemma m03J05_nemytskii_memLp
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u : m03J05H1) :
    MemLp (fun x => G (m03J05H1Value u x)) 2 m03J05UnitMeasure := by
  have hcont : ContinuousOn (fun x => G (m03J05H1Value u x)) (Icc (0 : ℝ) 1) :=
    hG.continuous.comp_continuousOn (m03J05H1Value_continuousOn u)
  have hmeas : AEStronglyMeasurable (fun x => G (m03J05H1Value u x))
      m03J05UnitMeasure := by
    rw [m03J05UnitMeasure_eq_restrict_Ioc]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  apply MemLp.of_bound hmeas (‖G 0‖ + (L : ℝ) * (2 * ‖u‖))
  have haeIoc : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Ioc (0 : ℝ) 1 := by
    unfold m03J05UnitMeasure
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨hx.1, hx.2.le⟩
  filter_upwards [haeIoc] with x hx
  calc
    ‖G (m03J05H1Value u x)‖ =
        ‖(G (m03J05H1Value u x) - G 0) + G 0‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖G (m03J05H1Value u x) - G 0‖ + ‖G 0‖ := norm_add_le _ _
    _ = ‖G 0‖ + ‖G (m03J05H1Value u x) - G 0‖ := add_comm _ _
    _ ≤ ‖G 0‖ + (L : ℝ) * ‖m03J05H1Value u x - 0‖ := by
      gcongr
      exact hG.norm_sub_le _ _
    _ ≤ ‖G 0‖ + (L : ℝ) * (2 * ‖u‖) := by
      gcongr
      rw [sub_zero, Real.norm_eq_abs]
      exact (m03J05H1Value_abs_le u ⟨hx.1.le, hx.2⟩).trans <| by
        rw [← Real.norm_eq_abs]
        exact add_le_add (norm_fst_le u) (norm_snd_le u) |>.trans_eq (by ring)

lemma m03J05_nemytskii_difference_memLp
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u v : m03J05H1) :
    MemLp (fun x => G (m03J05H1Value u x) - G (m03J05H1Value v x))
      2 m03J05UnitMeasure := by
  exact (m03J05_nemytskii_memLp hG u).sub (m03J05_nemytskii_memLp hG v)

lemma m03J05_nemytskii_difference_pointwise_le
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u v : m03J05H1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖G (m03J05H1Value u x) - G (m03J05H1Value v x)‖ ≤
      (L : ℝ) * (2 * ‖u - v‖) := by
  calc
    _ ≤ (L : ℝ) * ‖m03J05H1Value u x - m03J05H1Value v x‖ :=
      hG.norm_sub_le _ _
    _ = (L : ℝ) * ‖m03J05H1Value (u - v) x‖ := by
      rw [m03J05H1Value_sub u v hx]
    _ ≤ (L : ℝ) * (2 * ‖u - v‖) := by
      gcongr
      rw [Real.norm_eq_abs]
      exact (m03J05H1Value_abs_le (u - v) hx).trans <| by
        rw [← Real.norm_eq_abs]
        exact add_le_add (norm_fst_le (u - v)) (norm_snd_le (u - v)) |>.trans_eq (by ring)

lemma m03J05_nemytskii_difference_toLp_norm_le
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u v : m03J05H1) :
    ‖(m03J05_nemytskii_difference_memLp hG u v).toLp
        (fun x => G (m03J05H1Value u x) - G (m03J05H1Value v x))‖ ≤
      (L : ℝ) * (2 * ‖u - v‖) := by
  rw [Lp.norm_toLp]
  have haeIcc : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Icc (0 : ℝ) 1 := by
    unfold m03J05UnitMeasure
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hae : ∀ᵐ x ∂m03J05UnitMeasure,
      ‖G (m03J05H1Value u x) - G (m03J05H1Value v x)‖ ≤
        (L : ℝ) * (2 * ‖u - v‖) := by
    filter_upwards [haeIcc] with x hx
    exact m03J05_nemytskii_difference_pointwise_le hG u v hx
  have he := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hae
  rw [m03J05UnitMeasure_apply_univ] at he
  simp only [one_div, ENNReal.one_rpow, one_mul] at he
  calc
    ENNReal.toReal (eLpNorm
        (fun x => G (m03J05H1Value u x) - G (m03J05H1Value v x))
        2 m03J05UnitMeasure) ≤ ENNReal.toReal
          (ENNReal.ofReal ((L : ℝ) * (2 * ‖u - v‖))) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    _ = (L : ℝ) * (2 * ‖u - v‖) := by
      rw [ENNReal.toReal_ofReal]
      positivity

noncomputable def m03J05NemytskiiLp
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u : m03J05H1) : Lp ℝ 2 m03J05UnitMeasure :=
  (m03J05_nemytskii_memLp hG u).toLp
    (fun x => G (m03J05H1Value u x))

lemma m03J05NemytskiiLp_coe
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u : m03J05H1) :
    (fun x => m03J05NemytskiiLp hG u x) =ᵐ[m03J05UnitMeasure]
      fun x => G (m03J05H1Value u x) := by
  exact (m03J05_nemytskii_memLp hG u).coeFn_toLp

lemma m03J05NemytskiiLp_sub_norm_le
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u v : m03J05H1) :
    ‖m03J05NemytskiiLp hG u - m03J05NemytskiiLp hG v‖ ≤
      (L : ℝ) * (2 * ‖u - v‖) := by
  let hd := m03J05_nemytskii_difference_memLp hG u v
  have heq : m03J05NemytskiiLp hG u - m03J05NemytskiiLp hG v =
      hd.toLp (fun x => G (m03J05H1Value u x) - G (m03J05H1Value v x)) := by
    rw [Lp.ext_iff]
    filter_upwards [Lp.coeFn_sub (m03J05NemytskiiLp hG u)
      (m03J05NemytskiiLp hG v), m03J05NemytskiiLp_coe hG u,
      m03J05NemytskiiLp_coe hG v, hd.coeFn_toLp] with x hsub hu hv hd'
    rw [hsub]
    change m03J05NemytskiiLp hG u x - m03J05NemytskiiLp hG v x = _
    rw [hu, hv, hd']
  rw [heq]
  exact m03J05_nemytskii_difference_toLp_norm_le hG u v

/-- Concrete non-vacuity of the bundled Nemytskii map. -/
lemma m03J05NemytskiiLp_const_one_ne_zero :
    m03J05NemytskiiLp (LipschitzWith.const (α := ℝ) (1 : ℝ))
      ((0 : ℝ), (0 : Lp ℝ 2 m03J05UnitMeasure)) ≠ 0 := by
  intro hz
  have hcoe := m03J05NemytskiiLp_coe
    (LipschitzWith.const (α := ℝ) (1 : ℝ))
    ((0 : ℝ), (0 : Lp ℝ 2 m03J05UnitMeasure))
  rw [hz] at hcoe
  have hone : ∀ᵐ _x ∂m03J05UnitMeasure, (0 : ℝ) = 1 := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal))
      (μ := m03J05UnitMeasure), hcoe] with x hzero hx
    simpa [hzero] using hx
  have hm : m03J05UnitMeasure = 0 := by simpa using hone
  have hm' := congrArg (fun μ : Measure ℝ => μ Set.univ) hm
  dsimp at hm'
  rw [m03J05UnitMeasure_apply_univ] at hm'
  simp at hm'

lemma m03J05_zeroTrace_reconstruction_norm_le
    (q : Lp ℝ 2 m03J05UnitMeasure) :
    ‖m03J05H1ValueCLM ((0 : ℝ), q)‖ ≤ 2 * ‖q‖ := by
  have h := m03J05H1Value_toLp_norm_le ((0 : ℝ), q)
  change ‖(m03J05H1Value_memLp ((0 : ℝ), q)).toLp
    (m03J05H1Value ((0 : ℝ), q))‖ ≤ _
  simpa using h

/-- The zero-trace reconstruction has the sharper operator bound one. -/
lemma m03J05_zeroTrace_reconstruction_norm_le_one
    (q : Lp ℝ 2 m03J05UnitMeasure) :
    ‖m03J05H1ValueCLM ((0 : ℝ), q)‖ ≤ ‖q‖ := by
  change ‖(m03J05H1Value_memLp ((0 : ℝ), q)).toLp
    (m03J05H1Value ((0 : ℝ), q))‖ ≤ _
  rw [Lp.norm_toLp]
  have haeIcc : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Icc (0 : ℝ) 1 := by
    unfold m03J05UnitMeasure
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hae : ∀ᵐ x ∂m03J05UnitMeasure,
      ‖m03J05H1Value ((0 : ℝ), q) x‖ ≤ ‖q‖ := by
    filter_upwards [haeIcc] with x hx
    rw [Real.norm_eq_abs]
    simpa [m03J05H1Value] using
      m03J05_intervalIntegral_le_deriv_norm ((0 : ℝ), q) hx
  have he := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hae
  rw [m03J05UnitMeasure_apply_univ] at he
  simp only [one_div, ENNReal.one_rpow, one_mul] at he
  calc
    ENNReal.toReal (eLpNorm (m03J05H1Value ((0 : ℝ), q)) 2
        m03J05UnitMeasure) ≤ ENNReal.toReal (ENNReal.ofReal ‖q‖) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    _ = ‖q‖ := ENNReal.toReal_ofReal (norm_nonneg q)

lemma m03J05_zeroTrace_reconstruction_adjoint_norm_le_one
    (z : Lp ℝ 2 m03J05UnitMeasure) :
    ‖ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) z‖ ≤ ‖z‖ := by
  let K := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hK : ‖K‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa [K] using m03J05_zeroTrace_reconstruction_norm_le_one q
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖z‖ :=
      ContinuousLinearMap.le_opNorm _ z
    _ = ‖K‖ * ‖z‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * ‖z‖ := by gcongr
    _ = ‖z‖ := one_mul _

lemma m03J05_zeroTrace_nemytskii_sub_norm_le
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (q r : Lp ℝ 2 m03J05UnitMeasure) :
    ‖m03J05NemytskiiLp hG ((0 : ℝ), q) -
        m03J05NemytskiiLp hG ((0 : ℝ), r)‖ ≤
      (2 * (L : ℝ)) * ‖q - r‖ := by
  have h := m03J05NemytskiiLp_sub_norm_le hG
    ((0 : ℝ), q) ((0 : ℝ), r)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

lemma m03J05_zeroTrace_reconstruction_opNorm_le :
    ‖m03J05H1ValueCLM.comp
        (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  simpa using m03J05_zeroTrace_reconstruction_norm_le q

lemma m03J05_zeroTrace_reconstruction_adjoint_norm_le
    (z : Lp ℝ 2 m03J05UnitMeasure) :
    ‖ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) z‖ ≤
      2 * ‖z‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))‖ * ‖z‖ :=
      ContinuousLinearMap.le_opNorm _ z
    _ = ‖m03J05H1ValueCLM.comp
        (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))‖ * ‖z‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ 2 * ‖z‖ := by
      gcongr
      exact m03J05_zeroTrace_reconstruction_opNorm_le

lemma m03J05_zeroTrace_operator_sub_norm_le
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (q r : Lp ℝ 2 m03J05UnitMeasure) :
    let K := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    ‖(q + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), q))) -
        (r + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), r)))‖ ≤
      (1 + 4 * (L : ℝ)) * ‖q - r‖ := by
  dsimp only
  let K := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hadj :
      ‖ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), q)) -
        ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), r))‖ ≤
        4 * (L : ℝ) * ‖q - r‖ := by
    rw [← map_sub]
    calc
      _ ≤ 2 * ‖m03J05NemytskiiLp hG ((0 : ℝ), q) -
          m03J05NemytskiiLp hG ((0 : ℝ), r)‖ :=
        m03J05_zeroTrace_reconstruction_adjoint_norm_le _
      _ ≤ 2 * ((2 * (L : ℝ)) * ‖q - r‖) := by
        gcongr
        exact m03J05_zeroTrace_nemytskii_sub_norm_le hG q r
      _ = 4 * (L : ℝ) * ‖q - r‖ := by ring
  calc
    _ = ‖(q - r) +
        (ContinuousLinearMap.adjoint K (m03J05NemytskiiLp hG ((0 : ℝ), q)) -
          ContinuousLinearMap.adjoint K (m03J05NemytskiiLp hG ((0 : ℝ), r)))‖ := by
      congr 1
      abel
    _ ≤ ‖q - r‖ +
        ‖ContinuousLinearMap.adjoint K (m03J05NemytskiiLp hG ((0 : ℝ), q)) -
          ContinuousLinearMap.adjoint K (m03J05NemytskiiLp hG ((0 : ℝ), r))‖ :=
      norm_add_le _ _
    _ ≤ ‖q - r‖ + 4 * (L : ℝ) * ‖q - r‖ := by gcongr
    _ = (1 + 4 * (L : ℝ)) * ‖q - r‖ := by ring

lemma m03J05_zeroTrace_nemytskii_inner_eq
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (q r : Lp ℝ 2 m03J05UnitMeasure) :
    inner ℝ
      (m03J05NemytskiiLp hG ((0 : ℝ), q) -
        m03J05NemytskiiLp hG ((0 : ℝ), r))
      (m03J05H1ValueCLM ((0 : ℝ), q - r)) =
        ∫ x in (0 : ℝ)..1,
          (G (m03J05H1Value ((0 : ℝ), q) x) -
            G (m03J05H1Value ((0 : ℝ), r) x)) *
            (m03J05H1Value ((0 : ℝ), q) x -
              m03J05H1Value ((0 : ℝ), r) x) := by
  rw [MeasureTheory.L2.inner_def,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← m03J05UnitMeasure_eq_restrict_Ioc]
  apply integral_congr_ae
  have haeIoc : ∀ᵐ x ∂m03J05UnitMeasure, x ∈ Ioc (0 : ℝ) 1 := by
    unfold m03J05UnitMeasure
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ⟨hx.1, hx.2.le⟩
  filter_upwards [Lp.coeFn_sub (m03J05NemytskiiLp hG ((0 : ℝ), q))
      (m03J05NemytskiiLp hG ((0 : ℝ), r)),
    m03J05NemytskiiLp_coe hG ((0 : ℝ), q),
    m03J05NemytskiiLp_coe hG ((0 : ℝ), r),
    (m03J05H1Value_memLp ((0 : ℝ), q - r)).coeFn_toLp,
    haeIoc] with x hsub hq hr hqr hx
  rw [hsub]
  simp only [Pi.sub_apply]
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  rw [hq, hr]
  change inner ℝ
      (G (m03J05H1Value ((0 : ℝ), q) x) -
        G (m03J05H1Value ((0 : ℝ), r) x))
      (((m03J05H1Value_memLp ((0 : ℝ), q - r)).toLp
        (m03J05H1Value ((0 : ℝ), q - r))) x) = _
  rw [hqr, show ((0 : ℝ), q - r) = ((0 : ℝ), q) - ((0 : ℝ), r) by ext <;> simp,
    m03J05H1Value_sub _ _ hx']
  simp [inner, mul_comm]

lemma m03J05_zeroTrace_operator_strongly_monotone
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G) (hmono : Monotone G)
    (q r : Lp ℝ 2 m03J05UnitMeasure) :
    let K := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    ‖q - r‖ ^ 2 ≤ inner ℝ
      ((q + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), q))) -
        (r + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), r)))) (q - r) := by
  dsimp only
  let K := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  let z := m03J05NemytskiiLp hG ((0 : ℝ), q) -
    m03J05NemytskiiLp hG ((0 : ℝ), r)
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1,
      (G (m03J05H1Value ((0 : ℝ), q) x) -
        G (m03J05H1Value ((0 : ℝ), r) x)) *
        (m03J05H1Value ((0 : ℝ), q) x -
          m03J05H1Value ((0 : ℝ), r) x) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    by_cases hqr : m03J05H1Value ((0 : ℝ), q) x ≤
        m03J05H1Value ((0 : ℝ), r) x
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hmono hqr)) (sub_nonpos.mpr hqr)
    · have hrq : m03J05H1Value ((0 : ℝ), r) x ≤
          m03J05H1Value ((0 : ℝ), q) x := le_of_not_ge hqr
      exact mul_nonneg (sub_nonneg.mpr (hmono hrq)) (sub_nonneg.mpr hrq)
  have hn' : 0 ≤ inner ℝ z (K (q - r)) := by
    dsimp [z, K]
    rw [m03J05_zeroTrace_nemytskii_inner_eq hG q r]
    exact hn
  have hadj : 0 ≤ inner ℝ (ContinuousLinearMap.adjoint K z) (q - r) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hn'
  have heq :
      (q + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), q))) -
        (r + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), r))) =
        (q - r) + ContinuousLinearMap.adjoint K z := by
    dsimp [z]
    rw [map_sub]
    abel
  rw [heq, inner_add_left, real_inner_self_eq_norm_sq]
  linarith

lemma m03J05_contraction_step_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : ℝ) (hM : 1 ≤ M) (d e : H)
    (he : ‖e‖ ≤ M * ‖d‖) (hmon : ‖d‖ ^ 2 ≤ inner ℝ e d) :
    ‖d - (1 / (2 * M ^ 2)) • e‖ ≤
      (1 - 1 / (4 * M ^ 2)) * ‖d‖ := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM2pos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  let t : ℝ := 1 / M ^ 2
  have htpos : 0 < t := by dsimp [t]; positivity
  have htM : t * M ^ 2 = 1 := by
    dsimp [t]
    field_simp
  have ht : t ≤ 1 := by
    have hM2 : 1 ≤ M ^ 2 := by nlinarith [sq_nonneg (M - 1)]
    nlinarith
  have hα : 0 ≤ t / 2 := by positivity
  have hk : 0 ≤ 1 - t / 4 := by nlinarith
  have he2 : ‖e‖ ^ 2 ≤ M ^ 2 * ‖d‖ ^ 2 := by
    nlinarith [norm_nonneg e, norm_nonneg d, sq_nonneg (M * ‖d‖ - ‖e‖)]
  have he_scaled := mul_le_mul_of_nonneg_left he2 (sq_nonneg t)
  have hmon' : ‖d‖ ^ 2 ≤ inner ℝ d e := by
    rwa [real_inner_comm]
  have hsquare : ‖d - (t / 2) • e‖ ^ 2 ≤
      ((1 - t / 4) * ‖d‖) ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hα]
    nlinarith [sq_nonneg ‖d‖, sq_nonneg ‖e‖]
  have hroot : ‖d - (t / 2) • e‖ ≤ (1 - t / 4) * ‖d‖ := by
    nlinarith [norm_nonneg (d - (t / 2) • e), norm_nonneg d,
      mul_nonneg hk (norm_nonneg d)]
  simpa [t, div_eq_mul_inv] using hroot

lemma m03J05_contractingWith_of_lipschitz_stronglyMonotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → H) (b : H) (M : ℝ) (hM : 1 ≤ M)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ M * ‖x - y‖)
    (hmon : ∀ x y, ‖x - y‖ ^ 2 ≤ inner ℝ (A x - A y) (x - y)) :
    ∃ k : NNReal, k < 1 ∧ ContractingWith k
      (fun x => x - (1 / (2 * M ^ 2)) • (A x - b)) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM2pos : 0 < M ^ 2 := sq_pos_of_pos hMpos
  have hk0 : 0 ≤ 1 - 1 / (4 * M ^ 2) := by
    have hM2 : 1 ≤ M ^ 2 := by nlinarith [sq_nonneg (M - 1)]
    have hden : 1 ≤ 4 * M ^ 2 := by nlinarith
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : 0 < 4 * M ^ 2)).2 hden
  let k : NNReal := ⟨1 - 1 / (4 * M ^ 2), hk0⟩
  have hk1 : k < 1 := by
    change 1 - 1 / (4 * M ^ 2) < 1
    exact sub_lt_self _ (div_pos zero_lt_one (by positivity))
  refine ⟨k, hk1, hk1, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have heq :
      (x - (1 / (2 * M ^ 2)) • (A x - b)) -
          (y - (1 / (2 * M ^ 2)) • (A y - b)) =
        (x - y) - (1 / (2 * M ^ 2)) • (A x - A y) := by
    module
  rw [heq]
  change ‖(x - y) - (1 / (2 * M ^ 2)) • (A x - A y)‖ ≤
    (1 - 1 / (4 * M ^ 2)) * ‖x - y‖
  exact m03J05_contraction_step_bound M hM (x - y) (A x - A y)
    (hLip x y) (hmon x y)

/-- Candidate derivative of the potential energy at `u`. -/
noncomputable def m03J05PotentialDerivative
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u : m03J05H1) : m03J05H1 →L[ℝ] ℝ :=
  (innerSL ℝ ((m03J05_nemytskii_memLp hG u).toLp
    (fun x => G (m03J05H1Value u x)))).comp m03J05H1ValueCLM

lemma m03J05PotentialDerivative_apply
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (u h : m03J05H1) :
    m03J05PotentialDerivative hG u h =
      ∫ x in (0 : ℝ)..1, G (m03J05H1Value u x) * m03J05H1Value h x := by
  unfold m03J05PotentialDerivative
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, MeasureTheory.L2.inner_def,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← m03J05UnitMeasure_eq_restrict_Ioc]
  apply integral_congr_ae
  filter_upwards [(m03J05_nemytskii_memLp hG u).coeFn_toLp,
    (m03J05H1Value_memLp h).coeFn_toLp] with x hGx hhx
  have heval : (m03J05H1ValueCLM h) x =
      ((m03J05H1Value_memLp h).toLp (m03J05H1Value h)) x := rfl
  rw [heval, hhx, hGx]
  simp [inner, mul_comm]

/-- The potential energy has the expected Fréchet derivative. -/
lemma m03J05_potential_hasFDerivAt
    {G g : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G)
    (hg : ∀ z : ℝ, HasDerivAt g (G z) z) (u : m03J05H1) :
    HasFDerivAt (fun v : m03J05H1 =>
      ∫ x in (0 : ℝ)..1, g (m03J05H1Value v x))
      (m03J05PotentialDerivative hG u) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hsquare : (fun h : m03J05H1 => ‖h‖ ^ 2) =o[nhds 0] fun h => h :=
    Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2)
  apply Asymptotics.isLittleO_iff.2
  intro c hc
  have hden : 0 < 4 * (L : ℝ) + 1 := by positivity
  have hs := Asymptotics.isLittleO_iff.1 hsquare (div_pos hc hden)
  filter_upwards [hs] with h hh
  have hprod : IntervalIntegrable
      (fun x : ℝ => G (m03J05H1Value u x) * m03J05H1Value h x) volume 0 1 := by
    exact (hG.continuous.comp_continuousOn (m03J05H1Value_continuousOn u)).mul
      (m03J05H1Value_continuousOn h) |>.intervalIntegrable_of_Icc (by norm_num)
  have hrem :
      (∫ x in (0 : ℝ)..1, g (m03J05H1Value (u + h) x)) -
          (∫ x in (0 : ℝ)..1, g (m03J05H1Value u x)) -
          m03J05PotentialDerivative hG u h =
        ∫ x in (0 : ℝ)..1,
          (g (m03J05H1Value (u + h) x) - g (m03J05H1Value u x) -
            G (m03J05H1Value u x) * m03J05H1Value h x) := by
    rw [m03J05PotentialDerivative_apply]
    rw [← intervalIntegral.integral_sub
      (m03J05_potential_intervalIntegrable hg (u + h))
      (m03J05_potential_intervalIntegrable hg u)]
    rw [← intervalIntegral.integral_sub
      ((m03J05_potential_intervalIntegrable hg (u + h)).sub
        (m03J05_potential_intervalIntegrable hg u)) hprod]
  rw [hrem, Real.norm_eq_abs]
  calc
    _ ≤ 4 * (L : ℝ) * ‖h‖ ^ 2 := m03J05_potential_remainder_le hG hg u h
    _ ≤ (4 * (L : ℝ) + 1) * ‖h‖ ^ 2 := by
      have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
      nlinarith [sq_nonneg ‖h‖]
    _ ≤ (4 * (L : ℝ) + 1) * ((c / (4 * (L : ℝ) + 1)) * ‖h‖) := by
      gcongr
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using hh
    _ = c * ‖h‖ := by field_simp

/-- Monotonicity makes the nonlinear difference pairing nonnegative. -/
lemma m03J05_nemytskii_difference_integral_nonneg
    {G : ℝ → ℝ} {L : NNReal} (hG : LipschitzWith L G) (hmono : Monotone G)
    (u v : m03J05H1) :
    0 ≤ ∫ x in (0 : ℝ)..1,
      (G (m03J05H1Value u x) - G (m03J05H1Value v x)) *
        (m03J05H1Value u x - m03J05H1Value v x) := by
  have hcont : ContinuousOn (fun x : ℝ =>
      (G (m03J05H1Value u x) - G (m03J05H1Value v x)) *
        (m03J05H1Value u x - m03J05H1Value v x)) (Icc (0 : ℝ) 1) := by
    exact ((hG.continuous.comp_continuousOn (m03J05H1Value_continuousOn u)).sub
      (hG.continuous.comp_continuousOn (m03J05H1Value_continuousOn v))).mul
        ((m03J05H1Value_continuousOn u).sub (m03J05H1Value_continuousOn v))
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  by_cases huv : m03J05H1Value u x ≤ m03J05H1Value v x
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hmono huv)) (sub_nonpos.mpr huv)
  · have hvu : m03J05H1Value v x ≤ m03J05H1Value u x := le_of_not_ge huv
    exact mul_nonneg (sub_nonneg.mpr (hmono hvu)) (sub_nonneg.mpr hvu)

def m03J05MixedEigenvalue (n : ℕ) : ℝ :=
  (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) ^ 2

def m03J05MixedEigenfunction (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)

/-- The explicit mixed eigenfunctions satisfy the Dirichlet condition at the
left endpoint. -/
lemma m03J05MixedEigenfunction_zero (n : ℕ) :
    m03J05MixedEigenfunction n 0 = 0 := by
  simp [m03J05MixedEigenfunction]

/-- Every displayed eigenfunction is genuinely nonzero. -/
lemma m03J05MixedEigenfunction_nonzero (n : ℕ) :
    m03J05MixedEigenfunction n ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero
    (1 / (((2 * n + 1 : ℕ) : ℝ)))
  have hden : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have harg :
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) *
          (1 / (((2 * n + 1 : ℕ) : ℝ))) = Real.pi / 2 := by
    field_simp
  simp only [m03J05MixedEigenfunction, Pi.zero_apply] at hvalue
  rw [harg, Real.sin_pi_div_two] at hvalue
  norm_num at hvalue

/-- The frequency in the explicit mixed spectrum is strictly positive. -/
lemma m03J05MixedFrequency_pos (n : ℕ) :
    0 < ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 := by
  positivity

/-- Consequently every displayed mixed eigenvalue is strictly positive. -/
lemma m03J05MixedEigenvalue_pos (n : ℕ) :
    0 < m03J05MixedEigenvalue n := by
  unfold m03J05MixedEigenvalue
  positivity

/-- The half-integer frequencies are strictly increasing. -/
lemma m03J05MixedFrequency_strictMono : StrictMono (fun n : ℕ ↦
    ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) := by
  intro a b hab
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  norm_num [Nat.cast_add, Nat.cast_mul]
  nlinarith [Real.pi_pos]

/-- Hence the displayed mixed eigenvalues are pairwise strictly ordered. -/
lemma m03J05MixedEigenvalue_strictMono : StrictMono m03J05MixedEigenvalue := by
  intro a b hab
  have hfreq := m03J05MixedFrequency_strictMono hab
  have hapos := m03J05MixedFrequency_pos a
  have hbpos := m03J05MixedFrequency_pos b
  simp only [m03J05MixedEigenvalue]
  nlinarith

lemma m03J05MixedEigenvalue_injective : Function.Injective m03J05MixedEigenvalue :=
  m03J05MixedEigenvalue_strictMono.injective

/-- The first derivative of each displayed mixed eigenfunction. -/
lemma m03J05MixedEigenfunction_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (m03J05MixedEigenfunction n)
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)) x := by
  unfold m03J05MixedEigenfunction
  convert (((hasDerivAt_id x).const_mul
    (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)).sin) using 1 <;>
      simp only [id_eq] <;> ring

/-- The derivative coordinate of each mixed mode belongs to the frozen
`L²(0,1)` space. -/
lemma m03J05MixedEigenfunction_deriv_memLp (n : ℕ) :
    MemLp (fun x : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x))
      2 m03J05UnitMeasure := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x))
      m03J05UnitMeasure := by fun_prop
  apply MemLp.of_bound hmeas
    (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (m03J05MixedFrequency_pos n)]
  exact mul_le_of_le_one_right (m03J05MixedFrequency_pos n).le
    (Real.abs_cos_le_one _)

/-- Reconstructing a mixed mode from its classical derivative recovers the
mode pointwise. -/
lemma m03J05MixedEigenfunction_integral_deriv (n : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x,
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * t)) =
      m03J05MixedEigenfunction n x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := m03J05MixedEigenfunction n)
    (f' := fun t : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * t))
    (a := (0 : ℝ)) (b := x)
    (fun y _ => m03J05MixedEigenfunction_hasDerivAt n y)
    ((show Continuous (fun t : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * t)) by
          fun_prop).intervalIntegrable 0 x)
  simpa [m03J05MixedEigenfunction_zero] using h

/-- The derivative coordinate of the `n`th mixed eigenfunction, bundled in
the frozen real `L²(0,1)` space. -/
noncomputable def m03J05MixedDerivCoordinate (n : ℕ) :
    Lp ℝ 2 m03J05UnitMeasure :=
  (m03J05MixedEigenfunction_deriv_memLp n).toLp (fun x : ℝ =>
    ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
      Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x))

/-- The bundled coordinate has the expected classical representative almost
everywhere on the frozen interval. -/
lemma m03J05MixedDerivCoordinate_coeFn_ae (n : ℕ) :
    (fun x : ℝ => m03J05MixedDerivCoordinate n x) =ᵐ[m03J05UnitMeasure]
      (fun x : ℝ =>
        ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
          Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)) := by
  exact (m03J05MixedEigenfunction_deriv_memLp n).coeFn_toLp

/-- Pairing the bundled coordinate with an arbitrary `Lp` test is the
classical derivative pairing. -/
lemma m03J05MixedDerivCoordinate_inner (n : ℕ)
    (r : Lp ℝ 2 m03J05UnitMeasure) :
    inner ℝ (m03J05MixedDerivCoordinate n) r =
      ∫ x in (0 : ℝ)..1,
        (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
          Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)) * r x := by
  rw [← m03J05_deriv_pairing_eq_inner
    ((0 : ℝ), m03J05MixedDerivCoordinate n) ((0 : ℝ), r)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  have hcoe := m03J05MixedDerivCoordinate_coeFn_ae n
  have hcoe' := ae_mono
    (le_of_eq m03J05UnitMeasure_eq_restrict_Ioc.symm) hcoe
  filter_upwards [hcoe'] with x hx
  rw [hx]

/-- Every zero-trace reconstruction is absolutely continuous on the unit
interval, even though its derivative coordinate is represented only in
`L²`. -/
lemma m03J05H1Value_zero_absolutelyContinuousOnInterval
    (r : Lp ℝ 2 m03J05UnitMeasure) :
    AbsolutelyContinuousOnInterval
      (m03J05H1Value ((0 : ℝ), r)) 0 1 := by
  have hac := IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (m03J05H1_deriv_intervalIntegrable ((0 : ℝ), r))
    (c := (0 : ℝ)) (by simp [uIcc_of_le] : (0 : ℝ) ∈ uIcc 0 1)
  have hfun : m03J05H1Value ((0 : ℝ), r) =
      (fun x : ℝ => ∫ v in (0 : ℝ)..x, r v) := by
    funext x
    simp [m03J05H1Value]
  rw [hfun]
  exact hac

/-- The ordinary derivative of a zero-trace reconstruction agrees almost
everywhere with its bundled derivative coordinate on the unit interval. -/
lemma m03J05H1Value_zero_deriv_ae
    (r : Lp ℝ 2 m03J05UnitMeasure) :
    (fun x : ℝ => deriv (m03J05H1Value ((0 : ℝ), r)) x) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 1)] (fun x => r x) := by
  have hderiv :=
    (m03J05H1_deriv_intervalIntegrable ((0 : ℝ), r)).ae_hasDerivAt_integral
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae hderiv] with x hx hdx
  have hx' : x ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1.le, hx.2⟩
  have h := hdx hx' 0 (by simp [uIcc_of_le] : (0 : ℝ) ∈ uIcc 0 1)
  have hfun : m03J05H1Value ((0 : ℝ), r) =
      (fun y : ℝ => ∫ t in (0 : ℝ)..y, r t) := by
    funext y
    simp [m03J05H1Value]
  rw [hfun]
  exact h.deriv

/-- The classical derivative of each explicit mixed mode is absolutely
continuous on the unit interval. -/
lemma m03J05MixedEigenfunction_deriv_absolutelyContinuousOnInterval
    (n : ℕ) :
    AbsolutelyContinuousOnInterval
      (deriv (m03J05MixedEigenfunction n)) 0 1 := by
  have hfun : deriv (m03J05MixedEigenfunction n) = fun x : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x) := by
    funext x
    exact (m03J05MixedEigenfunction_hasDerivAt n x).deriv
  rw [hfun]
  have hc : ContDiffOn ℝ 1 (fun x : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x))
      (Icc (0 : ℝ) 1) := by
    fun_prop
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num)
    (convex_Icc (0 : ℝ) 1) isCompact_Icc
  have hKu : LipschitzOnWith K (fun x : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x))
      (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hK
  exact hKu.absolutelyContinuousOnInterval

/-- Reconstructing the bundled derivative coordinate gives the corresponding
mixed eigenfunction on the whole interval. -/
lemma m03J05MixedDerivCoordinate_reconstructs (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    m03J05H1Value ((0 : ℝ), m03J05MixedDerivCoordinate n) x =
      m03J05MixedEigenfunction n x := by
  let f : ℝ → ℝ := fun t =>
    ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
      Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * t)
  have hcoe : (fun t => m03J05MixedDerivCoordinate n t) =ᵐ[m03J05UnitMeasure]
      f := (m03J05MixedEigenfunction_deriv_memLp n).coeFn_toLp
  have hmeasure : volume.restrict (Ioc (0 : ℝ) x) ≤ m03J05UnitMeasure := by
    rw [m03J05UnitMeasure_eq_restrict_Ioc]
    exact Measure.restrict_mono (Ioc_subset_Ioc_right hx.2) le_rfl
  have hcoe' : (fun t => m03J05MixedDerivCoordinate n t) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) x)] f := ae_mono hmeasure hcoe
  have hint : (∫ t in (0 : ℝ)..x, m03J05MixedDerivCoordinate n t) =
      ∫ t in (0 : ℝ)..x, f t := by
    rw [intervalIntegral.integral_of_le hx.1,
      intervalIntegral.integral_of_le hx.1]
    exact integral_congr_ae hcoe'
  unfold m03J05H1Value
  rw [Prod.fst, zero_add, hint]
  exact m03J05MixedEigenfunction_integral_deriv n x

/-- The bundled derivative coordinate is nonzero. -/
lemma m03J05MixedDerivCoordinate_ne_zero (n : ℕ) :
    m03J05MixedDerivCoordinate n ≠ 0 := by
  intro hzero
  let x : ℝ := 1 / (((2 * n + 1 : ℕ) : ℝ))
  have hx : x ∈ Icc (0 : ℝ) 1 := by
    dsimp [x]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      norm_num
  have hrec := m03J05MixedDerivCoordinate_reconstructs n x hx
  rw [hzero] at hrec
  have harg :
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x = Real.pi / 2 := by
    dsimp [x]
    field_simp
  have hvalue : m03J05MixedEigenfunction n x = 1 := by
    unfold m03J05MixedEigenfunction
    rw [harg, Real.sin_pi_div_two]
  rw [hvalue] at hrec
  simpa [m03J05H1Value] using hrec

/-- Each explicit mixed eigenfunction is exactly the zero-trace
reconstruction of an `Lp` derivative coordinate. -/
lemma m03J05_exists_derivCoordinate_reconstructs_mixedEigenfunction (n : ℕ) :
    ∃ q : Lp ℝ 2 m03J05UnitMeasure,
      ∀ x ∈ Icc (0 : ℝ) 1,
        m03J05H1Value ((0 : ℝ), q) x = m03J05MixedEigenfunction n x := by
  let f : ℝ → ℝ := fun x =>
    ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
      Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)
  have hf : MemLp f 2 m03J05UnitMeasure :=
    m03J05MixedEigenfunction_deriv_memLp n
  let q : Lp ℝ 2 m03J05UnitMeasure := hf.toLp f
  refine ⟨q, ?_⟩
  intro x hx
  have hcoe : (fun t => q t) =ᵐ[m03J05UnitMeasure] f := hf.coeFn_toLp
  have hmeasure : volume.restrict (Ioc (0 : ℝ) x) ≤ m03J05UnitMeasure := by
    rw [m03J05UnitMeasure_eq_restrict_Ioc]
    exact Measure.restrict_mono (Ioc_subset_Ioc_right hx.2) le_rfl
  have hcoe' : (fun t => q t) =ᵐ[volume.restrict (Ioc (0 : ℝ) x)] f :=
    ae_mono hmeasure hcoe
  have hint : (∫ t in (0 : ℝ)..x, q t) = ∫ t in (0 : ℝ)..x, f t := by
    rw [intervalIntegral.integral_of_le hx.1,
      intervalIntegral.integral_of_le hx.1]
    exact integral_congr_ae hcoe'
  unfold m03J05H1Value
  rw [Prod.fst, zero_add, hint]
  exact m03J05MixedEigenfunction_integral_deriv n x

/-- Distinct indices give distinct mixed eigenfunctions. -/
lemma m03J05MixedEigenfunction_injective :
    Function.Injective m03J05MixedEigenfunction := by
  intro a b hab
  have hderiv := congrArg (fun f : ℝ → ℝ ↦ deriv f 0) hab
  dsimp only at hderiv
  rw [(m03J05MixedEigenfunction_hasDerivAt a 0).deriv,
    (m03J05MixedEigenfunction_hasDerivAt b 0).deriv] at hderiv
  simp only [mul_zero, Real.cos_zero, mul_one] at hderiv
  exact m03J05MixedFrequency_strictMono.injective hderiv

/-- The explicit eigenfunctions satisfy the right Neumann boundary condition. -/
lemma m03J05MixedEigenfunction_deriv_one (n : ℕ) :
    deriv (m03J05MixedEigenfunction n) 1 = 0 := by
  rw [(m03J05MixedEigenfunction_hasDerivAt n 1).deriv]
  suffices Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)) = 0 by
    simpa using congrArg
      (fun z : ℝ => (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * z) this
  rw [Real.cos_eq_zero_iff]
  refine ⟨(n : ℤ), ?_⟩
  push_cast
  ring

/-- Every mixed sine mode has squared `L²(0,1)` norm `1 / 2`. -/
lemma m03J05MixedEigenfunction_sq_integral (n : ℕ) :
    (∫ x in (0 : ℝ)..1, (m03J05MixedEigenfunction n x) ^ 2) = 1 / 2 := by
  let w : ℝ := ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2
  have hw : 0 < w := by
    dsimp [w]
    exact m03J05MixedFrequency_pos n
  have hcos : Real.cos w = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨(n : ℤ), ?_⟩
    dsimp [w]
    push_cast
    ring
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (f := fun y : ℝ ↦ Real.sin y ^ 2) w
  rw [integral_sin_sq] at hscale
  have heq :
      w * (∫ x in (0 : ℝ)..1, (Real.sin (w * x)) ^ 2) = w / 2 := by
    simpa [hcos] using hscale
  change (∫ x in (0 : ℝ)..1, (Real.sin (w * x)) ^ 2) = 1 / 2
  nlinarith

/-- A cosine with nonzero frequency and an integral number of half-turns has
zero integral on the unit interval.  This is the scalar calculation used in
pairwise orthogonality of the mixed modes. -/
lemma m03J05_integral_cos_mul_eq_zero {w : ℝ} (hw : w ≠ 0)
    (hsin : Real.sin w = 0) :
    (∫ x in (0 : ℝ)..1, Real.cos (w * x)) = 0 := by
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (f := Real.cos) w
  rw [integral_cos] at hscale
  have : w * (∫ x in (0 : ℝ)..1, Real.cos (w * x)) = 0 := by
    simpa [hsin] using hscale
  exact (mul_eq_zero.mp this).resolve_left hw

/-- Distinct mixed sine modes are orthogonal on `(0,1)`. -/
lemma m03J05MixedEigenfunction_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    (∫ x in (0 : ℝ)..1,
      m03J05MixedEigenfunction n x * m03J05MixedEigenfunction m x) = 0 := by
  let wn : ℝ := ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2
  let wm : ℝ := ((2 * m + 1 : ℕ) : ℝ) * Real.pi / 2
  have hdiff : wn - wm ≠ 0 := by
    intro h
    have : wn = wm := sub_eq_zero.mp h
    exact hnm (m03J05MixedFrequency_strictMono.injective this)
  have hsum : wn + wm ≠ 0 := by
    have hnpos : 0 < wn := m03J05MixedFrequency_pos n
    have hmpos : 0 < wm := m03J05MixedFrequency_pos m
    positivity
  have hsindiff : Real.sin (wn - wm) = 0 := by
    rw [Real.sin_eq_zero_iff]
    refine ⟨(n : ℤ) - (m : ℤ), ?_⟩
    dsimp [wn, wm]
    push_cast
    ring
  have hsinsum : Real.sin (wn + wm) = 0 := by
    rw [Real.sin_eq_zero_iff]
    refine ⟨(n : ℤ) + (m : ℤ) + 1, ?_⟩
    dsimp [wn, wm]
    push_cast
    ring
  have hcosdiff := m03J05_integral_cos_mul_eq_zero hdiff hsindiff
  have hcossum := m03J05_integral_cos_mul_eq_zero hsum hsinsum
  have htwice : 2 * (∫ x in (0 : ℝ)..1,
      Real.sin (wn * x) * Real.sin (wm * x)) = 0 := by
    rw [← intervalIntegral.integral_const_mul]
    calc
      (∫ x in (0 : ℝ)..1, 2 * (Real.sin (wn * x) * Real.sin (wm * x))) =
          ∫ x in (0 : ℝ)..1,
            Real.cos ((wn - wm) * x) - Real.cos ((wn + wm) * x) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp only
              have ht := Real.two_mul_sin_mul_sin (wn * x) (wm * x)
              convert ht using 1 <;> ring
      _ = 0 := by
        have hi1 : IntervalIntegrable (fun x : ℝ =>
            Real.cos ((wn - wm) * x)) volume 0 1 := by
          exact (Real.continuous_cos.comp
            (continuous_const.mul continuous_id)).intervalIntegrable 0 1
        have hi2 : IntervalIntegrable (fun x : ℝ =>
            Real.cos ((wn + wm) * x)) volume 0 1 := by
          exact (Real.continuous_cos.comp
            (continuous_const.mul continuous_id)).intervalIntegrable 0 1
        rw [intervalIntegral.integral_sub hi1 hi2, hcosdiff, hcossum, sub_zero]
  change (∫ x in (0 : ℝ)..1, Real.sin (wn * x) * Real.sin (wm * x)) = 0
  linarith

/-- The complete scalar Gram matrix of the displayed mixed modes. -/
lemma m03J05MixedEigenfunction_gram (n m : ℕ) :
    (∫ x in (0 : ℝ)..1,
      m03J05MixedEigenfunction n x * m03J05MixedEigenfunction m x) =
        if n = m then 1 / 2 else 0 := by
  by_cases h : n = m
  · subst m
    simp only [if_pos rfl, ← pow_two]
    exact m03J05MixedEigenfunction_sq_integral n
  · rw [if_neg h]
    exact m03J05MixedEigenfunction_orthogonal h

/-- The explicit mixed modes are linearly independent. -/
lemma m03J05MixedEigenfunction_linearIndependent :
    LinearIndependent ℝ m03J05MixedEigenfunction := by
  rw [linearIndependent_iff']
  intro s g h i hi
  have hpoint : ∀ x : ℝ,
      (∑ j ∈ s, g j * m03J05MixedEigenfunction j x) = 0 := by
    intro x
    simpa [Pi.smul_apply] using congrFun h x
  have hint : (∫ x in (0 : ℝ)..1,
      (∑ j ∈ s, g j * m03J05MixedEigenfunction j x) *
        m03J05MixedEigenfunction i x) = 0 := by
    rw [intervalIntegral.integral_congr (fun x _ => by rw [hpoint x, zero_mul])]
    simp
  simp_rw [Finset.sum_mul] at hint
  rw [intervalIntegral.integral_finset_sum] at hint
  · have hcollapse : (∑ j ∈ s, ∫ x in (0 : ℝ)..1,
        (g j * m03J05MixedEigenfunction j x) *
          m03J05MixedEigenfunction i x) = g i / 2 := by
      rw [Finset.sum_eq_single i]
      · rw [show (∫ x in (0 : ℝ)..1,
            (g i * m03J05MixedEigenfunction i x) *
              m03J05MixedEigenfunction i x) =
            g i * ∫ x in (0 : ℝ)..1,
              m03J05MixedEigenfunction i x *
                m03J05MixedEigenfunction i x by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x _
              ring]
        rw [m03J05MixedEigenfunction_gram]
        simp
        ring
      · intro j hj hji
        rw [show (∫ x in (0 : ℝ)..1,
            (g j * m03J05MixedEigenfunction j x) *
              m03J05MixedEigenfunction i x) =
            g j * ∫ x in (0 : ℝ)..1,
              m03J05MixedEigenfunction j x *
                m03J05MixedEigenfunction i x by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x _
              ring]
        rw [m03J05MixedEigenfunction_gram]
        simp [hji]
      · exact fun hni => (hni hi).elim
    rw [hcollapse] at hint
    linarith
  · intro j hj
    exact ((show Continuous (fun x : ℝ =>
        g j * m03J05MixedEigenfunction j x) by
          unfold m03J05MixedEigenfunction
          fun_prop).mul
        (show Continuous (m03J05MixedEigenfunction i) by
          unfold m03J05MixedEigenfunction
          fun_prop)).intervalIntegrable 0 1

/-- Interval Fourier coefficients determine an `L²` function.  This is the
Parseval uniqueness input needed for the odd antiperiodic extension. -/
lemma m03J05_ae_eq_zero_of_fourierCoeffOn_eq_zero
    {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hcoeff : ∀ i : ℤ, fourierCoeffOn hab f i = 0) :
    f =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hs := hasSum_sq_fourierCoeffOn hab hf
  have hz : HasSum (fun i : ℤ =>
      ‖fourierCoeffOn hab f i‖ ^ 2) 0 := by
    simpa [hcoeff] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)
  have heq := hs.unique hz
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hint : (∫ x in a..b, ‖f x‖ ^ 2) = 0 := by
    simpa [smul_eq_mul, hba] using
      (show (b - a)⁻¹ * (∫ x in a..b, ‖f x‖ ^ 2) = 0 by simpa using heq.symm)
  have hint' : (∫ x, ‖f x‖ ^ 2 ∂volume.restrict (Ioc a b)) = 0 := by
    rwa [intervalIntegral.integral_of_le hab.le] at hint
  have haeNorm : (fun x => ‖f x‖ ^ 2) =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hf.integrable_norm_pow (by norm_num))).1 hint'
  filter_upwards [haeNorm] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- Odd, endpoint-even extension used to turn mixed sine coefficients on
`(0,1)` into ordinary Fourier coefficients on `(-2,2)`. -/
noncomputable def m03J05MixedExtension (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  let g := fun y : ℝ => if y ≤ 1 then f y else f (2 - y)
  if 0 < x then g x else if x < 0 then -g (-x) else 0

/-- Concrete non-vacuity of the extension construction. -/
lemma m03J05MixedExtension_const_one_half :
    m03J05MixedExtension (fun _ : ℝ => (1 : ℂ)) (1 / 2 : ℝ) = 1 := by
  simp [m03J05MixedExtension]

lemma m03J05MixedExtension_of_pos {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) :
    m03J05MixedExtension f x = if x ≤ 1 then f x else f (2 - x) := by
  simp [m03J05MixedExtension, hx]

lemma m03J05MixedExtension_of_neg {f : ℝ → ℂ} {x : ℝ} (hx : x < 0) :
    m03J05MixedExtension f x =
      -(if -x ≤ 1 then f (-x) else f (2 + x)) := by
  rw [m03J05MixedExtension, if_neg (not_lt.mpr hx.le), if_pos hx]
  dsimp only
  congr 2
  ring

lemma m03J05MixedExtension_neg (f : ℝ → ℂ) (x : ℝ) :
    m03J05MixedExtension f (-x) = -m03J05MixedExtension f x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [m03J05MixedExtension_of_pos (neg_pos.mpr hx),
      m03J05MixedExtension_of_neg hx]
    congr 2
    ring
  · simp [m03J05MixedExtension]
  · rw [m03J05MixedExtension_of_neg (neg_lt_zero.mpr hx),
      m03J05MixedExtension_of_pos hx]
    simp only [neg_neg]
    congr 2

lemma m03J05MixedExtension_reflect_two {f : ℝ → ℂ} {x : ℝ}
    (hx0 : 0 < x) (hx2 : x < 2) :
    m03J05MixedExtension f (2 - x) = m03J05MixedExtension f x := by
  have hpos : 0 < 2 - x := sub_pos.mpr hx2
  rw [m03J05MixedExtension_of_pos hx0, m03J05MixedExtension_of_pos hpos]
  by_cases hx1 : x ≤ 1
  · rcases hx1.eq_or_lt with rfl | hx1'
    · norm_num
    · have hnot : ¬2 - x ≤ 1 := by linarith
      simp [hx1, hnot]
  · have hle : 2 - x ≤ 1 := by linarith
    simp [hx1, hle]

lemma m03J05MixedExtension_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (m03J05MixedExtension f) 2 (volume.restrict (Ioc (-2 : ℝ) 2)) := by
  let f0 : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator f
  have hf0 : MemLp f0 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc).2 hf
  let g : ℝ → ℂ := fun y => if y ≤ 1 then f0 y else f0 (2 - y)
  have hreflect : MemLp (fun y : ℝ => f0 (2 - y)) 2 volume := by
    simpa [Function.comp_def] using hf0.comp_measurePreserving
      (Measure.measurePreserving_sub_left volume (2 : ℝ))
  have hg : MemLp g 2 volume := by
    have hleft := hf0.mono_measure
      (Measure.restrict_le_self (μ := volume) (s := Iic (1 : ℝ)))
    have hright := hreflect.mono_measure
      (Measure.restrict_le_self (μ := volume) (s := (Iic (1 : ℝ))ᶜ))
    simpa [g, Set.piecewise, mem_Iic] using
      MemLp.piecewise measurableSet_Iic hleft hright
  have hgneg : MemLp (fun x : ℝ => -g (-x)) 2 volume := by
    exact (hg.comp_measurePreserving (Measure.measurePreserving_neg volume)).neg
  have hzero : MemLp (fun _ : ℝ => (0 : ℂ)) 2 volume := MemLp.zero
  have hnonpos : MemLp (fun x : ℝ => if x < 0 then -g (-x) else 0) 2 volume := by
    simpa [Set.piecewise, mem_Iio] using MemLp.piecewise measurableSet_Iio
      (hgneg.mono_measure
        (Measure.restrict_le_self (μ := volume) (s := Iio (0 : ℝ))))
      (hzero.mono_measure
        (Measure.restrict_le_self (μ := volume) (s := (Iio (0 : ℝ))ᶜ)))
  have hall : MemLp (fun x : ℝ => if 0 < x then g x else
      if x < 0 then -g (-x) else 0) 2 volume := by
    simpa [Set.piecewise, mem_Ioi] using MemLp.piecewise measurableSet_Ioi
      (hg.mono_measure
        (Measure.restrict_le_self (μ := volume) (s := Ioi (0 : ℝ))))
      (hnonpos.mono_measure
        (Measure.restrict_le_self (μ := volume) (s := (Ioi (0 : ℝ))ᶜ)))
  have hr := hall.mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioc (-2 : ℝ) 2))
  apply (memLp_congr_ae ?_).2 hr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    Measure.ae_ne (volume.restrict (Ioc (-2 : ℝ) 2)) 2] with x hx hxne
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · have hnpos : ¬0 < x := not_lt.mpr hxneg.le
    by_cases hxm : -1 ≤ x
    · have hcond : -x ≤ 1 := by linarith
      have hmem : -x ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith
      simp [m03J05MixedExtension, g, f0, hxneg, hnpos, hcond, hmem]
    · have hcond : ¬-x ≤ 1 := by linarith
      have hmem : 2 + x ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith [hx.1]
      simp [m03J05MixedExtension, g, f0, hxneg, hnpos, hcond, hmem]
  · simp [m03J05MixedExtension]
  · by_cases hx1 : x ≤ 1
    · have hmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hxpos, hx1⟩
      simp [m03J05MixedExtension, g, f0, hxpos, hx1, hmem]
    · have hxlt : x < 2 := lt_of_le_of_ne hx.2 hxne
      have hmem : 2 - x ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith
      simp [m03J05MixedExtension, g, f0, hxpos, hx1, hmem]

lemma m03J05_integral_symmetric_eq_zero_of_odd (q : ℝ → ℂ)
    (hqneg : ∀ x : ℝ, q (-x) = -q x)
    (hleft : IntervalIntegrable q volume (-2) 0)
    (hright : IntervalIntegrable q volume 0 2) :
    (∫ x in (-2 : ℝ)..2, q x) = 0 := by
  have hchange : (∫ x in (-2 : ℝ)..0, q x) = -∫ x in (0 : ℝ)..2, q x := by
    have hc : (∫ x in (-2 : ℝ)..0, q x) =
        ∫ x in (0 : ℝ)..2, q (-x) := by
      simpa using
        (intervalIntegral.integral_comp_neg (f := q) (a := 0) (b := 2)).symm
    rw [hc]
    simp_rw [hqneg]
    exact intervalIntegral.integral_neg
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hchange]
  exact neg_add_cancel _

lemma m03J05MixedExtension_mul_even_integral_eq_zero (f h : ℝ → ℂ)
    (heven : ∀ x : ℝ, h (-x) = h x)
    (hleft : IntervalIntegrable
      (fun x => h x * m03J05MixedExtension f x) volume (-2) 0)
    (hright : IntervalIntegrable
      (fun x => h x * m03J05MixedExtension f x) volume 0 2) :
    (∫ x in (-2 : ℝ)..2, h x * m03J05MixedExtension f x) = 0 := by
  apply m03J05_integral_symmetric_eq_zero_of_odd _ ?_ hleft hright
  intro x
  rw [heven, m03J05MixedExtension_neg]
  ring

lemma m03J05_integral_zero_two_eq_zero_of_reflect_neg (q : ℝ → ℂ)
    (hreflect : ∀ x : ℝ, q (2 - x) = -q x)
    (hleft : IntervalIntegrable q volume 0 1)
    (hright : IntervalIntegrable q volume 1 2) :
    (∫ x in (0 : ℝ)..2, q x) = 0 := by
  have hchange : (∫ x in (1 : ℝ)..2, q x) =
      -∫ x in (0 : ℝ)..1, q x := by
    have hc : (∫ x in (1 : ℝ)..2, q x) =
        ∫ x in (0 : ℝ)..1, q (2 - x) := by
      convert
        (intervalIntegral.integral_comp_sub_left (f := q) (a := 0) (b := 1) 2).symm using 1 <;>
        norm_num
    rw [hc]
    simp_rw [hreflect]
    exact intervalIntegral.integral_neg
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hchange]
  exact add_neg_cancel _

lemma m03J05_integral_zero_two_eq_two_mul_of_reflect (q : ℝ → ℂ)
    (hreflect : ∀ x : ℝ, q (2 - x) = q x)
    (hleft : IntervalIntegrable q volume 0 1)
    (hright : IntervalIntegrable q volume 1 2) :
    (∫ x in (0 : ℝ)..2, q x) = 2 * ∫ x in (0 : ℝ)..1, q x := by
  have hchange : (∫ x in (1 : ℝ)..2, q x) =
      ∫ x in (0 : ℝ)..1, q x := by
    have hc : (∫ x in (1 : ℝ)..2, q x) =
        ∫ x in (0 : ℝ)..1, q (2 - x) := by
      convert
        (intervalIntegral.integral_comp_sub_left (f := q) (a := 0) (b := 1) 2).symm using 1 <;>
        norm_num
    rw [hc]
    exact intervalIntegral.integral_congr (fun x _ => hreflect x)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hchange]
  ring

lemma m03J05_sin_fourier_reflect (k : ℤ) (x : ℝ) :
    Real.sin (((k : ℝ) * Real.pi / 2) * (2 - x)) =
      -((-1 : ℝ) ^ k * Real.sin (((k : ℝ) * Real.pi / 2) * x)) := by
  rw [← Real.sin_int_mul_pi_sub
    ((((k : ℝ) * Real.pi / 2) * x)) k]
  congr 1
  push_cast
  ring

lemma m03J05_sin_fourier_reflect_of_even (k : ℤ) (hk : Even k) (x : ℝ) :
    Real.sin (((k : ℝ) * Real.pi / 2) * (2 - x)) =
      -Real.sin (((k : ℝ) * Real.pi / 2) * x) := by
  rw [m03J05_sin_fourier_reflect, hk.neg_one_zpow]
  simp

lemma m03J05_sin_fourier_reflect_of_odd (k : ℤ) (hk : Odd k) (x : ℝ) :
    Real.sin (((k : ℝ) * Real.pi / 2) * (2 - x)) =
      Real.sin (((k : ℝ) * Real.pi / 2) * x) := by
  rw [m03J05_sin_fourier_reflect, hk.neg_one_zpow]
  simp

lemma m03J05_sin_mul_extension_reflect_ae_of_even (f : ℝ → ℂ) (k : ℤ)
    (hk : Even k) :
    (fun x : ℝ => (Real.sin (((k : ℝ) * Real.pi / 2) * (2 - x)) : ℂ) *
        m03J05MixedExtension f (2 - x)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x : ℝ => -((Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [m03J05_sin_fourier_reflect_of_even k hk x,
    m03J05MixedExtension_reflect_two hx.1 (by linarith [hx.2])]
  push_cast
  ring

lemma m03J05_sin_mul_extension_reflect_ae_of_odd (f : ℝ → ℂ) (k : ℤ)
    (hk : Odd k) :
    (fun x : ℝ => (Real.sin (((k : ℝ) * Real.pi / 2) * (2 - x)) : ℂ) *
        m03J05MixedExtension f (2 - x)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun x : ℝ => (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [m03J05_sin_fourier_reflect_of_odd k hk x,
    m03J05MixedExtension_reflect_two hx.1 (by linarith [hx.2])]

lemma m03J05_sin_mul_extension_intervalIntegrable {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ) :
    IntervalIntegrable
      (fun x : ℝ => (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) volume (-2) 2 := by
  let μ := volume.restrict (Ioc (-2 : ℝ) 2)
  have hext : Integrable (m03J05MixedExtension f) μ :=
    (m03J05MixedExtension_memLp hf).integrable (by norm_num)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ)) μ := by
    fun_prop
  have hbound : ∀ᵐ x ∂μ,
      ‖(Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ)‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Complex.norm_real]
    exact abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hint : Integrable
      (fun x : ℝ => (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) μ :=
    hext.bdd_mul hmeas hbound
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact hint

lemma m03J05_cos_mul_extension_intervalIntegrable {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ) :
    IntervalIntegrable
      (fun x : ℝ => (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) volume (-2) 2 := by
  let μ := volume.restrict (Ioc (-2 : ℝ) 2)
  have hext : Integrable (m03J05MixedExtension f) μ :=
    (m03J05MixedExtension_memLp hf).integrable (by norm_num)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ)) μ := by
    fun_prop
  have hbound : ∀ᵐ x ∂μ,
      ‖(Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ)‖ ≤ 1 := by
    filter_upwards [] with x
    rw [Complex.norm_real]
    exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hint : Integrable
      (fun x : ℝ => (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) μ :=
    hext.bdd_mul hmeas hbound
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact hint

/-- The negative-frequency kernel for the length-four Fourier interval is
the expected cosine-minus-sine expression. -/
lemma m03J05_fourier_kernel_four_expansion (k : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (-k : ℤ) * x / 4) =
      (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) -
        (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) * Complex.I := by
  let θ : ℝ := ((k : ℝ) * Real.pi / 2) * x
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((-k : ℤ) : ℂ) * (x : ℂ) / 4 =
      ((-θ : ℝ) : ℂ) * Complex.I := by
    dsimp [θ]
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  simp [θ, Real.cos_neg, Real.sin_neg]
  ring

lemma m03J05_fourierCoeffOn_mixedExtension_expansion {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ) :
    fourierCoeffOn (by norm_num : (-2 : ℝ) < 2) (m03J05MixedExtension f) k =
      (1 / 4 : ℝ) •
        ((∫ x in (-2 : ℝ)..2,
            (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x) -
          (∫ x in (-2 : ℝ)..2,
            (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x) * Complex.I) := by
  rw [fourierCoeffOn_eq_integral]
  simp_rw [fourier_coe_apply]
  norm_num only [sub_neg_eq_add]
  have hexp (x : ℝ) :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ)) * (x : ℂ) /
        (4 : ℂ)) =
        (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) -
          (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) * Complex.I := by
    simpa using m03J05_fourier_kernel_four_expansion k x
  simp_rw [smul_eq_mul]
  push_cast
  simp_rw [hexp]
  have hc := m03J05_cos_mul_extension_intervalIntegrable hf k
  have hs := m03J05_sin_mul_extension_intervalIntegrable hf k
  rw [show (∫ x in (-2 : ℝ)..2,
      ((Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) -
        (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) * Complex.I) *
          m03J05MixedExtension f x) =
      (∫ x in (-2 : ℝ)..2,
        (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
          m03J05MixedExtension f x) -
      (∫ x in (-2 : ℝ)..2,
        (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
          m03J05MixedExtension f x) * Complex.I by
    calc
      _ = ∫ x in (-2 : ℝ)..2,
          (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x -
            ((Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x) * Complex.I := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = (∫ x in (-2 : ℝ)..2,
            (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x) -
          ∫ x in (-2 : ℝ)..2,
            ((Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x) * Complex.I :=
            intervalIntegral.integral_sub hc (hs.mul_const Complex.I)
      _ = _ := by
        congr 1
        exact intervalIntegral.integral_mul_const Complex.I
          (fun x : ℝ ↦ (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
            m03J05MixedExtension f x)]
  congr 1 <;> simp

/-- The cosine part of every length-four Fourier coefficient of the odd
mixed extension vanishes. -/
lemma m03J05_cos_mul_mixedExtension_integral_eq_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ) :
    (∫ x in (-2 : ℝ)..2,
      (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) = 0 := by
  let q : ℝ → ℂ := fun x ↦
    (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
      m03J05MixedExtension f x
  have hfull : IntervalIntegrable q volume (-2) 2 :=
    m03J05_cos_mul_extension_intervalIntegrable hf k
  have hleft : IntervalIntegrable q volume (-2) 0 :=
    hfull.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 0),
        Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      exact Set.Icc_subset_Icc (le_refl _) (by norm_num))
  have hright : IntervalIntegrable q volume 0 2 :=
    hfull.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2),
        Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      exact Set.Icc_subset_Icc (by norm_num) (le_refl _))
  apply m03J05MixedExtension_mul_even_integral_eq_zero f
    (fun x : ℝ ↦ (Real.cos (((k : ℝ) * Real.pi / 2) * x) : ℂ))
  · intro x
    push_cast
    rw [show (k : ℂ) * (Real.pi : ℂ) / 2 * -(x : ℂ) =
      -((k : ℂ) * (Real.pi : ℂ) / 2 * (x : ℂ)) by ring, Complex.cos_neg]
  · exact hleft
  · exact hright

lemma m03J05_integral_symmetric_eq_two_mul_of_even (q : ℝ → ℂ)
    (hqneg : ∀ x : ℝ, q (-x) = q x)
    (hleft : IntervalIntegrable q volume (-2) 0)
    (hright : IntervalIntegrable q volume 0 2) :
    (∫ x in (-2 : ℝ)..2, q x) = 2 * ∫ x in (0 : ℝ)..2, q x := by
  have hchange : (∫ x in (-2 : ℝ)..0, q x) = ∫ x in (0 : ℝ)..2, q x := by
    calc
      _ = ∫ x in (0 : ℝ)..2, q (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg (f := q) (a := 0) (b := 2)).symm
      _ = _ := intervalIntegral.integral_congr (fun x hx ↦ hqneg x)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hchange]
  ring

lemma m03J05_sin_mul_mixedExtension_symmetric {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ) :
    (∫ x in (-2 : ℝ)..2,
      (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) =
      2 * ∫ x in (0 : ℝ)..2,
        (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
          m03J05MixedExtension f x := by
  let q : ℝ → ℂ := fun x ↦
    (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
      m03J05MixedExtension f x
  have hfull : IntervalIntegrable q volume (-2) 2 :=
    m03J05_sin_mul_extension_intervalIntegrable hf k
  apply m03J05_integral_symmetric_eq_two_mul_of_even q
  · intro x
    dsimp [q]
    rw [show ((k : ℝ) * Real.pi / 2) * -x =
      -(((k : ℝ) * Real.pi / 2) * x) by ring, Real.sin_neg,
      m03J05MixedExtension_neg]
    push_cast
    ring
  · exact hfull.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 0),
        Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      exact Set.Icc_subset_Icc (le_refl _) (by norm_num))
  · exact hfull.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2),
        Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      exact Set.Icc_subset_Icc (by norm_num) (le_refl _))

lemma m03J05_sin_mul_mixedExtension_zero_of_even {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ)
    (hk : Even k) :
    (∫ x in (0 : ℝ)..2,
      (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) = 0 := by
  let q : ℝ → ℂ := fun x ↦
    (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
      m03J05MixedExtension f x
  have hfull : IntervalIntegrable q volume (-2) 2 :=
    m03J05_sin_mul_extension_intervalIntegrable hf k
  have h01 : IntervalIntegrable q volume 0 1 := hfull.mono_set (by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h12 : IntervalIntegrable q volume 1 2 := hfull.mono_set (by
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc (by norm_num) (le_refl _))
  have hrefl : (∫ x in (0 : ℝ)..1, q (2 - x)) = -∫ x in (0 : ℝ)..1, q x := by
    have hae := m03J05_sin_mul_extension_reflect_ae_of_even f k hk
    rw [intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_of_le (by norm_num), ← MeasureTheory.integral_neg]
    exact MeasureTheory.integral_congr_ae hae
  have hchange : (∫ x in (1 : ℝ)..2, q x) = -∫ x in (0 : ℝ)..1, q x := by
    rw [← hrefl]
    convert
      (intervalIntegral.integral_comp_sub_left (f := q) (a := 0) (b := 1) 2).symm
        using 1 <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals h01 h12, hchange]
  exact add_neg_cancel _

lemma m03J05_sin_mul_mixedExtension_two_mul_of_odd {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (k : ℤ)
    (hk : Odd k) :
    (∫ x in (0 : ℝ)..2,
      (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) =
      2 * ∫ x in (0 : ℝ)..1,
        (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
          m03J05MixedExtension f x := by
  let q : ℝ → ℂ := fun x ↦
    (Real.sin (((k : ℝ) * Real.pi / 2) * x) : ℂ) *
      m03J05MixedExtension f x
  have hfull : IntervalIntegrable q volume (-2) 2 :=
    m03J05_sin_mul_extension_intervalIntegrable hf k
  have h01 : IntervalIntegrable q volume 0 1 := hfull.mono_set (by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h12 : IntervalIntegrable q volume 1 2 := hfull.mono_set (by
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc (by norm_num) (le_refl _))
  have hrefl : (∫ x in (0 : ℝ)..1, q (2 - x)) = ∫ x in (0 : ℝ)..1, q x := by
    have hae := m03J05_sin_mul_extension_reflect_ae_of_odd f k hk
    rw [intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_of_le (by norm_num)]
    exact MeasureTheory.integral_congr_ae hae
  have hchange : (∫ x in (1 : ℝ)..2, q x) = ∫ x in (0 : ℝ)..1, q x := by
    rw [← hrefl]
    convert
      (intervalIntegral.integral_comp_sub_left (f := q) (a := 0) (b := 1) 2).symm
        using 1 <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals h01 h12, hchange]
  ring

lemma m03J05_odd_int_eq_signed_two_mul_add_one (k : ℤ) (hk : Odd k) :
    ∃ n : ℕ, k = (2 * n + 1 : ℕ) ∨ k = -((2 * n + 1 : ℕ) : ℤ) := by
  rcases hk with ⟨j, hj⟩
  cases k with
  | ofNat m =>
      rcases Nat.even_or_odd m with hm | hm
      · rcases hm with ⟨n, rfl⟩
        exfalso
        change ((n + n : ℕ) : ℤ) = 2 * j + 1 at hj
        push_cast at hj
        omega
      · rcases hm with ⟨n, rfl⟩
        refine ⟨n, Or.inl ?_⟩
        simp [two_mul]
  | negSucc m =>
      rcases Nat.even_or_odd m with hm | hm
      · rcases hm with ⟨n, rfl⟩
        refine ⟨n, Or.inr ?_⟩
        change -(((n + n : ℕ) : ℤ) + 1) = -((2 * n + 1 : ℕ) : ℤ)
        push_cast
        ring
      · rcases hm with ⟨n, rfl⟩
        exfalso
        rw [Int.negSucc_eq] at hj
        push_cast at hj
        omega

lemma m03J05MixedExtension_ae_eq_on_zero_one (f : ℝ → ℂ) :
    m03J05MixedExtension f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [m03J05MixedExtension_of_pos hx.1, if_pos hx.2]

lemma m03J05_mixedMode_mul_extension_integral {f : ℝ → ℂ} (n : ℕ) :
    (∫ x in (0 : ℝ)..1,
      (Real.sin ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x) : ℂ) *
        m03J05MixedExtension f x) =
      ∫ x in (0 : ℝ)..1, (m03J05MixedEigenfunction n x : ℂ) * f x := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_of_le (by norm_num)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [m03J05MixedExtension_ae_eq_on_zero_one f] with x hx
  rw [hx]
  rfl

lemma m03J05_fourierCoeffOn_mixedExtension_eq_zero_of_orthogonal
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (horth : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, (m03J05MixedEigenfunction n x : ℂ) * f x) = 0) :
    ∀ k : ℤ,
      fourierCoeffOn (by norm_num : (-2 : ℝ) < 2)
        (m03J05MixedExtension f) k = 0 := by
  intro k
  rw [m03J05_fourierCoeffOn_mixedExtension_expansion hf k,
    m03J05_cos_mul_mixedExtension_integral_eq_zero hf k]
  rcases Int.even_or_odd k with hk | hk
  · have h02 := m03J05_sin_mul_mixedExtension_zero_of_even hf k hk
    have hall := m03J05_sin_mul_mixedExtension_symmetric hf k
    rw [h02, mul_zero] at hall
    rw [hall]
    simp
  · rcases m03J05_odd_int_eq_signed_two_mul_add_one k hk with ⟨n, hpos | hneg⟩
    · subst k
      have h01 : (∫ x in (0 : ℝ)..1,
          (Real.sin (((((2 * n + 1 : ℕ) : ℤ) : ℝ) * Real.pi / 2) * x) : ℂ) *
            m03J05MixedExtension f x) = 0 := by
        rw [show ((((2 * n + 1 : ℕ) : ℤ) : ℝ)) = ((2 * n + 1 : ℕ) : ℝ) by norm_num,
          m03J05_mixedMode_mul_extension_integral n, horth n]
      have h02 := m03J05_sin_mul_mixedExtension_two_mul_of_odd hf
        ((2 * n + 1 : ℕ) : ℤ) hk
      rw [h01, mul_zero] at h02
      have hall := m03J05_sin_mul_mixedExtension_symmetric hf
        ((2 * n + 1 : ℕ) : ℤ)
      rw [h02, mul_zero] at hall
      rw [hall]
      simp
    · subst k
      have hsin : (∫ x in (-2 : ℝ)..2,
          (Real.sin ((((-((2 * n + 1 : ℕ) : ℤ) : ℤ) : ℝ) * Real.pi / 2) * x) : ℂ) *
            m03J05MixedExtension f x) = 0 := by
        have hposall := m03J05_sin_mul_mixedExtension_symmetric hf
          ((2 * n + 1 : ℕ) : ℤ)
        have hoddpos : Odd ((2 * n + 1 : ℕ) : ℤ) := by
          refine ⟨(n : ℤ), ?_⟩
          push_cast
          ring
        have hpos02 := m03J05_sin_mul_mixedExtension_two_mul_of_odd hf
          ((2 * n + 1 : ℕ) : ℤ) hoddpos
        have h01 : (∫ x in (0 : ℝ)..1,
            (Real.sin (((((2 * n + 1 : ℕ) : ℤ) : ℝ) * Real.pi / 2) * x) : ℂ) *
              m03J05MixedExtension f x) = 0 := by
          rw [show ((((2 * n + 1 : ℕ) : ℤ) : ℝ)) = ((2 * n + 1 : ℕ) : ℝ) by norm_num,
            m03J05_mixedMode_mul_extension_integral n, horth n]
        rw [h01, mul_zero] at hpos02
        rw [hpos02, mul_zero] at hposall
        rw [← neg_zero]
        convert congrArg Neg.neg hposall using 1
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro x hx
        push_cast
        rw [show (-(2 * (n : ℂ) + 1) * (Real.pi : ℂ) / 2) * (x : ℂ) =
          -(((2 * (n : ℂ) + 1) * (Real.pi : ℂ) / 2) * (x : ℂ)) by ring,
          Complex.sin_neg]
        ring
      rw [hsin]
      simp

lemma m03J05_mixedEigenfunction_complete_complex
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (horth : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, (m03J05MixedEigenfunction n x : ℂ) * f x) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
  have hextLp := m03J05MixedExtension_memLp hf
  have hcoeff := m03J05_fourierCoeffOn_mixedExtension_eq_zero_of_orthogonal hf horth
  have hextzero : m03J05MixedExtension f =ᵐ[
      volume.restrict (Ioc (-2 : ℝ) 2)] 0 :=
    m03J05_ae_eq_zero_of_fourierCoeffOn_eq_zero (by norm_num) hextLp hcoeff
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioc (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hextzero' : m03J05MixedExtension f =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    (ae_mono (Measure.restrict_mono hsub (le_refl volume))) hextzero
  filter_upwards [m03J05MixedExtension_ae_eq_on_zero_one f, hextzero'] with x hxf hx0
  rw [← hxf]
  exact hx0

lemma m03J05_mixedEigenfunction_complete_real
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (horth : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, m03J05MixedEigenfunction n x * f x) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
  let fc : ℝ → ℂ := fun x ↦ (f x : ℂ)
  have hfcmeas : AEStronglyMeasurable fc
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hf.1
  have hfc : MemLp fc 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hf.congr_norm hfcmeas (Filter.Eventually.of_forall fun x ↦ by
      dsimp [fc]
      exact (Complex.norm_real (f x)).symm)
  have horthc : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, (m03J05MixedEigenfunction n x : ℂ) * fc x) = 0 := by
    intro n
    have hfint : Integrable f (volume.restrict (Ioc (0 : ℝ) 1)) :=
      hf.integrable (by norm_num)
    have hmmeas : AEStronglyMeasurable (m03J05MixedEigenfunction n)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      unfold m03J05MixedEigenfunction
      fun_prop
    have hmbound : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖m03J05MixedEigenfunction n x‖ ≤ 1 := by
      filter_upwards [] with x
      exact abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have hprod : IntervalIntegrable
        (fun x ↦ m03J05MixedEigenfunction n x * f x) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
      simpa [mul_comm] using hfint.bdd_mul hmmeas hmbound
    have hcomm := Complex.ofRealCLM.intervalIntegral_comp_comm hprod
    rw [horth n] at hcomm
    simpa [fc, Complex.ofRealCLM_apply, map_mul] using hcomm
  have hzero := m03J05_mixedEigenfunction_complete_complex hfc horthc
  filter_upwards [hzero] with x hx
  exact Complex.ofReal_injective (by simpa [fc] using hx)

lemma m03J05_mixedEigenfunction_complete_Lp
    (q : Lp ℝ 2 m03J05UnitMeasure)
    (horth : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, m03J05MixedEigenfunction n x * q x) = 0) :
    q = 0 := by
  apply Lp.ext
  have hf : MemLp (fun x : ℝ ↦ q x) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact Lp.memLp q
  have hz := m03J05_mixedEigenfunction_complete_real
    (f := fun x : ℝ ↦ q x) hf horth
  have hz' : (fun x : ℝ ↦ q x) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hz
  have hqzero : (fun x : ℝ ↦ q x) =ᵐ[m03J05UnitMeasure] 0 := by
    simpa [m03J05UnitMeasure] using hz'
  exact hqzero.trans (Lp.coeFn_zero ℝ 2 m03J05UnitMeasure).symm

/-- The displayed functions solve the expected constant-coefficient
eigenvalue equation pointwise. -/
lemma m03J05MixedEigenfunction_neg_deriv_deriv (n : ℕ) (x : ℝ) :
    -deriv (deriv (m03J05MixedEigenfunction n)) x =
      m03J05MixedEigenvalue n * m03J05MixedEigenfunction n x := by
  have hfirst : deriv (m03J05MixedEigenfunction n) = fun y : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * y) := by
    funext y
    exact (m03J05MixedEigenfunction_hasDerivAt n y).deriv
  rw [hfirst]
  have hsecond := (((hasDerivAt_id x).const_mul
    (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)).cos).const_mul
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)
  have hsecond' : deriv (fun y : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * y)) x =
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        (-Real.sin ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x) *
          (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)) := by
    simpa only [id_eq, mul_one] using hsecond.deriv
  rw [hsecond']
  simp only [m03J05MixedEigenvalue, m03J05MixedEigenfunction]
  ring

/-- Weak integration by parts for a mixed mode against an arbitrary
zero-trace reconstructed test function. -/
lemma m03J05_mixedEigenfunction_weak_integrationByParts (n : ℕ)
    (r : Lp ℝ 2 m03J05UnitMeasure) :
    inner ℝ (m03J05MixedDerivCoordinate n) r =
      m03J05MixedEigenvalue n *
        ∫ x in (0 : ℝ)..1,
          m03J05MixedEigenfunction n x *
            m03J05H1Value ((0 : ℝ), r) x := by
  let phi := m03J05MixedEigenfunction n
  let v := m03J05H1Value ((0 : ℝ), r)
  have hip :=
    AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
      (m03J05MixedEigenfunction_deriv_absolutelyContinuousOnInterval n)
      (m03J05H1Value_zero_absolutelyContinuousOnInterval r)
  have hleft : (∫ x in (0 : ℝ)..1, deriv phi x * deriv v x) =
      inner ℝ (m03J05MixedDerivCoordinate n) r := by
    rw [m03J05MixedDerivCoordinate_inner]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_congr_ae
    have hv := m03J05H1Value_zero_deriv_ae r
    filter_upwards [hv] with x hvx
    dsimp [phi, v]
    rw [hvx, (m03J05MixedEigenfunction_hasDerivAt n x).deriv]
  have hright : (∫ x in (0 : ℝ)..1, deriv (deriv phi) x * v x) =
      -m03J05MixedEigenvalue n *
        ∫ x in (0 : ℝ)..1, phi x * v x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    have hode := m03J05MixedEigenfunction_neg_deriv_deriv n x
    dsimp [phi, v] at hode ⊢
    have heq : deriv (deriv (m03J05MixedEigenfunction n)) x =
        -m03J05MixedEigenvalue n * m03J05MixedEigenfunction n x := by
      linarith
    rw [heq]
    ring
  have hphi1 : deriv phi 1 = 0 := by
    exact m03J05MixedEigenfunction_deriv_one n
  have hv0 : m03J05H1Value ((0 : ℝ), r) 0 = 0 := by
    simp [m03J05H1Value]
  rw [hleft, hright, hphi1, hv0] at hip
  dsimp [phi, v] at hip ⊢
  linarith

def m03J05LinearWeakSolution
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure) (u : m03J05H1) : Prop :=
  u.1 = 0 ∧ ∀ v : m03J05H1, v.1 = 0 →
    (∫ x in (0 : ℝ)..1, u.2 x * v.2 x) +
      c * ∫ x in (0 : ℝ)..1, m03J05H1Value u x * m03J05H1Value v x =
        ∫ x in (0 : ℝ)..1, F x * m03J05H1Value v x

lemma m03J05_linearWeakSolution_zero_iff
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure)
    (q : Lp ℝ 2 m03J05UnitMeasure) :
    m03J05LinearWeakSolution c F (0, q) ↔
      ∀ r : Lp ℝ 2 m03J05UnitMeasure,
        (∫ x in (0 : ℝ)..1, q x * r x) +
          c * ∫ x in (0 : ℝ)..1,
            m03J05H1Value (0, q) x * m03J05H1Value (0, r) x =
              ∫ x in (0 : ℝ)..1, F x * m03J05H1Value (0, r) x := by
  constructor
  · intro h r
    exact h.2 (0, r) rfl
  · intro h
    refine ⟨rfl, ?_⟩
    intro v hv
    have heq : v = (0, v.2) := by
      apply Prod.ext
      · simpa using hv
      · rfl
    rw [heq]
    exact h _

lemma m03J05_zeroTrace_reconstruction_inner_eq
    (q r : Lp ℝ 2 m03J05UnitMeasure) :
    inner ℝ (m03J05H1ValueCLM ((0 : ℝ), q))
        (m03J05H1ValueCLM ((0 : ℝ), r)) =
      ∫ x in (0 : ℝ)..1,
        m03J05H1Value ((0 : ℝ), q) x * m03J05H1Value ((0 : ℝ), r) x := by
  rw [MeasureTheory.L2.inner_def,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← m03J05UnitMeasure_eq_restrict_Ioc]
  apply integral_congr_ae
  filter_upwards [(m03J05H1Value_memLp ((0 : ℝ), q)).coeFn_toLp,
    (m03J05H1Value_memLp ((0 : ℝ), r)).coeFn_toLp] with x hq hr
  change inner ℝ
      (((m03J05H1Value_memLp ((0 : ℝ), q)).toLp
        (m03J05H1Value ((0 : ℝ), q))) x)
      (((m03J05H1Value_memLp ((0 : ℝ), r)).toLp
        (m03J05H1Value ((0 : ℝ), r))) x) = _
  rw [hq, hr]
  simp [inner, mul_comm]

/-- Each mixed derivative coordinate is an eigenvector of the compact
positive operator `K†K`, with reciprocal mixed eigenvalue. -/
lemma m03J05_adjoint_reconstruction_eigenvector (n : ℕ) :
    let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
        Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    ContinuousLinearMap.adjoint K (K (m03J05MixedDerivCoordinate n)) =
      (m03J05MixedEigenvalue n)⁻¹ • m03J05MixedDerivCoordinate n := by
  dsimp only
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  let a := ContinuousLinearMap.adjoint K
    (K (m03J05MixedDerivCoordinate n))
  let b := (m03J05MixedEigenvalue n)⁻¹ • m03J05MixedDerivCoordinate n
  have hall : ∀ r : Lp ℝ 2 m03J05UnitMeasure,
      inner ℝ a r = inner ℝ b r := by
    intro r
    have hvalue : inner ℝ (K (m03J05MixedDerivCoordinate n)) (K r) =
        ∫ x in (0 : ℝ)..1,
          m03J05MixedEigenfunction n x *
            m03J05H1Value ((0 : ℝ), r) x := by
      change inner ℝ
        (m03J05H1ValueCLM ((0 : ℝ), m03J05MixedDerivCoordinate n))
        (m03J05H1ValueCLM ((0 : ℝ), r)) = _
      rw [m03J05_zeroTrace_reconstruction_inner_eq]
      apply intervalIntegral.integral_congr
      intro x hx
      change m03J05H1Value ((0 : ℝ), m03J05MixedDerivCoordinate n) x *
          m03J05H1Value ((0 : ℝ), r) x =
        m03J05MixedEigenfunction n x * m03J05H1Value ((0 : ℝ), r) x
      rw [m03J05MixedDerivCoordinate_reconstructs n x (by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)]
    have hweak := m03J05_mixedEigenfunction_weak_integrationByParts n r
    have hne : m03J05MixedEigenvalue n ≠ 0 :=
      ne_of_gt (m03J05MixedEigenvalue_pos n)
    dsimp [a, b]
    rw [ContinuousLinearMap.adjoint_inner_left, hvalue]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    change (∫ x in (0 : ℝ)..1,
        m03J05MixedEigenfunction n x * m03J05H1Value ((0 : ℝ), r) x) =
      (m03J05MixedEigenvalue n)⁻¹ *
        inner ℝ (m03J05MixedDerivCoordinate n) r
    rw [hweak]
    field_simp
  have hz : inner ℝ (a - b) (a - b) = 0 := by
    rw [inner_sub_left, hall (a - b)]
    exact sub_self _
  have hn : ‖a - b‖ ^ 2 = 0 := by
    rwa [real_inner_self_eq_norm_sq] at hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

/-- The exact Gram matrix of the bundled mixed derivative coordinates. -/
lemma m03J05MixedDerivCoordinate_gram (m n : ℕ) :
    inner ℝ (m03J05MixedDerivCoordinate m)
        (m03J05MixedDerivCoordinate n) =
      if m = n then m03J05MixedEigenvalue n / 2 else 0 := by
  have hweak := m03J05_mixedEigenfunction_weak_integrationByParts n
    (m03J05MixedDerivCoordinate m)
  have hint : (∫ x in (0 : ℝ)..1,
      m03J05MixedEigenfunction n x *
        m03J05H1Value ((0 : ℝ), m03J05MixedDerivCoordinate m) x) =
      ∫ x in (0 : ℝ)..1,
        m03J05MixedEigenfunction n x * m03J05MixedEigenfunction m x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change m03J05MixedEigenfunction n x *
        m03J05H1Value ((0 : ℝ), m03J05MixedDerivCoordinate m) x = _
    rw [m03J05MixedDerivCoordinate_reconstructs m x (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)]
  rw [hint, m03J05MixedEigenfunction_gram n m] at hweak
  rw [real_inner_comm]
  by_cases hmn : m = n
  · subst m
    simpa using hweak
  · have hnm : n ≠ m := Ne.symm hmn
    rw [if_neg hmn]
    simpa [hnm] using hweak

lemma m03J05MixedDerivCoordinate_norm_sq (n : ℕ) :
    ‖m03J05MixedDerivCoordinate n‖ ^ 2 =
      m03J05MixedEigenvalue n / 2 := by
  rw [← real_inner_self_eq_norm_sq,
    m03J05MixedDerivCoordinate_gram n n, if_pos rfl]

lemma m03J05MixedDerivCoordinate_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (m03J05MixedDerivCoordinate m)
      (m03J05MixedDerivCoordinate n) = 0 := by
  rw [m03J05MixedDerivCoordinate_gram, if_neg hmn]

/-- The normalized mixed derivative modes. -/
noncomputable def m03J05NormalizedMixedDerivCoordinate (n : ℕ) :
    Lp ℝ 2 m03J05UnitMeasure :=
  (Real.sqrt (m03J05MixedEigenvalue n / 2))⁻¹ •
    m03J05MixedDerivCoordinate n

/-- Every normalized mixed derivative mode has norm one; in particular the
newly defined family is nontrivial. -/
lemma m03J05NormalizedMixedDerivCoordinate_norm (n : ℕ) :
    ‖m03J05NormalizedMixedDerivCoordinate n‖ = 1 := by
  have hp : 0 < m03J05MixedEigenvalue n / 2 := by
    exact div_pos (m03J05MixedEigenvalue_pos n) (by norm_num)
  have hs : Real.sqrt (m03J05MixedEigenvalue n / 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hp)
  have hdn := m03J05MixedDerivCoordinate_norm_sq n
  have hnnonneg : 0 ≤ ‖m03J05MixedDerivCoordinate n‖ := norm_nonneg _
  have hsqrt : ‖m03J05MixedDerivCoordinate n‖ =
      Real.sqrt (m03J05MixedEigenvalue n / 2) := by
    apply (sq_eq_sq₀ hnnonneg (Real.sqrt_nonneg _)).mp
    rw [hdn, Real.sq_sqrt hp.le]
  rw [m03J05NormalizedMixedDerivCoordinate, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), hsqrt]
  exact inv_mul_cancel₀ hs

/-- The normalized derivative modes form an orthonormal family. -/
lemma m03J05NormalizedMixedDerivCoordinate_orthonormal :
    Orthonormal ℝ m03J05NormalizedMixedDerivCoordinate := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
      m03J05NormalizedMixedDerivCoordinate_norm]
    norm_num
  · rw [if_neg hmn]
    unfold m03J05NormalizedMixedDerivCoordinate
    rw [inner_smul_left, inner_smul_right,
      m03J05MixedDerivCoordinate_orthogonal hmn]
    simp

/-- Orthogonality to every normalized derivative mode forces the zero-trace
reconstruction to vanish in `L²`. -/
lemma m03J05_zeroTrace_reconstruction_eq_zero_of_normalized_orthogonal
    (q : Lp ℝ 2 m03J05UnitMeasure)
    (horth : ∀ n : ℕ,
      inner ℝ q (m03J05NormalizedMixedDerivCoordinate n) = 0) :
    m03J05H1ValueCLM ((0 : ℝ), q) = 0 := by
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hdorth : ∀ n : ℕ,
      inner ℝ (m03J05MixedDerivCoordinate n) q = 0 := by
    intro n
    have hp : 0 < m03J05MixedEigenvalue n / 2 :=
      div_pos (m03J05MixedEigenvalue_pos n) (by norm_num)
    have hs : (Real.sqrt (m03J05MixedEigenvalue n / 2))⁻¹ ≠ 0 := by
      exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hp))
    have h := horth n
    unfold m03J05NormalizedMixedDerivCoordinate at h
    rw [inner_smul_right] at h
    have hi : inner ℝ q (m03J05MixedDerivCoordinate n) = 0 := by
      apply (mul_eq_zero.mp h).resolve_left hs
    rwa [real_inner_comm] at hi
  have hpair : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, m03J05MixedEigenfunction n x * (K q) x) = 0 := by
    intro n
    have hw := m03J05_mixedEigenfunction_weak_integrationByParts n q
    rw [hdorth n] at hw
    have hval : (∫ x in (0 : ℝ)..1,
        m03J05MixedEigenfunction n x * (K q) x) =
        ∫ x in (0 : ℝ)..1,
          m03J05MixedEigenfunction n x *
            m03J05H1Value ((0 : ℝ), q) x := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply integral_congr_ae
      have hcoe := (m03J05H1Value_memLp ((0 : ℝ), q)).coeFn_toLp
      have hcoe' := ae_mono
        (le_of_eq m03J05UnitMeasure_eq_restrict_Ioc.symm) hcoe
      filter_upwards [hcoe'] with x hx
      change m03J05MixedEigenfunction n x * (K q) x = _
      rw [show (K q) x = m03J05H1Value ((0 : ℝ), q) x by exact hx]
    rw [hval]
    exact (mul_eq_zero.mp hw.symm).resolve_left
      (ne_of_gt (m03J05MixedEigenvalue_pos n))
  have hK : K q = 0 := m03J05_mixedEigenfunction_complete_Lp (K q) hpair
  exact hK

/-- Zero-trace reconstruction is injective on the bundled derivative
coordinate. -/
lemma m03J05_zeroTrace_reconstruction_injective
    (q : Lp ℝ 2 m03J05UnitMeasure)
    (hq : m03J05H1ValueCLM ((0 : ℝ), q) = 0) : q = 0 := by
  have hcoeZero : (fun x : ℝ => m03J05H1ValueCLM ((0 : ℝ), q) x) =ᵐ[
      m03J05UnitMeasure] 0 := by
    rw [hq]
    exact Lp.coeFn_zero ℝ 2 m03J05UnitMeasure
  have hrep := (m03J05H1Value_memLp ((0 : ℝ), q)).coeFn_toLp
  have haeUnit : m03J05H1Value ((0 : ℝ), q) =ᵐ[m03J05UnitMeasure] 0 :=
    hrep.symm.trans hcoeZero
  have haeIoc : m03J05H1Value ((0 : ℝ), q) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    ae_mono (le_of_eq m03J05UnitMeasure_eq_restrict_Ioc.symm) haeUnit
  have hpoint : Set.EqOn (m03J05H1Value ((0 : ℝ), q)) 0
      (Ioc (0 : ℝ) 1) := by
    apply MeasureTheory.Measure.eqOn_Ioc_of_ae_eq volume haeIoc
    · exact (m03J05H1Value_continuousOn ((0 : ℝ), q)).mono
        (Ioc_subset_Icc_self)
    · exact continuousOn_const
  have hderivZero : (fun x : ℝ => deriv
      (m03J05H1Value ((0 : ℝ), q)) x) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hloc : m03J05H1Value ((0 : ℝ), q) =ᶠ[nhds x] 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hpoint ⟨hy.1, hy.2.le⟩
    rw [hloc.deriv_eq]
    simp
  have hderiv := m03J05H1Value_zero_deriv_ae q
  have hderiv' : (fun x : ℝ => deriv
      (m03J05H1Value ((0 : ℝ), q)) x) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun x => q x) :=
    ae_mono (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl) hderiv
  apply Lp.ext
  have hqzero : (fun x : ℝ => q x) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] 0 := hderiv'.symm.trans hderivZero
  simpa [m03J05UnitMeasure] using
    hqzero.trans (Lp.coeFn_zero ℝ 2 m03J05UnitMeasure).symm

/-- The normalized mixed derivative coordinates have trivial orthogonal
complement, hence are complete in the Hilbert-space sense. -/
lemma m03J05NormalizedMixedDerivCoordinate_orthogonal_eq_bot :
    (Submodule.span ℝ
      (Set.range m03J05NormalizedMixedDerivCoordinate))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro q hq
  apply m03J05_zeroTrace_reconstruction_injective q
  apply m03J05_zeroTrace_reconstruction_eq_zero_of_normalized_orthogonal q
  intro n
  exact (Submodule.mem_orthogonal'
    (Submodule.span ℝ (Set.range m03J05NormalizedMixedDerivCoordinate)) q).mp
      hq (m03J05NormalizedMixedDerivCoordinate n)
      (Submodule.subset_span (Set.mem_range_self n))

/-- The complete normalized mixed derivative family as a Hilbert basis. -/
noncomputable def m03J05MixedDerivHilbertBasis :
    HilbertBasis ℕ ℝ (Lp ℝ 2 m03J05UnitMeasure) :=
  HilbertBasis.mkOfOrthogonalEqBot
    m03J05NormalizedMixedDerivCoordinate_orthonormal
    m03J05NormalizedMixedDerivCoordinate_orthogonal_eq_bot

@[simp] lemma m03J05MixedDerivHilbertBasis_apply (n : ℕ) :
    m03J05MixedDerivHilbertBasis n =
      m03J05NormalizedMixedDerivCoordinate n := by
  exact congrFun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      m03J05NormalizedMixedDerivCoordinate_orthonormal
      m03J05NormalizedMixedDerivCoordinate_orthogonal_eq_bot) n

/-- Non-vacuity check for the locally constructed Hilbert basis. -/
lemma m03J05MixedDerivHilbertBasis_norm (n : ℕ) :
    ‖m03J05MixedDerivHilbertBasis n‖ = 1 := by
  rw [m03J05MixedDerivHilbertBasis_apply]
  exact m03J05NormalizedMixedDerivCoordinate_norm n

/-- The normalized mixed derivative modes retain the reciprocal-eigenvalue
identity of the unnormalized coordinates. -/
lemma m03J05_adjoint_reconstruction_normalized_eigenvector (n : ℕ) :
    let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
        Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    ContinuousLinearMap.adjoint K
        (K (m03J05NormalizedMixedDerivCoordinate n)) =
      (m03J05MixedEigenvalue n)⁻¹ •
        m03J05NormalizedMixedDerivCoordinate n := by
  dsimp only
  unfold m03J05NormalizedMixedDerivCoordinate
  rw [map_smul, map_smul, m03J05_adjoint_reconstruction_eigenvector]
  simp only [smul_smul]
  ring

/-- `K†K` is diagonal in the complete mixed derivative Hilbert basis. -/
lemma m03J05_adjoint_reconstruction_basis_coefficient
    (q : Lp ℝ 2 m03J05UnitMeasure) (n : ℕ) :
    let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
        Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint K (K q))) n =
      (m03J05MixedEigenvalue n)⁻¹ *
        (m03J05MixedDerivHilbertBasis.repr q) n := by
  dsimp only
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  rw [m03J05MixedDerivHilbertBasis.repr_apply_apply,
    m03J05MixedDerivHilbertBasis.repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [show ContinuousLinearMap.adjoint K
      (K (m03J05MixedDerivHilbertBasis n)) =
        (m03J05MixedEigenvalue n)⁻¹ •
          m03J05MixedDerivHilbertBasis n by
    rw [m03J05MixedDerivHilbertBasis_apply]
    exact m03J05_adjoint_reconstruction_normalized_eigenvector n]
  rw [inner_smul_left]
  simp

lemma m03J05MixedEigenvalue_tendsto_atTop :
    Filter.Tendsto m03J05MixedEigenvalue Filter.atTop Filter.atTop := by
  have hfreq : Filter.Tendsto
      (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2))
      Filter.atTop Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_right Filter.atTop (Real.pi / 2)
      (tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos)
    convert h using 1
    funext n
    push_cast
    ring
  convert hfreq.atTop_mul_atTop₀ hfreq using 1
  funext n
  simp only [m03J05MixedEigenvalue, pow_two]

lemma m03J05_nonresonant_denominator_uniform
    (c : ℝ) (hc : ¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
      δ ≤ |1 + c / m03J05MixedEigenvalue n| := by
  let d : ℕ → ℝ := fun n => |1 + c / m03J05MixedEigenvalue n|
  have hlim0 : Filter.Tendsto
      (fun n : ℕ => c / m03J05MixedEigenvalue n)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop m03J05MixedEigenvalue_tendsto_atTop
  have hlim : Filter.Tendsto d Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have h := (hone.add hlim0).abs
    simpa [d] using h
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) < d n :=
    hlim.eventually_const_lt (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  let s : Finset ℝ := (Finset.range (N + 1)).image d
  have hs : s.Nonempty := by
    refine ⟨d 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  let δ : ℝ := min (1 / 2 : ℝ) (s.min' hs)
  have hdne : ∀ n : ℕ, d n ≠ 0 := by
    intro n hn
    have hz : 1 + c / m03J05MixedEigenvalue n = 0 := abs_eq_zero.mp hn
    have hlne := ne_of_gt (m03J05MixedEigenvalue_pos n)
    apply hc
    refine ⟨n, ?_⟩
    field_simp at hz
    linarith
  have hminpos : 0 < s.min' hs := by
    have hm := s.min'_mem hs
    rcases Finset.mem_image.mp hm with ⟨n, _hn, hn⟩
    rw [← hn]
    exact abs_pos.mpr (by
      intro hz
      exact hdne n (abs_eq_zero.mpr hz))
  refine ⟨δ, lt_min (by norm_num) hminpos, ?_⟩
  intro n
  by_cases hn : n < N + 1
  · exact (min_le_right _ _).trans
      (Finset.min'_le s (d n) (Finset.mem_image.mpr
        ⟨n, Finset.mem_range.mpr hn, rfl⟩))
  · exact (min_le_left _ _).trans (le_of_lt (hN n (by omega)))

lemma m03J05_resonant_denominator_uniform (j : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
      δ ≤ |if n = j then 1 else
        1 - m03J05MixedEigenvalue j / m03J05MixedEigenvalue n| := by
  let d : ℕ → ℝ := fun n => |if n = j then 1 else
    1 - m03J05MixedEigenvalue j / m03J05MixedEigenvalue n|
  have hlim0 : Filter.Tendsto
      (fun n : ℕ => m03J05MixedEigenvalue j / m03J05MixedEigenvalue n)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop m03J05MixedEigenvalue_tendsto_atTop
  have hlimBase : Filter.Tendsto
      (fun n : ℕ => |1 - m03J05MixedEigenvalue j /
        m03J05MixedEigenvalue n|) Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    simpa using (hone.sub hlim0).abs
  have heq : Filter.Eventually (fun n : ℕ =>
      d n = |1 - m03J05MixedEigenvalue j / m03J05MixedEigenvalue n|)
      Filter.atTop := by
    filter_upwards [Filter.eventually_gt_atTop j] with n hn
    simp [d, ne_of_gt hn]
  have hlim : Filter.Tendsto d Filter.atTop (nhds 1) :=
    hlimBase.congr' (Filter.EventuallyEq.symm heq)
  have hevent : Filter.Eventually (fun n : ℕ => (1 / 2 : ℝ) < d n)
      Filter.atTop :=
    hlim.eventually_const_lt (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  let s : Finset ℝ := (Finset.range (N + 1)).image d
  have hs : s.Nonempty := by
    refine ⟨d 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  let δ : ℝ := min (1 / 2 : ℝ) (s.min' hs)
  have hdne : ∀ n : ℕ, d n ≠ 0 := by
    intro n hn
    by_cases hnj : n = j
    · simp [d, hnj] at hn
    · have hz : 1 - m03J05MixedEigenvalue j /
          m03J05MixedEigenvalue n = 0 := by
        exact abs_eq_zero.mp (by simpa [d, hnj] using hn)
      have hln : m03J05MixedEigenvalue n ≠ 0 :=
        ne_of_gt (m03J05MixedEigenvalue_pos n)
      have heigen : m03J05MixedEigenvalue j = m03J05MixedEigenvalue n := by
        field_simp [hln] at hz
        linarith
      exact hnj (m03J05MixedEigenvalue_injective heigen).symm
  have hminpos : 0 < s.min' hs := by
    have hm := s.min'_mem hs
    rcases Finset.mem_image.mp hm with ⟨n, _hn, hn⟩
    rw [← hn]
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm (hdne n))
  refine ⟨δ, lt_min (by norm_num) hminpos, ?_⟩
  intro n
  by_cases hn : n < N + 1
  · exact (min_le_right _ _).trans
      (Finset.min'_le s (d n) (Finset.mem_image.mpr
        ⟨n, Finset.mem_range.mpr hn, rfl⟩))
  · exact (min_le_left _ _).trans (le_of_lt (hN n (by omega)))

/-- Division by a scalar sequence uniformly bounded away from zero preserves
square summability. -/
lemma m03J05_memℓp_two_div_of_uniform_lower
    (a d : ℕ → ℝ) (ha : Memℓp a 2) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ n : ℕ, δ ≤ |d n|) :
    Memℓp (fun n => a n / d n) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hasum : Summable (fun n => Real.rpow ‖a n‖ 2) := by
    simpa only [ENNReal.toReal_ofNat] using ha.summable (by norm_num)
  have hmajor : Summable (fun n => Real.rpow (δ⁻¹) 2 *
      Real.rpow ‖a n‖ 2) :=
    hasum.mul_left (Real.rpow (δ⁻¹) 2)
  simp only [ENNReal.toReal_ofNat]
  apply hmajor.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    simp only [Real.norm_eq_abs]
    have hdpos : 0 < |d n| := hδ.trans_le (hd n)
    have habs : |a n / d n| ≤ δ⁻¹ * |a n| := by
      rw [abs_div]
      apply (div_le_iff₀ hdpos).2
      have hone : 1 ≤ δ⁻¹ * |d n| := by
        rw [← div_eq_inv_mul]
        exact (le_div_iff₀ hδ).2 (by simpa only [one_mul] using hd n)
      nlinarith [abs_nonneg (a n)]
    calc
      Real.rpow |a n / d n| 2 ≤ Real.rpow (δ⁻¹ * |a n|) 2 :=
        Real.rpow_le_rpow (abs_nonneg _) habs (by norm_num)
      _ = Real.rpow (δ⁻¹) 2 * Real.rpow |a n| 2 :=
        Real.mul_rpow (inv_nonneg.mpr hδ.le) (abs_nonneg _)

/-- In the nonresonant case the diagonal operator `1 + c K†K` is
surjective. -/
lemma m03J05_nonresonant_operator_exists
    (c : ℝ) (b : Lp ℝ 2 m03J05UnitMeasure)
    (hc : ¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n) :
    ∃ q : Lp ℝ 2 m03J05UnitMeasure,
      let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
          Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
        (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
      q + c • ContinuousLinearMap.adjoint K (K q) = b := by
  let den : ℕ → ℝ := fun n => 1 + c / m03J05MixedEigenvalue n
  obtain ⟨δ, hδ, hden⟩ := m03J05_nonresonant_denominator_uniform c hc
  let rb := m03J05MixedDerivHilbertBasis.repr b
  have hcoeff : Memℓp (fun n => rb n / den n) 2 :=
    m03J05_memℓp_two_div_of_uniform_lower rb den rb.property hδ hden
  let coeff : lp (fun _ : ℕ => ℝ) 2 := ⟨fun n => rb n / den n, hcoeff⟩
  let q : Lp ℝ 2 m03J05UnitMeasure :=
    m03J05MixedDerivHilbertBasis.repr.symm coeff
  refine ⟨q, ?_⟩
  dsimp only
  apply m03J05MixedDerivHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [map_add, map_smul]
  simp only [q, coeff, LinearIsometryEquiv.apply_symm_apply]
  change rb n / den n + c *
      (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
          ((m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q))) n = rb n
  rw [m03J05_adjoint_reconstruction_basis_coefficient]
  have hqcoeff : (m03J05MixedDerivHilbertBasis.repr q) n =
      rb n / den n := by
    simp [q, coeff]
  rw [hqcoeff]
  dsimp only [rb, den]
  have hlne : m03J05MixedEigenvalue n ≠ 0 :=
    ne_of_gt (m03J05MixedEigenvalue_pos n)
  have hdene : 1 + c / m03J05MixedEigenvalue n ≠ 0 := by
    intro hz
    apply hc
    refine ⟨n, ?_⟩
    field_simp at hz
    linarith
  have hsum : m03J05MixedEigenvalue n + c ≠ 0 := by
    intro hz
    apply hdene
    field_simp [hlne]
    linarith
  field_simp [hdene, hlne, hsum]

lemma m03J05_nonresonant_operator_unique
    (c : ℝ) (hc : ¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n)
    (q₁ q₂ : Lp ℝ 2 m03J05UnitMeasure)
    (h₁ : q₁ + c • ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
        ((m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q₁) = 0)
    (h₂ : q₂ + c • ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
        ((m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q₂) = 0) :
    q₁ = q₂ := by
  apply m03J05MixedDerivHilbertBasis.repr.injective
  apply lp.ext
  funext n
  have h₁n := congrArg
    (fun z => (m03J05MixedDerivHilbertBasis.repr z) n) h₁
  have h₂n := congrArg
    (fun z => (m03J05MixedDerivHilbertBasis.repr z) n) h₂
  simp only [map_add, map_smul, map_zero] at h₁n h₂n
  change (m03J05MixedDerivHilbertBasis.repr q₁) n + c *
      (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
          ((m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q₁))) n = 0 at h₁n
  change (m03J05MixedDerivHilbertBasis.repr q₂) n + c *
      (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
          ((m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q₂))) n = 0 at h₂n
  rw [m03J05_adjoint_reconstruction_basis_coefficient] at h₁n h₂n
  have hlne : m03J05MixedEigenvalue n ≠ 0 :=
    ne_of_gt (m03J05MixedEigenvalue_pos n)
  have hden : 1 + c / m03J05MixedEigenvalue n ≠ 0 := by
    intro hz
    apply hc
    refine ⟨n, ?_⟩
    field_simp at hz
    linarith
  have hz₁ : (1 + c / m03J05MixedEigenvalue n) *
      (m03J05MixedDerivHilbertBasis.repr q₁) n = 0 := by
    field_simp [hlne] at h₁n ⊢
    linarith
  have hz₂ : (1 + c / m03J05MixedEigenvalue n) *
      (m03J05MixedDerivHilbertBasis.repr q₂) n = 0 := by
    field_simp [hlne] at h₂n ⊢
    linarith
  rw [(mul_eq_zero.mp hz₁).resolve_left hden,
    (mul_eq_zero.mp hz₂).resolve_left hden]

lemma m03J05_linearWeakSolution_of_operator_eq
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure)
    (q : Lp ℝ 2 m03J05UnitMeasure)
    (hEq : q + c • ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
        ((m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q) =
      ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) F) :
    m03J05LinearWeakSolution c F ((0 : ℝ), q) := by
  apply (m03J05_linearWeakSolution_zero_iff c F q).2
  intro r
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hi := congrArg (fun z : Lp ℝ 2 m03J05UnitMeasure => inner ℝ z r) hEq
  change inner ℝ (q + c • ContinuousLinearMap.adjoint K (K q)) r =
    inner ℝ (ContinuousLinearMap.adjoint K F) r at hi
  rw [inner_add_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left] at hi
  have hderiv : inner ℝ q r = ∫ x in (0 : ℝ)..1, q x * r x := by
    symm
    exact m03J05_deriv_pairing_eq_inner ((0 : ℝ), q) ((0 : ℝ), r)
  have hvalue : inner ℝ (K q) (K r) =
      ∫ x in (0 : ℝ)..1,
        m03J05H1Value ((0 : ℝ), q) x * m03J05H1Value ((0 : ℝ), r) x := by
    exact m03J05_zeroTrace_reconstruction_inner_eq q r
  have hforcing : inner ℝ F (K r) =
      ∫ x in (0 : ℝ)..1, F x * m03J05H1Value ((0 : ℝ), r) x := by
    change m03J05ForcingCLM F ((0 : ℝ), r) = _
    exact m03J05ForcingCLM_apply F ((0 : ℝ), r)
  rwa [hderiv, hvalue, hforcing] at hi

lemma m03J05_operator_eq_of_linearWeakSolution
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure)
    (q : Lp ℝ 2 m03J05UnitMeasure)
    (hsol : m03J05LinearWeakSolution c F ((0 : ℝ), q)) :
    q + c • ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
        ((m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q) =
      ContinuousLinearMap.adjoint
        (m03J05H1ValueCLM.comp
          (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) F := by
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  let a := q + c • ContinuousLinearMap.adjoint K (K q)
  let b := ContinuousLinearMap.adjoint K F
  have hall : ∀ r : Lp ℝ 2 m03J05UnitMeasure, inner ℝ a r = inner ℝ b r := by
    intro r
    have hr := (m03J05_linearWeakSolution_zero_iff c F q).1 hsol r
    have hderiv : (∫ x in (0 : ℝ)..1, q x * r x) = inner ℝ q r :=
      m03J05_deriv_pairing_eq_inner ((0 : ℝ), q) ((0 : ℝ), r)
    have hvalue : (∫ x in (0 : ℝ)..1,
        m03J05H1Value ((0 : ℝ), q) x * m03J05H1Value ((0 : ℝ), r) x) =
        inner ℝ (K q) (K r) :=
      (m03J05_zeroTrace_reconstruction_inner_eq q r).symm
    have hforcing : (∫ x in (0 : ℝ)..1,
        F x * m03J05H1Value ((0 : ℝ), r) x) = inner ℝ F (K r) := by
      symm
      change m03J05ForcingCLM F ((0 : ℝ), r) = _
      exact m03J05ForcingCLM_apply F ((0 : ℝ), r)
    rw [hderiv, hvalue, hforcing] at hr
    dsimp [a, b]
    rw [inner_add_left, inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    exact hr
  have hz : inner ℝ (a - b) (a - b) = 0 := by
    rw [inner_sub_left, hall (a - b)]
    exact sub_self _
  have hn : ‖a - b‖ ^ 2 = 0 := by
    rwa [real_inner_self_eq_norm_sq] at hz
  have hab : a = b := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  exact hab

lemma m03J05_linearWeakSolution_zero_iff_operator_eq
    (c : ℝ) (F q : Lp ℝ 2 m03J05UnitMeasure) :
    m03J05LinearWeakSolution c F ((0 : ℝ), q) ↔
      q + c • ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
          ((m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q) =
        ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) F := by
  constructor
  · exact m03J05_operator_eq_of_linearWeakSolution c F q
  · exact m03J05_linearWeakSolution_of_operator_eq c F q

lemma m03J05_nonresonant_weakSolution_unique
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure)
    (hc : ¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n) :
    ∃! u : m03J05H1, m03J05LinearWeakSolution c F u := by
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  obtain ⟨q, hq⟩ := m03J05_nonresonant_operator_exists c
    (ContinuousLinearMap.adjoint K F) hc
  refine ⟨((0 : ℝ), q),
    (m03J05_linearWeakSolution_zero_iff_operator_eq c F q).2 hq, ?_⟩
  intro v hv
  rcases v with ⟨v₀, r⟩
  have hv₀ : v₀ = 0 := hv.1
  subst v₀
  have hr := (m03J05_linearWeakSolution_zero_iff_operator_eq c F r).1 hv
  have hdiff : (r - q) + c • ContinuousLinearMap.adjoint K (K (r - q)) = 0 := by
    rw [map_sub, map_sub, smul_sub]
    dsimp only [K] at hr hq ⊢
    rw [sub_add_sub_comm, hr, hq, sub_self]
  have hzero : (0 : Lp ℝ 2 m03J05UnitMeasure) +
      c • ContinuousLinearMap.adjoint K (K 0) = 0 := by simp
  have hd := m03J05_nonresonant_operator_unique c hc (r - q) 0 hdiff hzero
  have hrq : r = q := sub_eq_zero.mp hd
  exact Prod.ext (by simp) hrq

lemma m03J05_resonant_forcing_coefficient (F : Lp ℝ 2 m03J05UnitMeasure)
    (j : ℕ) :
    let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
        Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint K F)) j =
      (Real.sqrt (m03J05MixedEigenvalue j / 2))⁻¹ *
        ∫ x in (0 : ℝ)..1, F x * m03J05MixedEigenfunction j x := by
  dsimp only
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  rw [m03J05MixedDerivHilbertBasis.repr_apply_apply,
    m03J05MixedDerivHilbertBasis_apply]
  unfold m03J05NormalizedMixedDerivCoordinate
  rw [inner_smul_left, ContinuousLinearMap.adjoint_inner_right]
  simp only [map_inv₀, RCLike.star_def, conj_trivial]
  congr 1
  rw [real_inner_comm]
  change m03J05ForcingCLM F ((0 : ℝ), m03J05MixedDerivCoordinate j) = _
  rw [m03J05ForcingCLM_apply]
  apply intervalIntegral.integral_congr
  intro x hx
  change F x * m03J05H1Value ((0 : ℝ), m03J05MixedDerivCoordinate j) x =
    F x * m03J05MixedEigenfunction j x
  rw [m03J05MixedDerivCoordinate_reconstructs j x (by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)]

lemma m03J05_resonant_forcing_coefficient_zero_iff
    (F : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ) :
    let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
        Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint K F)) j = 0 ↔
      ∫ x in (0 : ℝ)..1, F x * m03J05MixedEigenfunction j x = 0 := by
  dsimp only
  rw [m03J05_resonant_forcing_coefficient]
  have hp : 0 < m03J05MixedEigenvalue j / 2 :=
    div_pos (m03J05MixedEigenvalue_pos j) (by norm_num)
  have hs : (Real.sqrt (m03J05MixedEigenvalue j / 2))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hp))
  exact mul_eq_zero_iff_left hs

lemma m03J05_resonant_operator_exists
    (b : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ)
    (hb : (m03J05MixedDerivHilbertBasis.repr b) j = 0) :
    ∃ q : Lp ℝ 2 m03J05UnitMeasure,
      let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
          Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
        (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
      q + (-m03J05MixedEigenvalue j) •
          ContinuousLinearMap.adjoint K (K q) = b := by
  let rb := m03J05MixedDerivHilbertBasis.repr b
  let num : ℕ → ℝ := fun n => if n = j then 0 else rb n
  let den : ℕ → ℝ := fun n => if n = j then 1 else
    1 - m03J05MixedEigenvalue j / m03J05MixedEigenvalue n
  have hnum_eq : num = rb := by
    funext n
    by_cases hn : n = j
    · subst n
      simp [num, rb, hb]
    · simp [num, hn]
  obtain ⟨δ, hδ, hden⟩ := m03J05_resonant_denominator_uniform j
  have hcoeff : Memℓp (fun n => num n / den n) 2 :=
    m03J05_memℓp_two_div_of_uniform_lower num den
      (hnum_eq.symm ▸ rb.property) hδ hden
  let coeff : lp (fun _ : ℕ => ℝ) 2 :=
    ⟨fun n => num n / den n, hcoeff⟩
  let q : Lp ℝ 2 m03J05UnitMeasure :=
    m03J05MixedDerivHilbertBasis.repr.symm coeff
  refine ⟨q, ?_⟩
  dsimp only
  apply m03J05MixedDerivHilbertBasis.repr.injective
  apply lp.ext
  funext n
  rw [map_add, map_smul]
  simp only [q, coeff, LinearIsometryEquiv.apply_symm_apply]
  change num n / den n + (-m03J05MixedEigenvalue j) *
      (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
          ((m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q))) n = rb n
  rw [m03J05_adjoint_reconstruction_basis_coefficient]
  have hqcoeff : (m03J05MixedDerivHilbertBasis.repr q) n =
      num n / den n := by
    simp [q, coeff]
  rw [hqcoeff]
  by_cases hn : n = j
  · subst n
    simp [num, den, rb, hb]
  · have hln : m03J05MixedEigenvalue n ≠ 0 :=
      ne_of_gt (m03J05MixedEigenvalue_pos n)
    have hneq : m03J05MixedEigenvalue j ≠ m03J05MixedEigenvalue n := by
      intro heq
      exact hn (m03J05MixedEigenvalue_injective heq).symm
    have hdiff : m03J05MixedEigenvalue n - m03J05MixedEigenvalue j ≠ 0 :=
      sub_ne_zero.mpr hneq.symm
    simp only [num, den, hn, if_false]
    field_simp [hln, hneq, hdiff]
    ring

lemma m03J05_resonant_operator_compatibility
    (b q : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ)
    (hEq : q + (-m03J05MixedEigenvalue j) •
        ContinuousLinearMap.adjoint
          (m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
          ((m03J05H1ValueCLM.comp
            (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q) = b) :
    (m03J05MixedDerivHilbertBasis.repr b) j = 0 := by
  have hj := congrArg
    (fun z => (m03J05MixedDerivHilbertBasis.repr z) j) hEq
  simp only [map_add, map_smul] at hj
  change (m03J05MixedDerivHilbertBasis.repr q) j +
      (-m03J05MixedEigenvalue j) *
        (m03J05MixedDerivHilbertBasis.repr
          (ContinuousLinearMap.adjoint
            (m03J05H1ValueCLM.comp
              (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
            ((m03J05H1ValueCLM.comp
              (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q))) j =
        (m03J05MixedDerivHilbertBasis.repr b) j at hj
  rw [m03J05_adjoint_reconstruction_basis_coefficient] at hj
  have hlne : m03J05MixedEigenvalue j ≠ 0 :=
    ne_of_gt (m03J05MixedEigenvalue_pos j)
  field_simp [hlne] at hj
  linarith

lemma m03J05_resonant_operator_kernel
    (q : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ) :
    let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
        Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    q + (-m03J05MixedEigenvalue j) •
        ContinuousLinearMap.adjoint K (K q) = 0 ↔
      ∃ a : ℝ, q = a • m03J05NormalizedMixedDerivCoordinate j := by
  dsimp only
  constructor
  · intro hq
    let a : ℝ := (m03J05MixedDerivHilbertBasis.repr q) j
    refine ⟨a, ?_⟩
    apply m03J05MixedDerivHilbertBasis.repr.injective
    apply lp.ext
    funext n
    have hn := congrArg
      (fun z => (m03J05MixedDerivHilbertBasis.repr z) n) hq
    simp only [map_add, map_smul, map_zero] at hn
    change (m03J05MixedDerivHilbertBasis.repr q) n +
        (-m03J05MixedEigenvalue j) *
          (m03J05MixedDerivHilbertBasis.repr
            (ContinuousLinearMap.adjoint
              (m03J05H1ValueCLM.comp
                (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure)))
              ((m03J05H1ValueCLM.comp
                (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))) q))) n = 0 at hn
    rw [m03J05_adjoint_reconstruction_basis_coefficient] at hn
    rw [map_smul]
    change (m03J05MixedDerivHilbertBasis.repr q) n =
      a * (m03J05MixedDerivHilbertBasis.repr
        (m03J05NormalizedMixedDerivCoordinate j)) n
    rw [← m03J05MixedDerivHilbertBasis_apply]
    rw [HilbertBasis.repr_self]
    by_cases hnj : n = j
    · subst n
      simp [a]
    · have hln : m03J05MixedEigenvalue n ≠ 0 :=
        ne_of_gt (m03J05MixedEigenvalue_pos n)
      have hneq : m03J05MixedEigenvalue j ≠ m03J05MixedEigenvalue n := by
        intro heq
        exact hnj (m03J05MixedEigenvalue_injective heq).symm
      have hcoeff : (m03J05MixedDerivHilbertBasis.repr q) n = 0 := by
        field_simp [hln] at hn
        have hz : (m03J05MixedEigenvalue n - m03J05MixedEigenvalue j) *
            (m03J05MixedDerivHilbertBasis.repr q) n = 0 := by
          nlinarith
        exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hneq.symm)
      rw [hcoeff]
      simp [lp.single_apply, hnj]
  · rintro ⟨a, rfl⟩
    rw [map_smul, map_smul,
      m03J05_adjoint_reconstruction_normalized_eigenvector]
    have hlne : m03J05MixedEigenvalue j ≠ 0 :=
      ne_of_gt (m03J05MixedEigenvalue_pos j)
    simp only [smul_smul]
    have hs : m03J05MixedEigenvalue j *
        (a * (m03J05MixedEigenvalue j)⁻¹) = a := by
      field_simp [hlne]
    have hsneg : -m03J05MixedEigenvalue j *
        (a * (m03J05MixedEigenvalue j)⁻¹) = -a := by
      rw [neg_mul, hs]
    rw [hsneg]
    simp

lemma m03J05_resonant_weakSolution_exists_iff
    (F : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ) :
    (∃ u : m03J05H1,
        m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F u) ↔
      ∫ x in (0 : ℝ)..1, F x * m03J05MixedEigenfunction j x = 0 := by
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  constructor
  · rintro ⟨⟨u₀, q⟩, hu⟩
    have hu₀ : u₀ = 0 := hu.1
    subst u₀
    have heq := (m03J05_linearWeakSolution_zero_iff_operator_eq
      (-m03J05MixedEigenvalue j) F q).1 hu
    have hc : (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint K F)) j = 0 := by
      apply m03J05_resonant_operator_compatibility
      exact heq
    exact (m03J05_resonant_forcing_coefficient_zero_iff F j).1 hc
  · intro hcompat
    have hc : (m03J05MixedDerivHilbertBasis.repr
        (ContinuousLinearMap.adjoint K F)) j = 0 :=
      (m03J05_resonant_forcing_coefficient_zero_iff F j).2 hcompat
    obtain ⟨q, hq⟩ := m03J05_resonant_operator_exists
      (ContinuousLinearMap.adjoint K F) j hc
    refine ⟨((0 : ℝ), q), ?_⟩
    exact (m03J05_linearWeakSolution_zero_iff_operator_eq
      (-m03J05MixedEigenvalue j) F q).2 hq

lemma m03J05_resonant_affine_of_weakSolutions
    (F : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ) (u v : m03J05H1)
    (hu : m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F u)
    (hv : m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F v) :
    ∃ a : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      m03J05H1Value v x =
        m03J05H1Value u x + a * m03J05MixedEigenfunction j x := by
  have hu₀ : u.1 = 0 := hu.1
  have hv₀ : v.1 = 0 := hv.1
  have hupair : u = ((0 : ℝ), u.2) := Prod.ext hu₀ rfl
  have hvpair : v = ((0 : ℝ), v.2) := Prod.ext hv₀ rfl
  have hu' : m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F
      ((0 : ℝ), u.2) := by
    rw [← hupair]
    exact hu
  have hv' : m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F
      ((0 : ℝ), v.2) := by
    rw [← hvpair]
    exact hv
  have heu := (m03J05_linearWeakSolution_zero_iff_operator_eq
    (-m03J05MixedEigenvalue j) F u.2).1 hu'
  have hev := (m03J05_linearWeakSolution_zero_iff_operator_eq
    (-m03J05MixedEigenvalue j) F v.2).1 hv'
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hdiff : (v.2 - u.2) + (-m03J05MixedEigenvalue j) •
      ContinuousLinearMap.adjoint K (K (v.2 - u.2)) = 0 := by
    rw [map_sub, map_sub, smul_sub]
    dsimp only [K] at heu hev ⊢
    rw [sub_add_sub_comm, hev, heu, sub_self]
  obtain ⟨a, ha⟩ := (m03J05_resonant_operator_kernel (v.2 - u.2) j).1 hdiff
  let s : ℝ := (Real.sqrt (m03J05MixedEigenvalue j / 2))⁻¹
  refine ⟨a * s, ?_⟩
  intro x hx
  have hcoord : v.2 - u.2 =
      (a * s) • m03J05MixedDerivCoordinate j := by
    simpa [m03J05NormalizedMixedDerivCoordinate, s, smul_smul] using ha
  have hpair : v - u = (a * s) •
      ((0 : ℝ), m03J05MixedDerivCoordinate j) := by
    apply Prod.ext
    · simp [hu₀, hv₀]
    · simpa using hcoord
  have hsub := m03J05H1Value_sub v u hx
  rw [hpair, m03J05H1Value_smul _ _ hx,
    m03J05MixedDerivCoordinate_reconstructs j x hx] at hsub
  linarith

lemma m03J05_resonant_weakSolution_of_affine
    (F : Lp ℝ 2 m03J05UnitMeasure) (j : ℕ) (u v : m03J05H1)
    (hu : m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F u)
    (haff : ∃ a : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      m03J05H1Value v x =
        m03J05H1Value u x + a * m03J05MixedEigenfunction j x) :
    m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F v := by
  obtain ⟨a, ha⟩ := haff
  have hu₀ : u.1 = 0 := hu.1
  have hv₀ : v.1 = 0 := by
    have h := ha 0 (by norm_num)
    have hvueq : v.1 = u.1 := by
      simpa [m03J05H1Value_zero, m03J05MixedEigenfunction] using h
    exact hvueq.trans hu₀
  let q : Lp ℝ 2 m03J05UnitMeasure :=
    v.2 - u.2 - a • m03J05MixedDerivCoordinate j
  have hval : ∀ x ∈ Icc (0 : ℝ) 1,
      m03J05H1Value ((0 : ℝ), q) x = 0 := by
    intro x hx
    have hsub := m03J05H1Value_sub v u hx
    have hsmul := m03J05H1Value_smul a
      ((0 : ℝ), m03J05MixedDerivCoordinate j) hx
    have hsub2 := m03J05H1Value_sub (v - u)
      (a • ((0 : ℝ), m03J05MixedDerivCoordinate j)) hx
    have hpair : (v - u) - a •
        ((0 : ℝ), m03J05MixedDerivCoordinate j) = ((0 : ℝ), q) := by
      apply Prod.ext
      · simp [hu₀, hv₀]
      · rfl
    rw [hpair] at hsub2
    rw [hsub, hsmul,
      m03J05MixedDerivCoordinate_reconstructs j x hx] at hsub2
    rw [ha x hx] at hsub2
    linarith
  have hK : m03J05H1ValueCLM ((0 : ℝ), q) = 0 := by
    apply Lp.ext
    have hrep := (m03J05H1Value_memLp ((0 : ℝ), q)).coeFn_toLp
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo,
      Lp.coeFn_zero ℝ 2 m03J05UnitMeasure] with x hx hxi hxzero
    change ((m03J05H1Value_memLp ((0 : ℝ), q)).toLp
      (m03J05H1Value ((0 : ℝ), q))) x =
        (0 : Lp ℝ 2 m03J05UnitMeasure) x
    rw [hx, hxzero]
    exact hval x ⟨hxi.1.le, hxi.2.le⟩
  have hq : q = 0 := m03J05_zeroTrace_reconstruction_injective q hK
  have hcoord : v.2 - u.2 = a • m03J05MixedDerivCoordinate j := by
    exact sub_eq_zero.mp hq
  have hupair : u = ((0 : ℝ), u.2) := Prod.ext hu₀ rfl
  have hu' : m03J05LinearWeakSolution (-m03J05MixedEigenvalue j) F
      ((0 : ℝ), u.2) := by rw [← hupair]; exact hu
  have heu := (m03J05_linearWeakSolution_zero_iff_operator_eq
    (-m03J05MixedEigenvalue j) F u.2).1 hu'
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ]
      Lp ℝ 2 m03J05UnitMeasure := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hdHom : (a • m03J05MixedDerivCoordinate j) +
      (-m03J05MixedEigenvalue j) • ContinuousLinearMap.adjoint K
        (K (a • m03J05MixedDerivCoordinate j)) = 0 := by
    rw [map_smul, map_smul, m03J05_adjoint_reconstruction_eigenvector]
    have hlne : m03J05MixedEigenvalue j ≠ 0 :=
      ne_of_gt (m03J05MixedEigenvalue_pos j)
    simp only [smul_smul]
    have hs : -m03J05MixedEigenvalue j *
        (a * (m03J05MixedEigenvalue j)⁻¹) = -a := by
      rw [neg_mul]
      field_simp [hlne]
    rw [hs]
    simp
  have hv2 : v.2 = u.2 + a • m03J05MixedDerivCoordinate j := by
    exact sub_eq_iff_eq_add'.mp hcoord
  have hveq : v.2 + (-m03J05MixedEigenvalue j) •
      ContinuousLinearMap.adjoint K (K v.2) =
      ContinuousLinearMap.adjoint K F := by
    rw [hv2, map_add, map_add, smul_add]
    dsimp only [K] at heu hdHom ⊢
    rw [add_add_add_comm, heu, hdHom, add_zero]
  have hv' := (m03J05_linearWeakSolution_zero_iff_operator_eq
    (-m03J05MixedEigenvalue j) F v.2).2 hveq
  have hvpair : v = ((0 : ℝ), v.2) := Prod.ext hv₀ rfl
  rwa [← hvpair] at hv'

def m03J05Energy
    (F : Lp ℝ 2 m03J05UnitMeasure) (g : ℝ → ℝ) (u : m03J05H1) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, (u.2 x) ^ 2 +
    ∫ x in (0 : ℝ)..1, g (m03J05H1Value u x) -
      ∫ x in (0 : ℝ)..1, F x * m03J05H1Value u x

lemma m03J05Energy_eq
    (F : Lp ℝ 2 m03J05UnitMeasure) (g : ℝ → ℝ) (u : m03J05H1)
    (hgc : Continuous g) :
    m03J05Energy F g u =
      (1 / 2 : ℝ) * ((∫ x in (0 : ℝ)..1, (u.2 x) ^ 2) +
        (∫ x in (0 : ℝ)..1, g (m03J05H1Value u x)) -
          (∫ x in (0 : ℝ)..1, F x * m03J05H1Value u x)) := by
  unfold m03J05Energy
  rw [intervalIntegral.integral_add (m03J05_deriv_sq_intervalIntegrable u)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ∫ x in (0 : ℝ)..1,
        g (m03J05H1Value u x) -
          ∫ y in (0 : ℝ)..1, F y * m03J05H1Value u y) volume 0 1)]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  have hin : (∫ x in (0 : ℝ)..1,
      g (m03J05H1Value u x) -
        ∫ y in (0 : ℝ)..1, F y * m03J05H1Value u y) =
      (∫ x in (0 : ℝ)..1, g (m03J05H1Value u x)) -
        ∫ y in (0 : ℝ)..1, F y * m03J05H1Value u y := by
    simpa only [Function.comp_apply, intervalIntegral.integral_const, sub_zero, one_smul] using
      intervalIntegral.integral_sub
      (hgc.comp_continuousOn (m03J05H1Value_continuousOn u) |>.intervalIntegrable_of_Icc
        (by norm_num))
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => ∫ y in (0 : ℝ)..1, F y * m03J05H1Value u y) volume 0 1)
  rw [hin]
  ring

def m03J05NonlinearWeakSolution
    (F : Lp ℝ 2 m03J05UnitMeasure) (G : ℝ → ℝ) (u : m03J05H1) : Prop :=
  u.1 = 0 ∧ ∀ v : m03J05H1, v.1 = 0 →
    (∫ x in (0 : ℝ)..1, u.2 x * v.2 x) +
      ∫ x in (0 : ℝ)..1, G (m03J05H1Value u x) * m03J05H1Value v x =
        ∫ x in (0 : ℝ)..1, F x * m03J05H1Value v x

/-- Why this unblocks `apm_m03j05`: this is the exact mixed-boundary
Fredholm alternative missing from Mathlib, including both the nonresonant
unique solution and the resonant compatibility/kernel classification. -/
theorem apm_m03J05_bridge_1
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure) :
    ((¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n) →
      ∃! u : m03J05H1, m03J05LinearWeakSolution c F u) ∧
    (∀ n : ℕ, c = -m03J05MixedEigenvalue n →
      ((∃ u : m03J05H1, m03J05LinearWeakSolution c F u) ↔
        ∫ x in (0 : ℝ)..1, F x * m03J05MixedEigenfunction n x = 0) ∧
      ∀ u : m03J05H1, m03J05LinearWeakSolution c F u →
        ∀ v : m03J05H1,
          m03J05LinearWeakSolution c F v ↔
            ∃ a : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
              m03J05H1Value v x =
                m03J05H1Value u x + a * m03J05MixedEigenfunction n x) := by
  constructor
  · exact m03J05_nonresonant_weakSolution_unique c F
  · intro n hc
    subst c
    constructor
    · exact m03J05_resonant_weakSolution_exists_iff F n
    · intro u hu v
      constructor
      · exact m03J05_resonant_affine_of_weakSolutions F n u v hu
      · exact m03J05_resonant_weakSolution_of_affine F n u v hu

/-- Why this unblocks `apm_m03j05`: this is the precise Sobolev/Nemytskii
differentiability statement for the frozen energy functional. -/
theorem apm_m03J05_bridge_2
    (F : Lp ℝ 2 m03J05UnitMeasure) :
    ∀ (G g : ℝ → ℝ) (L : NNReal), LipschitzWith L G → Monotone G →
      (∀ x : ℝ, HasDerivAt g (G x) x) → g 0 = 0 →
        Differentiable ℝ (m03J05Energy F g) := by
  intro G g L hG _hmono hg _hg0
  have hpotential : Differentiable ℝ (fun u : m03J05H1 =>
      ∫ x in (0 : ℝ)..1, g (m03J05H1Value u x)) :=
    fun u => (m03J05_potential_hasFDerivAt hG hg u).differentiableAt
  have hkinetic : Differentiable ℝ (fun u : m03J05H1 =>
      ∫ x in (0 : ℝ)..1, (u.2 x) ^ 2) := by
    simp_rw [m03J05_deriv_sq_integral_eq_norm_sq]
    exact (ContinuousLinearMap.snd ℝ ℝ
      (Lp ℝ 2 m03J05UnitMeasure)).differentiable.norm_sq ℝ
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z => (hg z).continuousAt
  have heq : m03J05Energy F g = fun u : m03J05H1 =>
      (1 / 2 : ℝ) * ((∫ x in (0 : ℝ)..1, (u.2 x) ^ 2) +
        (∫ x in (0 : ℝ)..1, g (m03J05H1Value u x)) -
          (∫ x in (0 : ℝ)..1, F x * m03J05H1Value u x)) := by
    funext u
    exact m03J05Energy_eq F g u hgc
  rw [heq]
  exact (differentiable_const (c := (1 / 2 : ℝ))).mul <|
    (hkinetic.add hpotential).sub (m03J05_forcing_differentiable F)

lemma m03J05_nonlinearWeakSolution_unique
    (F : Lp ℝ 2 m03J05UnitMeasure) {G : ℝ → ℝ} {L : NNReal}
    (hG : LipschitzWith L G) (hmono : Monotone G)
    {u v : m03J05H1}
    (hu : m03J05NonlinearWeakSolution F G u)
    (hv : m03J05NonlinearWeakSolution F G v) : u = v := by
  let w : m03J05H1 := u - v
  have hw0 : w.1 = 0 := by simp [w, hu.1, hv.1]
  have heu := hu.2 w hw0
  have hev := hv.2 w hw0
  have hval (z : m03J05H1) :
      (∫ x in (0 : ℝ)..1, G (m03J05H1Value z x) * m03J05H1Value w x) =
        ∫ x in (0 : ℝ)..1, G (m03J05H1Value z x) *
          (m03J05H1Value u x - m03J05H1Value v x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change G (m03J05H1Value z x) * m03J05H1Value (u - v) x = _
    rw [m03J05H1Value_sub u v]
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  rw [m03J05_deriv_pairing_eq_inner, hval] at heu hev
  have hdiff :
      inner ℝ u.2 w.2 - inner ℝ v.2 w.2 +
        ((∫ x in (0 : ℝ)..1, G (m03J05H1Value u x) *
            (m03J05H1Value u x - m03J05H1Value v x)) -
          ∫ x in (0 : ℝ)..1, G (m03J05H1Value v x) *
            (m03J05H1Value u x - m03J05H1Value v x)) = 0 := by
    linarith
  have hcontu : ContinuousOn (fun x : ℝ => G (m03J05H1Value u x) *
      (m03J05H1Value u x - m03J05H1Value v x)) (Icc 0 1) :=
    (hG.continuous.comp_continuousOn (m03J05H1Value_continuousOn u)).mul
      ((m03J05H1Value_continuousOn u).sub (m03J05H1Value_continuousOn v))
  have hcontv : ContinuousOn (fun x : ℝ => G (m03J05H1Value v x) *
      (m03J05H1Value u x - m03J05H1Value v x)) (Icc 0 1) :=
    (hG.continuous.comp_continuousOn (m03J05H1Value_continuousOn v)).mul
      ((m03J05H1Value_continuousOn u).sub (m03J05H1Value_continuousOn v))
  have hfull : ‖w.2‖ ^ 2 +
      ∫ x in (0 : ℝ)..1,
        (G (m03J05H1Value u x) - G (m03J05H1Value v x)) *
          (m03J05H1Value u x - m03J05H1Value v x) = 0 := by
    have hint : (∫ x in (0 : ℝ)..1,
        (G (m03J05H1Value u x) - G (m03J05H1Value v x)) *
          (m03J05H1Value u x - m03J05H1Value v x)) =
        ∫ x in (0 : ℝ)..1,
          G (m03J05H1Value u x) *
              (m03J05H1Value u x - m03J05H1Value v x) -
            G (m03J05H1Value v x) *
              (m03J05H1Value u x - m03J05H1Value v x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    rw [hint, intervalIntegral.integral_sub
      (hcontu.intervalIntegrable_of_Icc (by norm_num))
      (hcontv.intervalIntegrable_of_Icc (by norm_num))]
    have hinner : inner ℝ u.2 w.2 - inner ℝ v.2 w.2 = ‖w.2‖ ^ 2 := by
      rw [← inner_sub_left]
      change inner ℝ w.2 w.2 = ‖w.2‖ ^ 2
      exact real_inner_self_eq_norm_sq w.2
    linarith
  have hn := m03J05_nemytskii_difference_integral_nonneg hG hmono u v
  have hwzero : w.2 = 0 := by
    have : ‖w.2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w.2‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
  apply Prod.ext
  · simpa [hu.1, hv.1]
  · have : u.2 - v.2 = 0 := by simpa [w] using hwzero
    exact sub_eq_zero.mp this

lemma m03J05_nonlinearWeakSolution_zero_iff
    (F : Lp ℝ 2 m03J05UnitMeasure) (G : ℝ → ℝ)
    (q : Lp ℝ 2 m03J05UnitMeasure) :
    m03J05NonlinearWeakSolution F G (0, q) ↔
      ∀ r : Lp ℝ 2 m03J05UnitMeasure,
        (∫ x in (0 : ℝ)..1, q x * r x) +
          ∫ x in (0 : ℝ)..1,
            G (m03J05H1Value (0, q) x) * m03J05H1Value (0, r) x =
              ∫ x in (0 : ℝ)..1, F x * m03J05H1Value (0, r) x := by
  constructor
  · intro h r
    exact h.2 (0, r) rfl
  · intro h
    refine ⟨rfl, ?_⟩
    intro v hv
    have heq : v = (0, v.2) := by
      apply Prod.ext
      · simpa using hv
      · rfl
    rw [heq]
    exact h _

lemma m03J05_exists_zeroTrace_operator_eq
    (F : Lp ℝ 2 m03J05UnitMeasure) (G : ℝ → ℝ) (L : NNReal)
    (hG : LipschitzWith L G) (hmono : Monotone G) :
    let K := m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
    ∃ q : Lp ℝ 2 m03J05UnitMeasure,
      q + ContinuousLinearMap.adjoint K
          (m03J05NemytskiiLp hG ((0 : ℝ), q)) =
        ContinuousLinearMap.adjoint K F := by
  dsimp only
  let K := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  let A : Lp ℝ 2 m03J05UnitMeasure → Lp ℝ 2 m03J05UnitMeasure := fun q =>
    q + ContinuousLinearMap.adjoint K (m03J05NemytskiiLp hG ((0 : ℝ), q))
  let b := ContinuousLinearMap.adjoint K F
  let M : ℝ := 1 + 4 * (L : ℝ)
  have hM : 1 ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) L.2)
  have hLip : ∀ q r, ‖A q - A r‖ ≤ M * ‖q - r‖ := by
    intro q r
    dsimp [A, M, K]
    exact m03J05_zeroTrace_operator_sub_norm_le hG q r
  have hmon' : ∀ q r, ‖q - r‖ ^ 2 ≤ inner ℝ (A q - A r) (q - r) := by
    intro q r
    dsimp [A, K]
    exact m03J05_zeroTrace_operator_strongly_monotone hG hmono q r
  obtain ⟨k, hk, hc⟩ :=
    m03J05_contractingWith_of_lipschitz_stronglyMonotone A b M hM hLip hmon'
  obtain ⟨q, hq, _⟩ := hc.exists_fixedPoint (0 : Lp ℝ 2 m03J05UnitMeasure) (by simp)
  refine ⟨q, ?_⟩
  have hα : (1 / (2 * M ^ 2) : ℝ) ≠ 0 := by
    have : 0 < M := lt_of_lt_of_le zero_lt_one hM
    positivity
  have hz : (1 / (2 * M ^ 2) : ℝ) • (A q - b) = 0 := by
    dsimp [Function.IsFixedPt] at hq
    have hzneg : -((1 / (2 * M ^ 2) : ℝ) • (A q - b)) = 0 := by
      calc
        _ = (q - (1 / (2 * M ^ 2)) • (A q - b)) - q := by abel
        _ = q - q := congrArg (fun z => z - q) hq
        _ = 0 := sub_self q
    exact neg_eq_zero.mp hzneg
  have hab : A q - b = 0 := (smul_eq_zero.mp hz).resolve_left hα
  dsimp [A, b, K] at hab ⊢
  exact sub_eq_zero.mp hab

/-- The remaining existence statement after reducing the zero-trace product
space to its derivative `L²` coordinate. -/
theorem m03J05_nonlinearWeakSolution_exists
    (F : Lp ℝ 2 m03J05UnitMeasure) (G : ℝ → ℝ) (L : NNReal)
    (hG : LipschitzWith L G) (hmono : Monotone G) :
    ∃ u : m03J05H1, m03J05NonlinearWeakSolution F G u := by
  obtain ⟨q, hq⟩ := m03J05_exists_zeroTrace_operator_eq F G L hG hmono
  refine ⟨((0 : ℝ), q), (m03J05_nonlinearWeakSolution_zero_iff F G q).2 ?_⟩
  intro r
  let K := m03J05H1ValueCLM.comp
    (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  have hi := congrArg (fun z : Lp ℝ 2 m03J05UnitMeasure => inner ℝ z r) hq
  change inner ℝ
      (q + ContinuousLinearMap.adjoint K
        (m03J05NemytskiiLp hG ((0 : ℝ), q))) r =
    inner ℝ (ContinuousLinearMap.adjoint K F) r at hi
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left] at hi
  have hderiv : inner ℝ q r = ∫ x in (0 : ℝ)..1, q x * r x := by
    symm
    exact m03J05_deriv_pairing_eq_inner ((0 : ℝ), q) ((0 : ℝ), r)
  have hnonlin : inner ℝ (m03J05NemytskiiLp hG ((0 : ℝ), q)) (K r) =
      ∫ x in (0 : ℝ)..1,
        G (m03J05H1Value ((0 : ℝ), q) x) *
          m03J05H1Value ((0 : ℝ), r) x := by
    change m03J05PotentialDerivative hG ((0 : ℝ), q) ((0 : ℝ), r) = _
    exact m03J05PotentialDerivative_apply hG ((0 : ℝ), q) ((0 : ℝ), r)
  have hforcing : inner ℝ F (K r) =
      ∫ x in (0 : ℝ)..1, F x * m03J05H1Value ((0 : ℝ), r) x := by
    change m03J05ForcingCLM F ((0 : ℝ), r) = _
    exact m03J05ForcingCLM_apply F ((0 : ℝ), r)
  rwa [hderiv, hnonlin, hforcing] at hi

/-- Why this unblocks `apm_m03j05`: this is the exact coercive monotone
existence-and-uniqueness theorem on the zero-trace Sobolev realization used
by the frozen nonlinear weak equation. -/
theorem apm_m03J05_bridge_3
    (F : Lp ℝ 2 m03J05UnitMeasure) :
    ∀ (G : ℝ → ℝ) (L : NNReal), LipschitzWith L G → Monotone G →
      ∃! u : m03J05H1, m03J05NonlinearWeakSolution F G u := by
  intro G L hG hmono
  obtain ⟨u, hu⟩ := m03J05_nonlinearWeakSolution_exists F G L hG hmono
  exact ⟨u, hu, fun v hv => m03J05_nonlinearWeakSolution_unique F hG hmono hv hu⟩

/-- For a nonnegative constant potential, the linear weak problem is exactly
the already solved monotone nonlinear problem. -/
lemma m03J05_linearWeakSolution_iff_nonlinear_const_mul
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure) (u : m03J05H1) :
    m03J05LinearWeakSolution c F u ↔
      m03J05NonlinearWeakSolution F (fun x : ℝ => c * x) u := by
  constructor <;> intro h
  · refine ⟨h.1, ?_⟩
    intro v hv
    have hscale : (∫ x in (0 : ℝ)..1,
        c * (m03J05H1Value u x * m03J05H1Value v x)) =
        c * ∫ x in (0 : ℝ)..1,
          m03J05H1Value u x * m03J05H1Value v x := by
      rw [intervalIntegral.integral_const_mul]
    simpa only [mul_assoc, hscale] using h.2 v hv
  · refine ⟨h.1, ?_⟩
    intro v hv
    have hscale : (∫ x in (0 : ℝ)..1,
        c * (m03J05H1Value u x * m03J05H1Value v x)) =
        c * ∫ x in (0 : ℝ)..1,
          m03J05H1Value u x * m03J05H1Value v x := by
      rw [intervalIntegral.integral_const_mul]
    simpa only [mul_assoc, hscale] using h.2 v hv

/-- The nonresonant solvability clause is complete for every nonnegative
potential, without spectral theory. -/
lemma m03J05_linearWeakSolution_existsUnique_of_nonneg
    (c : ℝ) (hc : 0 ≤ c) (F : Lp ℝ 2 m03J05UnitMeasure) :
    ∃! u : m03J05H1, m03J05LinearWeakSolution c F u := by
  let L : NNReal := ⟨c, hc⟩
  have hLip : LipschitzWith L (fun x : ℝ => c * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub]
    rw [abs_mul, abs_of_nonneg hc]
    rfl
  have hmono : Monotone (fun x : ℝ => c * x) := by
    intro x y hxy
    exact mul_le_mul_of_nonneg_left hxy hc
  obtain ⟨u, hu, huniq⟩ := apm_m03J05_bridge_3 F (fun x : ℝ => c * x) L hLip hmono
  refine ⟨u, (m03J05_linearWeakSolution_iff_nonlinear_const_mul c F u).2 hu, ?_⟩
  intro v hv
  exact huniq v ((m03J05_linearWeakSolution_iff_nonlinear_const_mul c F v).1 hv)

/-- A direct Neumann-contraction range extending slightly into negative
potentials; no spectral completeness is needed here. -/
lemma m03J05_linearWeakSolution_existsUnique_of_abs_lt_one
    (c : ℝ) (hc : |c| < 1) (F : Lp ℝ 2 m03J05UnitMeasure) :
    ∃! u : m03J05H1, m03J05LinearWeakSolution c F u := by
  let K : Lp ℝ 2 m03J05UnitMeasure →L[ℝ] Lp ℝ 2 m03J05UnitMeasure :=
    m03J05H1ValueCLM.comp
      (ContinuousLinearMap.inr ℝ ℝ (Lp ℝ 2 m03J05UnitMeasure))
  let b := ContinuousLinearMap.adjoint K F
  let T : Lp ℝ 2 m03J05UnitMeasure → Lp ℝ 2 m03J05UnitMeasure :=
    fun q => b - c • ContinuousLinearMap.adjoint K (K q)
  let k : NNReal := ⟨|c|, abs_nonneg c⟩
  have hT : ContractingWith k T := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro q r
    rw [dist_eq_norm, dist_eq_norm]
    have hadj : ‖ContinuousLinearMap.adjoint K (K q) -
        ContinuousLinearMap.adjoint K (K r)‖ ≤ ‖q - r‖ := by
      rw [← map_sub, ← map_sub]
      calc
        _ ≤ ‖K (q - r)‖ := m03J05_zeroTrace_reconstruction_adjoint_norm_le_one _
        _ ≤ ‖q - r‖ := m03J05_zeroTrace_reconstruction_norm_le_one (q - r)
    dsimp [T]
    rw [sub_sub_sub_cancel_left, ← smul_sub]
    calc
      ‖c • (ContinuousLinearMap.adjoint K (K r) -
          ContinuousLinearMap.adjoint K (K q))‖ =
          |c| * ‖ContinuousLinearMap.adjoint K (K q) -
            ContinuousLinearMap.adjoint K (K r)‖ := by
              rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
      _ ≤ |c| * ‖q - r‖ := mul_le_mul_of_nonneg_left hadj (abs_nonneg c)
      _ = (k : ℝ) * ‖q - r‖ := by rfl
  obtain ⟨q, hq, _⟩ := hT.exists_fixedPoint
    (0 : Lp ℝ 2 m03J05UnitMeasure) (by simp)
  have hEq : q + c • ContinuousLinearMap.adjoint K (K q) =
      ContinuousLinearMap.adjoint K F := by
    dsimp [Function.IsFixedPt, T, b] at hq
    calc
      q + c • ContinuousLinearMap.adjoint K (K q) =
          (ContinuousLinearMap.adjoint K F -
            c • ContinuousLinearMap.adjoint K (K q)) +
              c • ContinuousLinearMap.adjoint K (K q) := by rw [hq]
      _ = ContinuousLinearMap.adjoint K F := by abel
  refine ⟨((0 : ℝ), q),
    (m03J05_linearWeakSolution_zero_iff_operator_eq c F q).2 hEq, ?_⟩
  intro u hu
  have hu0 : u = ((0 : ℝ), u.2) := by
    apply Prod.ext
    · simpa using hu.1
    · rfl
  have huEq := (m03J05_linearWeakSolution_zero_iff_operator_eq c F u.2).1
    (hu0 ▸ hu)
  have hufix : Function.IsFixedPt T u.2 := by
    dsimp [Function.IsFixedPt, T, b]
    rw [← huEq]
    abel
  exact hu0.trans (Prod.ext (by simp) (hT.fixedPoint_unique' hufix hq))

theorem apm_m03j05 (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure) :
    ((¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n) →
      ∃! u : m03J05H1, m03J05LinearWeakSolution c F u) ∧
    (∀ n : ℕ, c = -m03J05MixedEigenvalue n →
      ((∃ u : m03J05H1, m03J05LinearWeakSolution c F u) ↔
        ∫ x in (0 : ℝ)..1, F x * m03J05MixedEigenfunction n x = 0) ∧
      ∀ u : m03J05H1, m03J05LinearWeakSolution c F u →
        ∀ v : m03J05H1,
          m03J05LinearWeakSolution c F v ↔
            ∃ a : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
              m03J05H1Value v x =
                m03J05H1Value u x + a * m03J05MixedEigenfunction n x) ∧
    (∀ (G g : ℝ → ℝ) (L : NNReal), LipschitzWith L G → Monotone G →
      (∀ x : ℝ, HasDerivAt g (G x) x) → g 0 = 0 →
        Differentiable ℝ (m03J05Energy F g)) ∧
    (∀ (G : ℝ → ℝ) (L : NNReal), LipschitzWith L G → Monotone G →
      ∃! u : m03J05H1, m03J05NonlinearWeakSolution F G u) := by
  rcases apm_m03J05_bridge_1 c F with ⟨hNonresonant, hResonant⟩
  exact ⟨hNonresonant, hResonant, apm_m03J05_bridge_2 F,
    apm_m03J05_bridge_3 F⟩

import Mathlib
import ConstructionTargets.EuclideanHausdorffIntegralTransport
import ConstructionTargets.IntrinsicSphereSecondMoments
import ConstructionTargets.SphereCapNullEquatorMeasureAssembly

open MeasureTheory
noncomputable section

abbrev t95J05R4 := EuclideanSpace ℝ (Fin 4)
abbrev t95J05SphereThree := Metric.sphere (0 : t95J05R4) 1

def t95J05Antipode (x : t95J05SphereThree) : t95J05SphereThree :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

inductive T95J05AntipodalRel : t95J05SphereThree → t95J05SphereThree → Prop
  | antipodal (x) : T95J05AntipodalRel x (t95J05Antipode x)

def t95J05RealProjectiveThree :=
  Quotient (Relation.EqvGen.setoid T95J05AntipodalRel)

noncomputable instance : TopologicalSpace t95J05RealProjectiveThree :=
  TopologicalSpace.coinduced
    (fun x : t95J05SphereThree ↦
      Quotient.mk (Relation.EqvGen.setoid T95J05AntipodalRel) x) inferInstance

def T95J05ProjectiveThreeForm :=
  {ρ : t95J05SphereThree → ℝ // ∀ x, ρ (t95J05Antipode x) = ρ x}

def t95J05Omega (x : t95J05R4) : ℝ := x 1 ^ 3 - 4 * x 0
def t95J05InclusionPullback (x : t95J05SphereThree) : ℝ :=
  t95J05Omega x.1 * x.1 0
def t95J05ProjectionPullback (η : T95J05ProjectiveThreeForm) :
    t95J05SphereThree → ℝ := η.1
def t95J05Integral (η : T95J05ProjectiveThreeForm) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, η.1 x ∂μHE[3]

lemma t95J05InclusionPullback_antipodal (x : t95J05SphereThree) :
    t95J05InclusionPullback (t95J05Antipode x) = t95J05InclusionPullback x := by
  simp [t95J05InclusionPullback, t95J05Omega, t95J05Antipode]
  ring

lemma t95J05_existsUnique_projectiveThreeForm :
    ∃! η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback := by
  let η : T95J05ProjectiveThreeForm :=
    ⟨t95J05InclusionPullback, t95J05InclusionPullback_antipodal⟩
  refine ⟨η, rfl, ?_⟩
  intro z hz
  apply Subtype.ext
  exact hz

lemma t95J05InclusionPullback_expand (x : t95J05SphereThree) :
    t95J05InclusionPullback x = x.1 1 ^ 3 * x.1 0 - 4 * x.1 0 ^ 2 := by
  simp [t95J05InclusionPullback, t95J05Omega]
  ring

/-- LIBRARY: normalized Euclidean three-dimensional surface mass of `S³`. -/
lemma t95J05_euclideanHausdorff_unitSphere_mass_aux_subtype :
    μHE[3] (Set.univ : Set t95J05SphereThree) =
      μHE[3] (Metric.sphere (0 : t95J05R4) 1) := by
  have h := (isometry_subtype_coe : Isometry
    (Subtype.val : t95J05SphereThree → t95J05R4))
    |>.euclideanHausdorffMeasure_image (d := 3) Set.univ
  have himage :
      Subtype.val '' (Set.univ : Set t95J05SphereThree) =
        Metric.sphere (0 : t95J05R4) 1 := by
    ext x
    simp
  calc
    μHE[3] (Set.univ : Set t95J05SphereThree) =
        μHE[3] (Subtype.val '' (Set.univ : Set t95J05SphereThree)) := h.symm
    _ = μHE[3] (Metric.sphere (0 : t95J05R4) 1) := by rw [himage]

lemma t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_volume_ball :
    volume (Metric.ball (0 : t95J05R4) 1) =
      ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  norm_num

lemma t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_toSphere :
    (volume.toSphere (Set.univ : Set t95J05SphereThree)).toReal =
      2 * Real.pi ^ 2 := by
  rw [Measure.toSphere_apply_univ,
    t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_volume_ball,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · norm_num
    ring
  · positivity

def t95J05SphereUpper : Set t95J05R4 :=
  Metric.sphere 0 1 ∩ {x | 0 < x 3}

def t95J05SphereLower : Set t95J05R4 :=
  Metric.sphere 0 1 ∩ {x | x 3 < 0}

def t95J05SphereEquator : Set t95J05R4 :=
  Metric.sphere 0 1 ∩ {x | x 3 = 0}

/-- Seat (claude-14, from lemma-8's partial): the normalised graph-density
integral over the unit 3-ball equals `2 · vol(B⁴)`; i.e.
`∫_{B³} (1 - ‖x‖²)^{-1/2} dx = π² = 2 · (π²/2)`, with Mathlib's Hausdorff
normalisation factor.  Polar coordinates in `ℝ³`
(`MeasureTheory.integral_fun_norm_addHaar` / `lintegral_fun_norm`) reduce it to
`4π ∫₀¹ r² (1 - r²)^{-1/2} dr = 4π · π/4`; compare with
`InnerProductSpace.volume_ball` / `EuclideanSpace.volume_ball` in dimension 4. -/
-- BEGIN SEAT AREA
lemma t95J05_cap_integral_aux_radial_hasDeriv
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => (Real.arcsin t - t * Real.sqrt (1 - t ^ 2)) / 2)
      (r ^ 2 / Real.sqrt (1 - r ^ 2)) r := by
  have hp : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hs : Real.sqrt (1 - r ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have ha := Real.hasDerivAt_arcsin (by nlinarith [hr.1, hr.2])
    (by nlinarith [hr.1, hr.2])
  have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (-r / Real.sqrt (1 - r ^ 2)) r := by
    convert (Real.hasDerivAt_sqrt hp.ne').comp r
      ((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2)) using 1
    simp only [Nat.cast_ofNat, id_eq, pow_one, mul_one, one_mul, zero_sub]
    field_simp
    ring
  convert (ha.sub ((hasDerivAt_id r).mul hsq)).div_const 2 using 1
  · simp only [id_eq]
    field_simp
    nlinarith [Real.sq_sqrt hp.le]

lemma t95J05_cap_integral_aux_radial :
    (∫ r in Set.Ioi (0 : ℝ),
      r ^ 2 * (if r < 1 then (1 / Real.sqrt (1 - r ^ 2)) else 0)) =
      Real.pi / 4 := by
  have hcont : ContinuousOn
      (fun t : ℝ => (Real.arcsin t - t * Real.sqrt (1 - t ^ 2)) / 2)
      (Set.Icc 0 1) := by fun_prop
  let g : ℝ → ℝ := fun r => r ^ 2 / Real.sqrt (1 - r ^ 2)
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g x := by
    intro x hx
    exact div_nonneg (sq_nonneg x) (Real.sqrt_nonneg _)
  have hint : MeasureTheory.IntegrableOn g (Set.Ioc 0 1) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont
      t95J05_cap_integral_aux_radial_hasDeriv hnn
  have hftc : ∫ y in (0 : ℝ)..1, g y = Real.pi / 4 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
      t95J05_cap_integral_aux_radial_hasDeriv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint)]
    rw [Real.arcsin_one, Real.arcsin_zero]
    ring
  rw [intervalIntegral.integral_of_le zero_le_one] at hftc
  have hrestrict : (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
      volume.restrict (Set.Ioc 0 1) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  rw [← hrestrict] at hftc
  rw [← hftc]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioo]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  by_cases h0 : 0 < r <;> by_cases h1 : r < 1 <;> simp [h0, h1, g, div_eq_mul_inv]

lemma t95J05_cap_integral_aux_volume :
    (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2)) ∂volume) =
      ENNReal.ofReal (Real.pi ^ 2) := by
  let f : ℝ → ℝ := fun r => if r < 1 then 1 / Real.sqrt (1 - r ^ 2) else 0
  have hrad := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) f
  have hrad' : (∫ x : EuclideanSpace ℝ (Fin 3), f ‖x‖) = Real.pi ^ 2 := by
    rw [hrad]
    simp only [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp,
      Nat.reduceSubDiff, nsmul_eq_mul, smul_eq_mul, f]
    rw [t95J05_cap_integral_aux_radial]
    simp only [Measure.real_def]
    rw [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp)]
    simp only [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
    ring
  have hnonneg : 0 ≤ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin 3) => f ‖x‖) := by
    filter_upwards with x
    unfold f
    split_ifs
    · positivity
    · positivity
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => f ‖x‖) volume := by
    rw [MeasureTheory.integrable_fun_norm_addHaar]
    simp only [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp,
      Nat.reduceSubDiff, nsmul_eq_mul, smul_eq_mul]
    let g : ℝ → ℝ := fun r => r ^ 2 / Real.sqrt (1 - r ^ 2)
    have hg : IntegrableOn g (Set.Ioc 0 1) := by
      have hcont : ContinuousOn
          (fun t : ℝ => (Real.arcsin t - t * Real.sqrt (1 - t ^ 2)) / 2)
          (Set.Icc 0 1) := by fun_prop
      exact intervalIntegral.integrableOn_deriv_of_nonneg hcont
        t95J05_cap_integral_aux_radial_hasDeriv
        (fun x hx => div_nonneg (sq_nonneg x) (Real.sqrt_nonneg _))
    have hi := (hg.mono_set Set.Ioo_subset_Ioc_self).integrable_indicator measurableSet_Ioo
    exact hi.integrableOn.congr_fun (by
      intro r hr
      have h0 : 0 < r := hr
      by_cases h1 : r < 1
      · simp [f, g, h0, h1, div_eq_mul_inv]
      · simp [f, g, h0, h1]) measurableSet_Ioi
  have hall : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (f ‖x‖) ∂volume) =
      ENNReal.ofReal (Real.pi ^ 2) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg, hrad']
  rw [← hall]
  rw [← MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
  apply MeasureTheory.lintegral_congr
  intro x
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  · have hn : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    simp [hx, f, hn]
  · have hn : ¬ ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    simp [hx, f, hn]

lemma t95J05_cap_integral :
    (↑(Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (Measure.hausdorffMeasure (↑(3 : ℕ)) :
          Measure (EuclideanSpace ℝ (Fin 3)))) : ENNReal) *
      (∫⁻ x in ConstructionTargets.SphereCapHeight.domain 3,
        ENNReal.ofReal
          (1 / ConstructionTargets.SphereCapHeight.upper 3 x)
          ∂ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure 3) =
      (2 : ENNReal) * volume (Metric.ball (0 : t95J05R4) 1) := by
  change (↑(Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (Measure.hausdorffMeasure (↑(3 : ℕ)) :
          Measure (EuclideanSpace ℝ (Fin 3)))) : ENNReal) •
      (∫⁻ x in ConstructionTargets.SphereCapHeight.domain 3,
        ENNReal.ofReal (1 / ConstructionTargets.SphereCapHeight.upper 3 x)
          ∂ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure 3) = _
  rw [← MeasureTheory.lintegral_smul_measure]
  rw [← Measure.restrict_smul]
  change (∫⁻ x in ConstructionTargets.SphereCapHeight.domain 3,
      ENNReal.ofReal (1 / ConstructionTargets.SphereCapHeight.upper 3 x)
        ∂(Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin 3)))
          (Measure.hausdorffMeasure (↑(3 : ℕ)) :
            Measure (EuclideanSpace ℝ (Fin 3)))) •
          Measure.hausdorffMeasure (↑(3 : ℕ))) = _
  rw [← Measure.euclideanHausdorffMeasure_def,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  change (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2)) ∂volume) = _
  rw [t95J05_cap_integral_aux_volume]
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  norm_num
  rw [← ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  congr 1
  ring
-- END SEAT AREA

/-- LIBRARY: the normalized Hausdorff mass of the strict upper hemisphere of
`S³` is half the full surface mass.  This is an independent graph-chart leaf. -/
lemma t95J05_unitSphere_upper_mass :
    μHE[3] t95J05SphereUpper =
      (2 : ENNReal) * volume (Metric.ball (0 : t95J05R4) 1) := by
  have hset :
      t95J05SphereUpper =
        ConstructionTargets.SphereCapEuclideanImage.strictUpperCap 3 := by
    ext x
    simp [t95J05SphereUpper,
      ConstructionTargets.SphereCapEuclideanImage.strictUpperCap]
  rw [hset, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ConstructionTargets.SphereCapHausdorffTransport.upper_strictCap_measure]
  exact t95J05_cap_integral

/-- LIBRARY: lower-hemisphere counterpart of `t95J05_unitSphere_upper_mass`.
It is deliberately independent, so a seat may prove it directly or by reflection. -/
lemma t95J05_unitSphere_lower_mass :
    μHE[3] t95J05SphereLower =
      (2 : ENNReal) * volume (Metric.ball (0 : t95J05R4) 1) := by
  have hset :
      t95J05SphereLower =
        ConstructionTargets.SphereCapEuclideanImage.strictLowerCap 3 := by
    ext x
    simp [t95J05SphereLower,
      ConstructionTargets.SphereCapEuclideanImage.strictLowerCap]
  rw [hset, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ConstructionTargets.SphereCapHausdorffTransport.lower_strictCap_measure]
  exact t95J05_cap_integral

/-- LIBRARY: the coordinate equator in `S³` has zero three-dimensional
normalized Hausdorff measure.  This is independent of both chart-area leaves. -/
lemma t95J05_unitSphere_equator_null :
    μHE[3] t95J05SphereEquator = 0 := by
  have heq :
      t95J05SphereEquator =
        ConstructionTargets.SphereEquatorImageNullity.equator 3 := by
    ext x
    simp [t95J05SphereEquator,
      ConstructionTargets.SphereEquatorImageNullity.equator]
  rw [heq, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ConstructionTargets.SphereEquatorHausdorffNullity.equator_three_ambient_null]
  simp

lemma t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_compare_aux_coarea :
    μHE[3] (Metric.sphere (0 : t95J05R4) 1) =
      (4 : ENNReal) * volume (Metric.ball (0 : t95J05R4) 1) := by
  have hpartition : Metric.sphere (0 : t95J05R4) 1 =
      (t95J05SphereUpper ∪ t95J05SphereLower) ∪ t95J05SphereEquator := by
    ext x
    simp only [t95J05SphereUpper, t95J05SphereLower, t95J05SphereEquator,
      Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx
      rcases lt_trichotomy (x 3) 0 with h | h | h
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl (Or.inl ⟨hx, h⟩)
    · rintro (⟨⟨hx, -⟩ | ⟨hx, -⟩⟩ | ⟨hx, -⟩)
      · exact hx
      · exact hx
      · exact hx
  have hmeasUpper : MeasurableSet t95J05SphereUpper := by
    exact Metric.isClosed_sphere.measurableSet.inter
      (measurableSet_lt measurable_const (Continuous.measurable (by fun_prop)))
  have hmeasLower : MeasurableSet t95J05SphereLower := by
    exact Metric.isClosed_sphere.measurableSet.inter
      (measurableSet_lt (Continuous.measurable (by fun_prop)) measurable_const)
  have hmeasEquator : MeasurableSet t95J05SphereEquator := by
    exact Metric.isClosed_sphere.measurableSet.inter
      (measurableSet_eq_fun (Continuous.measurable (by fun_prop)) measurable_const)
  rw [hpartition]
  have hdisjUL : Disjoint t95J05SphereUpper t95J05SphereLower := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ ⟨-, hy⟩
    change 0 < x 3 at hx
    change x 3 < 0 at hy
    exact (not_lt_of_ge (le_of_lt hx)) hy
  have hdisjEq : Disjoint (t95J05SphereUpper ∪ t95J05SphereLower)
      t95J05SphereEquator := by
    rw [Set.disjoint_left]
    rintro x (⟨-, hx⟩ | ⟨-, hx⟩) ⟨-, heq⟩
    · exact (ne_of_gt hx) heq
    · exact (ne_of_lt hx) heq
  rw [measure_union hdisjEq hmeasEquator, measure_union hdisjUL hmeasLower]
  rw [t95J05_unitSphere_upper_mass, t95J05_unitSphere_lower_mass,
    t95J05_unitSphere_equator_null]
  ring

lemma t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_compare :
    μHE[3] (Metric.sphere (0 : t95J05R4) 1) =
      volume.toSphere (Set.univ : Set t95J05SphereThree) := by
  rw [t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_compare_aux_coarea,
    Measure.toSphere_apply_univ]
  norm_num

lemma t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient :
    (μHE[3] (Metric.sphere (0 : t95J05R4) 1)).toReal =
      2 * Real.pi ^ 2 := by
  rw [t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_compare]
  exact t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient_aux_toSphere

theorem t95J05_euclideanHausdorff_unitSphere_mass :
    (μHE[3] (Set.univ : Set t95J05SphereThree)).toReal =
      2 * Real.pi ^ 2 := by
  rw [t95J05_euclideanHausdorff_unitSphere_mass_aux_subtype]
  exact t95J05_euclideanHausdorff_unitSphere_mass_aux_ambient

/-- Scalar transport from the banked raw moment.  The mass equality is an
argument so this lemma can be proved in parallel with the LIBRARY lemma. -/
theorem t95J05_inclusionPullback_integral
    (hmass : (μHE[3] (Set.univ : Set t95J05SphereThree)).toReal =
      2 * Real.pi ^ 2) :
    (∫ x : t95J05SphereThree, t95J05InclusionPullback x ∂μHE[3]) =
      -2 * Real.pi ^ 2 := by
  rw [Measure.euclideanHausdorffMeasure_def, integral_smul_nnreal_measure]
  have hdensity :
      (fun x : t95J05SphereThree => t95J05InclusionPullback x) =
        (fun x => x.1 1 ^ 3 * x.1 0 - 4 * x.1 0 ^ 2) := by
    funext x
    exact t95J05InclusionPullback_expand x
  rw [hdensity]
  have hmoment :
      (∫ x : t95J05SphereThree, x.1 1 ^ 3 * x.1 0 - 4 * x.1 0 ^ 2
        ∂Measure.hausdorffMeasure (↑(3 : ℕ))) =
        -ConstructionTargets.IntrinsicSphereSecondMoments.mass 3 := by
    simpa only [show 3 + 1 = 4 by omega] using
      ConstructionTargets.IntrinsicSphereSecondMoments.projective_density_moment
  rw [hmoment]
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply] at hmass
  change
    ((↑(Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (Measure.hausdorffMeasure (↑(3 : ℕ)) :
          Measure (EuclideanSpace ℝ (Fin 3)))) : ENNReal) *
      Measure.hausdorffMeasure (↑(3 : ℕ))
        (Set.univ : Set t95J05SphereThree)).toReal = 2 * Real.pi ^ 2 at hmass
  rw [ENNReal.toReal_mul] at hmass
  · unfold ConstructionTargets.IntrinsicSphereSecondMoments.mass
    simp only [ENNReal.coe_toReal] at hmass
    rw [NNReal.smul_def, smul_eq_mul, mul_neg]
    rw [hmass]
    ring

theorem apm_t95j05 :
    (∃! η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback) ∧
    (∀ η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback →
      t95J05Integral η = -Real.pi ^ 2) := by
  refine ⟨t95J05_existsUnique_projectiveThreeForm, ?_⟩
  intro η hη
  unfold t95J05Integral t95J05ProjectionPullback at *
  rw [hη, t95J05_inclusionPullback_integral
    t95J05_euclideanHausdorff_unitSphere_mass]
  ring

#print axioms apm_t95j05

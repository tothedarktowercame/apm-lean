import Mathlib
import ConstructionTargets.EuclideanHausdorffIntegralTransport
import ConstructionTargets.IntrinsicSphereSecondMoments

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

/-- LIBRARY: the normalized Hausdorff mass of the strict upper hemisphere of
`S³` is half the full surface mass.  This is an independent graph-chart leaf. -/
lemma t95J05_unitSphere_upper_mass :
    μHE[3] t95J05SphereUpper =
      (2 : ENNReal) * volume (Metric.ball (0 : t95J05R4) 1) := by
  sorry

/-- LIBRARY: lower-hemisphere counterpart of `t95J05_unitSphere_upper_mass`.
It is deliberately independent, so a seat may prove it directly or by reflection. -/
lemma t95J05_unitSphere_lower_mass :
    μHE[3] t95J05SphereLower =
      (2 : ENNReal) * volume (Metric.ball (0 : t95J05R4) 1) := by
  sorry

/-- LIBRARY: the coordinate equator in `S³` has zero three-dimensional
normalized Hausdorff measure.  This is independent of both chart-area leaves. -/
lemma t95J05_unitSphere_equator_null :
    μHE[3] t95J05SphereEquator = 0 := by
  sorry

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

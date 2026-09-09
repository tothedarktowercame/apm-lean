import ConstructionTargets.NestedOrientedChartCompatibility
import ConstructionTargets.CircleMetricFundamentalGroup

open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.OrientedOverlapPuncturedCircle
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.ChartPairRelativeHomologyTransport
open ConstructionTargets.ModelPairLocalHomologyOne
open ConstructionTargets.OneDiskIncreasingOrientation
open ConstructionTargets.OneDiskLocalOrientation
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.OneDimensionalChartLocalGenerator
open ConstructionTargets.NestedOrientedChartCompatibility
open ConstructionTargets.NestedOrientedChartCompatibility.PointedModelChart

variable {M : Type} [TopologicalSpace M] {x : M}

theorem ambient_injective (c : PointedModelChart x) : Function.Injective c.ambient :=
  Subtype.val_injective.comp c.coordinates.injective

/-- Positive scaling stays in the open unit disk. -/
def scale (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : C(D,D) where
  toFun u := ⟨r • u.1, by
    have hu := u.2
    change dist u.1 0 < 1 at hu
    change dist (r • u.1) 0 < 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [dist_zero_right] at hu
    nlinarith [norm_nonneg u.1]⟩
  continuous_toFun := by fun_prop

theorem scale_increasing (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : Increasing (scale r hr hr1) := by
  intro u v huv
  exact mul_lt_mul_of_pos_left huv hr

/-- The actual smaller neighborhood, as the image of a coordinate ball. -/
def smallNeighborhood (c : PointedModelChart x) (r : ℝ) : Set M :=
  c.ambient '' {u : D | ‖u.1‖ < r}

theorem smallNeighborhood_subset (c : PointedModelChart x) (r : ℝ) :
    smallNeighborhood c r ⊆ c.neighborhood := by
  rintro y ⟨u, _, rfl⟩
  exact (c.coordinates u).2

theorem smallNeighborhood_open (c : PointedModelChart x) (r : ℝ) :
    IsOpen (smallNeighborhood c r) := by
  have hc : IsOpenMap c.ambient :=
    c.open_neighborhood.isOpenMap_subtype_val.comp c.coordinates.isOpenMap
  exact hc _ (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)

def smallCoordinate (c : PointedModelChart x) (r : ℝ) (y : smallNeighborhood c r) : D :=
  c.coordinates.symm ⟨y.1, smallNeighborhood_subset c r y.2⟩

theorem smallCoordinate_norm (c : PointedModelChart x) (r : ℝ) (y : smallNeighborhood c r) :
    ‖(smallCoordinate c r y).1‖ < r := by
  obtain ⟨u, hu, he⟩ := y.2
  have hy : (⟨y.1, smallNeighborhood_subset c r y.2⟩ : c.neighborhood) = c.coordinates u :=
    Subtype.ext he.symm
  simp only [smallCoordinate, hy, c.coordinates.symm_apply_apply]
  exact hu

/-- Restrict a given pointed chart by a positive coordinate scaling. -/
def shrinkCoordinates (c : PointedModelChart x) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    D ≃ₜ smallNeighborhood c r where
  toFun u := ⟨c.ambient (scale r hr hr1 u), by
    refine ⟨scale r hr hr1 u, ?_, rfl⟩
    change ‖r • u.1‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hu : ‖u.1‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using u.2
    nlinarith⟩
  invFun y := ⟨r⁻¹ • (smallCoordinate c r y).1, by
    change dist (r⁻¹ • (smallCoordinate c r y).1) 0 < 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have h := smallCoordinate_norm c r y
    exact (inv_mul_lt_iff₀ hr).mpr (by simpa using h)⟩
  left_inv u := by
    apply Subtype.ext
    change r⁻¹ • (c.coordinates.symm _).1 = u.1
    have he : (⟨c.ambient (scale r hr hr1 u), _⟩ : c.neighborhood) = c.coordinates (scale r hr hr1 u) := rfl
    rw [he, c.coordinates.symm_apply_apply]
    change r⁻¹ • (r • u.1) = u.1
    simp [hr.ne']
  right_inv y := by
    apply Subtype.ext
    have hv : (scale r hr hr1 ⟨r⁻¹ • (smallCoordinate c r y).1, by
        change dist (r⁻¹ • (smallCoordinate c r y).1) 0 < 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        exact (inv_mul_lt_iff₀ hr).mpr (by simpa using smallCoordinate_norm c r y)⟩) = smallCoordinate c r y := by
      apply Subtype.ext
      change r • (r⁻¹ • (smallCoordinate c r y).1) = (smallCoordinate c r y).1
      simp [hr.ne']
    change c.ambient (scale r hr hr1 _) = y.1
    rw [hv]
    exact congrArg Subtype.val (c.coordinates.apply_symm_apply _)
  continuous_toFun := by
    exact (c.ambient.continuous.comp (scale r hr hr1).continuous).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.const_smul
    exact continuous_subtype_val.comp (c.coordinates.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))

def shrinkChart (c : PointedModelChart x) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : PointedModelChart x where
  neighborhood := smallNeighborhood c r
  open_neighborhood := smallNeighborhood_open c r
  coordinates := shrinkCoordinates c r hr hr1
  origin_eq := by
    change c.ambient (scale r hr hr1 origin) = x
    have he : scale r hr hr1 origin = origin := by apply Subtype.ext; simp [scale, origin]
    rw [he]
    exact c.origin_eq

theorem shrink_transition (c : PointedModelChart x) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    transition (shrinkChart c r hr hr1) c (smallNeighborhood_subset c r) = scale r hr hr1 := by
  apply ContinuousMap.ext
  intro u
  change c.coordinates.symm _ = scale r hr hr1 u
  exact c.coordinates.symm_apply_apply _

theorem shrink_compatible (c : PointedModelChart x) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Compatible (shrinkChart c r hr hr1) c (smallNeighborhood_subset c r) := by
  unfold Compatible
  rw [shrink_transition]
  exact scale_increasing r hr hr1

/-- Construct a positive coordinate radius whose chart image lies in the overlap. -/
theorem exists_common_radius (c d : PointedModelChart x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ smallNeighborhood c r ⊆ d.neighborhood := by
  have hx : x ∈ d.neighborhood := by
    have h := (d.coordinates origin).2
    simpa only [d.origin_eq] using h
  have ho := d.open_neighborhood.preimage c.ambient.continuous
  have hm : origin ∈ c.ambient ⁻¹' d.neighborhood := by
    change c.ambient origin ∈ d.neighborhood
    change (c.coordinates origin).1 ∈ d.neighborhood
    rw [c.origin_eq]
    exact hx
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp ho origin hm
  refine ⟨min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  apply hball
  change dist u origin < s
  change dist u.1 (0 : E) < s
  rw [dist_zero_right]
  exact lt_of_lt_of_le hu (min_le_left _ _)

def commonRadius (c d : PointedModelChart x) : ℝ := (exists_common_radius c d).choose

def commonChart (c d : PointedModelChart x) : PointedModelChart x :=
  shrinkChart c (commonRadius c d) (exists_common_radius c d).choose_spec.1
    (exists_common_radius c d).choose_spec.2.1

theorem commonChart_subset_left (c d : PointedModelChart x) :
    (commonChart c d).neighborhood ⊆ c.neighborhood := smallNeighborhood_subset c _

theorem commonChart_subset_right (c d : PointedModelChart x) :
    (commonChart c d).neighborhood ⊆ d.neighborhood := (exists_common_radius c d).choose_spec.2.2

/-- Both comparison maps commute with the same ambient inclusion. -/
theorem common_ambient_maps (c d : PointedModelChart x) :
    c.ambient.comp (transition (commonChart c d) c (commonChart_subset_left c d)) =
        (commonChart c d).ambient ∧
    d.ambient.comp (transition (commonChart c d) d (commonChart_subset_right c d)) =
        (commonChart c d).ambient :=
  ⟨ambient_transition _ _ _, ambient_transition _ _ _⟩

/-- Geometric positive transition on a constructed common neighborhood. -/
def OrientedCompatible (c d : PointedModelChart x) : Prop :=
  Compatible (commonChart c d) d (commonChart_subset_right c d)

theorem oriented_overlap_localClass_eq (c d : PointedModelChart x) (h : OrientedCompatible c d) :
    c.localClass = d.localClass :=
  localClass_eq_of_common_nested_chart c d (commonChart c d)
    (commonChart_subset_left c d) (commonChart_subset_right c d)
    (shrink_compatible c _ _ _) h

/-- The half-radius chart is a genuinely smaller neighborhood. -/
theorem half_neighborhood_ne (c : PointedModelChart x) :
    smallNeighborhood c (1/2) ≠ c.neighborhood := by
  let v : E := realLineCoordinates (3/4)
  have hv : ‖v‖ = 3/4 := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_one, Real.norm_eq_abs]
    rw [Real.sqrt_sq_eq_abs, abs_abs]
    norm_num [v, realLineCoordinates]
  let u : D := ⟨v, by simpa only [Metric.mem_ball, dist_zero_right, hv] using (by norm_num : (3:ℝ)/4 < 1)⟩
  intro he
  have hm : c.ambient u ∈ smallNeighborhood c (1/2) := he.symm ▸ (c.coordinates u).2
  obtain ⟨w, hw, hew⟩ := hm
  have hwu : w = u := ambient_injective c hew
  subst w
  change ‖v‖ < 1/2 at hw
  rw [hv] at hw
  norm_num at hw

/-- Two concrete oriented Circle charts: the constructed chart and its half-radius restriction. -/
theorem circle_half_chart_overlap (x : Circle) :
    (shrinkChart (constructedChart x) (1/2) (by norm_num) (by norm_num)).localClass =
      ambientLocalGenerator x := by
  rw [← constructedChart_localClass]
  exact compatible_localClass_eq _ _ (smallNeighborhood_subset _ _)
    (shrink_compatible _ _ _ _)

open ConstructionTargets.CircleMetricFundamentalGroup

local instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩

/-- The actual circle identification restricted away from the specified point. -/
def puncturedCircleToMetric (x : Circle) :
    deletedPoint x ≃ₜ ({metricCircleHomeomorphCircle.symm x}ᶜ : Set (Metric.sphere (0 : ℂ) 1)) :=
  metricCircleHomeomorphCircle.symm.subtype (by
    intro y
    change y ≠ x ↔ metricCircleHomeomorphCircle.symm y ≠ metricCircleHomeomorphCircle.symm x
    exact metricCircleHomeomorphCircle.symm.injective.ne_iff.symm)

/-- Stereographic projection, including its actual source and target restrictions. -/
def puncturedCircleLine (x : Circle) : deletedPoint x ≃ₜ ℝ :=
  (puncturedCircleToMetric x).trans
    ((Homeomorph.setCongr (stereographic'_source (metricCircleHomeomorphCircle.symm x)).symm).trans
    (((stereographic' 1 (metricCircleHomeomorphCircle.symm x)).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic'_target (metricCircleHomeomorphCircle.symm x))).trans
    ((Homeomorph.Set.univ E).trans realLineCoordinates.symm))))

/-- The homology comparison is induced by this geometric homeomorphism. -/
def puncturedCircleHomologyIsoLine (x : Circle) (n : ℕ) :
    SingularHomology n (TopCat.of (deletedPoint x)) ≅ SingularHomology n (TopCat.of ℝ) :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).mapIso
    (TopCat.isoOfHomeo (puncturedCircleLine x))

theorem puncturedCircleHomologyIsoLine_hom (x : Circle) (n : ℕ) :
    (puncturedCircleHomologyIsoLine x n).hom =
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom (pairContinuousMap (puncturedCircleLine x))) := rfl

theorem puncturedCircle_positive_homology (x : Circle) (n : ℕ) (hn : n ≠ 0) :
    Limits.IsZero (SingularHomology n (TopCat.of (deletedPoint x))) := by
  letI : ContractibleSpace (deletedPoint x) :=
    (puncturedCircleLine x).contractibleSpace_iff.mpr inferInstance
  exact contractibleHigherHomology_isZero (deletedPoint x) n hn

/-- The ambient relative generator is the image under the exhibited chart map. -/
theorem circle_relative_generator (x : Circle) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1,
      ∃ n : ℤ, n • (constructedChart x).localClass = z :=
  (constructedChart x).localClass_generates

/-- Exact equality with chart-pair transport followed by neighborhood excision. -/
theorem circle_relative_generator_comparison (x : Circle) :
    (constructedChart x).localClass =
      HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (chartNeighborhood x) x) (deletedPoint x)
          (neighborhoodInclusion (chartNeighborhood x))
          (neighborhoodInclusion_mapsTo (chartNeighborhood x) x)) 1
        (transportedOpenDiskOnePunctureGenerator (modelChart x)
          (neighborhoodDeletedPoint (chartNeighborhood x) x) (modelChart_deletedPoint_iff x)) :=
  ambientLocalGenerator_eq_inclusion_transport x

end ConstructionTargets.OrientedOverlapPuncturedCircle
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.shrinkCoordinates
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.exists_common_radius
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.oriented_overlap_localClass_eq
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.circle_half_chart_overlap

#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.puncturedCircleLine
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.puncturedCircleHomologyIsoLine_hom
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.puncturedCircle_positive_homology
#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.circle_relative_generator

#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.circle_relative_generator_comparison

#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.half_neighborhood_ne

#print axioms ConstructionTargets.OrientedOverlapPuncturedCircle.common_ambient_maps

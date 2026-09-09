import ConstructionTargets.CircleAngleTransition
import Mathlib.Topology.Order.IntermediateValue
open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.CircleCoherentFundamentalClass
open OneDimensionalChartLocalGenerator OneDiskIncreasingOrientation
open NestedOrientedChartCompatibility NestedOrientedChartCompatibility.PointedModelChart
open OrientedOverlapPuncturedCircle CircleUniversalCover
abbrev J := Set.Ioo (-1 : ℝ) 1
lemma norm_one (v : E) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]
def diskInterval : D ≃ₜ J := realLineCoordinates.symm.subtype (by
  intro v
  change (v ∈ Metric.ball (0 : E) 1) ↔ (-1 < v 0 ∧ v 0 < 1)
  rw [Metric.mem_ball, dist_zero_right, norm_one, abs_lt])
def base : C(J, Circle) := (constructedChart (1 : Circle)).ambient.comp
  ⟨diskInterval.symm, diskInterval.symm.continuous⟩
lemma base_injective : Function.Injective base :=
  (ambient_injective (constructedChart (1 : Circle))).comp diskInterval.symm.injective
lemma exists_angle : ∃ F : C(J, ℝ), (∀ u, Circle.exp (F u) = base u) ∧
    (StrictMono F ∨ StrictAnti F) := by
  letI : ContractibleSpace J := (convex_Ioo (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  letI : LocPathConnectedSpace J := isOpen_Ioo.locPathConnectedSpace
  obtain ⟨F, hF, _⟩ := circleCover_isCoveringMap.existsUnique_continuousMap_lifts base
    ⟨0, by norm_num⟩ 0 (by
      rw [circleCover_zero]
      change 1 = (constructedChart (1 : Circle)).ambient (diskInterval.symm ⟨0, _⟩)
      have he : diskInterval.symm ⟨0, by norm_num⟩ = origin := by
        apply Subtype.ext
        ext i
        fin_cases i
        rfl
      rw [he]
      exact (constructedChart (1 : Circle)).origin_eq.symm)
  letI : Inhabited J := ⟨⟨0, by norm_num⟩⟩
  have hexp : ∀ u, Circle.exp (F u) = base u := fun u => congrFun hF.2 u
  refine ⟨F, hexp, F.continuous.strictMono_of_inj ?_⟩
  intro u v huv
  apply base_injective
  rw [← hexp u, ← hexp v, huv]


open RotatedCircleChartTransport PointedChartRecentering CircleAngleTransition

def coordinateTransition {p q : Circle} (c : PointedModelChart p) (d : PointedModelChart q)
    (h : c.neighborhood ⊆ d.neighborhood) : C(D,D) :=
  ⟨fun u => d.coordinates.symm ⟨c.ambient u, h (c.coordinates u).2⟩, by
    apply d.coordinates.symm.continuous.comp
    exact c.ambient.continuous.subtype_mk _⟩

lemma transition_ambient {p q : Circle} (c : PointedModelChart p) (d : PointedModelChart q)
    (h : c.neighborhood ⊆ d.neighborhood) (u : D) :
    d.ambient (coordinateTransition c d h u) = c.ambient u := by
  change (d.coordinates (d.coordinates.symm _)).val = _
  rw [d.coordinates.apply_symm_apply]

lemma rotated_transition_increasing (x y : Circle) (A T : C(D,D))
    (hA : Increasing A)
    (he : ∀ u, (rotatedChart y).ambient (T u) = (rotatedChart x).ambient (A u)) :
    Increasing T := by
  obtain ⟨F, hF, hmono | hanti⟩ := exists_angle
  all_goals
    letI : PreconnectedSpace D := Subtype.preconnectedSpace (convex_ball (0 : E) 1).isPreconnected
    let f : C(D,ℝ) := F.comp ((⟨diskInterval, diskInterval.continuous⟩ : C(D,J)).comp T)
    let g : C(D,ℝ) := F.comp ((⟨diskInterval, diskInterval.continuous⟩ : C(D,J)).comp A)
    have hg : ∀ u, Circle.exp (f u) = (y⁻¹ * x) * Circle.exp (g u) := by
      intro u
      change Circle.exp (F (diskInterval (T u))) = (y⁻¹ * x) * Circle.exp (F (diskInterval (A u)))
      simp only [hF, base, ContinuousMap.comp_apply, ContinuousMap.coe_mk, diskInterval.symm_apply_apply]
      have hu := he u
      change y * (constructedChart (1 : Circle)).ambient (T u) =
        x * (constructedChart (1 : Circle)).ambient (A u) at hu
      rw [mul_assoc, ← hu]
      simp
    intro u v huv
  · have hlt : g u < g v := hmono (hA u v huv)
    have ht := (angle_order_iff f g (y⁻¹ * x) hg u v).mpr hlt
    exact hmono.lt_iff_lt.mp ht
  · have hlt : g v < g u := hanti (hA u v huv)
    have ht := (angle_order_iff f g (y⁻¹ * x) hg v u).mpr hlt
    exact hanti.lt_iff_gt.mp ht

lemma recentered_transition_increasing (x y : Circle) (v : D) (r : ℝ) (hr : 0 < r)
    (hs : Metric.ball v.val r ⊆ Metric.ball (0 : E) 1)
    (h : (recenteredChart (rotatedChart x) v r hr hs).neighborhood ⊆ (rotatedChart y).neighborhood) :
    Increasing (coordinateTransition (recenteredChart (rotatedChart x) v r hr hs) (rotatedChart y) h) := by
  let A : C(D,D) := ⟨fun u => (affineBall v r hr hs u).val,
    continuous_subtype_val.comp (affineBall v r hr hs).continuous⟩
  apply rotated_transition_increasing x y A
  · exact recentered_coordinate_increasing v r hr hs
  · intro u
    exact transition_ambient _ _ h u

theorem geometric_overlap (x y : Circle) (v : D)
    (hv : (rotatedChart x).ambient v ∈ (rotatedChart y).neighborhood) :
    ∃ d : PointedModelChart ((rotatedChart x).ambient v),
      ∃ hx : d.neighborhood ⊆ (rotatedChart x).neighborhood,
      ∃ hy : d.neighborhood ⊆ (rotatedChart y).neighborhood,
      Increasing (coordinateTransition d (rotatedChart x) hx) ∧
      Increasing (coordinateTransition d (rotatedChart y) hy) := by
  obtain ⟨r, hr, hs, hy⟩ := exists_recenter_radius (rotatedChart x) v
    (rotatedChart y).neighborhood (rotatedChart y).open_neighborhood hv
  let d := recenteredChart (rotatedChart x) v r hr hs
  have hx : d.neighborhood ⊆ (rotatedChart x).neighborhood := by
    rintro z ⟨u, _, rfl⟩
    exact ((rotatedChart x).coordinates u).2
  exact ⟨d, hx, hy, recentered_transition_increasing x x v r hr hs hx,
    recentered_transition_increasing x y v r hr hs hy⟩

/-- Compatibility uses the actual coordinate transitions on a constructed common chart. -/
def GeometricCompatibility : Prop :=
  ∀ (x y : Circle) (v : D),
    (rotatedChart x).ambient v ∈ (rotatedChart y).neighborhood →
    ∃ d : PointedModelChart ((rotatedChart x).ambient v),
      ∃ hx : d.neighborhood ⊆ (rotatedChart x).neighborhood,
      ∃ hy : d.neighborhood ⊆ (rotatedChart y).neighborhood,
      Increasing (coordinateTransition d (rotatedChart x) hx) ∧
      Increasing (coordinateTransition d (rotatedChart y) hy)

open SingularHomologyConcrete CircleActualLocalization CircleRotationLocalization

/-- The constructed rotation atlas is geometrically compatible and one integral
absolute generator satisfies all its actual localization equations, uniquely. -/
theorem coherent_circle_fundamental_class :
    GeometricCompatibility ∧
    ∃! z : (SingularChains (TopCat.of Circle)).homology 1,
      (∀ w : (SingularChains (TopCat.of Circle)).homology 1, ∃ n : ℤ, n • z = w) ∧
      ∀ x : Circle, localization x z = (rotatedChart x).localClass :=
  ⟨geometric_overlap, unique_global_chart_class⟩

end ConstructionTargets.CircleCoherentFundamentalClass


#print axioms ConstructionTargets.CircleCoherentFundamentalClass.exists_angle
#print axioms ConstructionTargets.CircleCoherentFundamentalClass.coordinateTransition
#print axioms ConstructionTargets.CircleCoherentFundamentalClass.transition_ambient
#print axioms ConstructionTargets.CircleCoherentFundamentalClass.rotated_transition_increasing
#print axioms ConstructionTargets.CircleCoherentFundamentalClass.recentered_transition_increasing
#print axioms ConstructionTargets.CircleCoherentFundamentalClass.geometric_overlap
#print axioms ConstructionTargets.CircleCoherentFundamentalClass.coherent_circle_fundamental_class
#print axioms ConstructionTargets.RotatedCircleChartTransport.rotatedChart_chain_map
#print axioms ConstructionTargets.CircleRotationLocalization.localization_rotation_square

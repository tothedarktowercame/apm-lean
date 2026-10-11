import ConstructionTargets.PointWedgeExactEquality

noncomputable section

namespace ConstructionTargets.PolygonThreeLoopHalfOpenEquality

open PointWedgeQuotient
open PointWedgeExactEquality
open IntervalEndpointQuotientCircle
open ThreeEndpointLoopsHomeomorph
open PolygonBoundaryThreeLoopSurjectivityReduction
open PolygonThreeLoopHalfOpenNormalForm

theorem endpoint_halfOpen_injective :
    Function.Injective
      (fun t : Set.Ico (0 : ℝ) 1 => intervalQuotientMap (halfOpenToInterval t)) := by
  intro t u h
  have hc := congrArg endpointQuotientHomeomorphCircle h
  change endpointQuotientHomeomorphCircle
      (intervalQuotientMap (halfOpenToInterval t)) =
    endpointQuotientHomeomorphCircle
      (intervalQuotientMap (halfOpenToInterval u)) at hc
  simp only [intervalQuotientMap] at hc
  rw [endpointQuotientHomeomorphCircle_mk,
    endpointQuotientHomeomorphCircle_mk] at hc
  have ha : (t.1 : AddCircle (1 : ℝ)) = (u.1 : AddCircle (1 : ℝ)) :=
    AddCircle.injective_toCircle one_ne_zero hc
  have htu : t.1 = u.1 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using t.2) (by simpa using u.2)).mp ha
  exact Subtype.ext htu

theorem endpoint_halfOpen_eq_base_iff (t : Set.Ico (0 : ℝ) 1) :
    intervalQuotientMap (halfOpenToInterval t) = endpointBase ↔ t.1 = 0 := by
  constructor
  · intro h
    let z : Set.Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
    have htz : t = z := endpoint_halfOpen_injective (by
      simpa [z, endpointBase, halfOpenToInterval] using h)
    exact congrArg Subtype.val htz
  · intro h
    have htz : t = (⟨0, by norm_num⟩ : Set.Ico (0 : ℝ) 1) := Subtype.ext h
    subst t
    rfl

theorem firstLoopPoint_eq_iff (t u : Set.Ico (0 : ℝ) 1) :
    firstLoopPoint (halfOpenToInterval t) = firstLoopPoint (halfOpenToInterval u) ↔
      t = u := by
  constructor
  · intro h
    apply endpoint_halfOpen_injective
    apply quotientMap_inl_injective endpointBase endpointBase
    apply quotientMap_inl_injective twoEndpointLoopsPoint endpointBase
    exact h
  · rintro rfl; rfl

theorem secondLoopPoint_eq_iff (t u : Set.Ico (0 : ℝ) 1) :
    secondLoopPoint (halfOpenToInterval t) = secondLoopPoint (halfOpenToInterval u) ↔
      t = u := by
  constructor
  · intro h
    apply endpoint_halfOpen_injective
    apply quotientMap_inr_injective endpointBase endpointBase
    apply quotientMap_inl_injective twoEndpointLoopsPoint endpointBase
    exact h
  · rintro rfl; rfl

theorem thirdLoopPoint_eq_iff (t u : Set.Ico (0 : ℝ) 1) :
    thirdLoopPoint (halfOpenToInterval t) = thirdLoopPoint (halfOpenToInterval u) ↔
      t = u := by
  constructor
  · intro h
    apply endpoint_halfOpen_injective
    apply quotientMap_inr_injective twoEndpointLoopsPoint endpointBase
    exact h
  · rintro rfl; rfl

theorem firstLoopPoint_eq_secondLoopPoint_iff (t u : Set.Ico (0 : ℝ) 1) :
    firstLoopPoint (halfOpenToInterval t) = secondLoopPoint (halfOpenToInterval u) ↔
      t.1 = 0 ∧ u.1 = 0 := by
  rw [firstLoopPoint, secondLoopPoint,
    (quotientMap_inl_injective twoEndpointLoopsPoint endpointBase).eq_iff,
    quotientMap_inl_eq_inr_iff, endpoint_halfOpen_eq_base_iff,
    endpoint_halfOpen_eq_base_iff]

theorem firstLoopPoint_eq_thirdLoopPoint_iff (t u : Set.Ico (0 : ℝ) 1) :
    firstLoopPoint (halfOpenToInterval t) = thirdLoopPoint (halfOpenToInterval u) ↔
      t.1 = 0 ∧ u.1 = 0 := by
  rw [firstLoopPoint, thirdLoopPoint, quotientMap_inl_eq_inr_iff]
  simp only [twoEndpointLoopsPoint]
  rw [(quotientMap_inl_injective endpointBase endpointBase).eq_iff,
    endpoint_halfOpen_eq_base_iff, endpoint_halfOpen_eq_base_iff]

theorem secondLoopPoint_eq_thirdLoopPoint_iff (t u : Set.Ico (0 : ℝ) 1) :
    secondLoopPoint (halfOpenToInterval t) = thirdLoopPoint (halfOpenToInterval u) ↔
      t.1 = 0 ∧ u.1 = 0 := by
  rw [secondLoopPoint, thirdLoopPoint, quotientMap_inl_eq_inr_iff]
  constructor
  · rintro ⟨h, hu⟩
    have hp := (quotientMap_inl_eq_inr_iff endpointBase endpointBase endpointBase
      (intervalQuotientMap (halfOpenToInterval t))).mp (by
        simpa [twoEndpointLoopsPoint] using h.symm)
    have ht : intervalQuotientMap (halfOpenToInterval t) = endpointBase := hp.2
    exact ⟨(endpoint_halfOpen_eq_base_iff t).mp ht,
      (endpoint_halfOpen_eq_base_iff u).mp hu⟩
  · rintro ⟨ht, hu⟩
    constructor
    · exact ((quotientMap_inl_eq_inr_iff endpointBase endpointBase endpointBase
        (intervalQuotientMap (halfOpenToInterval t))).mpr
          ⟨rfl, (endpoint_halfOpen_eq_base_iff t).mpr ht⟩).symm
    · exact (endpoint_halfOpen_eq_base_iff u).mpr hu

end ConstructionTargets.PolygonThreeLoopHalfOpenEquality

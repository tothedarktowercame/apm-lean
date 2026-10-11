import ConstructionTargets.PolygonBoundaryThreeLoopBijections
import ConstructionTargets.PolygonBoundaryThreeLoopContinuity
import ConstructionTargets.CompactClosedEquivalenceQuotient

open Set Topology
open ConstructionTargets

noncomputable section

namespace ConstructionTargets.PolygonBoundaryCompactHausdorffInstances

open PointWedgeQuotient
open IntervalEndpointQuotientCircle
open PolygonBoundaryCircleSource
open PolygonBoundaryCircleRelations
open PolygonBoundaryCircleDecoderWellDefined
open PolygonBoundaryCircleDecoderRelationInvariant
open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryThreeLoopContinuity
open PolygonBoundaryThreeLoopDecoderLeftInverse
open PolygonBoundaryThreeLoopBijections
open PolygonBoundaryThreeLoopSurjectivityReduction
open PolygonBoundaryInducedQuotient
open PolygonBoundaryEdgeDecoders
open PolygonSixEdgeCircleCover
open ThreeEndpointLoopsHomeomorph
open PolygonTorusCrosscapRelation
open Surfaces

private theorem compactSpace_wedge {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    (x₀ : X) (y₀ : Y) : CompactSpace (Wedge x₀ y₀) := by
  constructor
  rw [← Set.range_eq_univ.mpr (surjective_quotientMap x₀ y₀)]
  simpa only [Set.image_univ] using
    isCompact_univ.image (continuous_quotientMap x₀ y₀)

private theorem wedge_eqvGen_iff {X Y : Type*} (x₀ : X) (y₀ : Y)
    (a b : Sum X Y) :
    Relation.EqvGen (Rel x₀ y₀) a b ↔
      a = b ∨ (a = .inl x₀ ∧ b = .inr y₀) ∨
        (a = .inr y₀ ∧ b = .inl x₀) := by
  constructor
  · intro h
    induction h with
    | rel a b h => cases h; aesop
    | refl => aesop
    | symm _ _ _ ih => rcases ih with h | h | h <;> aesop
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with h | h | h <;> rcases ih₂ with h' | h' | h' <;>
          simp_all
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .refl _
    · exact Relation.EqvGen.rel _ _ .base
    · exact (Relation.EqvGen.rel _ _
        (.base : Rel x₀ y₀ (.inl x₀) (.inr y₀))).symm

private theorem t2Space_wedge {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    (x₀ : X) (y₀ : Y) : T2Space (Wedge x₀ y₀) := by
  apply compact_closed_equivalence_quotient_t2 (WedgeSetoid x₀ y₀)
  have hclosed : IsClosed (diagonal (Sum X Y) ∪
      {(.inl x₀, .inr y₀), (.inr y₀, .inl x₀)}) :=
    isClosed_diagonal.union (isClosed_singleton.union isClosed_singleton)
  convert hclosed using 1
  ext p
  change Relation.EqvGen (Rel x₀ y₀) p.1 p.2 ↔ _
  rw [wedge_eqvGen_iff]
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_diagonal_iff]
  constructor <;> aesop

theorem compactSpace_threeEndpointLoops : CompactSpace ThreeEndpointLoops := by
  letI : CompactSpace TwoEndpointLoops := compactSpace_wedge endpointBase endpointBase
  exact compactSpace_wedge twoEndpointLoopsPoint endpointBase

private theorem t2Space_threeEndpointLoops : T2Space ThreeEndpointLoops := by
  letI : T2Space EndpointQuotient := endpointQuotientHomeomorphCircle.symm.t2Space
  letI : CompactSpace TwoEndpointLoops := compactSpace_wedge endpointBase endpointBase
  letI : T2Space TwoEndpointLoops := t2Space_wedge endpointBase endpointBase
  exact t2Space_wedge twoEndpointLoopsPoint endpointBase

private def sixEdgeParam (p : Fin 6 × Set.Icc (0 : ℝ) 1) : Circle :=
  circleEdgePoint p.1 p.2

private theorem continuous_sixEdgeParam : Continuous sixEdgeParam := by
  rw [continuous_prod_of_discrete_left]
  exact fun j => continuous_circleEdgePoint j

private theorem surjective_sixEdgeParam : Function.Surjective sixEdgeParam := by
  intro z
  obtain ⟨j, t, h⟩ := sixEdgeCircleCover z
  exact ⟨(j, t), h⟩

private theorem continuous_fromUnitIcc : Continuous fromUnitIcc := by
  unfold fromUnitIcc
  exact continuous_subtype_val.subtype_mk _

private theorem continuous_firstDecode :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 => firstLoopPoint (fromUnitIcc t)) := by
  unfold firstLoopPoint
  exact (continuous_quotientMap _ _).comp
    (continuous_inl.comp ((continuous_quotientMap _ _).comp
      (continuous_inl.comp (continuous_quot_mk.comp continuous_fromUnitIcc))))

private theorem continuous_secondDecode :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 => secondLoopPoint (fromUnitIcc t)) := by
  unfold secondLoopPoint
  exact (continuous_quotientMap _ _).comp
    (continuous_inl.comp ((continuous_quotientMap _ _).comp
      (continuous_inr.comp (continuous_quot_mk.comp continuous_fromUnitIcc))))

private theorem continuous_thirdDecode :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 => thirdLoopPoint (fromUnitIcc t)) := by
  unfold thirdLoopPoint
  exact (continuous_quotientMap _ _).comp
    (continuous_inr.comp (continuous_quot_mk.comp continuous_fromUnitIcc))

private theorem continuous_n3CircleDecode : Continuous n3CircleDecode := by
  apply (IsQuotientMap.of_surjective_continuous surjective_sixEdgeParam
    continuous_sixEdgeParam).continuous_iff.mpr
  rw [continuous_prod_of_discrete_left]
  intro j
  fin_cases j <;> simp only [Function.comp_apply, sixEdgeParam,
    n3CircleDecode_edge, n3EdgeDecode_zero, n3EdgeDecode_one,
    n3EdgeDecode_two, n3EdgeDecode_three, n3EdgeDecode_four, n3EdgeDecode_five]
  all_goals first | exact continuous_firstDecode | exact continuous_secondDecode |
    exact continuous_thirdDecode

private theorem continuous_reverse :
    Continuous (reverse : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1) := by
  unfold reverse
  fun_prop

private theorem continuous_torusCrosscapCircleDecode :
    Continuous torusCrosscapCircleDecode := by
  apply (IsQuotientMap.of_surjective_continuous surjective_sixEdgeParam
    continuous_sixEdgeParam).continuous_iff.mpr
  rw [continuous_prod_of_discrete_left]
  intro j
  fin_cases j <;> simp only [Function.comp_apply, sixEdgeParam,
    torusCrosscapCircleDecode_edge, torusCrosscapEdgeDecode_zero,
    torusCrosscapEdgeDecode_one, torusCrosscapEdgeDecode_two,
    torusCrosscapEdgeDecode_three, torusCrosscapEdgeDecode_four,
    torusCrosscapEdgeDecode_five]
  · exact continuous_firstDecode
  · exact continuous_secondDecode
  · exact continuous_firstDecode.comp continuous_reverse
  · exact continuous_secondDecode.comp continuous_reverse
  · exact continuous_thirdDecode
  · exact continuous_thirdDecode

private theorem n3_eqvGen_iff_decode_eq (z w : Circle) :
    Relation.EqvGen N3CircleRel z w ↔ n3CircleDecode z = n3CircleDecode w := by
  constructor
  · exact fun h => RelationQuotientLeftInverse.eqvGen_respects N3CircleRel
      n3CircleDecode (fun {_ _} h => n3CircleDecode_respects h) h
  · intro h
    have hr : Function.RightInverse n3QuotientDecode n3ThreeLoops :=
      n3QuotientDecode_leftInverse.rightInverse_of_surjective surjective_n3ThreeLoops
    change (Relation.EqvGen.setoid N3CircleRel).r z w
    apply Quotient.exact
    change n3CircleQuotientMap z = n3CircleQuotientMap w
    rw [← hr (n3CircleQuotientMap z), ← hr (n3CircleQuotientMap w)]
    exact congrArg n3ThreeLoops h

private theorem torusCrosscap_eqvGen_iff_decode_eq (z w : Circle) :
    Relation.EqvGen TorusCrosscapCircleRel z w ↔
      torusCrosscapCircleDecode z = torusCrosscapCircleDecode w := by
  constructor
  · exact fun h => RelationQuotientLeftInverse.eqvGen_respects
      TorusCrosscapCircleRel torusCrosscapCircleDecode
      (fun {_ _} h => torusCrosscapCircleDecode_respects h) h
  · intro h
    have hr : Function.RightInverse torusCrosscapQuotientDecode
        torusCrosscapThreeLoops :=
      torusCrosscapQuotientDecode_leftInverse.rightInverse_of_surjective
        surjective_torusCrosscapThreeLoops
    change (Relation.EqvGen.setoid TorusCrosscapCircleRel).r z w
    apply Quotient.exact
    change torusCrosscapCircleQuotientMap z = torusCrosscapCircleQuotientMap w
    rw [← hr (torusCrosscapCircleQuotientMap z),
      ← hr (torusCrosscapCircleQuotientMap w)]
    exact congrArg torusCrosscapThreeLoops h

private theorem isClosed_n3_eqvGen :
    IsClosed {p : Circle × Circle | Relation.EqvGen N3CircleRel p.1 p.2} := by
  letI : T2Space ThreeEndpointLoops := t2Space_threeEndpointLoops
  have hclosed : IsClosed {p : Circle × Circle |
      n3CircleDecode p.1 = n3CircleDecode p.2} :=
    isClosed_diagonal.preimage
      (continuous_n3CircleDecode.fst'.prodMk continuous_n3CircleDecode.snd')
  simpa only [n3_eqvGen_iff_decode_eq] using hclosed

private theorem isClosed_torusCrosscap_eqvGen :
    IsClosed {p : Circle × Circle |
      Relation.EqvGen TorusCrosscapCircleRel p.1 p.2} := by
  letI : T2Space ThreeEndpointLoops := t2Space_threeEndpointLoops
  have hclosed : IsClosed {p : Circle × Circle |
      torusCrosscapCircleDecode p.1 = torusCrosscapCircleDecode p.2} :=
    isClosed_diagonal.preimage
      (continuous_torusCrosscapCircleDecode.fst'.prodMk
        continuous_torusCrosscapCircleDecode.snd')
  simpa only [torusCrosscap_eqvGen_iff_decode_eq] using hclosed

theorem t2Space_n3CircleQuotient :
    T2Space (CircleQuotient (SurfaceRel false 3)) :=
  compact_closed_equivalence_quotient_t2
    (Relation.EqvGen.setoid N3CircleRel) isClosed_n3_eqvGen

theorem t2Space_torusCrosscapCircleQuotient :
    T2Space (CircleQuotient TorusCrosscapRel) :=
  compact_closed_equivalence_quotient_t2
    (Relation.EqvGen.setoid TorusCrosscapCircleRel)
    isClosed_torusCrosscap_eqvGen

theorem polygonBoundaryCompactHausdorffInstances :
    CompactSpace ThreeEndpointLoops ∧
      T2Space (CircleQuotient (SurfaceRel false 3)) ∧
      T2Space (CircleQuotient TorusCrosscapRel) :=
  ⟨compactSpace_threeEndpointLoops, t2Space_n3CircleQuotient,
    t2Space_torusCrosscapCircleQuotient⟩

#print axioms polygonBoundaryCompactHausdorffInstances

end ConstructionTargets.PolygonBoundaryCompactHausdorffInstances

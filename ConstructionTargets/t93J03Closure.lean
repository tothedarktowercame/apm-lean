import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.KleinPlaneActionFree
import ConstructionTargets.KleinPlaneOrbitQuotientTopology
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.KleinClosedSquareOrbitInverseContinuity
import ConstructionTargets.KleinSquareEqvGenCasesIff
import ConstructionTargets.PolygonSurfacePiOne

/-! # Generic closing lemmas for t93J03

The Klein-bottle-specific library obligations supply a cover and an exact
subgroup equality.  These lemmas contain the already proved generic lifting
and embedding arguments used after that equality is available.
-/

open ConstructionTargets.StatementSurfaceModels Set
noncomputable section
namespace ConstructionTargets.t93J03Closure

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm
open KleinPlaneAffineAction
open KleinCoordinateInversionPower
open ConstructionTargets.KleinOrbitQuotientHomeomorph
open ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv
open ConstructionTargets.KleinClosedSquareOrbitInverseContinuity
open KleinPlaneActionSquareOrbitClassification
open KleinSquareBoundaryRelation
open ConstructionTargets.PolygonSurfacePiOne

/-- An orbit intersection determines both integer normal-form coordinates by
the source and target points.  These are the equations used to bound the
possible deck transformations meeting two compact subsets of the plane. -/
theorem coordinate_equations_of_smul_eq
    (g : PresentedKleinGroup) (p q : ℝ × ℝ) (h : g • p = q) :
    (((Multiplicative.toAdd (coordinateEquiv g).2 : ℤ) : ℝ) = q.2 - p.2) ∧
      (((Multiplicative.toAdd (coordinateEquiv g).1 : ℤ) : ℝ) =
        q.1 -
          ((Multiplicative.toAdd
            (action (coordinateEquiv g).2 (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * p.1) := by
  change coordinateAct (coordinateEquiv g) p = q at h
  constructor
  · have hy := congrArg Prod.snd h
    dsimp [coordinateAct] at hy
    linarith
  · have hx := congrArg Prod.fst h
    dsimp [coordinateAct] at hx
    linarith

/-- Only finitely many presented Klein-group elements have their two normal
form coordinates in prescribed finite sets. -/
theorem finite_of_coordinatePair_mem {S T : Set ZMul}
    (hS : S.Finite) (hT : T.Finite) :
    {g : PresentedKleinGroup | coordinatePairEquiv g ∈ S ×ˢ T}.Finite :=
  (hS.prod hT).preimage coordinatePairEquiv.injective.injOn

/-- Integer coordinates whose real casts lie in a continuous image of a
compact set form a finite set. -/
theorem finite_zmul_cast_mem_compact_image
    {A : Type*} [TopologicalSpace A] {K : Set A} (hK : IsCompact K)
    (f : A → ℝ) (hf : Continuous f) :
    {z : ZMul | ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}.Finite := by
  let S : Set ZMul :=
    {z | ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}
  have hc : IsCompact (f '' K) := hK.image hf
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  obtain ⟨za : ℤ, hza : (za : ℝ) ≤ a⟩ := exists_int_le a
  obtain ⟨zb : ℤ, hzb : b ≤ (zb : ℝ)⟩ := exists_int_ge b
  have hbelow : BddBelow S := by
    refine ⟨Multiplicative.ofAdd za, ?_⟩
    intro z hz
    change za ≤ Multiplicative.toAdd z
    rw [← Int.cast_le (R := ℝ)]
    exact hza.trans (ha hz)
  have habove : BddAbove S := by
    refine ⟨Multiplicative.ofAdd zb, ?_⟩
    intro z hz
    change Multiplicative.toAdd z ≤ zb
    rw [← Int.cast_le (R := ℝ)]
    exact (hb hz).trans hzb
  exact hbelow.finite_of_bddAbove habove

/-- For two compact plane sets, only finitely many vertical integer
translations can occur in an orbit intersection. -/
theorem finite_vertical_coordinates_of_compact
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {n : ZMul |
      ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
        (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}.Finite := by
  apply finite_zmul_cast_mem_compact_image (hK.prod hL)
  fun_prop

/-- After fixing the vertical normal-form coordinate, compactness permits only
finitely many horizontal coordinates.  The multiplier is kept in its literal
`action n 1` form, so no parity surrogate for the affine action is introduced. -/
theorem finite_horizontal_coordinates_of_compact
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) (n : ZMul) :
    {m : ZMul |
      ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
        (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
          pq.2.1 -
            ((Multiplicative.toAdd
              (action n (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) ''
          (K ×ˢ L)}.Finite := by
  apply finite_zmul_cast_mem_compact_image (hK.prod hL)
  fun_prop

/-- Compact subsets of the plane meet only finitely many translates under the
literal affine Klein action. -/
theorem finite_klein_actors_of_compact {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : PresentedKleinGroup | ((g • ·) '' K ∩ L).Nonempty}.Finite := by
  let V : Set ZMul := {n |
    ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}
  let H : ZMul → Set ZMul := fun n => {m |
    ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        pq.2.1 -
          ((Multiplicative.toAdd
            (action n (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) ''
        (K ×ˢ L)}
  have hV : V.Finite := finite_vertical_coordinates_of_compact hK hL
  have hH : ∀ n, (H n).Finite := fun n =>
    finite_horizontal_coordinates_of_compact hK hL n
  have hPairs : (⋃ n ∈ V, H n ×ˢ ({n} : Set ZMul)).Finite :=
    hV.biUnion fun n _ => (hH n).prod (Set.finite_singleton n)
  apply (hPairs.preimage coordinatePairEquiv.injective.injOn).subset
  intro g hg
  obtain ⟨q, ⟨p, hp, hgp⟩, hq⟩ := hg
  have heq := coordinate_equations_of_smul_eq g p q hgp
  apply Set.mem_iUnion₂.mpr
  refine ⟨(coordinateEquiv g).2, ?_, ?_⟩
  · exact ⟨⟨p, q⟩, ⟨hp, hq⟩, heq.1.symm⟩
  · change (coordinateEquiv g).1 ∈ H (coordinateEquiv g).2 ∧
      (coordinateEquiv g).2 ∈ ({(coordinateEquiv g).2} : Set ZMul)
    exact ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, heq.2.symm⟩, Set.mem_singleton _⟩

/-- The literal affine Klein action is continuous in the plane variable. -/
noncomputable instance kleinPlaneContinuousConstSMul :
    ContinuousConstSMul PresentedKleinGroup (ℝ × ℝ) where
  continuous_const_smul := KleinPlaneOrbitQuotient.continuous_smul

noncomputable instance kleinPlaneProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul PresentedKleinGroup (ℝ × ℝ) where
  finite_disjoint_inter_image hK hL :=
    finite_klein_actors_of_compact hK hL

theorem sameOrbit_iff_orbitRel (p q : ℝ × ℝ) :
    KleinSquareEqvGenToCases.SameOrbit p q ↔
      MulAction.orbitRel PresentedKleinGroup (ℝ × ℝ) p q := by
  change q ∈ MulAction.orbit PresentedKleinGroup p ↔
    p ∈ MulAction.orbit PresentedKleinGroup q
  exact MulAction.mem_orbit_symm

/-- Identity on plane representatives, comparing the banked explicit orbit
setoid with Mathlib's action-orbit setoid. -/
noncomputable def planeOrbitRelHomeomorph :
    PlaneOrbitQuotient ≃ₜ
      MulAction.orbitRel.Quotient PresentedKleinGroup (ℝ × ℝ) where
  toFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound ((sameOrbit_iff_orbitRel p q).mp h)
  invFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound ((sameOrbit_iff_orbitRel p q).mpr h)
  left_inv := by rintro ⟨p⟩; rfl
  right_inv := by rintro ⟨p⟩; rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

noncomputable instance kleinPlaneOrbitT2Space : T2Space PlaneOrbitQuotient := by
  letI : ContinuousConstSMul PresentedKleinGroup (ℝ × ℝ) :=
    kleinPlaneContinuousConstSMul
  letI : ProperlyDiscontinuousSMul PresentedKleinGroup (ℝ × ℝ) :=
    kleinPlaneProperlyDiscontinuousSMul
  letI : T2Space
      (MulAction.orbitRel.Quotient PresentedKleinGroup (ℝ × ℝ)) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
      (Γ := PresentedKleinGroup) (T := ℝ × ℝ)
  exact planeOrbitRelHomeomorph.symm.t2Space

/-- The banked closed-fundamental-square equivalence is a homeomorphism once
the literal affine action supplies the Hausdorff orbit quotient. -/
noncomputable def closedSquareOrbitHomeomorph :
    ClosedSquareOrbitQuotient ≃ₜ PlaneOrbitQuotient where
  toEquiv := closedSquareOrbitQuotientEquiv
  continuous_toFun := continuous_closedSquareOrbitQuotientEquiv
  continuous_invFun := closedSquareOrbitQuotientEquiv_continuous_symm_of_t2

def closedSquareEdgeSetoid : Setoid ClosedSquare where
  r p q := Relation.EqvGen SquareRel p.1 q.1
  iseqv := ⟨fun p => Relation.EqvGen.refl p.1,
    fun {_ _} h => h.symm,
    fun {_ _ _} h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev ClosedSquareEdgeQuotient := Quotient closedSquareEdgeSetoid

/-- On square representatives the generated polygon relation is exactly the
orbit relation of the literal affine Klein action. -/
theorem closedSquare_eqvGen_iff_sameOrbit (p q : ClosedSquare) :
    Relation.EqvGen SquareRel p.1 q.1 ↔
      KleinSquareEqvGenToCases.SameOrbit p.1 q.1 := by
  rw [KleinSquareEqvGenCasesIff.eqvGen_iff_cases p.2 q.2]
  exact (sameOrbit_iff_cases p.2 q.2).symm

/-- Identity on closed-square representatives, descending the exact relation
comparison to the two quotient spaces. -/
noncomputable def closedSquareEdgeOrbitHomeomorph :
    ClosedSquareEdgeQuotient ≃ₜ ClosedSquareOrbitQuotient where
  toFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound ((closedSquare_eqvGen_iff_sameOrbit p q).mp (by
      change Relation.EqvGen SquareRel p.1 q.1 at h
      exact h))
  invFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound (show closedSquareEdgeSetoid.r p q from
      (closedSquare_eqvGen_iff_sameOrbit p q).mpr h)
  left_inv := by rintro ⟨p⟩; rfl
  right_inv := by rintro ⟨p⟩; rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

/-- The standard four-edge nonorientable pairing specialized to the frozen
Klein-bottle genus. -/
noncomputable def kleinPairingData : PairingData :=
  nonorientableStandardPairingData 2 (by omega)

/-- The standard polygon quotient is exactly the frozen `KleinBottle`, with
the direction needed to transport its fundamental-group computation. -/
noncomputable def kleinPairingSpaceHomeomorph :
    kleinPairingData.Space ≃ₜ KleinBottle :=
  nonorientableStandardSpaceHomeomorph 2

/-- The boundary skeleton of the frozen Klein polygon is the wedge indexed by
the two nonorientable edge-pairing orbits. -/
noncomputable def kleinSkeletonHomeomorphTwoCircles :
    kleinPairingData.skeleton ≃ₜ
      PointWedgeQuotient.FiniteWedge (PairingOrbit kleinPairingData.pair) :=
  kleinPairingData.skeletonHomeomorphWedge

/-- The two circle factors are labeled by the registered generators `false`
and `true`, in the order of the two nonorientable edge pairs. -/
noncomputable def kleinPairingOrbitEquivBool :
    PairingOrbit kleinPairingData.pair ≃ Bool :=
  (nonorientableOrbitEquiv 2).trans finTwoEquiv

@[simp] theorem kleinPairingOrbitEquivBool_edge_zero :
    kleinPairingOrbitEquivBool (kleinPairingData.orbit (0 : Fin 4)) = false := by
  rfl

@[simp] theorem kleinPairingOrbitEquivBool_edge_one :
    kleinPairingOrbitEquivBool (kleinPairingData.orbit (1 : Fin 4)) = false := by
  rfl

@[simp] theorem kleinPairingOrbitEquivBool_edge_two :
    kleinPairingOrbitEquivBool (kleinPairingData.orbit (2 : Fin 4)) = true := by
  rfl

@[simp] theorem kleinPairingOrbitEquivBool_edge_three :
    kleinPairingOrbitEquivBool (kleinPairingData.orbit (3 : Fin 4)) = true := by
  rfl

/-- The four oriented boundary arcs of the standard Klein polygon, after
identifying its skeleton with the orbit-indexed circle wedge.  Thus its
attaching word is the nonorientable word `a a b b`; every occurrence uses
the reversed interval coordinate because all four standard signs are false. -/
theorem kleinPolygon_attaching_arcs (t : Set.Icc (0 : ℝ) 1) :
    kleinSkeletonHomeomorphTwoCircles (kleinPairingData.skeletonArc
        ⟨0, by simp [kleinPairingData]⟩ t) =
        PointWedgeQuotient.wedgeCircle (kleinPairingData.orbit
          ⟨0, by simp [kleinPairingData]⟩)
          (circleArc (reverseIcc t)) ∧
    kleinSkeletonHomeomorphTwoCircles (kleinPairingData.skeletonArc
        ⟨1, by simp [kleinPairingData]⟩ t) =
        PointWedgeQuotient.wedgeCircle (kleinPairingData.orbit
          ⟨1, by simp [kleinPairingData]⟩)
          (circleArc (reverseIcc t)) ∧
    kleinSkeletonHomeomorphTwoCircles (kleinPairingData.skeletonArc
        ⟨2, by simp [kleinPairingData]⟩ t) =
        PointWedgeQuotient.wedgeCircle (kleinPairingData.orbit
          ⟨2, by simp [kleinPairingData]⟩)
          (circleArc (reverseIcc t)) ∧
    kleinSkeletonHomeomorphTwoCircles (kleinPairingData.skeletonArc
        ⟨3, by simp [kleinPairingData]⟩ t) =
        PointWedgeQuotient.wedgeCircle (kleinPairingData.orbit
          ⟨3, by simp [kleinPairingData]⟩)
          (circleArc (reverseIcc t)) := by
  repeat' apply And.intro
  all_goals
    rw [kleinSkeletonHomeomorphTwoCircles,
      PairingData.skeletonHomeomorphWedge_skeletonArc]
    apply PairingData.signedWedgeArc_of_not_sign
    rfl

/-- The change of generators from the polygon word `x x y y` to the frozen
presentation sends `a` to `x*y` and `b` to `y⁻¹`.  Its Klein relator is
the conjugate by `y` of the polygon attaching relator. -/
theorem kleinRelator_generatorChange {G : Type*} [Group G] (x y : G) :
    (y⁻¹)⁻¹ * (x * y) * y⁻¹ * (x * y) =
      y * (x * x * y * y) * y⁻¹ := by
  group

/-- Consequently the polygon relation and the registered Klein relation are
equivalent under that generator change. -/
theorem kleinRelator_generatorChange_eq_one_iff
    {G : Type*} [Group G] (x y : G) :
    (y⁻¹)⁻¹ * (x * y) * y⁻¹ * (x * y) = 1 ↔
      x * x * y * y = 1 := by
  rw [kleinRelator_generatorChange]
  constructor
  · intro h
    calc
      x * x * y * y = y⁻¹ * (y * (x * x * y * y) * y⁻¹) * y := by group
      _ = 1 := by rw [h]; simp
  · intro h
    rw [h]
    simp

/-- Once proper discontinuity of the explicit affine action is supplied, the
banked deck-group theorem computes the fundamental group at the canonical
orbit of the origin. -/
theorem kleinPlaneOrbit_pi1_at_origin
    [ProperlyDiscontinuousSMul PresentedKleinGroup (ℝ × ℝ)] :
    Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient PresentedKleinGroup (ℝ × ℝ))
          (Quotient.mk _ (0, 0)) ≃* PresentedKleinGroup) :=
  ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      eq_one_of_smul_eq (0, 0)

/-- Transport a computed fundamental group from one basepoint to every
basepoint of a path-connected space.  This is the final basepoint adapter in
C1: the orbit calculation may use the image of `(0, 0)`, while the registered
statement quantifies over an arbitrary point of the Klein bottle. -/
theorem fundamentalGroupEquiv_every_basepoint
    {Y G : Type*} [TopologicalSpace Y] [PathConnectedSpace Y] [Group G]
    (y₀ : Y) (h₀ : Nonempty (FundamentalGroup Y y₀ ≃* G)) :
    ∀ y : Y, Nonempty (FundamentalGroup Y y ≃* G) := by
  intro y
  obtain ⟨e₀⟩ := h₀
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y y₀).trans e₀⟩

def subspaceInclusion (X : Set KleinBottle) : C(X, KleinBottle) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Rewrite an exact covering subgroup computation and apply the standard
covering-space lifting criterion. -/
theorem coveringLift_of_subgroup_le
    {G C : Type} [Group G] [TopologicalSpace C] {p : C → KleinBottle}
    (hp : IsCoveringMap p) (c : C) {k : KleinBottle} (hpc : p c = k)
    (e : FundamentalGroup KleinBottle k ≃* G) (H : Subgroup G)
    (hcover :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range =
        Subgroup.comap e.toMonoidHom H)
    (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X]
    (x : X) (hx : (x : KleinBottle) = k)
    (hX : ∀ g ∈ (FundamentalGroup.mapOfEq (subspaceInclusion X) hx).range,
      e g ∈ H) :
    ∃ l : C(X, C), p ∘ l = subspaceInclusion X := by
  cases hx
  have hle :
      (FundamentalGroup.map (subspaceInclusion X) x).range ≤
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range := by
    rintro g ⟨y, rfl⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective y
    rw [hcover]
    apply hX
    refine ⟨FundamentalGroup.fromPath (.mk γ), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    congr
  obtain ⟨l, ⟨_, hl⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts_of_range_le hpc hle
  exact ⟨l, hl⟩

/-- A lift of a subtype inclusion is an embedding by cancellation; composing
with an embedding of the covering space preserves embedding. -/
theorem lift_isEmbedding_assembly
    {C : Type} [TopologicalSpace C] {p : C → KleinBottle}
    (hp : Continuous p) (jC : C(C, ℝ × ℝ))
    (hjC : Topology.IsEmbedding jC)
    (X : Set KleinBottle) (l : C(X, C))
    (hl : p ∘ l = subspaceInclusion X) :
    ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j := by
  have hl' : Topology.IsEmbedding l := by
    apply Topology.IsEmbedding.of_comp l.continuous hp
    rw [hl]
    exact Topology.IsEmbedding.subtypeVal
  exact ⟨jC.comp l, hjC.comp hl'⟩

#print axioms coveringLift_of_subgroup_le
#print axioms lift_isEmbedding_assembly
#print axioms fundamentalGroupEquiv_every_basepoint
#print axioms kleinPlaneContinuousConstSMul
#print axioms kleinPlaneOrbit_pi1_at_origin
#print axioms coordinate_equations_of_smul_eq
#print axioms finite_of_coordinatePair_mem
#print axioms finite_zmul_cast_mem_compact_image
#print axioms finite_vertical_coordinates_of_compact
#print axioms finite_horizontal_coordinates_of_compact
#print axioms finite_klein_actors_of_compact
#print axioms kleinPlaneProperlyDiscontinuousSMul
#print axioms planeOrbitRelHomeomorph
#print axioms closedSquareOrbitHomeomorph
#print axioms closedSquare_eqvGen_iff_sameOrbit
#print axioms closedSquareEdgeOrbitHomeomorph
#print axioms kleinPairingSpaceHomeomorph
#print axioms kleinSkeletonHomeomorphTwoCircles
#print axioms kleinPairingOrbitEquivBool
#print axioms kleinPolygon_attaching_arcs
#print axioms kleinRelator_generatorChange_eq_one_iff

end ConstructionTargets.t93J03Closure

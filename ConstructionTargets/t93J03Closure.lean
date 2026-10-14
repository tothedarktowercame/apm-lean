import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.KleinPlaneActionFree
import ConstructionTargets.KleinPlaneOrbitQuotientTopology
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.KleinClosedSquareOrbitInverseContinuity
import ConstructionTargets.KleinSquareEqvGenCasesIff
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.PolygonSurfaceHomology

/-! # Generic closing lemmas for t93J03

The Klein-bottle-specific library obligations supply a cover and an exact
subgroup equality.  These lemmas contain the already proved generic lifting
and embedding arguments used after that equality is available.
-/

open ConstructionTargets.StatementSurfaceModels Set CategoryTheory
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
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgeVanKampen
open ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan
open ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PolygonSurfaceHomology

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

/-- The presentation read directly from the polygon attaching word. -/
def kleinPolygonRelations : Set (FreeGroup Bool) :=
  {FreeGroup.of false * FreeGroup.of false *
    FreeGroup.of true * FreeGroup.of true}

abbrev KleinPolygonPresentedGroup := PresentedGroup kleinPolygonRelations

def kleinPolygonGeneratorX : KleinPolygonPresentedGroup := PresentedGroup.of false
def kleinPolygonGeneratorY : KleinPolygonPresentedGroup := PresentedGroup.of true

/-- Substitute `x = a*b`, `y = b⁻¹` in the polygon presentation. -/
def kleinPolygonToPresented : KleinPolygonPresentedGroup →* PresentedKleinGroup :=
  PresentedGroup.toGroup
    (f := fun i => if i then generatorB⁻¹ else generatorA * generatorB) (by
      intro r hr
      change r ∈ ({FreeGroup.of false * FreeGroup.of false *
        FreeGroup.of true * FreeGroup.of true} : Set (FreeGroup Bool)) at hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      simp only [map_mul, FreeGroup.lift_apply_of, if_false, if_true]
      apply (kleinRelator_generatorChange_eq_one_iff
        (generatorA * generatorB) generatorB⁻¹).mp
      simpa [generatorA, generatorB, relations] using
        (PresentedGroup.one_of_mem (rels := relations) (Set.mem_singleton _)))

/-- Substitute `a = x*y`, `b = y⁻¹` in the frozen presentation. -/
def kleinPresentedToPolygon : PresentedKleinGroup →* KleinPolygonPresentedGroup :=
  PresentedGroup.toGroup
    (f := fun i => if i then kleinPolygonGeneratorY⁻¹ else
      kleinPolygonGeneratorX * kleinPolygonGeneratorY) (by
      intro r hr
      change r ∈ ({(FreeGroup.of true)⁻¹ * FreeGroup.of false *
        FreeGroup.of true * FreeGroup.of false} : Set (FreeGroup Bool)) at hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, if_false, if_true]
      apply (kleinRelator_generatorChange_eq_one_iff
        kleinPolygonGeneratorX kleinPolygonGeneratorY).mpr
      simpa [kleinPolygonGeneratorX, kleinPolygonGeneratorY,
        kleinPolygonRelations] using
        (PresentedGroup.one_of_mem (rels := kleinPolygonRelations)
          (Set.mem_singleton _)))

@[simp] theorem kleinPolygonToPresented_x :
    kleinPolygonToPresented kleinPolygonGeneratorX = generatorA * generatorB := by
  simp [kleinPolygonToPresented, kleinPolygonGeneratorX]

@[simp] theorem kleinPolygonToPresented_y :
    kleinPolygonToPresented kleinPolygonGeneratorY = generatorB⁻¹ := by
  simp [kleinPolygonToPresented, kleinPolygonGeneratorY]

@[simp] theorem kleinPresentedToPolygon_a :
    kleinPresentedToPolygon generatorA =
      kleinPolygonGeneratorX * kleinPolygonGeneratorY := by
  simp [kleinPresentedToPolygon, generatorA]

@[simp] theorem kleinPresentedToPolygon_b :
    kleinPresentedToPolygon generatorB = kleinPolygonGeneratorY⁻¹ := by
  simp [kleinPresentedToPolygon, generatorB]

/-- The `aabb` polygon presentation is exactly the registered Klein group. -/
noncomputable def kleinPolygonPresentedGroupEquiv :
    KleinPolygonPresentedGroup ≃* PresentedKleinGroup where
  toFun := kleinPolygonToPresented
  invFun := kleinPresentedToPolygon
  left_inv := by
    intro g
    have hhom : kleinPresentedToPolygon.comp kleinPolygonToPresented =
        MonoidHom.id KleinPolygonPresentedGroup := by
      apply PresentedGroup.ext
      intro i
      cases i
      · change kleinPresentedToPolygon
          (kleinPolygonToPresented kleinPolygonGeneratorX) =
            kleinPolygonGeneratorX
        rw [kleinPolygonToPresented_x, map_mul,
          kleinPresentedToPolygon_a, kleinPresentedToPolygon_b]
        group
      · change kleinPresentedToPolygon
          (kleinPolygonToPresented kleinPolygonGeneratorY) =
            kleinPolygonGeneratorY
        rw [kleinPolygonToPresented_y, map_inv, kleinPresentedToPolygon_b]
        group
    exact DFunLike.congr_fun hhom g
  right_inv := by
    intro g
    have hhom : kleinPolygonToPresented.comp kleinPresentedToPolygon =
        MonoidHom.id PresentedKleinGroup := by
      apply PresentedGroup.ext
      intro i
      cases i
      · change kleinPolygonToPresented (kleinPresentedToPolygon generatorA) =
          generatorA
        rw [kleinPresentedToPolygon_a, map_mul,
          kleinPolygonToPresented_x, kleinPolygonToPresented_y]
        group
      · change kleinPolygonToPresented (kleinPresentedToPolygon generatorB) =
          generatorB
        rw [kleinPresentedToPolygon_b, map_inv, kleinPolygonToPresented_y]
        group
    exact DFunLike.congr_fun hhom g
  map_mul' := kleinPolygonToPresented.map_mul

/-- A homeomorphism transports the based fundamental group. -/
def fundamentalGroupEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

/-- Transporting a based loop along two paths with the same endpoints changes
its target loop only by conjugacy. -/
theorem fundamentalGroup_pathTransport_isConj
    {X : Type*} [TopologicalSpace X] {x y : X}
    (p q : Path x y) (g : FundamentalGroup X x) :
    IsConj (FundamentalGroup.fundamentalGroupMulEquivOfPath p g)
      (FundamentalGroup.fundamentalGroupMulEquivOfPath q g) := by
  let ep := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)).symm ⟦p⟧
  let eq := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)).symm ⟦q⟧
  refine ⟨toUnits (ep.inv ≫ eq.hom), ?_⟩
  change (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) ≫
      (ep.inv ≫ eq.hom) =
    (ep.inv ≫ eq.hom) ≫
      (FundamentalGroup.fundamentalGroupMulEquivOfPath q g)
  rw [show FundamentalGroup.fundamentalGroupMulEquivOfPath p g =
    ep.inv ≫ g ≫ ep.hom from rfl]
  rw [show FundamentalGroup.fundamentalGroupMulEquivOfPath q g =
    eq.inv ≫ g ≫ eq.hom from rfl]
  simp only [CategoryTheory.Category.assoc,
    CategoryTheory.Iso.hom_inv_id_assoc]

/-- Mapping a loop and then changing its basepoint along the mapped path is
the same as first changing basepoint and then mapping the loop.  This is the
based fundamental-group form of functoriality of conjugation. -/
theorem fundamentalGroup_map_pathTransport_natural
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ x₁ : X} (f : C(X, Y)) (p : Path x₀ x₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (p.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f x₀) =
      (FundamentalGroup.map f x₁).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom := by
  ext g
  induction g using Quotient.inductionOn with
  | h q =>
    change
      ((FundamentalGroupoid.map f).mapIso
        ((CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦p⟧)).conj
          ((FundamentalGroupoid.map f).map ⟦q⟧) =
        (FundamentalGroupoid.map f).map
          (((CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦p⟧).conj ⟦q⟧)
    exact ((FundamentalGroupoid.map f).map_conj _ _).symm

/-- The fully-faithful preimage supplied by an equivalence agrees with its
inverse functor after rebasing along the equivalence unit and a mapped target
connector.  This isolates the categorical identity used when comparing a
homotopy-equivalence coordinate with a concrete inverse map. -/
theorem equivalence_unit_mapIso_conj_preimage
    {C D : Type*} [Groupoid C] [Groupoid D]
    (E : C ≌ D) (A : C) (B : D) (q : E.functor.obj A ≅ B) (f : End B) :
    ((E.unitIso.app A) ≪≫ E.inverse.mapIso q).conj
        (E.fullyFaithfulFunctor.preimage (q.symm.conj f)) =
      E.inverse.map f := by
  simp [Iso.conj_apply, Equivalence.fullyFaithfulFunctor]
  change ((E.unitIso.app A ≪≫ E.inverse.mapIso q).inv ≫
      (E.unitIso.hom.app A ≫ E.inverse.map q.hom ≫ E.inverse.map f ≫
        E.inverse.map q.inv ≫ E.unitIso.inv.app A) ≫
      (E.unitIso.app A ≪≫ E.inverse.mapIso q).hom) = _
  simp

/-- The frozen Klein bottle is path connected because it is the continuous
surjective image of the convex closed disk under its defining quotient map. -/
noncomputable instance kleinBottlePathConnectedSpace :
    PathConnectedSpace KleinBottle := by
  letI : PathConnectedSpace ConstructionTargets.Surfaces.Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
  exact (ConstructionTargets.Surfaces.surjective_surfaceQuotient false 2).pathConnectedSpace
    (ConstructionTargets.Surfaces.continuous_surfaceQuotient false 2)

/-- The exact polygon quotient used by the van Kampen calculation is path
connected, transported back along its homeomorphism with the frozen model. -/
noncomputable instance kleinPairingSpacePathConnectedSpace :
    PathConnectedSpace kleinPairingData.Space :=
  kleinPairingSpaceHomeomorph.symm.surjective.pathConnectedSpace
    kleinPairingSpaceHomeomorph.symm.continuous

/-- The exact two-circle skeleton occurring in the Klein polygon has the
free-product fundamental group supplied by the generic point-wedge theorem. -/
noncomputable def kleinSkeletonFundamentalGroupEquivCoprod :
    FundamentalGroup TwoCircles twoCirclesPoint ≃*
      Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1) :=
  genericPointWedgeNormalizedFundamentalGroupEquiv
    (1 : Circle) (1 : Circle)
    circleBaseNeighborhood circleBaseNeighborhood
    circleBaseNeighborhood_isOpen circleBaseNeighborhood_isOpen
    circleBase_mem circleBase_mem
    circleBaseNeighborhood_contraction circleBaseNeighborhood_contraction

/-- Relabel the two orbit-indexed circle legs by the standard binary wedge,
preserving `false` as the left leg and `true` as the right leg. -/
noncomputable def finiteWedgeBoolHomeomorphTwoCircles :
    FiniteWedge Bool ≃ₜ TwoCircles where
  toFun := Quotient.lift
    (fun p => match p.1 with
      | false => quotientMap (1 : Circle) (1 : Circle) (.inl p.2)
      | true => quotientMap (1 : Circle) (1 : Circle) (.inr p.2)) fun p q h => by
        change Relation.EqvGen (FiniteWedgeRel Bool) p q at h
        rw [eqvGen_finiteWedgeRel_iff] at h
        rcases h with rfl | ⟨hp, hq⟩
        · rfl
        · cases p with | mk bp zp => cases q with | mk bq zq =>
          have hzp : zp = 1 := Subtype.ext hp
          have hzq : zq = 1 := Subtype.ext hq
          subst zp
          subst zq
          cases bp <;> cases bq
          · rfl
          · simpa [hp, hq] using
              Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
          · simpa [hp, hq] using
              (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm
          · rfl
  invFun := Quotient.lift
    (fun s => match s with
      | .inl z => wedgeCircle false z
      | .inr z => wedgeCircle true z) fun _ _ h => by
        induction h with
        | rel _ _ h => cases h; exact wedgeCircle_base_eq false true
        | refl => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  left_inv := by rintro ⟨⟨b, z⟩⟩; cases b <;> rfl
  right_inv := by rintro ⟨s⟩; cases s <;> rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    rw [continuous_prod_of_discrete_left]
    intro b
    cases b
    · exact (continuous_quotientMap (1 : Circle) (1 : Circle)).comp continuous_inl
    · exact (continuous_quotientMap (1 : Circle) (1 : Circle)).comp continuous_inr
  continuous_invFun := by
    apply Continuous.quotient_lift
    rw [continuous_sum_dom]
    exact ⟨continuous_wedgeCircle false, continuous_wedgeCircle true⟩

/-- Relabel a finite circle wedge along an equivalence of its leg indices. -/
noncomputable def finiteWedgeCongr {L K : Type*} (e : L ≃ K) :
    FiniteWedge L ≃ₜ FiniteWedge K where
  toFun := Quotient.lift (fun p => wedgeCircle (e p.1) p.2) fun p q h => by
    change Relation.EqvGen (FiniteWedgeRel L) p q at h
    rw [eqvGen_finiteWedgeRel_iff] at h
    rcases h with rfl | ⟨hp, hq⟩
    · rfl
    · apply Quotient.sound
      change Relation.EqvGen (FiniteWedgeRel K) (e p.1, p.2) (e q.1, q.2)
      rw [eqvGen_finiteWedgeRel_iff]
      exact Or.inr ⟨hp, hq⟩
  invFun := Quotient.lift (fun p => wedgeCircle (e.symm p.1) p.2) fun p q h => by
    change Relation.EqvGen (FiniteWedgeRel K) p q at h
    rw [eqvGen_finiteWedgeRel_iff] at h
    rcases h with rfl | ⟨hp, hq⟩
    · rfl
    · apply Quotient.sound
      change Relation.EqvGen (FiniteWedgeRel L)
        (e.symm p.1, p.2) (e.symm q.1, q.2)
      rw [eqvGen_finiteWedgeRel_iff]
      exact Or.inr ⟨hp, hq⟩
  left_inv := by
    rintro ⟨⟨l, z⟩⟩
    change wedgeCircle (e.symm (e l)) z = _
    rw [e.symm_apply_apply]
    rfl
  right_inv := by
    rintro ⟨⟨k, z⟩⟩
    change wedgeCircle (e (e.symm k)) z = _
    rw [e.apply_symm_apply]
    rfl
  continuous_toFun := by
    letI : TopologicalSpace L := ⊥
    letI : DiscreteTopology L := ⟨rfl⟩
    apply Continuous.quotient_lift
    rw [continuous_prod_of_discrete_left]
    exact fun l => continuous_wedgeCircle (e l)
  continuous_invFun := by
    letI : TopologicalSpace K := ⊥
    letI : DiscreteTopology K := ⟨rfl⟩
    apply Continuous.quotient_lift
    rw [continuous_prod_of_discrete_left]
    exact fun k => continuous_wedgeCircle (e.symm k)

/-- The actual polygon boundary skeleton, with its orbit labels changed to
the frozen Boolean generators, is the standard two-circle wedge. -/
noncomputable def kleinSkeletonHomeomorphStandardTwoCircles :
    kleinPairingData.skeleton ≃ₜ TwoCircles :=
  kleinSkeletonHomeomorphTwoCircles |>.trans
    (finiteWedgeCongr kleinPairingOrbitEquivBool) |>.trans
      finiteWedgeBoolHomeomorphTwoCircles

/-- The polygon-side basepoint corresponding to the common point of the two
standard circle legs. -/
noncomputable def kleinSkeletonPoint : kleinPairingData.skeleton :=
  kleinSkeletonHomeomorphStandardTwoCircles.symm twoCirclesPoint

/-- The free-product computation transported to the actual boundary skeleton
and its polygon-side basepoint. -/
noncomputable def kleinActualSkeletonFundamentalGroupEquivCoprod :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint ≃*
      Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1) :=
  let e := kleinSkeletonHomeomorphStandardTwoCircles
  let htarget : FundamentalGroup TwoCircles (e kleinSkeletonPoint) ≃*
      Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1) := by
    have hp : e kleinSkeletonPoint = twoCirclesPoint := by
      simp [e, kleinSkeletonPoint]
    rw [hp]
    exact kleinSkeletonFundamentalGroupEquivCoprod
  (fundamentalGroupEquivOfHomeomorph e kleinSkeletonPoint).trans htarget

/-- The two rank-one generator types, ordered left then right, are the frozen
Boolean generator type. -/
def finOneSumEquivBool : Fin 1 ⊕ Fin 1 ≃ Bool :=
  finSumFinEquiv.trans finTwoEquiv

/-- The circle-group coproduct in the skeleton computation, expressed as the
literal free group on the frozen Boolean generators. -/
noncomputable def circleFundamentalGroupCoprodEquivFreeGroupBool :
    Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1) ≃*
      FreeGroup Bool :=
  (MulEquiv.coprodCongr
      (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
        multiplicativeIntEquivFreeGroupFinOne)
      (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
        multiplicativeIntEquivFreeGroupFinOne)).trans
    ((coprodFreeGroupEquivFreeGroupSum (Fin 1) (Fin 1)).trans
      (MulEquiv.ofBijective (FreeGroup.map finOneSumEquivBool)
        ⟨FreeGroup.map_injective finOneSumEquivBool.injective,
          FreeGroup.map_surjective finOneSumEquivBool.surjective⟩))

/-- The actual polygon skeleton fundamental group in the exact free-group
coordinates in which the attaching word is `aabb`. -/
noncomputable def kleinActualSkeletonFundamentalGroupEquivFreeGroupBool :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint ≃*
      FreeGroup Bool :=
  kleinActualSkeletonFundamentalGroupEquivCoprod.trans
    circleFundamentalGroupCoprodEquivFreeGroupBool

/-- The literal attaching word read from the four polygon arcs. -/
def kleinAabbWord : FreeGroup Bool :=
  FreeGroup.of false * FreeGroup.of false *
    FreeGroup.of true * FreeGroup.of true

/-- The attaching class in the fundamental group of the actual polygon
skeleton, expressed by pulling `aabb` back through its free-group coordinates. -/
noncomputable def kleinSkeletonAttachingClass :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint :=
  kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.symm kleinAabbWord

/-- The algebraic quotient map that imposes the polygon attaching relation on
the actual skeleton fundamental group. -/
noncomputable def kleinSkeletonPresentationMap :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint →*
      KleinPolygonPresentedGroup :=
  (PresentedGroup.mk kleinPolygonRelations).comp
    kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom

theorem kleinSkeletonPresentationMap_surjective :
    Function.Surjective kleinSkeletonPresentationMap :=
  (PresentedGroup.mk_surjective kleinPolygonRelations).comp
    kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.surjective

/-- The exact `aabb` attaching class is killed by the presentation map. -/
@[simp] theorem kleinSkeletonPresentationMap_attachingClass :
    kleinSkeletonPresentationMap kleinSkeletonAttachingClass = 1 := by
  rw [kleinSkeletonPresentationMap, kleinSkeletonAttachingClass,
    MonoidHom.comp_apply]
  change PresentedGroup.mk kleinPolygonRelations
    (kleinActualSkeletonFundamentalGroupEquivFreeGroupBool
      (kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.symm kleinAabbWord)) = 1
  rw [MulEquiv.apply_symm_apply]
  exact PresentedGroup.one_of_mem (Set.mem_singleton kleinAabbWord)

/-- Its kernel is exactly the pullback of the normal closure of `aabb`; this
is the algebraic target of the remaining attaching-cell van Kampen theorem. -/
theorem kleinSkeletonPresentationMap_ker :
    MonoidHom.ker kleinSkeletonPresentationMap =
      Subgroup.comap
        kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom
        (Subgroup.normalClosure kleinPolygonRelations) := by
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_comap,
    kleinSkeletonPresentationMap, MonoidHom.coe_comp, Function.comp_apply,
    PresentedGroup.mk_eq_one_iff]

/-- The algebraic quotient demanded by based van Kampen is already the
frozen `aabb` presentation.  Thus the remaining topological extraction only
has to identify its kernel with this pulled-back normal closure. -/
noncomputable def kleinSkeletonAabbQuotientEquiv :
    (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint ⧸
      Subgroup.comap
        kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom
        (Subgroup.normalClosure kleinPolygonRelations)) ≃*
      KleinPolygonPresentedGroup :=
  (QuotientGroup.quotientMulEquivOfEq
      kleinSkeletonPresentationMap_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      kleinSkeletonPresentationMap kleinSkeletonPresentationMap_surjective)

/-- The generic two-open van Kampen mapping equivalence specialized to the
exact radial cover of the Klein polygon quotient.  This is the topological
input from which the remaining based normal-closure quotient is extracted. -/
noncomputable def kleinPolygonFundamentalGroupoidPseudopushout
    (C : Type*) [CategoryTheory.Category C] :
    (FundamentalGroupoid kleinPairingData.Space ⥤ C) ≌
      @PseudoFunctorCocone kleinPairingData.Space _
        (openCover kleinPairingData).inner
        (openCover kleinPairingData).outer C _ :=
  twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (openCover kleinPairingData).inner_open
    (openCover kleinPairingData).outer_open
    (openCover kleinPairingData).cover

/-- Reconstruct the identity functor of the polygon fundamental groupoid from
its two restricted cover-piece functors through the proved pseudopushout. -/
noncomputable def kleinPolygonPseudopushoutReconstructedIdentity :
    FundamentalGroupoid kleinPairingData.Space ⥤
      FundamentalGroupoid kleinPairingData.Space :=
  (kleinPolygonFundamentalGroupoidPseudopushout
    (FundamentalGroupoid kleinPairingData.Space)).inverse.obj
      ((kleinPolygonFundamentalGroupoidPseudopushout
        (FundamentalGroupoid kleinPairingData.Space)).functor.obj
          (𝟭 (FundamentalGroupoid kleinPairingData.Space)))

/-- The pseudopushout unit compares the literal identity functor with its
cover-piece reconstruction. -/
noncomputable def kleinPolygonPseudopushoutReconstructionUnit :
    (𝟭 (FundamentalGroupoid kleinPairingData.Space)) ≅
      kleinPolygonPseudopushoutReconstructedIdentity :=
  (kleinPolygonFundamentalGroupoidPseudopushout
    (FundamentalGroupoid kleinPairingData.Space)).unitIso.app _

/-- Every polygon-groupoid arrow is the reconstructed cover-piece arrow,
conjugated by the pseudopushout unit components.  This is the first direct
based extraction from the mapping-category pseudopushout. -/
theorem kleinPolygonPseudopushout_arrow_eq_reconstructed
    {x y : FundamentalGroupoid kleinPairingData.Space} (g : x ⟶ y) :
    g = kleinPolygonPseudopushoutReconstructionUnit.hom.app x ≫
      kleinPolygonPseudopushoutReconstructedIdentity.map g ≫
      kleinPolygonPseudopushoutReconstructionUnit.inv.app y := by
  rw [← Category.assoc,
    ← kleinPolygonPseudopushoutReconstructionUnit.hom.naturality g]
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- At every change of sides in a subordinate two-open subdivision, the
shared vertex lies in the overlap.  These are the exact vertices at which
inner-piece factors can be replaced during based van Kampen normalization. -/
theorem pathTwoOpenSubdivision_transition_mem_overlap
    {X : Type*} [TopologicalSpace X] {x y : X} {p : Path x y}
    {U V : Set X} (S : PathTwoOpenSubdivision p U V)
    (k : Fin S.n) (hside : S.side k.castSucc ≠ S.side k.succ) :
    S.point k.succ.castSucc ∈ U ∩ V := by
  have h₀ := S.piece_mem k.castSucc (1 : unitInterval)
  have h₁ := S.piece_mem k.succ (0 : unitInterval)
  have hp₀ : S.piece k.castSucc (1 : unitInterval) =
      S.point k.succ.castSucc := by
    calc
      _ = S.point k.castSucc.succ := (S.piece k.castSucc).target
      _ = _ := by congr 1
  have hp₁ : S.piece k.succ (0 : unitInterval) =
      S.point k.succ.castSucc := by
    exact (S.piece k.succ).source
  rw [hp₀] at h₀
  rw [hp₁] at h₁
  cases hs₀ : S.side k.castSucc <;> cases hs₁ : S.side k.succ
  · exact False.elim (hside (by simp [hs₀, hs₁]))
  · exact ⟨by simpa [twoChart, hs₁] using h₁,
      by simpa [twoChart, hs₀] using h₀⟩
  · exact ⟨by simpa [twoChart, hs₀] using h₀,
      by simpa [twoChart, hs₁] using h₁⟩
  · exact False.elim (hside (by simp [hs₀, hs₁]))

/-- Partition a finite Boolean side assignment into its ordered maximal
constant runs.  Flattening recovers every original index; blocks are nonempty
and constant-sided, while adjacent block boundaries change side. -/
def boolSideRunPartition {n : ℕ} (side : Fin n → Bool) :
    List (List (Fin n)) :=
  (List.finRange n).splitBy (fun i j => side i == side j)

theorem boolSideRunPartition_spec {n : ℕ} (side : Fin n → Bool) :
    List.finRange n = (boolSideRunPartition side).flatten ∧
      [] ∉ boolSideRunPartition side ∧
      (∀ block ∈ boolSideRunPartition side,
        block.IsChain fun i j => side i == side j) ∧
      (boolSideRunPartition side).IsChain fun a b =>
        ∃ ha hb, (side (a.getLast ha) == side (b.head hb)) = false := by
  exact List.splitBy_eq_iff.mp rfl

/-- Equality of the homotopy class of every factor propagates through the
dependent finite concatenation used by a subordinate subdivision.  This is
the finite-fold assembly step for replacing all maximal inner runs. -/
theorem pathHomotopicQuotient_concat_eq_of_pieceClass_eq
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (point : Fin (n + 1) → X)
    (F G : (k : Fin n) → Path (point k.castSucc) (point k.succ))
    (h : ∀ k, (⟦F k⟧ : Path.Homotopic.Quotient _ _) = ⟦G k⟧) :
    (⟦Path.concat point F⟧ : Path.Homotopic.Quotient _ _) =
      ⟦Path.concat point G⟧ := by
  apply Quotient.sound
  exact Path.Homotopic.concat_hcomp point F G
    (fun k => Quotient.eq.mp (h k))

/-- A nonempty dependent finite concatenation stays in a set whenever each
of its factors does.  This supplies the range proof for every maximal inner
block extracted from a subordinate subdivision. -/
theorem path_concat_mem_of_piece_mem
    {X : Type*} [TopologicalSpace X] {U : Set X} {n : ℕ}
    (point : Fin (n + 2) → X)
    (F : (k : Fin (n + 1)) → Path (point k.castSucc) (point k.succ))
    (hF : ∀ k t, F k t ∈ U) :
    ∀ t, Path.concat point F t ∈ U := by
  induction n with
  | zero =>
      intro t
      rw [Path.concat_succ]
      rw [Path.concat_zero]
      have ht : ((Path.concat (point ∘ Fin.castSucc)
          (fun k => F k.castSucc)).trans (F (Fin.last 0))) t ∈
          Set.range ((Path.concat (point ∘ Fin.castSucc)
            (fun k => F k.castSucc)).trans (F (Fin.last 0))) :=
        Set.mem_range_self t
      rw [Path.concat_zero] at ht
      rw [Path.trans_range] at ht
      rcases ht with ht | ht
      · rcases ht with ⟨s, hs⟩
        have hm : (Path.refl ((point ∘ Fin.castSucc) 0)) s ∈ U := by
          change point 0 ∈ U
          convert hF 0 0 using 1
          rw [(F 0).source]
          congr 1
        exact hs ▸ hm
      · rcases ht with ⟨s, hs⟩
        have hm : (F (Fin.last 0)) s ∈ U := hF _ s
        exact hs ▸ hm
  | succ n ih =>
      intro t
      rw [Path.concat_succ]
      change ((Path.concat (point ∘ Fin.castSucc)
        (fun k => F k.castSucc)).trans (F (Fin.last (n + 1)))) t ∈ U
      have ht : ((Path.concat (point ∘ Fin.castSucc)
          (fun k => F k.castSucc)).trans (F (Fin.last (n + 1)))) t ∈
          Set.range ((Path.concat (point ∘ Fin.castSucc)
            (fun k => F k.castSucc)).trans (F (Fin.last (n + 1)))) :=
        Set.mem_range_self t
      rw [Path.trans_range] at ht
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact hs ▸ ih (point ∘ Fin.castSucc) (fun k => F k.castSucc)
          (fun k u => hF k.castSucc u) s
      · exact hs ▸ hF (Fin.last (n + 1)) s

/-- A pointwise replacement of the pieces of a subordinate subdivision
reconstructs the class of its original path.  This combines the subdivision's
endpoint casts with the generic dependent finite-fold lemma. -/
theorem pathTwoOpenSubdivision_quotient_eq_concat_of_pieceClass_eq
    {X : Type*} [TopologicalSpace X]
    {x y : X} {p : Path x y} {U V : Set X}
    (S : PathTwoOpenSubdivision p U V)
    (G : (k : Fin (S.n + 1)) →
      Path (S.point k.castSucc) (S.point k.succ))
    (h : ∀ k, (⟦S.piece k⟧ : Path.Homotopic.Quotient _ _) = ⟦G k⟧) :
    (⟦p.cast S.point_zero S.point_last⟧ : Path.Homotopic.Quotient _ _) =
      ⟦Path.concat S.point G⟧ := by
  calc
    _ = ⟦Path.concat S.point S.piece⟧ := S.quotient_concat_eq.symm
    _ = _ := pathHomotopicQuotient_concat_eq_of_pieceClass_eq
      S.point S.piece G h

/-- The inner vertex of the exact radial cover is contractible, using the
pointed contraction carried by the polygon cover package. -/
theorem kleinPolygonInnerContractibleSpace :
    ContractibleSpace
      {q // q ∈ (openCover kleinPairingData).inner} := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨(openCover kleinPairingData).center,
    ⟨(openCover kleinPairingData).contraction.homotopy⟩⟩

/-- Hence the based fundamental group contributed by the inner cover piece
is trivial in the exact cover used for the Klein polygon. -/
theorem kleinPolygonInnerFundamentalGroup_subsingleton :
    Subsingleton
      (FundamentalGroup {q // q ∈ (openCover kleinPairingData).inner}
        (openCover kleinPairingData).center) := by
  letI : ContractibleSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    kleinPolygonInnerContractibleSpace
  letI : SimplyConnectedSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    SimplyConnectedSpace.ofContractible _
  change Subsingleton (Path.Homotopic.Quotient
    (openCover kleinPairingData).center (openCover kleinPairingData).center)
  infer_instance

/-- Contractibility of the inner piece controls paths between arbitrary
endpoints, not only loops at the chosen center. Thus every inner run with
fixed overlap endpoints has a unique fundamental-groupoid class. -/
theorem kleinPolygonInnerFundamentalGroupoid_hom_subsingleton
    (x y : {q // q ∈ (openCover kleinPairingData).inner}) :
    Subsingleton (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) := by
  letI : ContractibleSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    kleinPolygonInnerContractibleSpace
  letI : SimplyConnectedSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    SimplyConnectedSpace.ofContractible _
  change Subsingleton (Path.Homotopic.Quotient x y)
  infer_instance

/-- Two paths through the inner piece with the same endpoints represent the
same arrow. This replaces maximal inner runs whose boundary vertices lie in
the overlap. -/
theorem kleinPolygonInner_pathClass_eq
    {x y : {q // q ∈ (openCover kleinPairingData).inner}}
    (p q : Path x y) :
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) = ⟦q⟧ := by
  letI : ContractibleSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    kleinPolygonInnerContractibleSpace
  letI : SimplyConnectedSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    SimplyConnectedSpace.ofContractible _
  exact Quotient.sound (SimplyConnectedSpace.paths_homotopic p q)

/-- The annular overlap in the exact radial cover is path connected. -/
theorem kleinPolygonOverlapPathConnectedSpace :
    PathConnectedSpace (overlapOpen kleinPairingData.Rel) := by
  letI : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo 0 1).isPathConnected ⟨1 / 2, by norm_num⟩)
  letI : PathConnectedSpace (Set.Ioo (0 : ℝ) 1 × Circle) :=
    ⟨⟨(⟨1 / 2, by norm_num⟩, 1)⟩, fun x y ↦
      ⟨(PathConnectedSpace.joined x.1 y.1).some.prod
        (PathConnectedSpace.joined x.2 y.2).some⟩⟩
  exact (openCover kleinPairingData).overlap_homeomorph.symm.surjective.pathConnectedSpace
    (openCover kleinPairingData).overlap_homeomorph.symm.continuous

/-- A concrete basepoint of the annular overlap. -/
noncomputable def kleinPolygonOverlapPoint : overlapOpen kleinPairingData.Rel :=
  (openCover kleinPairingData).overlap_homeomorph.symm
    (⟨1 / 2, by norm_num⟩, (1 : Circle))

/-- The based overlap-to-outer-piece map used by the remaining quotient calculation. -/
noncomputable def kleinPolygonOverlapToOuter :
    C(overlapOpen kleinPairingData.Rel,
      {q // q ∈ (openCover kleinPairingData).outer}) :=
  ⟨fun z ↦ ⟨z.1, (by
      have hz : z.1 ∈ (openCover kleinPairingData).inner ∩
          (openCover kleinPairingData).outer := by
        rw [← (openCover kleinPairingData).overlap_eq]
        exact z.2
      exact hz.2)⟩,
    Continuous.subtype_mk continuous_subtype_val (fun z ↦ by
      have hz : z.1 ∈ (openCover kleinPairingData).inner ∩
          (openCover kleinPairingData).outer := by
        rw [← (openCover kleinPairingData).overlap_eq]
        exact z.2
      exact hz.2)⟩

noncomputable def kleinPolygonOverlapToOuterPiOne :
    FundamentalGroup (overlapOpen kleinPairingData.Rel) kleinPolygonOverlapPoint →*
      FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) :=
  FundamentalGroup.map kleinPolygonOverlapToOuter kleinPolygonOverlapPoint

/-- The same overlap inclusion, regarded as a map into the contractible inner
piece of the radial cover. -/
noncomputable def kleinPolygonOverlapToInner :
    C(overlapOpen kleinPairingData.Rel,
      {q // q ∈ (openCover kleinPairingData).inner}) :=
  ⟨fun z ↦ ⟨z.1, (by
      have hz : z.1 ∈ (openCover kleinPairingData).inner ∩
          (openCover kleinPairingData).outer := by
        rw [← (openCover kleinPairingData).overlap_eq]
        exact z.2
      exact hz.1)⟩,
    Continuous.subtype_mk continuous_subtype_val (fun z ↦ by
      have hz : z.1 ∈ (openCover kleinPairingData).inner ∩
          (openCover kleinPairingData).outer := by
        rw [← (openCover kleinPairingData).overlap_eq]
        exact z.2
      exact hz.1)⟩

/-- Inclusion of the inner radial piece into the polygon quotient. -/
noncomputable def kleinPolygonInnerToSpace :
    C({q // q ∈ (openCover kleinPairingData).inner}, kleinPairingData.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Any path through the contractible inner piece whose endpoints come from
the overlap can be replaced, in the fundamental groupoid, by the inner image
of an actual overlap path.  This is the concrete replacement used on each
maximal inner run of a subordinate subdivision. -/
theorem kleinPolygonInner_pathClass_eq_overlapReplacement
    (x y : overlapOpen kleinPairingData.Rel)
    (p : Path (kleinPolygonOverlapToInner x)
      (kleinPolygonOverlapToInner y)) :
    ∃ q : Path x y,
      (⟦p⟧ : FundamentalGroupoid.mk (kleinPolygonOverlapToInner x) ⟶
          FundamentalGroupoid.mk (kleinPolygonOverlapToInner y)) =
        ⟦q.map kleinPolygonOverlapToInner.continuous⟧ := by
  letI : PathConnectedSpace (overlapOpen kleinPairingData.Rel) :=
    kleinPolygonOverlapPathConnectedSpace
  let q : Path x y := PathConnectedSpace.somePath x y
  exact ⟨q, kleinPolygonInner_pathClass_eq p
    (q.map kleinPolygonOverlapToInner.continuous)⟩

/-- Inclusion of the outer radial piece into the polygon quotient. -/
noncomputable def kleinPolygonOuterToSpace :
    C({q // q ∈ (openCover kleinPairingData).outer}, kleinPairingData.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- After inclusion into the polygon quotient, an inner run between overlap
vertices is equal to an overlap replacement routed through the outer piece.
This is the factorwise equality needed to normalize a reconstructed finite
word to outer-piece arrows. -/
theorem kleinPolygonInner_ambientPathClass_eq_outerOverlapReplacement
    (x y : overlapOpen kleinPairingData.Rel)
    (p : Path (kleinPolygonOverlapToInner x)
      (kleinPolygonOverlapToInner y)) :
    ∃ q : Path x y,
      (⟦p.map kleinPolygonInnerToSpace.continuous⟧ :
          FundamentalGroupoid.mk x.1 ⟶ FundamentalGroupoid.mk y.1) =
        ⟦(q.map kleinPolygonOverlapToOuter.continuous).map
          kleinPolygonOuterToSpace.continuous⟧ := by
  obtain ⟨q, hq⟩ :=
    kleinPolygonInner_pathClass_eq_overlapReplacement x y p
  refine ⟨q, ?_⟩
  have hmap := congrArg
    (fun z : FundamentalGroupoid.mk (kleinPolygonOverlapToInner x) ⟶
        FundamentalGroupoid.mk (kleinPolygonOverlapToInner y) =>
      (FundamentalGroupoid.map kleinPolygonInnerToSpace).map z)
    hq
  simpa [kleinPolygonInnerToSpace, kleinPolygonOverlapToInner,
    kleinPolygonOuterToSpace, kleinPolygonOverlapToOuter] using hmap

/-- An ambient path forming an inner run can be normalized directly from
membership data: if both endpoints lie in the overlap, its ambient class is
represented by an actual overlap path routed through the outer piece. -/
theorem kleinPolygonInnerRun_exists_outerOverlapReplacement
    {x y : kleinPairingData.Space}
    (hx : x ∈ (openCover kleinPairingData).inner ∩
      (openCover kleinPairingData).outer)
    (hy : y ∈ (openCover kleinPairingData).inner ∩
      (openCover kleinPairingData).outer)
    (p : Path x y)
    (hp : ∀ t, p t ∈ (openCover kleinPairingData).inner) :
    ∃ q : Path
        (⟨x, by rw [(openCover kleinPairingData).overlap_eq]; exact hx⟩ :
          overlapOpen kleinPairingData.Rel)
        (⟨y, by rw [(openCover kleinPairingData).overlap_eq]; exact hy⟩ :
          overlapOpen kleinPairingData.Rel),
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
        ⟦(q.map kleinPolygonOverlapToOuter.continuous).map
          kleinPolygonOuterToSpace.continuous⟧ := by
  let xo : overlapOpen kleinPairingData.Rel := ⟨x, by
    rw [(openCover kleinPairingData).overlap_eq]
    exact hx⟩
  let yo : overlapOpen kleinPairingData.Rel := ⟨y, by
    rw [(openCover kleinPairingData).overlap_eq]
    exact hy⟩
  let pInner : Path (kleinPolygonOverlapToInner xo)
      (kleinPolygonOverlapToInner yo) :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  obtain ⟨q, hq⟩ :=
    kleinPolygonInner_ambientPathClass_eq_outerOverlapReplacement xo yo pInner
  refine ⟨q, ?_⟩
  simpa [pInner, kleinPolygonInnerToSpace, kleinPolygonOuterToSpace] using hq

/-- A whole nonempty inner block, presented as a dependent finite family of
paths, has one overlap replacement routed through the outer piece.  Thus the
remaining normalization only has to partition the subdivision side indices. -/
theorem kleinPolygonInnerBlock_exists_outerOverlapReplacement
    {n : ℕ}
    (point : Fin (n + 2) → kleinPairingData.Space)
    (F : (k : Fin (n + 1)) → Path (point k.castSucc) (point k.succ))
    (hx : point 0 ∈ (openCover kleinPairingData).inner ∩
      (openCover kleinPairingData).outer)
    (hy : point (Fin.last (n + 1)) ∈
      (openCover kleinPairingData).inner ∩
      (openCover kleinPairingData).outer)
    (hF : ∀ k t, F k t ∈ (openCover kleinPairingData).inner) :
    ∃ q : Path
        (⟨point 0, by rw [(openCover kleinPairingData).overlap_eq]; exact hx⟩ :
          overlapOpen kleinPairingData.Rel)
        (⟨point (Fin.last (n + 1)), by
          rw [(openCover kleinPairingData).overlap_eq]; exact hy⟩ :
          overlapOpen kleinPairingData.Rel),
      (⟦Path.concat point F⟧ : FundamentalGroupoid.mk (point 0) ⟶
          FundamentalGroupoid.mk (point (Fin.last (n + 1)))) =
        ⟦(q.map kleinPolygonOverlapToOuter.continuous).map
          kleinPolygonOuterToSpace.continuous⟧ := by
  exact kleinPolygonInnerRun_exists_outerOverlapReplacement hx hy
    (Path.concat point F) (path_concat_mem_of_piece_mem point F hF)

/-- Every overlap loop maps trivially in the polygon quotient.  This is the
kernel inclusion in based van Kampen: the overlap inclusion factors through
the contractible inner radial piece. -/
theorem kleinPolygonOverlapToSpacePiOne_eq_one
    (g : FundamentalGroup (overlapOpen kleinPairingData.Rel)
      kleinPolygonOverlapPoint) :
    FundamentalGroup.map
        (kleinPolygonOuterToSpace.comp kleinPolygonOverlapToOuter)
        kleinPolygonOverlapPoint g = 1 := by
  letI : ContractibleSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    kleinPolygonInnerContractibleSpace
  letI : SimplyConnectedSpace
      {q // q ∈ (openCover kleinPairingData).inner} :=
    SimplyConnectedSpace.ofContractible _
  letI : Subsingleton (FundamentalGroup
      {q // q ∈ (openCover kleinPairingData).inner}
      (kleinPolygonOverlapToInner kleinPolygonOverlapPoint)) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have hinner : FundamentalGroup.map kleinPolygonOverlapToInner
      kleinPolygonOverlapPoint g = 1 := by
    apply Subsingleton.elim
  have hnat :
      FundamentalGroup.map
          (kleinPolygonInnerToSpace.comp kleinPolygonOverlapToInner)
          kleinPolygonOverlapPoint g =
        FundamentalGroup.map kleinPolygonInnerToSpace
          (kleinPolygonOverlapToInner kleinPolygonOverlapPoint)
          (FundamentalGroup.map kleinPolygonOverlapToInner
            kleinPolygonOverlapPoint g) := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  rw [show (kleinPolygonOuterToSpace.comp kleinPolygonOverlapToOuter) =
      (kleinPolygonInnerToSpace.comp kleinPolygonOverlapToInner) by rfl]
  rw [hnat, hinner, map_one]
  rfl

/-- The based fundamental-group map from the outer radial piece into the
polygon quotient, at the chosen overlap image. -/
noncomputable def kleinPolygonOuterToSpacePiOne :
    FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) →*
      FundamentalGroup kleinPairingData.Space
        (kleinPolygonOuterToSpace
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) :=
  FundamentalGroup.map kleinPolygonOuterToSpace
    (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)

/-- The normal closure of the actual overlap image lies in the kernel of the
outer-piece inclusion.  This promotes the pointwise nullity through the
normal subgroup closure, giving the forward half of the based van Kampen
kernel equality before transport from the outer piece to the skeleton. -/
theorem kleinPolygonOverlapNormalClosure_le_outerToSpacePiOne_ker :
    Subgroup.normalClosure
        (kleinPolygonOverlapToOuterPiOne.range : Set
          (FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
            (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint))) ≤
      MonoidHom.ker kleinPolygonOuterToSpacePiOne := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨g, rfl⟩
  change kleinPolygonOuterToSpacePiOne
      (kleinPolygonOverlapToOuterPiOne g) = 1
  have hnat :
      kleinPolygonOuterToSpacePiOne
          (kleinPolygonOverlapToOuterPiOne g) =
        FundamentalGroup.map
          (kleinPolygonOuterToSpace.comp kleinPolygonOverlapToOuter)
          kleinPolygonOverlapPoint g := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  rw [hnat]
  exact kleinPolygonOverlapToSpacePiOne_eq_one g

/-- Winding number coordinates for the exact annular overlap.  The interval
factor is contractible, so only the circle coordinate contributes. -/
noncomputable def kleinPolygonOverlapFundamentalGroupEquivInt :
    FundamentalGroup (overlapOpen kleinPairingData.Rel) kleinPolygonOverlapPoint ≃*
      Multiplicative ℤ := by
  let I := Set.Ioo (0 : ℝ) 1
  let i : I := ⟨1 / 2, by change (0 : ℝ) < 1 / 2 ∧ 1 / 2 < 1; norm_num⟩
  letI : ContractibleSpace I := (convex_Ioo 0 1).contractibleSpace
    ⟨1 / 2, by change (0 : ℝ) < 1 / 2 ∧ 1 / 2 < 1; norm_num⟩
  letI : SimplyConnectedSpace I := SimplyConnectedSpace.ofContractible _
  letI : Subsingleton (FundamentalGroup I i) := by
    change Subsingleton (Path.Homotopic.Quotient i i)
    infer_instance
  letI : Unique (FundamentalGroup I i) :=
    { default := 1, uniq := fun x ↦ Subsingleton.elim x 1 }
  let e :=
    ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
        (openCover kleinPairingData).overlap_homeomorph kleinPolygonOverlapPoint
  have hp : (openCover kleinPairingData).overlap_homeomorph
      kleinPolygonOverlapPoint = (i, (1 : Circle)) := by
    simpa [i, kleinPolygonOverlapPoint] using
      (openCover kleinPairingData).overlap_homeomorph.apply_symm_apply
        (⟨(1 / 2 : ℝ), by norm_num⟩, (1 : Circle))
  rw [hp] at e
  exact e.trans
    ((ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv
      i (1 : Circle)).trans
        (MulEquiv.uniqueProd.trans
          ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt))

/-- The exact outer cover piece deformation retracts onto the actual polygon
skeleton, before any choice of free-group coordinates. -/
noncomputable def kleinPolygonOuterHomotopyEquivSkeleton :
    ContinuousMap.HomotopyEquiv
      (OuterPiece kleinPairingData) kleinPairingData.skeleton :=
  (outerHomotopyEquivBoundary kleinPairingData).trans
    (outerBoundaryHomeomorphSkeleton kleinPairingData).toHomotopyEquiv

/-- On an actual skeleton point the preceding equivalence is literally the
identity after forgetting the redundant outer-membership proof. -/
theorem kleinPolygonOuterHomotopyEquivSkeleton_on_skeleton
    (z : kleinPairingData.skeleton) :
    kleinPolygonOuterHomotopyEquivSkeleton
      (skeletonToOuter kleinPairingData z) = z := by
  change (outerBoundaryHomeomorphSkeleton kleinPairingData)
    ((outerHomotopyEquivBoundary kleinPairingData)
      (skeletonToOuter kleinPairingData z)) = z
  apply Subtype.ext
  exact congrArg (fun w : OuterPiece kleinPairingData ↦ w.1)
    ((punctureDeformationRetract kleinPairingData).fixed 1
      (skeletonToOuter kleinPairingData z)
      ((mem_outerBoundarySkeleton_iff kleinPairingData
        (skeletonToOuter kleinPairingData z)).mpr z.2))

/-- The preceding deformation equivalence at the fundamental-groupoid level;
this retains all basepoints while the winding generator is transported. -/
noncomputable def kleinPolygonOuterFundamentalGroupoidEquivalence :
    FundamentalGroupoid (OuterPiece kleinPairingData) ≌
      FundamentalGroupoid kleinPairingData.skeleton :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    kleinPolygonOuterHomotopyEquivSkeleton

/-- On embedded skeleton objects, the groupoid equivalence has the literal
skeleton object as its target. -/
theorem kleinPolygonOuterFundamentalGroupoidEquivalence_obj_skeleton
    (z : kleinPairingData.skeleton) :
    kleinPolygonOuterFundamentalGroupoidEquivalence.functor.obj
        (FundamentalGroupoid.mk (skeletonToOuter kleinPairingData z)) =
      FundamentalGroupoid.mk z := by
  change FundamentalGroupoid.mk (kleinPolygonOuterHomotopyEquivSkeleton
    (skeletonToOuter kleinPairingData z)) = FundamentalGroupoid.mk z
  rw [kleinPolygonOuterHomotopyEquivSkeleton_on_skeleton]

/-- Restriction of the outer groupoid equivalence to the automorphism group
at any literal outer-piece basepoint. -/
noncomputable def kleinPolygonOuterFundamentalGroupEquivSkeleton
    (x : OuterPiece kleinPairingData) :
    FundamentalGroup (OuterPiece kleinPairingData) x ≃*
      FundamentalGroup kleinPairingData.skeleton
        (kleinPolygonOuterHomotopyEquivSkeleton x) := by
  let e := kleinPolygonOuterFundamentalGroupoidEquivalence
  let h := e.fullyFaithfulFunctor
  let m := FundamentalGroup.map
    kleinPolygonOuterHomotopyEquivSkeleton.toFun x
  exact
    { toFun := m
      invFun := fun g ↦ h.preimage g
      left_inv := fun g ↦ h.preimage_map g
      right_inv := fun g ↦ h.map_preimage g
      map_mul' := m.map_mul }

/-- The based restriction at the actual image of the chosen overlap point. -/
noncomputable def kleinPolygonOverlapImageFundamentalGroupEquivSkeleton :
    FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ≃*
      FundamentalGroup kleinPairingData.skeleton
        (kleinPolygonOuterHomotopyEquivSkeleton
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) :=
  kleinPolygonOuterFundamentalGroupEquivSkeleton _

/-- The actual polygon skeleton is path connected, transported from the
standard two-circle wedge along the already fixed homeomorphism. -/
theorem kleinSkeletonPathConnectedSpace :
    PathConnectedSpace kleinPairingData.skeleton :=
  kleinSkeletonHomeomorphStandardTwoCircles.symm.surjective.pathConnectedSpace
    kleinSkeletonHomeomorphStandardTwoCircles.symm.continuous

/-- A chosen path from the deformed overlap image to the preferred skeleton
basepoint used by the literal free-group coordinates. -/
noncomputable def kleinPolygonOverlapImageToSkeletonPointPath :
    Path
      (kleinPolygonOuterHomotopyEquivSkeleton
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint))
      kleinSkeletonPoint := by
  letI : PathConnectedSpace kleinPairingData.skeleton :=
    kleinSkeletonPathConnectedSpace
  exact PathConnectedSpace.somePath _ _

/-- The overlap-image fundamental group transported all the way to the
preferred skeleton basepoint.  The final winding calculation can therefore
be stated directly in the fixed `FreeGroup Bool` coordinates. -/
noncomputable def kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint :
    FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ≃*
      FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint :=
  kleinPolygonOverlapImageFundamentalGroupEquivSkeleton.trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      kleinPolygonOverlapImageToSkeletonPointPath)

/-- The positive overlap generator after entering and deforming the outer
piece, but before making any path choice to the preferred skeleton basepoint. -/
noncomputable def kleinPolygonUntransportedWindingOne :
    FundamentalGroup kleinPairingData.skeleton
      (kleinPolygonOuterHomotopyEquivSkeleton
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) :=
  kleinPolygonOverlapImageFundamentalGroupEquivSkeleton
    (kleinPolygonOverlapToOuterPiOne
      (kleinPolygonOverlapFundamentalGroupEquivInt.symm
        (Multiplicative.ofAdd (1 : ℤ))))

/-- A connector chosen in the standard two-circle model and pulled back to
the actual polygon skeleton.  This moves the remaining calculation entirely
into the coordinates in which the two free generators were defined. -/
noncomputable def kleinPolygonStandardModelConnector :
    Path
      (kleinPolygonOuterHomotopyEquivSkeleton
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint))
      kleinSkeletonPoint := by
  let z := kleinPolygonOuterHomotopyEquivSkeleton
    (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)
  let q : Path (kleinSkeletonHomeomorphStandardTwoCircles z) twoCirclesPoint := by
    letI : PathConnectedSpace TwoCircles := inferInstance
    exact PathConnectedSpace.somePath _ _
  exact (q.map kleinSkeletonHomeomorphStandardTwoCircles.symm.continuous).cast
    (kleinSkeletonHomeomorphStandardTwoCircles.symm_apply_apply z).symm rfl

/-- The overlap inclusion expressed directly in the fixed free-group
coordinates on the actual polygon skeleton. -/
noncomputable def kleinPolygonOverlapToSkeletonFreeGroup :
    FundamentalGroup (overlapOpen kleinPairingData.Rel)
        kleinPolygonOverlapPoint →* FreeGroup Bool :=
  kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom.comp
    (kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.toMonoidHom.comp
      kleinPolygonOverlapToOuterPiOne)

/-- The same overlap inclusion before applying the fixed free-group
coordinates on the skeleton. -/
noncomputable def kleinPolygonOverlapToSkeletonPiOne :
    FundamentalGroup (overlapOpen kleinPairingData.Rel)
        kleinPolygonOverlapPoint →*
      FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint :=
  kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.toMonoidHom.comp
    kleinPolygonOverlapToOuterPiOne

/-- The outer-to-polygon map expressed on the preferred skeleton group by
precomposing with the inverse of the already fixed outer-to-skeleton
basepoint equivalence.  Its target basepoint is deliberately still the
original overlap image in the polygon; comparison with the literal skeleton
inclusion requires the remaining geometric basepoint transport. -/
noncomputable def kleinPolygonTransportedOuterToSpacePiOne :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint →*
      FundamentalGroup kleinPairingData.Space
        (kleinPolygonOuterToSpace
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) :=
  kleinPolygonOuterToSpacePiOne.comp
    kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm.toMonoidHom

/-- Exact forward-kernel transport from outer-piece coordinates to the
preferred skeleton coordinates.  This is equality-driven transport in the
direction needed by the consumer: the target skeleton overlap image is
pulled back through the inverse equivalence before applying the proved outer
kernel inclusion. -/
theorem kleinPolygonOverlapSkeletonNormalClosure_le_transportedKernel :
    Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint)) ≤
      MonoidHom.ker kleinPolygonTransportedOuterToSpacePiOne := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨g, rfl⟩
  change kleinPolygonTransportedOuterToSpacePiOne
      (kleinPolygonOverlapToSkeletonPiOne g) = 1
  change kleinPolygonOuterToSpacePiOne
      (kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm
        (kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint
          (kleinPolygonOverlapToOuterPiOne g))) = 1
  rw [kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm_apply_apply]
  exact (kleinPolygonOverlapNormalClosure_le_outerToSpacePiOne_ker
    (Subgroup.le_normalClosure ⟨g, rfl⟩))

/-- The same map with the annular source written in integer winding
coordinates.  Its value at `ofAdd 1` is the sole remaining geometric word
calculation in the attaching-cell argument. -/
noncomputable def kleinPolygonOverlapWindingHom :
    Multiplicative ℤ →* FreeGroup Bool :=
  kleinPolygonOverlapToSkeletonFreeGroup.comp
    kleinPolygonOverlapFundamentalGroupEquivInt.symm.toMonoidHom

/-- The winding-coordinate map recovers the literal overlap map on every
based loop. -/
theorem kleinPolygonOverlapWindingHom_factor
    (g : FundamentalGroup (overlapOpen kleinPairingData.Rel)
      kleinPolygonOverlapPoint) :
    kleinPolygonOverlapWindingHom
        (kleinPolygonOverlapFundamentalGroupEquivInt g) =
      kleinPolygonOverlapToSkeletonFreeGroup g := by
  simp [kleinPolygonOverlapWindingHom]

/-- Changing the annular source from based loops to integer winding
coordinates does not change the image subgroup in the skeleton coordinates. -/
theorem kleinPolygonOverlapWindingHom_range_eq_skeleton_range :
    kleinPolygonOverlapWindingHom.range =
      kleinPolygonOverlapToSkeletonFreeGroup.range := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact ⟨kleinPolygonOverlapFundamentalGroupEquivInt.symm n, by
      simp [kleinPolygonOverlapWindingHom]⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨kleinPolygonOverlapFundamentalGroupEquivInt g,
      kleinPolygonOverlapWindingHom_factor g⟩

/-- The exact free-group word traced by one positive turn around the radial
overlap. -/
noncomputable def kleinPolygonOverlapWindingOneImage : FreeGroup Bool :=
  kleinPolygonOverlapWindingHom (Multiplicative.ofAdd (1 : ℤ))

/-- To identify the overlap generator up to conjugacy, it suffices to compute
the untransported generator along any convenient connector. -/
theorem kleinPolygonOverlapWindingOne_isConj_aabb_of_path_eq
    (p : Path
      (kleinPolygonOuterHomotopyEquivSkeleton
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint))
      kleinSkeletonPoint)
    (h : kleinActualSkeletonFundamentalGroupEquivFreeGroupBool
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p
          kleinPolygonUntransportedWindingOne) = kleinAabbWord) :
    IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord := by
  have hc := fundamentalGroup_pathTransport_isConj
    kleinPolygonOverlapImageToSkeletonPointPath p
    kleinPolygonUntransportedWindingOne
  have hm := kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom.map_isConj hc
  change kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p
      kleinPolygonUntransportedWindingOne) = kleinAabbWord at h
  rw [h] at hm
  simpa [kleinPolygonOverlapWindingOneImage, kleinPolygonOverlapWindingHom,
    kleinPolygonOverlapToSkeletonFreeGroup,
    kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint,
    kleinPolygonUntransportedWindingOne] using hm

/-- The complete overlap image is the cyclic subgroup generated by the
winding-one word.  Thus identifying that one word with `aabb` also identifies
the normal subgroup imposed by van Kampen. -/
theorem kleinPolygonOverlapWindingHom_range :
    kleinPolygonOverlapWindingHom.range =
      Subgroup.zpowers kleinPolygonOverlapWindingOneImage := by
  have hhom : kleinPolygonOverlapWindingHom =
      zpowersHom (FreeGroup Bool) kleinPolygonOverlapWindingOneImage := by
    simpa [kleinPolygonOverlapWindingOneImage] using
      ((zpowersHom (FreeGroup Bool)).apply_symm_apply
        kleinPolygonOverlapWindingHom).symm
  rw [hhom]
  exact Subgroup.range_zpowersHom _

/-- Passing from the cyclic overlap image to its winding-one generator does
not change the normal subgroup imposed by van Kampen. -/
theorem kleinPolygonOverlapWindingHom_normalClosure :
    Subgroup.normalClosure
        (kleinPolygonOverlapWindingHom.range : Set (FreeGroup Bool)) =
      Subgroup.normalClosure {kleinPolygonOverlapWindingOneImage} := by
  rw [kleinPolygonOverlapWindingHom_range]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    exact Subgroup.zpowers_le_of_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton _))
  · apply Subgroup.normalClosure_mono
    exact Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers _)

/-- The arbitrary path used to move the overlap basepoint may conjugate its
word, but conjugation does not change the normal closure used by van Kampen. -/
theorem kleinPolygonOverlapNormalClosure_eq_aabb_of_isConj
    (h : IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord) :
    Subgroup.normalClosure
        (kleinPolygonOverlapWindingHom.range : Set (FreeGroup Bool)) =
      Subgroup.normalClosure kleinPolygonRelations := by
  rw [kleinPolygonOverlapWindingHom_normalClosure]
  change Subgroup.normalClosure {kleinPolygonOverlapWindingOneImage} =
    Subgroup.normalClosure {kleinAabbWord}
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    obtain ⟨c, hc⟩ := isConj_iff.mp h.symm
    rw [← hc]
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    rw [← hc]
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

/-- Once the winding-one word is identified up to conjugacy, the normal
closure of the actual overlap image in the skeleton group is exactly the
pullback of the `aabb` relation subgroup. -/
theorem kleinPolygonOverlapToSkeletonPiOne_normalClosure_eq_aabb
    (h : IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord) :
    Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint)) =
      Subgroup.comap
        kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom
        (Subgroup.normalClosure kleinPolygonRelations) := by
  apply Subgroup.map_injective
    (f := kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.toMonoidHom)
    kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.injective
  rw [Subgroup.map_normalClosure _ _
    kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.surjective]
  rw [Subgroup.map_comap_eq_self_of_surjective
    kleinActualSkeletonFundamentalGroupEquivFreeGroupBool.surjective]
  rw [← kleinPolygonOverlapNormalClosure_eq_aabb_of_isConj h]
  rw [kleinPolygonOverlapWindingHom_range_eq_skeleton_range]
  apply congrArg Subgroup.normalClosure
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨kleinPolygonOverlapToSkeletonPiOne g, ⟨g, rfl⟩, rfl⟩

/-- Inclusion of the actual polygon skeleton into the polygon quotient. -/
noncomputable def kleinPolygonSkeletonToSpace :
    C(kleinPairingData.skeleton, kleinPairingData.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The based map whose kernel is computed by the attaching-cell form of
van Kampen. -/
noncomputable def kleinPolygonSkeletonToSpacePiOne :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint →*
      FundamentalGroup kleinPairingData.Space
        (kleinPolygonSkeletonToSpace kleinSkeletonPoint) :=
  FundamentalGroup.map kleinPolygonSkeletonToSpace kleinSkeletonPoint

/-- The literal skeleton inclusion factored through the radial outer piece. -/
noncomputable def kleinPolygonSkeletonToOuter :
    C(kleinPairingData.skeleton,
      {q // q ∈ (openCover kleinPairingData).outer}) :=
  ⟨skeletonToOuter kleinPairingData,
    Continuous.subtype_mk continuous_subtype_val
      (skeleton_mem_outer kleinPairingData)⟩

/-- The induced map of the direct skeleton-to-outer inclusion at the preferred
basepoint. -/
noncomputable def kleinPolygonSkeletonToOuterPiOne :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint →*
      FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonSkeletonToOuter kleinSkeletonPoint) :=
  FundamentalGroup.map kleinPolygonSkeletonToOuter kleinSkeletonPoint

/-- Exact equality from the outer-piece composite representation to the
literal skeleton-in-polygon representation.  This proves the geometric half
of the remaining map comparison; no basepoint change occurs in this direct
factorization. -/
theorem kleinPolygonSkeletonToSpacePiOne_eq_outer_comp_direct :
    (FundamentalGroup.map kleinPolygonOuterToSpace
        (kleinPolygonSkeletonToOuter kleinSkeletonPoint)).comp
        kleinPolygonSkeletonToOuterPiOne =
      kleinPolygonSkeletonToSpacePiOne := by
  ext g
  induction g using Quotient.inductionOn with
  | h p =>
    apply Quotient.sound
    exact ⟨Path.Homotopy.refl _⟩

/-- The outer-piece connector whose two stages underlie both basepoint
changes.  Its first stage is the inverse homotopy-equivalence unit; its
second is the chosen connector inside the skeleton, included back into the
outer piece. -/
noncomputable def kleinPolygonOuterImageToDirectSkeletonPointPath :
    Path
      (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)
      (kleinPolygonSkeletonToOuter kleinSkeletonPoint) := by
  let x := kleinPolygonOverlapToOuter kleinPolygonOverlapPoint
  let p₁ := (kleinPolygonOuterHomotopyEquivSkeleton.left_inv.some.evalAt x).symm
  let p₂ := kleinPolygonOverlapImageToSkeletonPointPath.map
    kleinPolygonSkeletonToOuter.continuous
  exact p₁.trans p₂

/-- In the fundamental groupoid, the concrete outer connector is exactly the
inverse deformation-unit arrow followed by the inverse map of the chosen
skeleton connector.  This is the geometric identification required by
`equivalence_unit_mapIso_conj_preimage`. -/
theorem kleinPolygonOuterConnector_eq_inverseUnit_comp_mappedConnector :
    (⟦kleinPolygonOuterImageToDirectSkeletonPointPath⟧ :
      FundamentalGroupoid.mk
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ⟶
        FundamentalGroupoid.mk
          (kleinPolygonSkeletonToOuter kleinSkeletonPoint)) =
      ⟦(kleinPolygonOuterHomotopyEquivSkeleton.left_inv.some.evalAt
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)).symm⟧ ≫
        (FundamentalGroupoid.map
          kleinPolygonOuterHomotopyEquivSkeleton.invFun).map
            ⟦kleinPolygonOverlapImageToSkeletonPointPath⟧ := by
  rfl

/-- A concrete path representative of the unit component actually packaged
by Mathlib's groupoid equivalence.  `Equivalence.mk` adjointifies the raw
homotopy unit, so this representative is kept distinct from the deformation
path used above. -/
theorem exists_kleinPolygonPackagedUnitPath :
    ∃ p : Path
      (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)
      (kleinPolygonOuterFundamentalGroupoidEquivalence.inverse.obj
        (kleinPolygonOuterFundamentalGroupoidEquivalence.functor.obj
          (FundamentalGroupoid.mk
            (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)))).as,
      ⟦p⟧ = kleinPolygonOuterFundamentalGroupoidEquivalence.unitIso.hom.app
        (FundamentalGroupoid.mk
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) := by
  exact Path.Homotopic.Quotient.mk_surjective _

noncomputable def kleinPolygonPackagedUnitPath :=
  Classical.choose exists_kleinPolygonPackagedUnitPath

theorem kleinPolygonPackagedUnitPath_mk :
    ⟦kleinPolygonPackagedUnitPath⟧ =
      kleinPolygonOuterFundamentalGroupoidEquivalence.unitIso.hom.app
        (FundamentalGroupoid.mk
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) :=
  Classical.choose_spec exists_kleinPolygonPackagedUnitPath

/-- A concrete representative of the connector used by the packaged
outer-piece equivalence: first its actual unit component, then the inverse
image of the chosen skeleton connector. -/
noncomputable def kleinPolygonPackagedUnitConnector : Path
    (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)
    (kleinPolygonSkeletonToOuter kleinSkeletonPoint) :=
  kleinPolygonPackagedUnitPath.trans
    (kleinPolygonOverlapImageToSkeletonPointPath.map
      kleinPolygonOuterHomotopyEquivSkeleton.invFun.continuous)

/-- The packaged connector represents exactly the unit followed by the
inverse functor's image of the chosen skeleton connector. -/
theorem kleinPolygonPackagedUnitConnector_mk :
    (⟦kleinPolygonPackagedUnitConnector⟧ :
      FundamentalGroupoid.mk
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ⟶
        FundamentalGroupoid.mk
          (kleinPolygonSkeletonToOuter kleinSkeletonPoint)) =
      kleinPolygonOuterFundamentalGroupoidEquivalence.unitIso.hom.app _ ≫
        kleinPolygonOuterFundamentalGroupoidEquivalence.inverse.map
          ⟦kleinPolygonOverlapImageToSkeletonPointPath⟧ := by
  change ⟦kleinPolygonPackagedUnitPath.trans
    (kleinPolygonOverlapImageToSkeletonPointPath.map
      kleinPolygonOuterHomotopyEquivSkeleton.invFun.continuous)⟧ = _
  let q :
      FundamentalGroupoid.mk
          (kleinPolygonOuterFundamentalGroupoidEquivalence.inverse.obj
            (kleinPolygonOuterFundamentalGroupoidEquivalence.functor.obj
              (FundamentalGroupoid.mk
                (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)))).as ⟶
        FundamentalGroupoid.mk
          (kleinPolygonSkeletonToOuter kleinSkeletonPoint) :=
    ⟦kleinPolygonOverlapImageToSkeletonPointPath.map
      kleinPolygonOuterHomotopyEquivSkeleton.invFun.continuous⟧
  change (⟦kleinPolygonPackagedUnitPath⟧ :
      FundamentalGroupoid.mk
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ⟶
        FundamentalGroupoid.mk
          (kleinPolygonOuterFundamentalGroupoidEquivalence.inverse.obj
            (kleinPolygonOuterFundamentalGroupoidEquivalence.functor.obj
              (FundamentalGroupoid.mk
                (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)))).as) ≫ q = _
  calc
    _ = kleinPolygonOuterFundamentalGroupoidEquivalence.unitIso.hom.app _ ≫ q :=
      congrArg (fun f => f ≫ q) kleinPolygonPackagedUnitPath_mk
    _ = _ := by congr 1

/-- Basepoint transport in the outer piece along the connector belonging to
the actual unit packaged by Mathlib's groupoid equivalence. -/
noncomputable def kleinPolygonPackagedOuterImageFundamentalGroupEquivAtDirectSkeletonPoint :
    FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ≃*
      FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonSkeletonToOuter kleinSkeletonPoint) :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath
    kleinPolygonPackagedUnitConnector

/-- In packaged equivalence coordinates, returning from the skeleton and
then transporting along the packaged connector is exactly the literal
skeleton-to-outer map. -/
theorem kleinPolygonPackagedSourceCoordinate_eq_direct :
    kleinPolygonPackagedOuterImageFundamentalGroupEquivAtDirectSkeletonPoint.toMonoidHom.comp
        kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm.toMonoidHom =
      kleinPolygonSkeletonToOuterPiOne := by
  ext g
  change kleinPolygonPackagedOuterImageFundamentalGroupEquivAtDirectSkeletonPoint
      (kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm g) = _
  let q : kleinPolygonOuterFundamentalGroupoidEquivalence.functor.obj
        (FundamentalGroupoid.mk
          (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint)) ≅
      FundamentalGroupoid.mk kleinSkeletonPoint :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm
      ⟦kleinPolygonOverlapImageToSkeletonPointPath⟧
  have hinv :
      kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm g =
        kleinPolygonOuterFundamentalGroupoidEquivalence.fullyFaithfulFunctor.preimage
          (q.symm.conj g) := by rfl
  rw [hinv]
  change ((CategoryTheory.Groupoid.isoEquivHom _ _).symm
      ⟦kleinPolygonPackagedUnitConnector⟧).conj
      (kleinPolygonOuterFundamentalGroupoidEquivalence.fullyFaithfulFunctor.preimage
        (q.symm.conj g)) = _
  have hconn : (CategoryTheory.Groupoid.isoEquivHom _ _).symm
        ⟦kleinPolygonPackagedUnitConnector⟧ =
      (kleinPolygonOuterFundamentalGroupoidEquivalence.unitIso.app _) ≪≫
        kleinPolygonOuterFundamentalGroupoidEquivalence.inverse.mapIso q := by
    apply Iso.ext
    exact kleinPolygonPackagedUnitConnector_mk
  have h₁ := congrArg (fun z => z.conj
      (kleinPolygonOuterFundamentalGroupoidEquivalence.fullyFaithfulFunctor.preimage
        (q.symm.conj g))) hconn
  have h₂ := equivalence_unit_mapIso_conj_preimage
    kleinPolygonOuterFundamentalGroupoidEquivalence _ _ q g
  exact h₁.trans h₂

/-- On the preferred skeleton basepoint, the direct skeleton-to-outer map is
literally the inverse functor of the groupoid equivalence.  This removes the
target-side cast from the remaining source-coordinate comparison. -/
theorem kleinPolygonSkeletonToOuterPiOne_apply_eq_inverse_map
    (g : FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint) :
    kleinPolygonSkeletonToOuterPiOne g =
      kleinPolygonOuterFundamentalGroupoidEquivalence.inverse.map g := by
  rfl

/-- The target-basepoint path matching the two stages already used on the
domain side.  First the inverse homotopy-equivalence unit runs from the
overlap image to its radial deformation; then the chosen skeleton connector
runs to `kleinSkeletonPoint`.  Both stages are included into the polygon. -/
noncomputable def kleinPolygonOuterImageToSkeletonPointSpacePath :
    Path
      (kleinPolygonOuterToSpace
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint))
      (kleinPolygonSkeletonToSpace kleinSkeletonPoint) := by
  exact kleinPolygonOuterImageToDirectSkeletonPointPath.map
    kleinPolygonOuterToSpace.continuous

/-- The polygon target connector is exactly the image of the corresponding
outer-piece connector.  Thus the remaining homomorphism comparison has one
specified basepoint path rather than two independently chosen transports. -/
theorem kleinPolygonOuterImageToDirectSkeletonPointPath_map :
    kleinPolygonOuterImageToDirectSkeletonPointPath.map
        kleinPolygonOuterToSpace.continuous =
      kleinPolygonOuterImageToSkeletonPointSpacePath :=
  rfl

/-- Basepoint transport in the outer piece along the exact connector used by
the target-side transport. -/
noncomputable def kleinPolygonOuterImageFundamentalGroupEquivAtDirectSkeletonPoint :
    FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint) ≃*
      FundamentalGroup {q // q ∈ (openCover kleinPairingData).outer}
        (kleinPolygonSkeletonToOuter kleinSkeletonPoint) :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath
    kleinPolygonOuterImageToDirectSkeletonPointPath

/-- The transported outer-to-polygon map after applying the matching target
basepoint change.  It now has exactly the source and target groups of the
literal skeleton inclusion map. -/
noncomputable def kleinPolygonTargetTransportedOuterToSpacePiOne :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint →*
      FundamentalGroup kleinPairingData.Space
        (kleinPolygonSkeletonToSpace kleinSkeletonPoint) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      kleinPolygonOuterImageToSkeletonPointSpacePath).toMonoidHom.comp
    kleinPolygonTransportedOuterToSpacePiOne

/-- Naturality moves the target-side path transport through the outer-piece
inclusion.  Consequently the remaining comparison with the literal skeleton
map is entirely a comparison of the two source-coordinate maps into the
outer-piece fundamental group. -/
theorem kleinPolygonTargetTransportedOuterToSpacePiOne_factor :
    kleinPolygonTargetTransportedOuterToSpacePiOne =
      (FundamentalGroup.map kleinPolygonOuterToSpace
        (kleinPolygonSkeletonToOuter kleinSkeletonPoint)).comp
        (kleinPolygonOuterImageFundamentalGroupEquivAtDirectSkeletonPoint.toMonoidHom.comp
          kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm.toMonoidHom) := by
  ext g
  exact DFunLike.congr_fun
    (fundamentalGroup_map_pathTransport_natural kleinPolygonOuterToSpace
      kleinPolygonOuterImageToDirectSkeletonPointPath)
    (kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm g)

/-- The packaged connector included into the polygon quotient. -/
noncomputable def kleinPolygonPackagedUnitConnectorSpacePath : Path
    (kleinPolygonOuterToSpace
      (kleinPolygonOverlapToOuter kleinPolygonOverlapPoint))
    (kleinPolygonSkeletonToSpace kleinSkeletonPoint) :=
  kleinPolygonPackagedUnitConnector.map kleinPolygonOuterToSpace.continuous

/-- The outer-to-polygon map transported using the actual connector belonging
to the packaged groupoid equivalence. -/
noncomputable def kleinPolygonPackagedTargetTransportedOuterToSpacePiOne :
    FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint →*
      FundamentalGroup kleinPairingData.Space
        (kleinPolygonSkeletonToSpace kleinSkeletonPoint) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      kleinPolygonPackagedUnitConnectorSpacePath).toMonoidHom.comp
    kleinPolygonTransportedOuterToSpacePiOne

/-- Naturality and the packaged source-coordinate identity identify the
packaged transported map with the literal skeleton inclusion map. -/
theorem kleinPolygonPackagedTargetTransportedOuterToSpacePiOne_eq_direct :
    kleinPolygonPackagedTargetTransportedOuterToSpacePiOne =
      kleinPolygonSkeletonToSpacePiOne := by
  rw [← kleinPolygonSkeletonToSpacePiOne_eq_outer_comp_direct,
    ← kleinPolygonPackagedSourceCoordinate_eq_direct]
  ext g
  exact DFunLike.congr_fun
    (fundamentalGroup_map_pathTransport_natural kleinPolygonOuterToSpace
      kleinPolygonPackagedUnitConnector)
    (kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint.symm g)

/-- Target basepoint transport is an equivalence, so the forward kernel
inclusion survives unchanged and now lands in the kernel of a map with the
literal skeleton inclusion's exact source and target types. -/
theorem kleinPolygonOverlapSkeletonNormalClosure_le_targetTransportedKernel :
    Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint)) ≤
      MonoidHom.ker kleinPolygonTargetTransportedOuterToSpacePiOne := by
  intro g hg
  change kleinPolygonTargetTransportedOuterToSpacePiOne g = 1
  change (FundamentalGroup.fundamentalGroupMulEquivOfPath
    kleinPolygonOuterImageToSkeletonPointSpacePath)
      (kleinPolygonTransportedOuterToSpacePiOne g) = 1
  rw [show kleinPolygonTransportedOuterToSpacePiOne g = 1 from
    kleinPolygonOverlapSkeletonNormalClosure_le_transportedKernel hg]
  exact map_one _

/-- The already proved forward van Kampen kernel inclusion, now expressed for
the literal skeleton-to-polygon map via the packaged connector identity. -/
theorem kleinPolygonOverlapSkeletonNormalClosure_le_skeletonToSpaceKernel :
    Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint)) ≤
      MonoidHom.ker kleinPolygonSkeletonToSpacePiOne := by
  rw [← kleinPolygonPackagedTargetTransportedOuterToSpacePiOne_eq_direct]
  intro g hg
  change (FundamentalGroup.fundamentalGroupMulEquivOfPath
    kleinPolygonPackagedUnitConnectorSpacePath)
      (kleinPolygonTransportedOuterToSpacePiOne g) = 1
  rw [show kleinPolygonTransportedOuterToSpacePiOne g = 1 from
    kleinPolygonOverlapSkeletonNormalClosure_le_transportedKernel hg]
  exact map_one _

/-- Quotient assembly after the two remaining topological facts have been
supplied: winding-one conjugacy identifies the relation subgroup, while based
van Kampen says that subgroup is exactly the kernel and that the skeleton map
is onto. -/
noncomputable def kleinPolygonFundamentalGroupEquivPresented_of_vanKampen
    (hconj : IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord)
    (hsurj : Function.Surjective kleinPolygonSkeletonToSpacePiOne)
    (hker : MonoidHom.ker kleinPolygonSkeletonToSpacePiOne =
      Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint))) :
    FundamentalGroup kleinPairingData.Space
        (kleinPolygonSkeletonToSpace kleinSkeletonPoint) ≃*
      KleinPolygonPresentedGroup :=
  (QuotientGroup.quotientKerEquivOfSurjective
      kleinPolygonSkeletonToSpacePiOne hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (hker.trans
        (kleinPolygonOverlapToSkeletonPiOne_normalClosure_eq_aabb hconj))).trans
      kleinSkeletonAabbQuotientEquiv)

/-- Exact based consequence still to extract from the already proved
fundamental-groupoid pseudopushout.  Surjectivity and the kernel calculation
belong together because they are the two outputs of the same van Kampen map. -/
structure KleinPolygonBasedVanKampen : Prop where
  surjective : Function.Surjective kleinPolygonSkeletonToSpacePiOne
  ker_eq_overlap_normalClosure :
    MonoidHom.ker kleinPolygonSkeletonToSpacePiOne =
      Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint))

/-- The exact polygon presentation from the packaged based van Kampen
consequence and the independent geometric winding comparison. -/
noncomputable def kleinPolygonFundamentalGroupEquivPresented
    (hconj : IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord)
    (hvk : KleinPolygonBasedVanKampen) :
    FundamentalGroup kleinPairingData.Space
        (kleinPolygonSkeletonToSpace kleinSkeletonPoint) ≃*
      KleinPolygonPresentedGroup :=
  kleinPolygonFundamentalGroupEquivPresented_of_vanKampen
    hconj hvk.surjective hvk.ker_eq_overlap_normalClosure

def finiteWedgeBoolPoint : FiniteWedge Bool := wedgeCircle false 1

@[simp] theorem finiteWedgeBoolHomeomorphTwoCircles_point :
    finiteWedgeBoolHomeomorphTwoCircles finiteWedgeBoolPoint = twoCirclesPoint := rfl

/-- Final C1 adapter: a van Kampen computation of the `aabb` presentation at
one point of the polygon model yields the registered presentation at every
basepoint of the frozen Klein bottle. -/
theorem kleinBottle_pi1_every_basepoint_of_polygon_van_kampen
    (q₀ : kleinPairingData.Space)
    (h₀ : Nonempty
      (FundamentalGroup kleinPairingData.Space q₀ ≃*
        KleinPolygonPresentedGroup)) :
    ∀ k : KleinBottle,
      Nonempty (FundamentalGroup KleinBottle k ≃* PresentedKleinGroup) := by
  obtain ⟨e₀⟩ := h₀
  have himage : Nonempty
      (FundamentalGroup KleinBottle (kleinPairingSpaceHomeomorph q₀) ≃*
        PresentedKleinGroup) :=
    ⟨(fundamentalGroupEquivOfHomeomorph kleinPairingSpaceHomeomorph q₀).symm |>.trans
      (e₀.trans kleinPolygonPresentedGroupEquiv)⟩
  intro k
  obtain ⟨eimage⟩ := himage
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected k
    (kleinPairingSpaceHomeomorph q₀)).trans eimage⟩

/-- Complete C1 assembly from the two remaining topological inputs.  This
also transports the polygon computation through the fixed Klein-bottle
homeomorphism and from the skeleton image to every basepoint. -/
theorem kleinBottle_pi1_every_basepoint_of_vanKampen_inputs
    (hconj : IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord)
    (hsurj : Function.Surjective kleinPolygonSkeletonToSpacePiOne)
    (hker : MonoidHom.ker kleinPolygonSkeletonToSpacePiOne =
      Subgroup.normalClosure
        (kleinPolygonOverlapToSkeletonPiOne.range : Set
          (FundamentalGroup kleinPairingData.skeleton kleinSkeletonPoint))) :
    ∀ k : KleinBottle,
      Nonempty (FundamentalGroup KleinBottle k ≃* PresentedKleinGroup) :=
  kleinBottle_pi1_every_basepoint_of_polygon_van_kampen
    (kleinPolygonSkeletonToSpace kleinSkeletonPoint)
    ⟨kleinPolygonFundamentalGroupEquivPresented_of_vanKampen
      hconj hsurj hker⟩

/-- C1 in its final two-input form: one geometric word comparison and one
based consequence of the groupoid pseudopushout. -/
theorem kleinBottle_pi1_every_basepoint_of_basedVanKampen
    (hconj : IsConj kleinPolygonOverlapWindingOneImage kleinAabbWord)
    (hvk : KleinPolygonBasedVanKampen) :
    ∀ k : KleinBottle,
      Nonempty (FundamentalGroup KleinBottle k ≃* PresentedKleinGroup) :=
  kleinBottle_pi1_every_basepoint_of_vanKampen_inputs
    hconj hvk.surjective hvk.ker_eq_overlap_normalClosure

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
#print axioms fundamentalGroup_pathTransport_isConj
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
#print axioms kleinPolygonPresentedGroupEquiv
#print axioms kleinBottlePathConnectedSpace
#print axioms kleinPairingSpacePathConnectedSpace
#print axioms kleinSkeletonFundamentalGroupEquivCoprod
#print axioms finiteWedgeBoolHomeomorphTwoCircles
#print axioms finiteWedgeCongr
#print axioms kleinSkeletonHomeomorphStandardTwoCircles
#print axioms kleinActualSkeletonFundamentalGroupEquivCoprod
#print axioms circleFundamentalGroupCoprodEquivFreeGroupBool
#print axioms kleinActualSkeletonFundamentalGroupEquivFreeGroupBool
#print axioms kleinSkeletonPresentationMap_surjective
#print axioms kleinSkeletonPresentationMap_attachingClass
#print axioms kleinSkeletonPresentationMap_ker
#print axioms kleinPolygonFundamentalGroupoidPseudopushout
#print axioms kleinPolygonPseudopushout_arrow_eq_reconstructed
#print axioms pathTwoOpenSubdivision_transition_mem_overlap
#print axioms boolSideRunPartition_spec
#print axioms pathHomotopicQuotient_concat_eq_of_pieceClass_eq
#print axioms path_concat_mem_of_piece_mem
#print axioms pathTwoOpenSubdivision_quotient_eq_concat_of_pieceClass_eq
#print axioms kleinPolygonInnerContractibleSpace
#print axioms kleinPolygonInnerFundamentalGroup_subsingleton
#print axioms kleinPolygonInnerFundamentalGroupoid_hom_subsingleton
#print axioms kleinPolygonInner_pathClass_eq
#print axioms kleinPolygonInner_pathClass_eq_overlapReplacement
#print axioms kleinPolygonInner_ambientPathClass_eq_outerOverlapReplacement
#print axioms kleinPolygonInnerRun_exists_outerOverlapReplacement
#print axioms kleinPolygonInnerBlock_exists_outerOverlapReplacement
#print axioms kleinPolygonOverlapPathConnectedSpace
#print axioms kleinPolygonOverlapToOuterPiOne
#print axioms kleinPolygonOverlapFundamentalGroupEquivInt
#print axioms kleinPolygonOuterHomotopyEquivSkeleton_on_skeleton
#print axioms kleinPolygonOuterFundamentalGroupoidEquivalence_obj_skeleton
#print axioms kleinPolygonOverlapImageFundamentalGroupEquivSkeleton
#print axioms kleinSkeletonPathConnectedSpace
#print axioms kleinPolygonOverlapImageToSkeletonPointPath
#print axioms kleinPolygonOverlapImageFundamentalGroupEquivAtSkeletonPoint
#print axioms kleinPolygonOverlapToSkeletonFreeGroup
#print axioms kleinPolygonOverlapWindingHom
#print axioms kleinPolygonOverlapWindingHom_factor
#print axioms kleinPolygonOverlapWindingOneImage
#print axioms kleinPolygonUntransportedWindingOne
#print axioms kleinPolygonStandardModelConnector
#print axioms kleinPolygonOverlapWindingOne_isConj_aabb_of_path_eq
#print axioms kleinPolygonOverlapWindingHom_range
#print axioms kleinPolygonOverlapWindingHom_normalClosure
#print axioms kleinPolygonOverlapNormalClosure_eq_aabb_of_isConj
#print axioms kleinPolygonOverlapWindingHom_range_eq_skeleton_range
#print axioms kleinPolygonOverlapToSkeletonPiOne_normalClosure_eq_aabb
#print axioms kleinPolygonPackagedUnitPath_mk
#print axioms kleinPolygonPackagedUnitConnector_mk
#print axioms kleinPolygonPackagedSourceCoordinate_eq_direct
#print axioms kleinPolygonPackagedTargetTransportedOuterToSpacePiOne_eq_direct
#print axioms kleinPolygonOverlapSkeletonNormalClosure_le_skeletonToSpaceKernel
#print axioms kleinPolygonSkeletonToOuterPiOne_apply_eq_inverse_map
#print axioms kleinPolygonFundamentalGroupEquivPresented_of_vanKampen
#print axioms kleinPolygonFundamentalGroupEquivPresented
#print axioms kleinBottle_pi1_every_basepoint_of_polygon_van_kampen
#print axioms kleinBottle_pi1_every_basepoint_of_vanKampen_inputs
#print axioms kleinBottle_pi1_every_basepoint_of_basedVanKampen

end ConstructionTargets.t93J03Closure

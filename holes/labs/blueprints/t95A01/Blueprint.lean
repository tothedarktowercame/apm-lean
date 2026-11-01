import Mathlib
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.KleinBottlePiOne
import ConstructionTargets.StandardSurfaceFiniteCover
import ConstructionTargets.t93J03Closure
import ConstructionTargets.CoveringTotalLocPathConnected
import ConstructionTargets.SuppliedCoverAlgebra

/-!
# APM t95A01: examples and obstruction for double covers

The three imperative parts of the printed problem are encoded as one
conjunction giving their answers.

For the first part, the explicit space is the presentation complex
`S¹ ∪_{z ↦ z³} D²`.  Its displayed fundamental group is `ZMod 3`; the
statement separately records path connectedness, failure of simple
connectedness, and the absence of every connected two-sheeted covering.

For the second part, the space is the repository's concrete `aabb` polygon
quotient model of the Klein bottle.  Non-orientability is stated intrinsically,
as vanishing of integral `H₂` of this closed surface (a closed connected orientable
surface has `H₂ = ℤ`), and the asserted self-map is a genuine covering map with
every fibre of cardinal two.  Compactness is included explicitly; “surface” is carried by the
standard disk-polygon quotient construction itself.

For the third part, “finite fundamental group” is expressed by `Finite` on
the actual based fundamental group.  The conclusion universally rules out a
two-sheeted covering self-map of every path-connected space.  No local
path-connectedness or semilocally-simply-connectedness is added: the
nonexistence direction only uses path lifting for the supplied covering map.
-/

open Set
open ConstructionTargets
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace APM.T95A01

/-- The degree-three attaching loop used for the explicit `ℤ/3` presentation
complex. -/
def degreeThreeLoop : C(Circle, Circle) where
  toFun z := z ^ (3 : ℕ)
  continuous_toFun := continuous_pow 3

/-- The concrete presentation complex `S¹ ∪_{z ↦ z³} D²`. -/
abbrev ThreePresentationComplex :=
  ConstructionTargets.AttachTwoCell.Cell degreeThreeLoop

/-- Its canonical basepoint, coming from `1 ∈ S¹`. -/
def threePresentationBasepoint : ThreePresentationComplex :=
  ConstructionTargets.AttachTwoCell.cellIncl degreeThreeLoop 1

/-- The exact `aabb` polygon pairing whose quotient is the concrete Klein
bottle used below. -/
abbrev KleinPairing := ConstructionTargets.t93J03Closure.kleinPairingData

/-- Compute van Kampen for the degree-three cell attachment.  Apply
`AttachTwoCell.cell_piOne` with its sorry-free cover, contraction, homotopy
equivalence and generator lemmas; identify the normal closure of the cube in
the one-generator free group with `Multiplicative (ZMod 3)`. -/
-- `1 ^ 3 = 1` on the circle: the attaching loop preserves the basepoint.
theorem threePresentationComplex_piOne_aux_one : degreeThreeLoop 1 = 1 := by
  simp [degreeThreeLoop]

-- The winding coordinate of the explicit generator is one.
theorem threePresentationComplex_piOne_aux_winding_one :
    ConstructionTargets.CircleUniversalCover.circleWindingHom
      ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass =
      Multiplicative.ofAdd 1 := by
  simp [ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass,
    ConstructionTargets.CircleUniversalCover.circleWindingHom_mk]

-- The cast representative of the attaching-loop class is
-- `t ↦ exp(2πit) ^ 3 = exp(6πit)` as a map on the interval.
theorem threePresentationComplex_piOne_aux_fun (t : Set.Icc (0 : ℝ) 1) :
    (↑(((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
        degreeThreeLoop.continuous).cast
        threePresentationComplex_piOne_aux_one.symm
        threePresentationComplex_piOne_aux_one.symm) :
        C(Set.Icc (0 : ℝ) 1, Circle)) t =
      ConstructionTargets.CircleUniversalCover.circleCover
        ((3 : ℤ) • (2 * Real.pi) * (t : ℝ)) := by
  rw [ContinuousMap.coe_coe, Path.cast_coe, Path.map_coe, Function.comp_apply]
  show degreeThreeLoop (ConstructionTargets.CircleUniversalCover.circleCover
      ((1 : ℤ) • (2 * Real.pi) * (t : ℝ))) = _
  rw [zsmul_eq_mul]
  rw [show degreeThreeLoop (ConstructionTargets.CircleUniversalCover.circleCover
      (↑(1 : ℤ) * (2 * Real.pi) * (t : ℝ))) =
      (ConstructionTargets.CircleUniversalCover.circleCover
        (↑(1 : ℤ) * (2 * Real.pi) * (t : ℝ))) ^ 3 from rfl]
  simp only [ConstructionTargets.CircleUniversalCover.circleCover]
  rw [pow_three, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  simp only [zsmul_eq_mul]
  push_cast
  ring

-- The canonical lift of the cast attaching loop is the linear path ending
-- at `3 • 2π`.
theorem threePresentationComplex_piOne_aux_lift :
    ConstructionTargets.CircleUniversalCover.liftBasedLoop
      (↑(((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
          degreeThreeLoop.continuous).cast
          threePresentationComplex_piOne_aux_one.symm
          threePresentationComplex_piOne_aux_one.symm) :
        C(Set.Icc (0 : ℝ) 1, Circle))
      (((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
          degreeThreeLoop.continuous).cast
          threePresentationComplex_piOne_aux_one.symm
          threePresentationComplex_piOne_aux_one.symm).source =
      ⟨fun t ↦ (3 : ℤ) • (2 * Real.pi) * (t : ℝ),
        continuous_const.mul continuous_subtype_val⟩ := by
  symm
  apply (ConstructionTargets.CircleUniversalCover.circleCover_isCoveringMap.eq_liftPath_iff'
    _).2
  constructor
  · funext t
    exact (threePresentationComplex_piOne_aux_fun t).symm
  · simp

-- The endpoint integer of the degree-three attaching loop class is `3`.
theorem threePresentationComplex_piOne_aux_end :
    ConstructionTargets.CircleUniversalCover.liftBasedLoopEndpointInteger
      (↑(((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
          degreeThreeLoop.continuous).cast
          threePresentationComplex_piOne_aux_one.symm
          threePresentationComplex_piOne_aux_one.symm) :
        C(Set.Icc (0 : ℝ) 1, Circle))
      (((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
          degreeThreeLoop.continuous).cast
          threePresentationComplex_piOne_aux_one.symm
          threePresentationComplex_piOne_aux_one.symm).source
      (((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
          degreeThreeLoop.continuous).cast
          threePresentationComplex_piOne_aux_one.symm
          threePresentationComplex_piOne_aux_one.symm).target = 3 := by
  apply ConstructionTargets.CircleUniversalCover.period_integer_unique
    (ConstructionTargets.CircleUniversalCover.liftBasedLoopEndpointInteger_spec _ _ _)
  rw [threePresentationComplex_piOne_aux_lift]
  simp

-- The class of the degree-three attaching loop is the cube of the
-- winding-one generator.
theorem threePresentationComplex_piOne_aux_r :
    ConstructionTargets.AttachTwoCell.loopClassAt degreeThreeLoop 1
      threePresentationComplex_piOne_aux_one =
      ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass ^ 3 := by
  apply ConstructionTargets.CircleUniversalCover.circleWindingHom_injective
  rw [map_pow, threePresentationComplex_piOne_aux_winding_one]
  have h1 := threePresentationComplex_piOne_aux_one
  rw [show ConstructionTargets.AttachTwoCell.loopClassAt degreeThreeLoop 1 h1 =
      Path.Homotopic.Quotient.mk
        (((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
          degreeThreeLoop.continuous).cast h1.symm h1.symm) from rfl,
    ConstructionTargets.CircleUniversalCover.circleWindingHom_mk,
    threePresentationComplex_piOne_aux_end]
  apply Multiplicative.toAdd.injective
  simp

-- Reduction mod three as a homomorphism on the multiplicative integers.
noncomputable def threePresentationComplex_piOne_aux_modMap :
    Multiplicative ℤ →* Multiplicative (ZMod 3) :=
  AddMonoidHom.toMultiplicative (Int.castRingHom (ZMod 3)).toAddMonoidHom

-- The mod-three map is surjective.
theorem threePresentationComplex_piOne_aux_modMap_surjective :
    Function.Surjective threePresentationComplex_piOne_aux_modMap := by
  intro y
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd y)
  exact ⟨Multiplicative.ofAdd k, by
    rw [show threePresentationComplex_piOne_aux_modMap (Multiplicative.ofAdd k) =
      Multiplicative.ofAdd ((k : ZMod 3)) from rfl, hk]
    rfl⟩

-- The kernel of the mod-three map is the normal closure of the cube.
theorem threePresentationComplex_piOne_aux_ker :
    MonoidHom.ker threePresentationComplex_piOne_aux_modMap =
      Subgroup.normalClosure ({Multiplicative.ofAdd 3} : Set (Multiplicative ℤ)) := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : ((Multiplicative.toAdd x : ℤ) : ZMod 3) = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa [threePresentationComplex_piOne_aux_modMap] using h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx'
    have hxk : x = Multiplicative.ofAdd 3 ^ k := by
      apply Multiplicative.toAdd.injective
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd 3 ^ k) = k * (3 : ℤ) from by
        simp [zsmul_eq_mul]]
      rw [hk]
      ring
    rw [hxk]
    exact Subgroup.zpow_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _)) k
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    show threePresentationComplex_piOne_aux_modMap (Multiplicative.ofAdd 3) = 1
    rw [show threePresentationComplex_piOne_aux_modMap (Multiplicative.ofAdd 3) =
      Multiplicative.ofAdd ((3 : ℤ) : ZMod 3) from rfl]
    rw [show ((3 : ℤ) : ZMod 3) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr (dvd_refl 3)]
    rfl

theorem threePresentationComplex_piOne :
    Nonempty
      (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
        Multiplicative (ZMod 3)) := by
  have h1 := threePresentationComplex_piOne_aux_one
  letI : PathConnectedSpace
      (ConstructionTargets.AttachTwoCell.Cell degreeThreeLoop) :=
    ConstructionTargets.AttachTwoCell.cell_pc degreeThreeLoop
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ :=
    ConstructionTargets.AttachTwoCell.cell_facts degreeThreeLoop
  obtain ⟨hps, hpk⟩ := ConstructionTargets.AttachTwoCell.cell_piOne degreeThreeLoop 1 h1
    hA1 hA2 hA3 hA4 hA5
    (ConstructionTargets.AttachTwoCell.cell_pathConnected degreeThreeLoop hA3 hA4)
    ConstructionTargets.AttachTwoCell.cell_piOne_aux_hequiv_bijective
    ConstructionTargets.AttachTwoCell.cell_piOne_aux_homotopic_conj
    (ConstructionTargets.AttachTwoCell.cell_piOne_aux_overlap_generator degreeThreeLoop hA3)
  rw [threePresentationComplex_piOne_aux_r] at hpk
  obtain ⟨hsurj2, hker2⟩ :=
    ConstructionTargets.AttachTwoCell.cell_piOne_aux_transport_kernel
      ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.symm _
      (ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass ^ 3) hps hpk
  simp only [MulEquiv.symm_symm] at hker2
  have her : ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
      (ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass ^ 3) =
      Multiplicative.ofAdd 3 := by
    rw [map_pow]
    have h3 : ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
        ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneClass =
        Multiplicative.ofAdd 1 :=
      threePresentationComplex_piOne_aux_winding_one
    rw [h3]
    apply Multiplicative.toAdd.injective
    simp
  rw [her] at hker2
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ hsurj2).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker2).trans
      ((QuotientGroup.quotientMulEquivOfEq
        threePresentationComplex_piOne_aux_ker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          threePresentationComplex_piOne_aux_modMap
          threePresentationComplex_piOne_aux_modMap_surjective)))⟩

/-- A connected two-sheeted cover would have an index-two induced subgroup
of `ZMod 3`.  First use
`IsCoveringMap.totalLocPathConnectedSpace` and connectedness to obtain a
path-connected total space, then `coveringFiberCard_eq_index`; transport the
subgroup through the supplied group equivalence and contradict divisibility
of the order three group. -/
private noncomputable instance
    threePresentationComplex_no_connected_double_cover_aux_sphereLocPathConnected :
    LocPathConnectedSpace (ConstructionTargets.SphereHomology.Sphere 1) :=
  ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1))
    (ConstructionTargets.SphereHomology.Sphere 1)

private noncomputable instance
    threePresentationComplex_no_connected_double_cover_aux_circleLocPathConnected :
    LocPathConnectedSpace Circle :=
  Topology.IsQuotientMap.locPathConnectedSpace
    ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.symm.isQuotientMap

private noncomputable instance
    threePresentationComplex_no_connected_double_cover_aux_diskLocPathConnected :
    LocPathConnectedSpace ConstructionTargets.AttachTwoCell.Disk :=
  (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace

theorem threePresentationComplex_no_connected_double_cover
    (hpi : Nonempty
      (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
        Multiplicative (ZMod 3))) :
    ∀ (E : Type) [TopologicalSpace E] [ConnectedSpace E]
        (p : E → ThreePresentationComplex),
      ¬ (IsCoveringMap p ∧
        ∀ x : ThreePresentationComplex,
          Nat.card {e : E // p e = x} = 2) := by
  intro E _ _ p ⟨hp, hcard⟩
  letI : LocPathConnectedSpace ThreePresentationComplex :=
    Quotient.locPathConnectedSpace
  letI : LocPathConnectedSpace E :=
    ConstructionTargets.CoveringTotalLocPathConnected.IsCoveringMap.totalLocPathConnectedSpace hp
  letI : PathConnectedSpace E := PathConnectedSpace.of_locPathConnectedSpace
  letI : PathConnectedSpace ThreePresentationComplex :=
    ConstructionTargets.AttachTwoCell.cell_pc degreeThreeLoop
  have hfiberpos : 0 < Nat.card {e : E // p e = threePresentationBasepoint} := by
    rw [hcard threePresentationBasepoint]
    norm_num
  obtain ⟨⟨e, he⟩⟩ := (Nat.card_pos_iff.mp hfiberpos).1
  have hindex :
      (ConstructionTargets.coveringInducedFundamentalGroupMap hp e).range.index = 2 := by
    rw [← ConstructionTargets.coveringFiberCard_eq_index hp e]
    simpa only [Set.mem_singleton_iff] using hcard (p e)
  have hbasecard : Nat.card (FundamentalGroup ThreePresentationComplex (p e)) = 3 := by
    let q : Path (p e) threePresentationBasepoint := PathConnectedSpace.somePath _ _
    obtain ⟨φ⟩ := hpi
    calc
      Nat.card (FundamentalGroup ThreePresentationComplex (p e)) =
          Nat.card (FundamentalGroup ThreePresentationComplex threePresentationBasepoint) :=
        Nat.card_congr (FundamentalGroup.fundamentalGroupMulEquivOfPath q).toEquiv
      _ = Nat.card (Multiplicative (ZMod 3)) := Nat.card_congr φ.toEquiv
      _ = 3 := by simp
  have hdvd : 2 ∣ Nat.card (FundamentalGroup ThreePresentationComplex (p e)) := by
    rw [← hindex]
    exact (ConstructionTargets.coveringInducedFundamentalGroupMap hp e).range.index_dvd_card
  rw [hbasecard] at hdvd
  norm_num at hdvd

/-- The degree-two singular homology of the `aabb` polygon vanishes.  Use
`PolygonSurfaceHomology.lowDegreeHomology`, compute its `BoundaryKernel` as
bottom from the two `-2` attaching coordinates, and transport through
`t93J03Closure.kleinPairingSpaceHomeomorph`. -/
theorem kleinBottle_h2_isZero_aux_orbit_eq_named (i : Fin 4) (j : Fin 2) :
    KleinPairing.orbit i =
      (ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitEquiv 2).symm j ↔
      ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitEquiv 2
        (KleinPairing.orbit i) = j :=
  (ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitEquiv 2).eq_symm_apply

@[simp]
theorem kleinBottle_h2_isZero_aux_orbitEquiv_orbit (i : Fin 4) :
    ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitEquiv 2
        (KleinPairing.orbit i) =
      ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitLabel 2 i := rfl

theorem kleinBottle_h2_isZero_aux_attachingDegree (j : Fin 2) :
    ConstructionTargets.PolygonSurfaceHomology.attachingDegree KleinPairing
        ((ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitEquiv 2).symm j) =
      -2 := by
  rw [ConstructionTargets.PolygonSurfaceHomology.attachingDegree_apply]
  simp_rw [ConstructionTargets.PolygonSurfaceHomology.edgeOrbitContribution,
    kleinBottle_h2_isZero_aux_orbit_eq_named]
  simp_rw [kleinBottle_h2_isZero_aux_orbitEquiv_orbit]
  fin_cases j <;>
    simp [t93J03Closure.kleinPairingData,
      PolygonSurfacePiOne.nonorientableStandardPairingData,
      PolygonSurfacePiOne.standardPairingDataOfOneVertex,
      PolygonSurfacePiOne.standardPair,
      PolygonSurfacePiOne.standardSign,
      PolygonSurfacePiOne.nonorientableOrbitLabel,
      PolygonSurfacePiOne.nonorientableCoord,
      ConstructionTargets.PolygonSurfaceHomology.edgeAttachingDegree] <;>
      decide

theorem kleinBottle_h2_isZero_aux_attachingBoundary_injective :
    Function.Injective
      (ConstructionTargets.PolygonSurfaceHomology.attachingBoundary KleinPairing) := by
  intro a b h
  have h2 := congrFun h
    ((ConstructionTargets.PolygonSurfacePiOne.nonorientableOrbitEquiv 2).symm 0)
  simp only [ConstructionTargets.PolygonSurfaceHomology.attachingBoundary_apply_apply,
    kleinBottle_h2_isZero_aux_attachingDegree] at h2
  exact Int.eq_of_mul_eq_mul_right (by norm_num) h2

theorem kleinBottle_h2_isZero_aux :
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of ConstructionTargets.t93J03Closure.kleinPairingData.Space)) := by
  have hker : ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel KleinPairing =
      ⊥ :=
    LinearMap.ker_eq_bot.mpr kleinBottle_h2_isZero_aux_attachingBoundary_injective
  have hsub : Subsingleton
      ↥(ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel KleinPairing) := by
    rw [hker]
    infer_instance
  have hzero : CategoryTheory.Limits.IsZero
      (ModuleCat.of ℤ
        ↥(ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel KleinPairing)) :=
    ModuleCat.isZero_of_subsingleton _
  obtain ⟨iso⟩ :=
    (ConstructionTargets.PolygonSurfaceHomology.lowDegreeHomology KleinPairing).2.2
  exact CategoryTheory.Limits.IsZero.of_iso hzero iso

theorem kleinBottle_h2_isZero :
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of KleinBottle)) := by
  refine CategoryTheory.Limits.IsZero.of_iso kleinBottle_h2_isZero_aux ?_.symm
  exact (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo
      ConstructionTargets.t93J03Closure.kleinPairingSpaceHomeomorph)).symm

/-- Construct the double self-cover on the affine-plane orbit model.  Use
`(x,y) ↦ (2*x,y)`, equivariant for the injective Klein-group endomorphism
`(m,n) ↦ (2*m,n)` of index two; descend it and use properly discontinuous
orbit charts plus the two cosets to prove the covering and fibre count. -/
theorem kleinPlaneQuotient_double_self_cover :
    ∃ p : ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient →
        ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient,
      IsCoveringMap p ∧
      ∀ x, Nat.card {y // p y = x} = 2 := by
  sorry

/-- Conjugating a finite-sheeted self-cover by a homeomorphism preserves both
`IsCoveringMap` and the exact fibre cardinality.  Use
`IsCoveringMap.homeomorph_comp`, `Homeomorph.isCoveringMap`, and the induced
equivalence between corresponding fibres. -/
theorem double_self_cover_conjugate_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X → X) (hp : IsCoveringMap p)
    (hcard : ∀ x : X, Nat.card {y : X // p y = x} = 2) :
    ∃ q : Y → Y, IsCoveringMap q ∧
      ∀ y : Y, Nat.card {z : Y // q z = y} = 2 := by
  let q : Y → Y := fun y ↦ e (p (e.symm y))
  have hq : IsCoveringMap q := by
    have h := (hp.comp_homeomorph e.symm).homeomorph_comp e
    simpa only [q, Function.comp_apply] using h
  refine ⟨q, hq, ?_⟩
  intro y
  let fiberEquiv : {z : Y // q z = y} ≃ {x : X // p x = e.symm y} :=
    { toFun := fun z ↦ ⟨e.symm z.1, by
          apply e.injective
          simpa [q] using z.2⟩
      invFun := fun x ↦ ⟨e x.1, by simpa [q] using congrArg e x.2⟩
      left_inv := fun z ↦ Subtype.ext (e.apply_symm_apply z.1)
      right_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.1) }
  exact (Nat.card_congr fiberEquiv).trans (hcard (e.symm y))

/-- Assembly of the affine quotient cover and the banked homeomorphism to the
disk-polygon Klein bottle. -/
theorem kleinBottle_double_self_cover :
    ∃ p : KleinBottle → KleinBottle,
      IsCoveringMap p ∧
      ∀ x : KleinBottle, Nat.card {y : KleinBottle // p y = x} = 2 := by
  obtain ⟨p, hp, hcard⟩ := kleinPlaneQuotient_double_self_cover
  obtain ⟨e⟩ :=
    ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_homeomorph
  exact double_self_cover_conjugate_homeomorph e p hp hcard

/-- A finite fundamental group cannot contain an isomorphic index-two copy of
itself.  Use `coveringInducedFundamentalGroupMap_injective` and
`coveringFiberCard_eq_index`; path-connectedness supplies the coset/fibre
equivalence without any local hypotheses.  Compare finite cardinalities of
the domain group and the induced range. -/
theorem finite_piOne_no_double_self_cover :
    ∀ (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
      Finite (FundamentalGroup X x) →
      ∀ p : X → X,
        ¬ (IsCoveringMap p ∧
          ∀ z : X, Nat.card {y : X // p y = z} = 2) := by
  intro X _ _ x hfinite p ⟨hp, hfiber⟩
  let f := ConstructionTargets.coveringInducedFundamentalGroupMap hp x
  let changeBase : FundamentalGroup X x ≃* FundamentalGroup X (p x) :=
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x (p x)
  let rangeEquiv : FundamentalGroup X x ≃* f.range :=
    MonoidHom.ofInjective
      (ConstructionTargets.coveringInducedFundamentalGroupMap_injective hp x)
  haveI : Finite (FundamentalGroup X (p x)) :=
    Finite.of_equiv (FundamentalGroup X x) changeBase.toEquiv
  have hindex : f.range.index = 2 := by
    rw [← ConstructionTargets.coveringFiberCard_eq_index hp x]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hfiber (p x)
  have hrange : Nat.card f.range = Nat.card (FundamentalGroup X x) :=
    Nat.card_congr rangeEquiv.toEquiv.symm
  have hbase : Nat.card (FundamentalGroup X (p x)) =
      Nat.card (FundamentalGroup X x) :=
    Nat.card_congr changeBase.toEquiv.symm
  have hmul := f.range.card_mul_index
  rw [hindex, hrange, hbase] at hmul
  have hpos : 0 < Nat.card (FundamentalGroup X x) := Nat.card_pos
  omega

end APM.T95A01

open APM.T95A01

#check ConstructionTargets.AttachTwoCell.cell_piOne
#check ConstructionTargets.coveringInducedFundamentalGroupMap_injective
#check ConstructionTargets.coveringFiberCard_eq_index
#check ConstructionTargets.CoveringTotalLocPathConnected.IsCoveringMap.totalLocPathConnectedSpace
#check ConstructionTargets.PolygonSurfaceHomology.lowDegreeHomology
#check ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_homeomorph

/-- APM t95A01.  The answers are respectively the degree-three presentation
complex, the Klein bottle, and nonexistence in the finite-fundamental-group
case. -/
theorem apm_t95a01 :
    (Nonempty ThreePresentationComplex ∧
      IsPathConnected (Set.univ : Set ThreePresentationComplex) ∧
      Nonempty
        (FundamentalGroup ThreePresentationComplex threePresentationBasepoint ≃*
          Multiplicative (ZMod 3)) ∧
      ¬ SimplyConnectedSpace ThreePresentationComplex ∧
      ∀ (E : Type) [TopologicalSpace E] [ConnectedSpace E]
          (p : E → ThreePresentationComplex),
        ¬ (IsCoveringMap p ∧
          ∀ x : ThreePresentationComplex,
            Nat.card {e : E // p e = x} = 2)) ∧
    (CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of KleinBottle)) ∧
      IsCompact (Set.univ : Set KleinBottle) ∧
      ∃ p : KleinBottle → KleinBottle,
        IsCoveringMap p ∧
        ∀ x : KleinBottle, Nat.card {y : KleinBottle // p y = x} = 2) ∧
    (∀ (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
      Finite (FundamentalGroup X x) →
      ∀ p : X → X,
        ¬ (IsCoveringMap p ∧
          ∀ z : X, Nat.card {y : X // p y = z} = 2)) := by
  have hpath : PathConnectedSpace ThreePresentationComplex :=
    (ConstructionTargets.AttachTwoCell.cell_pathConnected degreeThreeLoop
      (ConstructionTargets.AttachTwoCell.cell_overlap_hequiv degreeThreeLoop)
      (ConstructionTargets.AttachTwoCell.cell_outer_hequiv degreeThreeLoop)).2.2
  have hpi := threePresentationComplex_piOne
  have hnotsc : ¬ SimplyConnectedSpace ThreePresentationComplex := by
    intro hsc
    letI : SimplyConnectedSpace ThreePresentationComplex := hsc
    obtain ⟨e⟩ := hpi
    have htriv : Subsingleton (Path.Homotopic.Quotient
        threePresentationBasepoint threePresentationBasepoint) :=
      inferInstance
    have heq : e.symm (Multiplicative.ofAdd (0 : ZMod 3)) =
        e.symm (Multiplicative.ofAdd (1 : ZMod 3)) := htriv.elim _ _
    have hzero : (Multiplicative.ofAdd (0 : ZMod 3)) =
        Multiplicative.ofAdd (1 : ZMod 3) :=
      e.symm.injective heq
    have := congrArg Multiplicative.toAdd hzero
    norm_num at this
  have hcompact : IsCompact (Set.univ : Set KleinBottle) := by
    rw [← Set.image_univ_of_surjective
      (ConstructionTargets.Surfaces.surjective_surfaceQuotient false 2)]
    exact isCompact_univ.image
      (ConstructionTargets.Surfaces.continuous_surfaceQuotient false 2)
  refine ⟨?_, ?_, finite_piOne_no_double_self_cover⟩
  · exact ⟨⟨threePresentationBasepoint⟩,
      pathConnectedSpace_iff_univ.mp hpath, hpi, hnotsc,
      threePresentationComplex_no_connected_double_cover hpi⟩
  · exact ⟨kleinBottle_h2_isZero, hcompact,
      kleinBottle_double_self_cover⟩

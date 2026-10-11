import ConstructionTargets.T97A04FrozenH1Coordinate
import ConstructionTargets.BoundaryTorusOpenCover
import ConstructionTargets.BoundaryTorusMayerVietoris
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.HomotopyEquivHomologySquare

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.T97A04Closure

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.BoundaryTorusH2ConnectingIso
open ConstructionTargets.T97A04FrozenH1Coordinate
open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularExcision

abbrev FrozenTorus :=
  ConstructionTargets.T97A04FrozenH1Coordinate.FrozenTorus

/-- The integral top-class coordinate on the frozen `AddCircle × AddCircle`
torus, transported along the same homeomorphism used by its aligned H₁
coordinate. -/
noncomputable def frozenTorusH2GroupIsoInt :
    SingularHomology 2 (TopCat.of FrozenTorus) ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv
      frozenTorusHomeomorphBoundaryTorus.toHomotopyEquiv 2 ≪≫
    boundaryTorusH2IsoInt

/-- The vertical two-open cover of the frozen torus, transported through the
fixed homeomorphism used to define its integral top-class coordinate. -/
structure FrozenYCover where
  U : Set FrozenTorus
  V : Set FrozenTorus
  U_isOpen : IsOpen U
  V_isOpen : IsOpen V
  union_eq_univ : U ∪ V = Set.univ
  U_eq_preimage :
    U = frozenTorusHomeomorphBoundaryTorus ⁻¹' leftOpen
  V_eq_preimage :
    V = frozenTorusHomeomorphBoundaryTorus ⁻¹' rightOpen

/-- The canonical vertical cover, not merely a homotopy-equivalent cover. -/
noncomputable def frozenYCover : FrozenYCover where
  U := frozenTorusHomeomorphBoundaryTorus ⁻¹' leftOpen
  V := frozenTorusHomeomorphBoundaryTorus ⁻¹' rightOpen
  U_isOpen := leftOpen_isOpen.preimage frozenTorusHomeomorphBoundaryTorus.continuous
  V_isOpen := rightOpen_isOpen.preimage frozenTorusHomeomorphBoundaryTorus.continuous
  union_eq_univ := by
    rw [← Set.preimage_union, leftOpen_union_rightOpen, Set.preimage_univ]
  U_eq_preimage := rfl
  V_eq_preimage := rfl

/-- Restrict a homeomorphism to the preimage of a set. -/
def homeomorphPreimageRestrict {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (s : Set Y) :
    e ⁻¹' s ≃ₜ s where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, by simp only [Set.mem_preimage, e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv y := by ext; exact e.apply_symm_apply y.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The left member of `frozenYCover` is exactly the transported boundary
torus left member. -/
noncomputable def frozenYCoverUHomeomorph :
    frozenYCover.U ≃ₜ leftOpen :=
  (Homeomorph.ofEqSubtypes frozenYCover.U_eq_preimage).trans
    (homeomorphPreimageRestrict frozenTorusHomeomorphBoundaryTorus leftOpen)

/-- The right member of `frozenYCover` is exactly the transported boundary
torus right member. -/
noncomputable def frozenYCoverVHomeomorph :
    frozenYCover.V ≃ₜ rightOpen :=
  (Homeomorph.ofEqSubtypes frozenYCover.V_eq_preimage).trans
    (homeomorphPreimageRestrict frozenTorusHomeomorphBoundaryTorus rightOpen)

theorem frozenYCover_U_mem_iff (x : FrozenTorus) :
    x ∈ frozenYCover.U ↔ frozenTorusHomeomorphBoundaryTorus x ∈ leftOpen :=
  Iff.rfl

theorem frozenYCover_V_mem_iff (x : FrozenTorus) :
    x ∈ frozenYCover.V ↔ frozenTorusHomeomorphBoundaryTorus x ∈ rightOpen :=
  Iff.rfl

theorem frozenYCover_inter_mem_iff (x : FrozenTorus) :
    x ∈ frozenYCover.U ∩ frozenYCover.V ↔
      frozenTorusHomeomorphBoundaryTorus x ∈ leftOpen ∩ rightOpen :=
  Iff.rfl

/-- The cover overlap is transported by the same fixed homeomorphism. -/
noncomputable def frozenYCoverInterHomeomorph :
    (frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus) ≃ₜ
      (leftOpen ∩ rightOpen : Set BoundaryTorus) :=
  (Homeomorph.ofEqSubtypes (by
    ext x
    exact frozenYCover_inter_mem_iff x)).trans
    (homeomorphPreimageRestrict frozenTorusHomeomorphBoundaryTorus
      (leftOpen ∩ rightOpen))

/-- The ambient map carrying the frozen cover to the boundary-torus cover. -/
noncomputable def frozenToBoundary : C(FrozenTorus, BoundaryTorus) :=
  ⟨frozenTorusHomeomorphBoundaryTorus,
    frozenTorusHomeomorphBoundaryTorus.continuous⟩

/-- The inverse ambient map carrying the boundary-torus cover back to the
frozen cover. -/
noncomputable def boundaryToFrozen : C(BoundaryTorus, FrozenTorus) :=
  ⟨frozenTorusHomeomorphBoundaryTorus.symm,
    frozenTorusHomeomorphBoundaryTorus.symm.continuous⟩

theorem frozenToBoundary_mapsTo_U :
    Set.MapsTo frozenToBoundary frozenYCover.U leftOpen :=
  fun _ hx ↦ hx

theorem frozenToBoundary_mapsTo_V :
    Set.MapsTo frozenToBoundary frozenYCover.V rightOpen :=
  fun _ hx ↦ hx

theorem frozenToBoundary_mapsTo_inter :
    Set.MapsTo frozenToBoundary (frozenYCover.U ∩ frozenYCover.V)
      (leftOpen ∩ rightOpen) :=
  fun _ hx ↦ hx

theorem boundaryToFrozen_mapsTo_U :
    Set.MapsTo boundaryToFrozen leftOpen frozenYCover.U := by
  intro x hx
  change frozenTorusHomeomorphBoundaryTorus
      (frozenTorusHomeomorphBoundaryTorus.symm x) ∈ leftOpen
  simpa using hx

theorem boundaryToFrozen_mapsTo_V :
    Set.MapsTo boundaryToFrozen rightOpen frozenYCover.V := by
  intro x hx
  change frozenTorusHomeomorphBoundaryTorus
      (frozenTorusHomeomorphBoundaryTorus.symm x) ∈ rightOpen
  simpa using hx

theorem boundaryToFrozen_mapsTo_inter :
    Set.MapsTo boundaryToFrozen (leftOpen ∩ rightOpen)
      (frozenYCover.U ∩ frozenYCover.V) := by
  intro x hx
  exact ⟨boundaryToFrozen_mapsTo_U hx.1, boundaryToFrozen_mapsTo_V hx.2⟩

@[simp] theorem frozenToBoundary_boundaryToFrozen (x : BoundaryTorus) :
    frozenToBoundary (boundaryToFrozen x) = x :=
  frozenTorusHomeomorphBoundaryTorus.apply_symm_apply x

@[simp] theorem boundaryToFrozen_frozenToBoundary (x : FrozenTorus) :
    boundaryToFrozen (frozenToBoundary x) = x :=
  frozenTorusHomeomorphBoundaryTorus.symm_apply_apply x

/-- The upper-triangular shear of the frozen torus.  Its second coordinate is
fixed, so it preserves the vertical cover literally. -/
def shearY (a b : ℤ) : C(FrozenTorus, FrozenTorus) where
  toFun p := (a • p.1 + b • p.2, p.2)
  continuous_toFun := by fun_prop

@[simp]
theorem shearY_apply (a b : ℤ) (p : FrozenTorus) :
    shearY a b p = (a • p.1 + b • p.2, p.2) :=
  rfl

/-- Circle-product coordinate used to calculate the restricted shear. -/
def frozenTorusCircleProd : FrozenTorus ≃ₜ Circle × Circle :=
  Homeomorph.prodCongr (AddCircle.homeomorphCircle one_ne_zero)
    (AddCircle.homeomorphCircle one_ne_zero)

def circleShearY (a b : ℤ) : C(Circle × Circle, Circle × Circle) :=
  ⟨fun z ↦ (z.1 ^ a * z.2 ^ b, z.2), by fun_prop⟩

theorem frozenTorusCircleProd_shearY (a b : ℤ) (p : FrozenTorus) :
    frozenTorusCircleProd (shearY a b p) =
      circleShearY a b (frozenTorusCircleProd p) := by
  ext <;>
    simp [frozenTorusCircleProd, circleShearY, shearY,
      AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add,
      AddCircle.toCircle_zsmul]

theorem shearY_mem_U (a b : ℤ) {p : FrozenTorus}
    (hp : p ∈ frozenYCover.U) : shearY a b p ∈ frozenYCover.U := by
  rw [frozenYCover_U_mem_iff] at hp ⊢
  simpa [frozenTorusHomeomorphBoundaryTorus, leftOpen] using hp

theorem shearY_mem_V (a b : ℤ) {p : FrozenTorus}
    (hp : p ∈ frozenYCover.V) : shearY a b p ∈ frozenYCover.V := by
  rw [frozenYCover_V_mem_iff] at hp ⊢
  simpa [frozenTorusHomeomorphBoundaryTorus, rightOpen] using hp

theorem shearY_comp (a b c d : ℤ) :
    (shearY a b).comp (shearY c d) = shearY (a * c) (a * d + b) := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · simp only [ContinuousMap.comp_apply, shearY_apply, smul_add, mul_smul, add_smul]
    abel
  · rfl

theorem shearY_three_one_apply (p : FrozenTorus) :
    shearY 3 1 p = ((3 : ℤ) • p.1 + p.2, p.2) := by
  simp only [shearY_apply, one_smul]

theorem shearY_one_neg_one_apply (p : FrozenTorus) :
    shearY 1 (-1) p = (p.1 - p.2, p.2) := by
  simp only [shearY_apply, one_smul, neg_smul, sub_eq_add_neg]

theorem shearY_one_zero_apply (p : FrozenTorus) :
    shearY 1 0 p = p := by
  rcases p with ⟨x, y⟩
  simp

private abbrev closureChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

private theorem shearY_mapsTo_inter (a b : ℤ) :
    Set.MapsTo (shearY a b)
      (frozenYCover.U ∩ frozenYCover.V)
      (frozenYCover.U ∩ frozenYCover.V) :=
  fun _ hp ↦ ⟨shearY_mem_U a b hp.1, shearY_mem_V a b hp.2⟩

/-- The transported two-circle integral coordinate on the frozen vertical
cover overlap. -/
noncomputable def frozenOverlapH1IsoIntBiprod :
    SingularHomology 1
        (TopCat.of (frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus)) ≅
      (AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ) :=
  singularHomologyIsoOfHomotopyEquiv
      frozenYCoverInterHomeomorph.toHomotopyEquiv 1 ≪≫
    overlapH1IsoIntBiprod

/-- The restriction of the shear to the frozen cover overlap. -/
def shearYOverlap (a b : ℤ) :
    C((frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus),
      (frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus)) where
  toFun p := ⟨shearY a b p.1, shearY_mapsTo_inter a b p.2⟩
  continuous_toFun :=
    (shearY a b).continuous.comp continuous_subtype_val |>.subtype_mk _

@[simp] theorem shearYOverlap_apply (a b : ℤ)
    (p : (frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus)) :
    (shearYOverlap a b p : FrozenTorus) = shearY a b p.1 := rfl

/-- Multiplication by the same integer on the two overlap-circle
coordinates; this is the target normal form for blueprint node B6. -/
noncomputable def overlapScalar (a : ℤ) :
    ((AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ)) ⟶
      ((AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ)) :=
  biprod.map (a • 𝟙 (AddCommGrpCat.of ℤ)) (a • 𝟙 (AddCommGrpCat.of ℤ))

/-- The restricted shear transported to the boundary-torus overlap. -/
noncomputable def boundaryOverlapShear (a b : ℤ) :
    C(Overlap, Overlap) :=
  (⟨frozenYCoverInterHomeomorph,
      frozenYCoverInterHomeomorph.continuous⟩ :
    C((frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus), Overlap)).comp
    ((shearYOverlap a b).comp
      (⟨frozenYCoverInterHomeomorph.symm,
          frozenYCoverInterHomeomorph.symm.continuous⟩ :
        C(Overlap,
          (frozenYCover.U ∩ frozenYCover.V : Set FrozenTorus))))

/-- The overlap shear in the fixed disjoint-two-circle model used by the
Mayer--Vietoris coordinate. -/
noncomputable def twoCircleOverlapShear (a b : ℤ) :
    C(Circle ⊕ Circle, Circle ⊕ Circle) :=
  overlapHomotopyEquivTwoCircles.toFun.comp
    ((boundaryOverlapShear a b).comp
      overlapHomotopyEquivTwoCircles.invFun)

theorem twoCircleOverlapShear_eq_transport (a b : ℤ) :
    twoCircleOverlapShear a b =
      overlapHomotopyEquivTwoCircles.toFun.comp
        ((boundaryOverlapShear a b).comp
          overlapHomotopyEquivTwoCircles.invFun) := rfl

theorem overlapHomotopyEquivTwoCircles_inv_fst (q : Circle ⊕ Circle) :
    (overlapHomotopyEquivTwoCircles.invFun q).1.1 = twoCircleFold q := by
  have h := congrArg (fun f : C(Circle ⊕ Circle, Circle) ↦ f q)
    leftOverlapComposite_eq_fold
  simpa [leftOverlapComposite, leftPieceRetraction, overlapToLeft,
    twoCirclesToOverlap, leftOpenHomotopyEquivCircle,
    leftOpenProductHomeomorph, circleTimesNorthComplementHomotopyEquiv] using h

theorem twoCircleFold_boolTimesCircle (p : Bool × Circle) :
    twoCircleFold (boolTimesCircleHomeomorphTwoCircles p) = p.2 := by
  rcases p with ⟨b, z⟩
  cases b <;> rfl

theorem overlapHomotopyEquivTwoCircles_fold (p : Overlap) :
    twoCircleFold (overlapHomotopyEquivTwoCircles.toFun p) = p.1.1 := by
  change twoCircleFold (boolTimesCircleHomeomorphTwoCircles (_, p.1.1)) = p.1.1
  exact twoCircleFold_boolTimesCircle _

/-- The product-circle coordinate of a point in the boundary-torus overlap,
using the same frozen-torus transport as the restricted shear. -/
noncomputable def overlapCircleProd (p : Overlap) : Circle × Circle :=
  frozenTorusCircleProd (frozenYCoverInterHomeomorph.symm p).1

theorem overlapCircleProd_fst (p : Overlap) :
    (overlapCircleProd p).1 = p.1.1 := by
  have h := congrArg (fun q : Overlap ↦ q.1.1)
    (frozenYCoverInterHomeomorph.apply_symm_apply p)
  simpa [overlapCircleProd, frozenTorusCircleProd,
    frozenYCoverInterHomeomorph, homeomorphPreimageRestrict,
    frozenTorusHomeomorphBoundaryTorus] using h

theorem boundaryOverlapShear_fst (a b : ℤ) (p : Overlap) :
    (boundaryOverlapShear a b p).1.1 =
      (overlapCircleProd p).1 ^ a * (overlapCircleProd p).2 ^ b := by
  have h := congrArg Prod.fst
    (frozenTorusCircleProd_shearY a b
      (frozenYCoverInterHomeomorph.symm p).1)
  simpa [boundaryOverlapShear, shearYOverlap, overlapCircleProd,
    circleShearY, frozenYCoverInterHomeomorph,
    homeomorphPreimageRestrict] using h

/-- The boundary-overlap shear fixes the second boundary-torus coordinate,
which determines the overlap component. -/
theorem boundaryOverlapShear_snd (a b : ℤ) (p : Overlap) :
    (boundaryOverlapShear a b p).1.2 = p.1.2 := by
  have h := congrArg (fun q : Overlap ↦ q.1.2)
    (frozenYCoverInterHomeomorph.apply_symm_apply p)
  simpa [boundaryOverlapShear, shearYOverlap, shearY,
    frozenYCoverInterHomeomorph, homeomorphPreimageRestrict,
    frozenTorusHomeomorphBoundaryTorus] using h

/-- Consequently the orthogonal-sphere component used to split the overlap
into two circles is unchanged by the shear. -/
theorem overlapOrthogonalCoordinate_shear (a b : ℤ) (p : Overlap) :
    (overlapHomotopyEquivOrthogonalSphereTimesCircle.toFun
      (boundaryOverlapShear a b p)).1 =
    (overlapHomotopyEquivOrthogonalSphereTimesCircle.toFun p).1 := by
  dsimp [overlapHomotopyEquivOrthogonalSphereTimesCircle,
    overlapProductHomeomorph]
  change (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomotopyEquivOrthogonalSphere
      northPoleVector norm_northPoleVector).toFun
        ⟨(boundaryOverlapShear a b p).1.2, _⟩ =
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomotopyEquivOrthogonalSphere
      northPoleVector norm_northPoleVector).toFun ⟨p.1.2, _⟩
  apply congrArg
  apply Subtype.ext
  exact boundaryOverlapShear_snd a b p

/-- The discrete component label of the disjoint two-circle model. -/
def twoCircleBranch (q : Circle ⊕ Circle) : Bool :=
  (boolTimesCircleHomeomorphTwoCircles.symm q).1

theorem twoCircleBranch_boolTimesCircle (p : Bool × Circle) :
    twoCircleBranch (boolTimesCircleHomeomorphTwoCircles p) = p.1 := by
  exact congrArg Prod.fst
    (boolTimesCircleHomeomorphTwoCircles.symm_apply_apply p)

theorem overlapOrthogonalRetraction (s :
    ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.UnitSphere
      ((ℝ ∙ northPoleVector)ᗮ)) :
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomotopyEquivOrthogonalSphere
        northPoleVector norm_northPoleVector).toFun
      ((ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomotopyEquivOrthogonalSphere
        northPoleVector norm_northPoleVector).invFun s) = s := by
  change ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize _
      ((ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomeomorphPuncturedOrthogonal
        northPoleVector norm_northPoleVector)
        ((ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomeomorphPuncturedOrthogonal
          northPoleVector norm_northPoleVector).symm
          (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereInclusion _ s))) = s
  rw [Homeomorph.apply_symm_apply]
  exact ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize_unitSphereInclusion _ s

/-- The overlap equivalence followed by its chosen inverse preserves the
orthogonal-sphere coordinate exactly. -/
theorem overlapModelOrthogonalRetraction
    (s : ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.UnitSphere
      ((ℝ ∙ northPoleVector)ᗮ)) (z : Circle) :
    (overlapHomotopyEquivOrthogonalSphereTimesCircle.toFun
      (overlapHomotopyEquivOrthogonalSphereTimesCircle.invFun (s, z))).1 = s := by
  change (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomotopyEquivOrthogonalSphere
      northPoleVector norm_northPoleVector).toFun
    ((ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.twoPoleComplementHomotopyEquivOrthogonalSphere
      northPoleVector norm_northPoleVector).invFun s) = s
  exact overlapOrthogonalRetraction s

theorem twoCircleBranch_overlap_toFun (p : Overlap) :
    twoCircleBranch (overlapHomotopyEquivTwoCircles.toFun p) =
      orthogonalSphereHomeomorphBool
        (overlapHomotopyEquivOrthogonalSphereTimesCircle.toFun p).1 := by
  change twoCircleBranch (boolTimesCircleHomeomorphTwoCircles
      ((orthogonalSphereHomeomorphBool.prodCongr (Homeomorph.refl Circle))
        (overlapHomotopyEquivOrthogonalSphereTimesCircle.toFun p))) = _
  rw [twoCircleBranch_boolTimesCircle]
  rfl

theorem overlapTwoCircles_inv_model (q : Circle ⊕ Circle) :
    overlapHomotopyEquivTwoCircles.invFun q =
      overlapHomotopyEquivOrthogonalSphereTimesCircle.invFun
        ((orthogonalSphereHomeomorphBool.prodCongr (Homeomorph.refl Circle)).symm
          (boolTimesCircleHomeomorphTwoCircles.symm q)) := rfl

theorem twoCircleBranch_retraction (q : Circle ⊕ Circle) :
    twoCircleBranch (overlapHomotopyEquivTwoCircles.toFun
      (overlapHomotopyEquivTwoCircles.invFun q)) = twoCircleBranch q := by
  rw [twoCircleBranch_overlap_toFun, overlapTwoCircles_inv_model]
  rw [overlapModelOrthogonalRetraction]
  simp [twoCircleBranch]

/-- The transported overlap shear preserves the discrete circle summand. -/
theorem twoCircleOverlapShear_branch (a b : ℤ) (q : Circle ⊕ Circle) :
    twoCircleBranch (twoCircleOverlapShear a b q) = twoCircleBranch q := by
  rw [twoCircleOverlapShear, ContinuousMap.comp_apply,
    ContinuousMap.comp_apply, twoCircleBranch_overlap_toFun]
  calc
    _ = orthogonalSphereHomeomorphBool
        (overlapHomotopyEquivOrthogonalSphereTimesCircle.toFun
          (overlapHomotopyEquivTwoCircles.invFun q)).1 := by
      exact congrArg orthogonalSphereHomeomorphBool
        (overlapOrthogonalCoordinate_shear a b
          (overlapHomotopyEquivTwoCircles.invFun q))
    _ = twoCircleBranch
        (overlapHomotopyEquivTwoCircles.toFun
          (overlapHomotopyEquivTwoCircles.invFun q)) :=
      (twoCircleBranch_overlap_toFun _).symm
    _ = _ := twoCircleBranch_retraction q

theorem twoCircleBranch_inl (z : Circle) :
    twoCircleBranch (Sum.inl z) = false := by
  dsimp [twoCircleBranch, boolTimesCircleHomeomorphTwoCircles]
  change Equiv.boolEquivPUnitSumPUnit.symm (Sum.inl PUnit.unit) = false
  rfl

theorem twoCircleBranch_inr (z : Circle) :
    twoCircleBranch (Sum.inr z) = true := by
  dsimp [twoCircleBranch, boolTimesCircleHomeomorphTwoCircles]
  change Equiv.boolEquivPUnitSumPUnit.symm (Sum.inr PUnit.unit) = true
  rfl

theorem twoCircleBranchFold_reconstruct (q : Circle ⊕ Circle) :
    boolTimesCircleHomeomorphTwoCircles
      (twoCircleBranch q, twoCircleFold q) = q := by
  let p := boolTimesCircleHomeomorphTwoCircles.symm q
  have hq : boolTimesCircleHomeomorphTwoCircles p = q :=
    boolTimesCircleHomeomorphTwoCircles.apply_symm_apply q
  rw [← hq, twoCircleBranch_boolTimesCircle,
    twoCircleFold_boolTimesCircle]

theorem twoCircleOverlapShear_fold_apply (a b : ℤ) (q : Circle ⊕ Circle) :
    twoCircleFold (twoCircleOverlapShear a b q) =
      twoCircleFold q ^ a *
        (overlapCircleProd (overlapHomotopyEquivTwoCircles.invFun q)).2 ^ b := by
  rw [twoCircleOverlapShear, ContinuousMap.comp_apply,
    ContinuousMap.comp_apply, overlapHomotopyEquivTwoCircles_fold,
    boundaryOverlapShear_fst, overlapCircleProd_fst,
    overlapHomotopyEquivTwoCircles_inv_fst]

noncomputable def leftOverlapCircleConstant : Circle :=
  (overlapCircleProd (overlapHomotopyEquivTwoCircles.invFun (Sum.inl 1))).2

noncomputable def rightOverlapCircleConstant : Circle :=
  (overlapCircleProd (overlapHomotopyEquivTwoCircles.invFun (Sum.inr 1))).2

theorem overlapCircleProd_inv_inl_snd (z : Circle) :
    (overlapCircleProd
      (overlapHomotopyEquivTwoCircles.invFun (Sum.inl z))).2 =
        leftOverlapCircleConstant := by
  rfl

theorem overlapCircleProd_inv_inr_snd (z : Circle) :
    (overlapCircleProd
      (overlapHomotopyEquivTwoCircles.invFun (Sum.inr z))).2 =
        rightOverlapCircleConstant := by
  rfl

/-- The left overlap-circle summand followed by the transported shear. -/
def circleSumInl : C(Circle, Circle ⊕ Circle) :=
  ⟨Sum.inl, continuous_inl⟩

def circleSumInr : C(Circle, Circle ⊕ Circle) :=
  ⟨Sum.inr, continuous_inr⟩

def twoCircleOverlapShearLeft (a b : ℤ) : C(Circle, Circle ⊕ Circle) :=
  (twoCircleOverlapShear a b).comp circleSumInl

/-- The right overlap-circle summand followed by the transported shear. -/
def twoCircleOverlapShearRight (a b : ℤ) : C(Circle, Circle ⊕ Circle) :=
  (twoCircleOverlapShear a b).comp circleSumInr

@[simp] theorem twoCircleOverlapShearLeft_apply (a b : ℤ) (z : Circle) :
    twoCircleOverlapShearLeft a b z = twoCircleOverlapShear a b (Sum.inl z) := rfl

@[simp] theorem twoCircleOverlapShearRight_apply (a b : ℤ) (z : Circle) :
    twoCircleOverlapShearRight a b z = twoCircleOverlapShear a b (Sum.inr z) := rfl

/-- Functorial factorization of the left restricted shear on homology. -/
theorem twoCircleOverlapShearLeft_H1 (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          circleSumInl) 1 ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShear a b)) 1 =
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        (twoCircleOverlapShearLeft a b)) 1 := by
  rw [← HomologicalComplex.homologyMap_comp]
  dsimp only [ConstructionTargets.SingularSubdivision.singularPostcomposition]
  rw [← Functor.map_comp]
  rfl

/-- Functorial factorization of the right restricted shear on homology. -/
theorem twoCircleOverlapShearRight_H1 (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          circleSumInr) 1 ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShear a b)) 1 =
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        (twoCircleOverlapShearRight a b)) 1 := by
  rw [← HomologicalComplex.homologyMap_comp]
  dsimp only [ConstructionTargets.SingularSubdivision.singularPostcomposition]
  rw [← Functor.map_comp]
  rfl

/-- The circle coordinate of the transported left overlap summand. -/
def twoCircleOverlapShearLeftFold (a b : ℤ) : C(Circle, Circle) :=
  twoCircleFold.comp (twoCircleOverlapShearLeft a b)

/-- The circle coordinate of the transported right overlap summand. -/
def twoCircleOverlapShearRightFold (a b : ℤ) : C(Circle, Circle) :=
  twoCircleFold.comp (twoCircleOverlapShearRight a b)

theorem twoCircleOverlapShearLeft_eq_inl_fold (a b : ℤ) :
    twoCircleOverlapShearLeft a b =
      circleSumInl.comp (twoCircleOverlapShearLeftFold a b) := by
  ext z
  let q := twoCircleOverlapShear a b (Sum.inl z)
  have hb : twoCircleBranch q = false := by
    exact (twoCircleOverlapShear_branch a b (Sum.inl z)).trans
      (twoCircleBranch_inl z)
  have hq := twoCircleBranchFold_reconstruct q
  rw [hb] at hq
  have hi := twoCircleBranchFold_reconstruct (Sum.inl (twoCircleFold q))
  rw [twoCircleBranch_inl, twoCircleFold_inl] at hi
  exact hq.symm.trans hi

theorem twoCircleOverlapShearRight_eq_inr_fold (a b : ℤ) :
    twoCircleOverlapShearRight a b =
      circleSumInr.comp (twoCircleOverlapShearRightFold a b) := by
  ext z
  let q := twoCircleOverlapShear a b (Sum.inr z)
  have hb : twoCircleBranch q = true := by
    exact (twoCircleOverlapShear_branch a b (Sum.inr z)).trans
      (twoCircleBranch_inr z)
  have hq := twoCircleBranchFold_reconstruct q
  rw [hb] at hq
  have hi := twoCircleBranchFold_reconstruct (Sum.inr (twoCircleFold q))
  rw [twoCircleBranch_inr, twoCircleFold_inr] at hi
  exact hq.symm.trans hi

/-- Homology of the left restricted shear factors through its circle fold. -/
theorem twoCircleOverlapShearLeft_H1_eq_fold_inl (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShearLeft a b)) 1 =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShearLeftFold a b)) 1 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            circleSumInl) 1 := by
  rw [twoCircleOverlapShearLeft_eq_inl_fold, ← HomologicalComplex.homologyMap_comp]
  dsimp only [ConstructionTargets.SingularSubdivision.singularPostcomposition]
  rw [← Functor.map_comp]
  rfl

/-- Homology of the right restricted shear factors through its circle fold. -/
theorem twoCircleOverlapShearRight_H1_eq_fold_inr (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShearRight a b)) 1 =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShearRightFold a b)) 1 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            circleSumInr) 1 := by
  rw [twoCircleOverlapShearRight_eq_inr_fold, ← HomologicalComplex.homologyMap_comp]
  dsimp only [ConstructionTargets.SingularSubdivision.singularPostcomposition]
  rw [← Functor.map_comp]
  rfl

/-- The integer power map which remains on either overlap component after
the constant translation in the shear is removed. -/
def circleZPow (a : ℤ) : C(Circle, Circle) :=
  ⟨fun z ↦ z ^ a, by fun_prop⟩

/-- A translated integer power map on the circle. -/
def circleAffine (a : ℤ) (c : Circle) : C(Circle, Circle) :=
  ⟨fun z ↦ c * z ^ a, by fun_prop⟩

theorem twoCircleOverlapShearLeftFold_eq_affine (a b : ℤ) :
    twoCircleOverlapShearLeftFold a b =
      circleAffine a (leftOverlapCircleConstant ^ b) := by
  ext z
  rw [twoCircleOverlapShearLeftFold, ContinuousMap.comp_apply,
    twoCircleOverlapShearLeft_apply, twoCircleOverlapShear_fold_apply,
    twoCircleFold_inl, overlapCircleProd_inv_inl_snd]
  simp [circleAffine, mul_comm]

theorem twoCircleOverlapShearRightFold_eq_affine (a b : ℤ) :
    twoCircleOverlapShearRightFold a b =
      circleAffine a (rightOverlapCircleConstant ^ b) := by
  ext z
  rw [twoCircleOverlapShearRightFold, ContinuousMap.comp_apply,
    twoCircleOverlapShearRight_apply, twoCircleOverlapShear_fold_apply,
    twoCircleFold_inr, overlapCircleProd_inv_inr_snd]
  simp [circleAffine, mul_comm]

theorem twoCircleOverlapShearLeftFold_H1 (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShearLeft a b)) 1 ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          twoCircleFold) 1 =
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        (twoCircleOverlapShearLeftFold a b)) 1 := by
  rw [← HomologicalComplex.homologyMap_comp]
  dsimp only [ConstructionTargets.SingularSubdivision.singularPostcomposition]
  rw [← Functor.map_comp]
  rfl

theorem twoCircleOverlapShearRightFold_H1 (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShearRight a b)) 1 ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          twoCircleFold) 1 =
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        (twoCircleOverlapShearRightFold a b)) 1 := by
  rw [← HomologicalComplex.homologyMap_comp]
  dsimp only [ConstructionTargets.SingularSubdivision.singularPostcomposition]
  rw [← Functor.map_comp]
  rfl

/-- Translation does not affect the degree of an integer power map. -/
def circleAffineHomotopy (a : ℤ) (c : Circle) :
    ContinuousMap.Homotopy (circleZPow a) (circleAffine a c) where
  toFun tz := Circle.exp ((tz.1 : ℝ) * Complex.arg (c : ℂ)) * tz.2 ^ a
  continuous_toFun := by fun_prop
  map_zero_left z := by simp [circleZPow]
  map_one_left z := by simp [circleAffine, Circle.exp_arg]

theorem circleAffine_H1_eq_zpow (a : ℤ) (c : Circle) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (circleAffine a c)) 1 =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (circleZPow a)) 1 := by
  let H := circleAffineHomotopy a c
  exact (singularHomology_map_eq_of_topCatHomotopy
    (continuousMapHomotopyCylinder H)
    (continuousMapHomotopyCylinder_zero H)
    (continuousMapHomotopyCylinder_one H) 1).symm

theorem twoCircleOverlapShearLeftFold_H1_eq_zpow (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShearLeftFold a b)) 1 =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (circleZPow a)) 1 := by
  rw [twoCircleOverlapShearLeftFold_eq_affine,
    circleAffine_H1_eq_zpow]

theorem twoCircleOverlapShearRightFold_H1_eq_zpow (a b : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (twoCircleOverlapShearRightFold a b)) 1 =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (circleZPow a)) 1 := by
  rw [twoCircleOverlapShearRightFold_eq_affine,
    circleAffine_H1_eq_zpow]

open ConstructionTargets.CircleUniversalCover

theorem liftBasedLoop_circleZPow (a : ℤ) (gamma : Path (1 : Circle) 1) :
    liftBasedLoop (gamma.map (circleZPow a).continuous)
        (by simp [circleZPow]) =
      ⟨fun t ↦ a • liftBasedLoop gamma gamma.source t,
        (liftBasedLoop gamma gamma.source).continuous.const_smul a⟩ := by
  symm
  apply (circleCover_isCoveringMap.eq_liftPath_iff' _).2
  constructor
  · funext t
    change Circle.exp (a • liftBasedLoop gamma gamma.source t) = (gamma t) ^ a
    rw [Circle.exp_zsmul]
    exact congrArg (fun z : Circle ↦ z ^ a)
      (congrFun (circleCover_comp_liftBasedLoop gamma gamma.source) t)
  · simp

theorem liftBasedLoopEndpointInteger_circleZPow (a : ℤ)
    (gamma : Path (1 : Circle) 1) :
    liftBasedLoopEndpointInteger (gamma.map (circleZPow a).continuous)
        (by simp [circleZPow]) (by simp [circleZPow]) =
      a * liftBasedLoopEndpointInteger gamma gamma.source gamma.target := by
  apply period_integer_unique
    (liftBasedLoopEndpointInteger_spec
      (gamma.map (circleZPow a).continuous)
      (by simp [circleZPow]) (by simp [circleZPow]))
  rw [liftBasedLoop_circleZPow]
  simp only [ContinuousMap.coe_mk]
  rw [← liftBasedLoopEndpointInteger_spec]
  rw [mul_smul]

def circleZPowBasedPath (a : ℤ) (gamma : Path (1 : Circle) 1) :
    Path (1 : Circle) 1 :=
  (gamma.map (circleZPow a).continuous).cast
    (by simp [circleZPow]) (by simp [circleZPow])

def circleZPowPi1Map (a : ℤ) :
    FundamentalGroup Circle 1 →* FundamentalGroup Circle 1 :=
  FundamentalGroup.mapOfEq (circleZPow a) (by simp [circleZPow])

theorem circleZPowPi1Map_mk (a : ℤ) (gamma : Path (1 : Circle) 1) :
    circleZPowPi1Map a (Path.Homotopic.Quotient.mk gamma) =
      Path.Homotopic.Quotient.mk (circleZPowBasedPath a gamma) := by
  rw [circleZPowPi1Map, FundamentalGroup.mapOfEq_apply]
  rfl

theorem circleZPow_fundamentalGroup_coordinate (a : ℤ)
    (p : FundamentalGroup Circle 1) :
    (circleFundamentalGroupMulEquivInt (circleZPowPi1Map a p)).toAdd =
      a * (circleFundamentalGroupMulEquivInt p).toAdd := by
  induction p using Path.Homotopic.Quotient.ind with
  | _ gamma =>
      rw [circleZPowPi1Map_mk]
      change liftBasedLoopEndpointInteger (circleZPowBasedPath a gamma)
          (circleZPowBasedPath a gamma).source
          (circleZPowBasedPath a gamma).target =
        a * liftBasedLoopEndpointInteger gamma gamma.source gamma.target
      simpa [circleZPowBasedPath] using
        liftBasedLoopEndpointInteger_circleZPow a gamma

theorem circleZPowPi1Map_eq_zpow (a : ℤ)
    (p : FundamentalGroup Circle 1) : circleZPowPi1Map a p = p ^ a := by
  apply circleFundamentalGroupMulEquivInt.injective
  apply Multiplicative.toAdd.injective
  rw [circleZPow_fundamentalGroup_coordinate]
  simp

open ConstructionTargets.DegreeOneHurewiczMap

theorem fundamentalGroupH1Hom_circleZPowPi1Map (a : ℤ)
    (p : FundamentalGroup Circle 1) :
    fundamentalGroupH1Hom 1 (circleZPowPi1Map a p) =
      fundamentalGroupH1Hom (circleZPow a 1)
        (FundamentalGroup.map (circleZPow a) 1 p) := by
  induction p using Path.Homotopic.Quotient.ind with
  | _ gamma =>
      rw [circleZPowPi1Map_mk]
      change Multiplicative.ofAdd
          (basedLoopH1Element (circleZPowBasedPath a gamma)) =
        Multiplicative.ofAdd
          (basedLoopH1Element (gamma.map (circleZPow a).continuous))
      congr 2

open ConstructionTargets.DegreeOneHurewiczSurjective

theorem circleZPow_H1_apply (a : ℤ)
    (x : ConstructionTargets.DegreeOneHurewiczMap.IntegralH1 Circle) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (circleZPow a)) 1 x = a • x := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using h)
  obtain ⟨p, hp⟩ := fundamentalGroupH1Hom_surjective (1 : Circle)
    (Multiplicative.ofAdd x)
  have hnat := fundamentalGroupH1Hom_naturality (circleZPow a) 1 p
  rw [← fundamentalGroupH1Hom_circleZPowPi1Map,
    circleZPowPi1Map_eq_zpow, map_zpow, hp] at hnat
  exact Multiplicative.ofAdd.injective hnat

theorem circleZPow_H1 (a : ℤ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (circleZPow a)) 1 =
      a • 𝟙 (SingularHomology 1 (TopCat.of Circle)) := by
  ext x
  exact circleZPow_H1_apply a x

/-- The pure power calculation in the exact integral circle coordinate used
by the overlap biproduct. -/
theorem circleZPow_H1_coordinate (a : ℤ) :
    circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (circleZPow a)) 1 ≫
        circleH1GroupIsoInt.hom =
      a • 𝟙 (AddCommGrpCat.of ℤ) := by
  rw [circleZPow_H1]
  change
    (circleH1GroupIsoInt.inv ≫
        (a • 𝟙 (SingularHomology 1 (TopCat.of Circle)))) ≫
      circleH1GroupIsoInt.hom = _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.comp_id, Iso.inv_hom_id]

theorem twoCircleOverlapShearLeftFold_H1_coordinate (a b : ℤ) :
    circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShearLeftFold a b)) 1 ≫
        circleH1GroupIsoInt.hom =
      a • 𝟙 (AddCommGrpCat.of ℤ) := by
  rw [twoCircleOverlapShearLeftFold_H1_eq_zpow,
    circleZPow_H1_coordinate]

theorem twoCircleOverlapShearRightFold_H1_coordinate (a b : ℤ) :
    circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShearRightFold a b)) 1 ≫
        circleH1GroupIsoInt.hom =
      a • 𝟙 (AddCommGrpCat.of ℤ) := by
  rw [twoCircleOverlapShearRightFold_H1_eq_zpow,
    circleZPow_H1_coordinate]

private noncomputable def shearYIntersectionMap (a b : ℤ) :=
  (ambientIntersectionRangeChainsIso frozenYCover.U frozenYCover.V).inv ≫
    closureChains.map
      (coverRangeMap
        (frozenYCover.U ∩ frozenYCover.V)
        (frozenYCover.U ∩ frozenYCover.V)
        (shearY a b) (shearY_mapsTo_inter a b)) ≫
    (ambientIntersectionRangeChainsIso frozenYCover.U frozenYCover.V).hom

private theorem intersectionChainsIso_hom_comp_left :
    (ambientIntersectionRangeChainsIso frozenYCover.U frozenYCover.V).hom ≫
        closureChains.map (subcomplexIntersectionToLeft
          (ambientSubspaceRange frozenYCover.U)
          (ambientSubspaceRange frozenYCover.V)) =
      closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_left) :=
  ambientIntersectionRangeChainsIso_hom_comp_left _ _

private theorem intersectionChainsIso_hom_comp_right :
    (ambientIntersectionRangeChainsIso frozenYCover.U frozenYCover.V).hom ≫
        closureChains.map (subcomplexIntersectionToRight
          (ambientSubspaceRange frozenYCover.U)
          (ambientSubspaceRange frozenYCover.V)) =
      closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_right) :=
  ambientIntersectionRangeChainsIso_hom_comp_right _ _

private theorem intersectionChainsIso_inv_comp_left :
    (ambientIntersectionRangeChainsIso frozenYCover.U frozenYCover.V).inv ≫
        closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_left) =
      closureChains.map (subcomplexIntersectionToLeft
        (ambientSubspaceRange frozenYCover.U)
        (ambientSubspaceRange frozenYCover.V)) := by
  rw [← intersectionChainsIso_hom_comp_left, Iso.inv_hom_id_assoc]

private theorem intersectionChainsIso_inv_comp_right :
    (ambientIntersectionRangeChainsIso frozenYCover.U frozenYCover.V).inv ≫
        closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_right) =
      closureChains.map (subcomplexIntersectionToRight
        (ambientSubspaceRange frozenYCover.U)
        (ambientSubspaceRange frozenYCover.V)) := by
  rw [← intersectionChainsIso_hom_comp_right, Iso.inv_hom_id_assoc]

private theorem shearY_inter_left_chain (a b : ℤ) :
    closureChains.map
        (coverRangeMap
          (frozenYCover.U ∩ frozenYCover.V)
          (frozenYCover.U ∩ frozenYCover.V)
          (shearY a b) (shearY_mapsTo_inter a b)) ≫
      closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_left) =
    closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_left) ≫
      closureChains.map
        (coverRangeMap frozenYCover.U frozenYCover.U (shearY a b)
          (fun _ hp ↦ shearY_mem_U a b hp)) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    coverRangeMap_inter_left frozenYCover.U frozenYCover.V
      frozenYCover.U frozenYCover.V (shearY a b)
      (fun _ hp ↦ shearY_mem_U a b hp)
      (fun _ hp ↦ shearY_mem_V a b hp)]

private theorem shearY_inter_right_chain (a b : ℤ) :
    closureChains.map
        (coverRangeMap
          (frozenYCover.U ∩ frozenYCover.V)
          (frozenYCover.U ∩ frozenYCover.V)
          (shearY a b) (shearY_mapsTo_inter a b)) ≫
      closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_right) =
    closureChains.map (ambientSubspaceRangeInclusion Set.inter_subset_right) ≫
      closureChains.map
        (coverRangeMap frozenYCover.V frozenYCover.V (shearY a b)
          (fun _ hp ↦ shearY_mem_V a b hp)) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    coverRangeMap_inter_right frozenYCover.U frozenYCover.V
      frozenYCover.U frozenYCover.V (shearY a b)
      (fun _ hp ↦ shearY_mem_U a b hp)
      (fun _ hp ↦ shearY_mem_V a b hp)]

private theorem shearYIntersectionMap_comp_left (a b : ℤ) :
    shearYIntersectionMap a b ≫
        closureChains.map (subcomplexIntersectionToLeft
          (ambientSubspaceRange frozenYCover.U)
          (ambientSubspaceRange frozenYCover.V)) =
      closureChains.map (subcomplexIntersectionToLeft
          (ambientSubspaceRange frozenYCover.U)
          (ambientSubspaceRange frozenYCover.V)) ≫
        closureChains.map
          (coverRangeMap frozenYCover.U frozenYCover.U (shearY a b)
            (fun _ hp ↦ shearY_mem_U a b hp)) := by
  dsimp [shearYIntersectionMap]
  slice_lhs 3 4 => rw [intersectionChainsIso_hom_comp_left]
  slice_lhs 2 3 => rw [shearY_inter_left_chain]
  slice_lhs 1 2 => rw [intersectionChainsIso_inv_comp_left]

private theorem shearYIntersectionMap_comp_right (a b : ℤ) :
    shearYIntersectionMap a b ≫
        closureChains.map (subcomplexIntersectionToRight
          (ambientSubspaceRange frozenYCover.U)
          (ambientSubspaceRange frozenYCover.V)) =
      closureChains.map (subcomplexIntersectionToRight
          (ambientSubspaceRange frozenYCover.U)
          (ambientSubspaceRange frozenYCover.V)) ≫
        closureChains.map
          (coverRangeMap frozenYCover.V frozenYCover.V (shearY a b)
            (fun _ hp ↦ shearY_mem_V a b hp)) := by
  dsimp [shearYIntersectionMap]
  slice_lhs 3 4 => rw [intersectionChainsIso_hom_comp_right]
  slice_lhs 2 3 => rw [shearY_inter_right_chain]
  slice_lhs 1 2 => rw [intersectionChainsIso_inv_comp_right]

private noncomputable def shearYPiecesMap (a b : ℤ) :=
  biprod.map
    (closureChains.map
      (coverRangeMap frozenYCover.U frozenYCover.U (shearY a b)
        (fun _ hp ↦ shearY_mem_U a b hp)))
    (closureChains.map
      (coverRangeMap frozenYCover.V frozenYCover.V (shearY a b)
        (fun _ hp ↦ shearY_mem_V a b hp)))

private noncomputable def shearYUnionMap (a b : ℤ) :=
  (subcomplexChains_isPushout
    (leftRange frozenYCover.U) (rightRange frozenYCover.V)).desc
    (closureChains.map
        (coverRangeMap frozenYCover.U frozenYCover.U (shearY a b)
          (fun _ hp ↦ shearY_mem_U a b hp)) ≫
      closureChains.map
        (subcomplexLeftToUnion
          (leftRange frozenYCover.U) (rightRange frozenYCover.V)))
    (closureChains.map
        (coverRangeMap frozenYCover.V frozenYCover.V (shearY a b)
          (fun _ hp ↦ shearY_mem_V a b hp)) ≫
      closureChains.map
        (subcomplexRightToUnion
          (leftRange frozenYCover.U) (rightRange frozenYCover.V)))
    (by
      apply (cancel_epi
        (ambientIntersectionRangeChainsIso
          frozenYCover.U frozenYCover.V).hom).1
      simp only [leftRange, rightRange, ← Category.assoc]
      rw [intersectionChainsIso_hom_comp_left,
        intersectionChainsIso_hom_comp_right]
      rw [← shearY_inter_left_chain, ← shearY_inter_right_chain]
      simp only [Category.assoc]
      congr 1
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

/-- The chain-level morphism of the Boolean-cover Mayer--Vietoris short
complex induced by the cover-preserving upper-triangular shear. -/
noncomputable def shearYShortComplexHom (a b : ℤ) :
    shortComplex frozenYCover.U frozenYCover.V ⟶
      shortComplex frozenYCover.U frozenYCover.V where
  τ₁ := shearYIntersectionMap a b
  τ₂ := shearYPiecesMap a b
  τ₃ := shearYUnionMap a b
  comm₁₂ := by
    dsimp [shortComplex, subcomplexMayerVietorisShortComplex,
      shearYPiecesMap, closureChains]
    apply biprod.hom_ext
    · slice_lhs 2 3 => erw [biprod.lift_fst]
      slice_rhs 2 3 => erw [biprod.map_fst]
      erw [biprod.lift_fst_assoc]
      exact shearYIntersectionMap_comp_left a b
    · slice_lhs 2 3 => erw [biprod.lift_snd]
      slice_rhs 2 3 => erw [biprod.map_snd]
      erw [biprod.lift_snd_assoc]
      simpa only [Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg (shearYIntersectionMap_comp_right a b)
  comm₂₃ := by
    dsimp [shortComplex, subcomplexMayerVietorisShortComplex,
      shearYPiecesMap, closureChains]
    apply biprod.hom_ext'
    · slice_lhs 1 2 => erw [biprod.inl_map]
      erw [Category.assoc, biprod.inl_desc]
      slice_rhs 1 2 => erw [biprod.inl_desc]
      dsimp only [shearYUnionMap]
      exact ((subcomplexChains_isPushout
        (leftRange frozenYCover.U) (rightRange frozenYCover.V)).inl_desc
          _ _ _).symm
    · slice_lhs 1 2 => erw [biprod.inr_map]
      erw [Category.assoc, biprod.inr_desc]
      slice_rhs 1 2 => erw [biprod.inr_desc]
      dsimp only [shearYUnionMap]
      exact ((subcomplexChains_isPushout
        (leftRange frozenYCover.U) (rightRange frozenYCover.V)).inr_desc
          _ _ _).symm

private theorem shearYUnionMap_comp_ambient (a b : ℤ) :
    shearYUnionMap a b ≫
        closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι =
      closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι ≫
        closureChains.map (TopCat.toSSet.map (TopCat.ofHom (shearY a b))) := by
  apply (subcomplexChains_isPushout
    (leftRange frozenYCover.U) (rightRange frozenYCover.V)).hom_ext
  · dsimp only [shearYUnionMap]
    slice_lhs 1 2 => erw [(subcomplexChains_isPushout
      (leftRange frozenYCover.U) (rightRange frozenYCover.V)).inl_desc]
    have hleft :
        coverRangeMap frozenYCover.U frozenYCover.U (shearY a b)
            (fun _ hp ↦ shearY_mem_U a b hp) ≫
            subcomplexLeftToUnion
              (leftRange frozenYCover.U) (rightRange frozenYCover.V) ≫
            (smallSSet frozenYCover.U frozenYCover.V).ι =
          (ambientSubspaceRange frozenYCover.U).ι ≫
            TopCat.toSSet.map (TopCat.ofHom (shearY a b)) := by
      simpa only [Category.assoc] using
        coverRangeMap_comp_ι frozenYCover.U frozenYCover.U (shearY a b) _
    change _ = closureChains.map (subcomplexLeftToUnion
        (leftRange frozenYCover.U) (rightRange frozenYCover.V)) ≫
      closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι ≫ _
    have hιmap : closureChains.map (subcomplexLeftToUnion
          (leftRange frozenYCover.U) (rightRange frozenYCover.V)) ≫
        closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι =
      closureChains.map (ambientSubspaceRange frozenYCover.U).ι := by
      rw [← Functor.map_comp]
      rfl
    rw [← Category.assoc, hιmap]
    simpa only [Functor.map_comp, Category.assoc, leftRange] using
      congrArg closureChains.map hleft
  · dsimp only [shearYUnionMap]
    slice_lhs 1 2 => erw [(subcomplexChains_isPushout
      (leftRange frozenYCover.U) (rightRange frozenYCover.V)).inr_desc]
    have hright :
        coverRangeMap frozenYCover.V frozenYCover.V (shearY a b)
            (fun _ hp ↦ shearY_mem_V a b hp) ≫
            subcomplexRightToUnion
              (leftRange frozenYCover.U) (rightRange frozenYCover.V) ≫
            (smallSSet frozenYCover.U frozenYCover.V).ι =
          (ambientSubspaceRange frozenYCover.V).ι ≫
            TopCat.toSSet.map (TopCat.ofHom (shearY a b)) := by
      simpa only [Category.assoc] using
        coverRangeMap_comp_ι frozenYCover.V frozenYCover.V (shearY a b) _
    change _ = closureChains.map (subcomplexRightToUnion
        (leftRange frozenYCover.U) (rightRange frozenYCover.V)) ≫
      closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι ≫ _
    have hιmap : closureChains.map (subcomplexRightToUnion
          (leftRange frozenYCover.U) (rightRange frozenYCover.V)) ≫
        closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι =
      closureChains.map (ambientSubspaceRange frozenYCover.V).ι := by
      rw [← Functor.map_comp]
      rfl
    rw [← Category.assoc, hιmap]
    simpa only [Functor.map_comp, Category.assoc, rightRange] using
      congrArg closureChains.map hright

/-- The union endpoint of the shear short-complex morphism is the actual map
induced by the shear on production singular homology. -/
theorem shearY_productionUnionMap (a b : ℤ) (n : ℕ) :
    productionUnionMap
        frozenYCover.U frozenYCover.V frozenYCover.U frozenYCover.V
        frozenYCover.U_isOpen frozenYCover.V_isOpen frozenYCover.union_eq_univ
        frozenYCover.U_isOpen frozenYCover.V_isOpen frozenYCover.union_eq_univ
        (shearYShortComplexHom a b) n =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (shearY a b)) n := by
  let unionIso := booleanUnionProductionHomologyIso
    frozenYCover.U frozenYCover.V frozenYCover.U_isOpen
    frozenYCover.V_isOpen frozenYCover.union_eq_univ n
  have hnat :
      HomologicalComplex.homologyMap (shearYUnionMap a b) n ≫ unionIso.hom =
        unionIso.hom ≫ HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY a b)) n := by
    let hOpen : ∀ c, IsOpen (booleanCover frozenYCover.U frozenYCover.V c) := by
      intro c
      cases c
      · exact frozenYCover.V_isOpen
      · exact frozenYCover.U_isOpen
    let hCover : Set.univ ⊆ ⋃ c, booleanCover frozenYCover.U frozenYCover.V c := by
      intro x _
      have hx : x ∈ frozenYCover.U ∪ frozenYCover.V := by
        rw [frozenYCover.union_eq_univ]
        trivial
      rcases hx with hx | hx
      · exact Set.mem_iUnion.2 ⟨true, hx⟩
      · exact Set.mem_iUnion.2 ⟨false, hx⟩
    have hsmall :
        (coverSmallHomologyIso (booleanCover frozenYCover.U frozenYCover.V)
          hOpen hCover n).hom =
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.coverSmallChains.ι
              (booleanCover frozenYCover.U frozenYCover.V)) n := by
      letI := coverSmall_homologyMap_isIso
        (booleanCover frozenYCover.U frozenYCover.V) hOpen hCover n
      exact asIso_hom _
    have hchain :
        shearYUnionMap a b ≫
            ((booleanSmallChainsIso frozenYCover.U frozenYCover.V).hom ≫
              ConstructionTargets.SingularSubdivision.coverSmallChains.ι
                (booleanCover frozenYCover.U frozenYCover.V)) =
          ((booleanSmallChainsIso frozenYCover.U frozenYCover.V).hom ≫
              ConstructionTargets.SingularSubdivision.coverSmallChains.ι
              (booleanCover frozenYCover.U frozenYCover.V)) ≫
            ConstructionTargets.SingularSubdivision.singularPostcomposition
              (shearY a b) := by
      have hamb :
          (booleanSmallChainsIso frozenYCover.U frozenYCover.V).hom ≫
              ConstructionTargets.SingularSubdivision.coverSmallChains.ι
                (booleanCover frozenYCover.U frozenYCover.V) =
            closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι := by
        exact booleanSmallChainsIso_hom_comp_ambient
          frozenYCover.U frozenYCover.V
      calc
        _ = shearYUnionMap a b ≫
            closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι := by
              exact congrArg (fun k ↦ shearYUnionMap a b ≫ k) hamb
        _ = closureChains.map (smallSSet frozenYCover.U frozenYCover.V).ι ≫
            closureChains.map (TopCat.toSSet.map (TopCat.ofHom (shearY a b))) :=
              shearYUnionMap_comp_ambient a b
        _ = _ := by
          rw [ConstructionTargets.SingularSubdivision.ssetChainMap_eq_singularPostcomposition]
          exact congrArg (fun k ↦ k ≫
            ConstructionTargets.SingularSubdivision.singularPostcomposition
              (shearY a b)) hamb.symm
    dsimp [unionIso]
    simp only [booleanUnionProductionHomologyIso, Iso.trans_hom,
      booleanSmallHomologyIso_hom]
    rw [hsmall]
    have hh := congrArg (fun k ↦ HomologicalComplex.homologyMap k n) hchain
    slice_lhs 2 3 => erw [← HomologicalComplex.homologyMap_comp]
    erw [← HomologicalComplex.homologyMap_comp]
    slice_rhs 1 2 => erw [← HomologicalComplex.homologyMap_comp]
    erw [← HomologicalComplex.homologyMap_comp]
    exact hh
  dsimp [productionUnionMap, shearYShortComplexHom]
  calc
    _ = unionIso.inv ≫
        (HomologicalComplex.homologyMap (shearYUnionMap a b) n ≫
          unionIso.hom) := rfl
    _ = unionIso.inv ≫
        (unionIso.hom ≫ HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY a b)) n) := congrArg (fun k ↦ unionIso.inv ≫ k) hnat
    _ = _ := unionIso.inv_hom_id_assoc _

private theorem shearYIntersectionHomology_conjugation (a b : ℤ) :
    (ambientIntersectionRangeHomologyIso frozenYCover.U frozenYCover.V 1).hom ≫
        HomologicalComplex.homologyMap (shearYIntersectionMap a b) 1 ≫
        (ambientIntersectionRangeHomologyIso frozenYCover.U frozenYCover.V 1).inv =
      HomologicalComplex.homologyMap
        (closureChains.map
          (coverRangeMap
            (frozenYCover.U ∩ frozenYCover.V)
            (frozenYCover.U ∩ frozenYCover.V)
            (shearY a b) (shearY_mapsTo_inter a b))) 1 := by
  change HomologicalComplex.homologyMap
      (ambientIntersectionRangeChainsIso
        frozenYCover.U frozenYCover.V).hom 1 ≫
    HomologicalComplex.homologyMap
      ((ambientIntersectionRangeChainsIso
          frozenYCover.U frozenYCover.V).inv ≫ _ ≫
        (ambientIntersectionRangeChainsIso
          frozenYCover.U frozenYCover.V).hom) 1 ≫
    HomologicalComplex.homologyMap
      (ambientIntersectionRangeChainsIso
        frozenYCover.U frozenYCover.V).inv 1 = _
  rw [HomologicalComplex.homologyMap_comp
      (ambientIntersectionRangeChainsIso
        frozenYCover.U frozenYCover.V).inv,
    HomologicalComplex.homologyMap_comp]
  slice_lhs 4 5 =>
    rw [← HomologicalComplex.homologyMap_comp,
      (ambientIntersectionRangeChainsIso
        frozenYCover.U frozenYCover.V).hom_inv_id,
      HomologicalComplex.homologyMap_id]
  simp only [Category.comp_id]
  slice_lhs 1 2 =>
    rw [← HomologicalComplex.homologyMap_comp,
      (ambientIntersectionRangeChainsIso
        frozenYCover.U frozenYCover.V).hom_inv_id,
      HomologicalComplex.homologyMap_id]
  simp

/-- The production intersection endpoint reduces to the range presentation
of the actual restricted shear. -/
theorem shearY_productionIntersectionMap_range (a b : ℤ) :
    productionIntersectionMap
        frozenYCover.U frozenYCover.V frozenYCover.U frozenYCover.V
        (shearYShortComplexHom a b) 1 =
      (ambientRangeProductionHomologyIso
          (frozenYCover.U ∩ frozenYCover.V) 1).inv ≫
        HomologicalComplex.homologyMap
          (closureChains.map
            (coverRangeMap
              (frozenYCover.U ∩ frozenYCover.V)
              (frozenYCover.U ∩ frozenYCover.V)
              (shearY a b) (shearY_mapsTo_inter a b))) 1 ≫
        (ambientRangeProductionHomologyIso
          (frozenYCover.U ∩ frozenYCover.V) 1).hom := by
  simp only [productionIntersectionMap, shearYShortComplexHom,
    booleanIntersectionProductionHomologyIso_inv,
    booleanIntersectionProductionHomologyIso_hom]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (ambientRangeProductionHomologyIso
        (frozenYCover.U ∩ frozenYCover.V) 1).inv ≫ k ≫
      (ambientRangeProductionHomologyIso
        (frozenYCover.U ∩ frozenYCover.V) 1).hom)
    (shearYIntersectionHomology_conjugation a b)

/-- The chosen range restriction of the shear is the actual restricted map
after passing through the canonical range presentation. -/
theorem shearY_coverRangeMap_naturality (a b : ℤ) :
    (ambientSubspaceRangeChainsIso
        (frozenYCover.U ∩ frozenYCover.V)).hom ≫
      ConstructionTargets.SingularSubdivision.singularPostcomposition
        (shearYOverlap a b) =
    closureChains.map
        (coverRangeMap
          (frozenYCover.U ∩ frozenYCover.V)
          (frozenYCover.U ∩ frozenYCover.V)
          (shearY a b) (shearY_mapsTo_inter a b)) ≫
      (ambientSubspaceRangeChainsIso
        (frozenYCover.U ∩ frozenYCover.V)).hom := by
  change closureChains.map _ ≫ closureChains.map _ =
    closureChains.map _ ≫ closureChains.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg closureChains.map
  apply (cancel_mono (TopCat.toSSet.map
    (subspaceInclusion (frozenYCover.U ∩ frozenYCover.V)))).1
  simp only [Category.assoc]
  have hrange :
      (asIso (Subfunctor.toRange (TopCat.toSSet.map
        (subspaceInclusion (frozenYCover.U ∩ frozenYCover.V))))).symm.hom ≫
          TopCat.toSSet.map
            (subspaceInclusion (frozenYCover.U ∩ frozenYCover.V)) =
        (ambientSubspaceRange
          (frozenYCover.U ∩ frozenYCover.V)).ι := by
    exact rangeIso_hom_comp _
  slice_rhs 2 3 => exact hrange
  have hcover := coverRangeMap_comp_ι
    (frozenYCover.U ∩ frozenYCover.V)
    (frozenYCover.U ∩ frozenYCover.V)
    (shearY a b) (shearY_mapsTo_inter a b)
  slice_rhs 1 2 => exact hcover
  rw [← TopCat.toSSet.map_comp]
  have htop :
      TopCat.ofHom (shearYOverlap a b) ≫
          subspaceInclusion (frozenYCover.U ∩ frozenYCover.V) =
        subspaceInclusion (frozenYCover.U ∩ frozenYCover.V) ≫
          TopCat.ofHom (shearY a b) := by
    rfl
  rw [htop, TopCat.toSSet.map_comp, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ TopCat.toSSet.map
    (TopCat.ofHom (shearY a b))) hrange

/-- Thus the production intersection endpoint is the homology map of the
actual overlap restriction. -/
theorem shearY_productionIntersectionMap_eq_overlap (a b : ℤ) :
    productionIntersectionMap
        frozenYCover.U frozenYCover.V frozenYCover.U frozenYCover.V
        (shearYShortComplexHom a b) 1 =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (shearYOverlap a b)) 1 := by
  rw [shearY_productionIntersectionMap_range]
  have hnat := congrArg
    (fun k ↦ HomologicalComplex.homologyMap k 1)
    (shearY_coverRangeMap_naturality a b)
  simp only [HomologicalComplex.homologyMap_comp] at hnat
  rw [ambientRangeProductionHomologyIso_inv,
    ambientRangeProductionHomologyIso_hom]
  rw [← hnat, ← Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp,
    (ambientSubspaceRangeChainsIso
      (frozenYCover.U ∩ frozenYCover.V)).inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]

/-- Transporting the actual restricted shear through the frozen-overlap
homeomorphism gives the boundary-overlap shear. -/
theorem shearYOverlap_H1_boundary_transport (a b : ℤ) :
    (singularHomologyIsoOfHomotopyEquiv
        frozenYCoverInterHomeomorph.toHomotopyEquiv 1).inv ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (shearYOverlap a b)) 1 ≫
      (singularHomologyIsoOfHomotopyEquiv
        frozenYCoverInterHomeomorph.toHomotopyEquiv 1).hom =
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        (boundaryOverlapShear a b)) 1 := by
  exact ConstructionTargets.HomotopyEquivHomologySquare.conjugated_homologyMap_of_strict_square
    frozenYCoverInterHomeomorph.toHomotopyEquiv
    frozenYCoverInterHomeomorph.toHomotopyEquiv
    (shearYOverlap a b) (boundaryOverlapShear a b) rfl 1

/-- Transporting once more to the disjoint-circle model gives the previously
computed two-circle shear. -/
theorem boundaryOverlapShear_H1_twoCircle_transport (a b : ℤ) :
    (singularHomologyIsoOfHomotopyEquiv
        overlapHomotopyEquivTwoCircles 1).inv ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (boundaryOverlapShear a b)) 1 ≫
      (singularHomologyIsoOfHomotopyEquiv
        overlapHomotopyEquivTwoCircles 1).hom =
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        (twoCircleOverlapShear a b)) 1 := by
  exact ConstructionTargets.HomotopyEquivHomologySquare.conjugated_homologyMap_of_strict_square
    overlapHomotopyEquivTwoCircles overlapHomotopyEquivTwoCircles
    (boundaryOverlapShear a b) (twoCircleOverlapShear a b) rfl 1

/-- The integral biproduct coordinate on the disjoint two-circle model. -/
noncomputable def twoCircleH1IsoIntBiprod :
    SingularHomology 1 (TopCat.of (Circle ⊕ Circle)) ≅
      (AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ) :=
  ConstructionTargets.TopologicalSumSingularHomology.sumHomologyIsoBiprod
      Circle Circle 1 ≪≫
    biprod.mapIso circleH1GroupIsoInt circleH1GroupIsoInt

/-- The left topological summand inclusion is the left injection in the
integral two-circle coordinate. -/
theorem circleSumInl_H1_coordinate :
    circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            circleSumInl) 1 ≫
        twoCircleH1IsoIntBiprod.hom = biprod.inl := by
  rw [twoCircleH1IsoIntBiprod, Iso.trans_hom]
  have h := ConstructionTargets.TopologicalSumSingularHomology.sumInl_homologyMap_comp_iso_hom
    Circle Circle 1
  change HomologicalComplex.homologyMap
      (closureChains.map (TopCat.toSSet.map
        (ConstructionTargets.TopologicalSumSingularHomology.sumInl
          Circle Circle))) 1 ≫ _ = _ at h
  have hmap : HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          circleSumInl) 1 =
      HomologicalComplex.homologyMap
        (closureChains.map (TopCat.toSSet.map
          (ConstructionTargets.TopologicalSumSingularHomology.sumInl
            Circle Circle))) 1 := by rfl
  change circleH1GroupIsoInt.inv ≫ _ ≫ _ ≫ _ = _
  rw [hmap]
  calc
    _ = circleH1GroupIsoInt.inv ≫ biprod.inl ≫
        (biprod.mapIso circleH1GroupIsoInt circleH1GroupIsoInt).hom :=
      congrArg (fun k ↦ circleH1GroupIsoInt.inv ≫ k ≫
        (biprod.mapIso circleH1GroupIsoInt circleH1GroupIsoInt).hom) h
    _ = _ := by simp

/-- The right topological summand inclusion is the right injection in the
integral two-circle coordinate. -/
theorem circleSumInr_H1_coordinate :
    circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            circleSumInr) 1 ≫
        twoCircleH1IsoIntBiprod.hom = biprod.inr := by
  rw [twoCircleH1IsoIntBiprod, Iso.trans_hom]
  have h := ConstructionTargets.TopologicalSumSingularHomology.sumInr_homologyMap_comp_iso_hom
    Circle Circle 1
  change HomologicalComplex.homologyMap
      (closureChains.map (TopCat.toSSet.map
        (ConstructionTargets.TopologicalSumSingularHomology.sumInr
          Circle Circle))) 1 ≫ _ = _ at h
  have hmap : HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          circleSumInr) 1 =
      HomologicalComplex.homologyMap
        (closureChains.map (TopCat.toSSet.map
          (ConstructionTargets.TopologicalSumSingularHomology.sumInr
            Circle Circle))) 1 := by rfl
  change circleH1GroupIsoInt.inv ≫ _ ≫ _ ≫ _ = _
  rw [hmap]
  calc
    _ = circleH1GroupIsoInt.inv ≫ biprod.inr ≫
        (biprod.mapIso circleH1GroupIsoInt circleH1GroupIsoInt).hom :=
      congrArg (fun k ↦ circleH1GroupIsoInt.inv ≫ k ≫
        (biprod.mapIso circleH1GroupIsoInt circleH1GroupIsoInt).hom) h
    _ = _ := by simp

/-- The production overlap endpoint written in the fixed integral
two-component coordinate. -/
noncomputable def shearYOverlapCoordinateMap (a b : ℤ) :
    ((AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ)) ⟶
      ((AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ)) :=
  frozenOverlapH1IsoIntBiprod.inv ≫
    productionIntersectionMap
      frozenYCover.U frozenYCover.V frozenYCover.U frozenYCover.V
      (shearYShortComplexHom a b) 1 ≫
    frozenOverlapH1IsoIntBiprod.hom

/-- The production overlap coordinate is exactly the two-circle shear in
the standard disjoint-sum integral coordinate. -/
theorem shearYOverlapCoordinateMap_eq_twoCircle (a b : ℤ) :
    shearYOverlapCoordinateMap a b =
      twoCircleH1IsoIntBiprod.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShear a b)) 1 ≫
        twoCircleH1IsoIntBiprod.hom := by
  rw [shearYOverlapCoordinateMap,
    shearY_productionIntersectionMap_eq_overlap]
  simp only [frozenOverlapH1IsoIntBiprod, overlapH1IsoIntBiprod,
    overlapHomologyIsoCircleBiprod, overlapHomologyIsoTwoCircles,
    twoCircleH1IsoIntBiprod, Iso.trans_inv, Iso.trans_hom]
  let J := biprod.mapIso circleH1GroupIsoInt circleH1GroupIsoInt
  let S := ConstructionTargets.TopologicalSumSingularHomology.sumHomologyIsoBiprod
    Circle Circle 1
  let E := singularHomologyIsoOfHomotopyEquiv
    overlapHomotopyEquivTwoCircles 1
  have h₁ := congrArg
    (fun k ↦ J.inv ≫ S.inv ≫ E.inv ≫ k ≫ E.hom ≫ S.hom ≫ J.hom)
    (shearYOverlap_H1_boundary_transport a b)
  have h₂ := congrArg
    (fun k ↦ J.inv ≫ S.inv ≫ k ≫ S.hom ≫ J.hom)
    (boundaryOverlapShear_H1_twoCircle_transport a b)
  exact h₁.trans h₂

theorem shearY_overlap_coordinate_components (a b : ℤ) :
    (biprod.inl ≫ shearYOverlapCoordinateMap a b =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ biprod.inl) ∧
    (biprod.inr ≫ shearYOverlapCoordinateMap a b =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ biprod.inr) := by
  constructor
  · rw [shearYOverlapCoordinateMap_eq_twoCircle,
      ← circleSumInl_H1_coordinate]
    slice_lhs 3 5 =>
      erw [twoCircleH1IsoIntBiprod.hom_inv_id_assoc]
    slice_lhs 2 3 => erw [twoCircleOverlapShearLeft_H1]
    rw [twoCircleOverlapShearLeft_H1_eq_fold_inl]
    have h := congrArg (fun k ↦ k ≫ circleH1GroupIsoInt.inv)
      (twoCircleOverlapShearLeftFold_H1_coordinate a b)
    simp only [Category.assoc] at h
    erw [circleH1GroupIsoInt.hom_inv_id] at h
    have h' : circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShearLeftFold a b)) 1 =
        (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ circleH1GroupIsoInt.inv := by
      simpa only [Category.comp_id] using h
    calc
      _ = ((a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ circleH1GroupIsoInt.inv) ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              circleSumInl) 1 ≫ twoCircleH1IsoIntBiprod.hom :=
        congrArg (fun k ↦ k ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              circleSumInl) 1 ≫ twoCircleH1IsoIntBiprod.hom) h'
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ k)
          circleSumInl_H1_coordinate
  · rw [shearYOverlapCoordinateMap_eq_twoCircle,
      ← circleSumInr_H1_coordinate]
    slice_lhs 3 5 =>
      erw [twoCircleH1IsoIntBiprod.hom_inv_id_assoc]
    slice_lhs 2 3 => erw [twoCircleOverlapShearRight_H1]
    rw [twoCircleOverlapShearRight_H1_eq_fold_inr]
    have h := congrArg (fun k ↦ k ≫ circleH1GroupIsoInt.inv)
      (twoCircleOverlapShearRightFold_H1_coordinate a b)
    simp only [Category.assoc] at h
    erw [circleH1GroupIsoInt.hom_inv_id] at h
    have h' : circleH1GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (twoCircleOverlapShearRightFold a b)) 1 =
        (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ circleH1GroupIsoInt.inv := by
      simpa only [Category.comp_id] using h
    calc
      _ = ((a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ circleH1GroupIsoInt.inv) ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              circleSumInr) 1 ≫ twoCircleH1IsoIntBiprod.hom :=
        congrArg (fun k ↦ k ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              circleSumInr) 1 ≫ twoCircleH1IsoIntBiprod.hom) h'
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ k)
          circleSumInr_H1_coordinate

/-- B6 reduces exactly to the degree calculation on the two overlap
components. -/
theorem shearY_overlap_coordinate_of_injections (a b : ℤ)
    (hleft : biprod.inl ≫ shearYOverlapCoordinateMap a b =
      biprod.inl ≫ overlapScalar a)
    (hright : biprod.inr ≫ shearYOverlapCoordinateMap a b =
      biprod.inr ≫ overlapScalar a) :
    shearYOverlapCoordinateMap a b = overlapScalar a := by
  apply biprod.hom_ext'
  · exact hleft
  · exact hright

theorem inl_comp_overlapScalar (a : ℤ) :
    biprod.inl ≫ overlapScalar a =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ biprod.inl := by
  simp [overlapScalar]

theorem inr_comp_overlapScalar (a : ℤ) :
    biprod.inr ≫ overlapScalar a =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ biprod.inr := by
  simp [overlapScalar]

/-- Once the two component degree calculations are available in their
normalized scalar form, they assemble to the overlap-coordinate formula. -/
theorem shearY_overlap_coordinate_of_degree_components (a b : ℤ)
    (hleft : biprod.inl ≫ shearYOverlapCoordinateMap a b =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ biprod.inl)
    (hright : biprod.inr ≫ shearYOverlapCoordinateMap a b =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ biprod.inr) :
    shearYOverlapCoordinateMap a b = overlapScalar a := by
  apply shearY_overlap_coordinate_of_injections
  · simpa only [inl_comp_overlapScalar] using hleft
  · simpa only [inr_comp_overlapScalar] using hright

theorem shearY_overlap_coordinate (a b : ℤ) :
    shearYOverlapCoordinateMap a b = overlapScalar a := by
  exact shearY_overlap_coordinate_of_degree_components a b
    (shearY_overlap_coordinate_components a b).1
    (shearY_overlap_coordinate_components a b).2

/-- The degree-one production connecting square for the frozen shear, with
the union endpoint rewritten as the actual induced map on degree two. -/
theorem shearY_productionConnecting_naturality (a b : ℤ) :
    productionConnecting frozenYCover.U frozenYCover.V
        frozenYCover.U_isOpen frozenYCover.V_isOpen
        frozenYCover.union_eq_univ 1 ≫
      productionIntersectionMap
        frozenYCover.U frozenYCover.V frozenYCover.U frozenYCover.V
        (shearYShortComplexHom a b) 1 =
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (shearY a b)) 2 ≫
      productionConnecting frozenYCover.U frozenYCover.V
        frozenYCover.U_isOpen frozenYCover.V_isOpen
        frozenYCover.union_eq_univ 1 := by
  rw [productionConnecting_naturality]
  rw [shearY_productionUnionMap]

noncomputable def frozenConnectingCoordinate :
    AddCommGrpCat.of ℤ ⟶
      ((AddCommGrpCat.of ℤ) ⊞ (AddCommGrpCat.of ℤ)) :=
  frozenTorusH2GroupIsoInt.inv ≫
    productionConnecting frozenYCover.U frozenYCover.V
      frozenYCover.U_isOpen frozenYCover.V_isOpen
      frozenYCover.union_eq_univ 1 ≫
    frozenOverlapH1IsoIntBiprod.hom

/-- The degree-two homology of each frozen-cover member vanishes, because
the fixed cover homeomorphisms identify them with the two solid-torus
members of the boundary cover. -/
theorem frozenH2Pieces_isZero : IsZero
    (SingularHomology 2 (TopCat.of frozenYCover.U) ⊞
      SingularHomology 2 (TopCat.of frozenYCover.V)) := by
  rw [biprod_isZero_iff]
  exact ⟨
    IsZero.of_iso (leftHomology_isZero_of_one_lt 2 (by omega))
      (singularHomologyIsoOfHomotopyEquiv
        frozenYCoverUHomeomorph.toHomotopyEquiv 2),
    IsZero.of_iso (rightHomology_isZero_of_one_lt 2 (by omega))
      (singularHomologyIsoOfHomotopyEquiv
        frozenYCoverVHomeomorph.toHomotopyEquiv 2)⟩

instance frozenProductionConnecting_mono : Mono
    (productionConnecting frozenYCover.U frozenYCover.V
      frozenYCover.U_isOpen frozenYCover.V_isOpen
      frozenYCover.union_eq_univ 1) := by
  exact (productionMayerVietoris_exact_union frozenYCover.U frozenYCover.V
    frozenYCover.U_isOpen frozenYCover.V_isOpen
    frozenYCover.union_eq_univ 1).mono_g
      (frozenH2Pieces_isZero.eq_of_src _ _)

instance frozenConnectingCoordinate_mono : Mono frozenConnectingCoordinate := by
  dsimp only [frozenConnectingCoordinate]
  constructor
  intro Z f g hfg
  apply (cancel_mono frozenTorusH2GroupIsoInt.inv).1
  apply (cancel_mono (productionConnecting frozenYCover.U frozenYCover.V
    frozenYCover.U_isOpen frozenYCover.V_isOpen
    frozenYCover.union_eq_univ 1)).1
  apply (cancel_mono frozenOverlapH1IsoIntBiprod.hom).1
  simpa only [Category.assoc] using hfg

theorem shearY_frozenConnectingCoordinate_naturality (a b : ℤ) :
    (frozenTorusH2GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY a b)) 2 ≫
        frozenTorusH2GroupIsoInt.hom) ≫ frozenConnectingCoordinate =
      frozenConnectingCoordinate ≫ overlapScalar a := by
  rw [frozenConnectingCoordinate, ← shearY_overlap_coordinate,
    shearYOverlapCoordinateMap]
  slice_lhs 3 5 =>
    erw [frozenTorusH2GroupIsoInt.hom_inv_id_assoc]
  slice_rhs 3 5 =>
    erw [frozenOverlapH1IsoIntBiprod.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ frozenTorusH2GroupIsoInt.inv ≫ k ≫
      frozenOverlapH1IsoIntBiprod.hom)
    (shearY_productionConnecting_naturality a b).symm

theorem frozenConnectingCoordinate_comp_overlapScalar (a : ℤ) :
    frozenConnectingCoordinate ≫ overlapScalar a =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ frozenConnectingCoordinate := by
  apply biprod.hom_ext
  · simp [overlapScalar]
  · simp [overlapScalar]

theorem shearY_frozenConnectingCoordinate_scalar (a b : ℤ) :
    (frozenTorusH2GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY a b)) 2 ≫
        frozenTorusH2GroupIsoInt.hom) ≫ frozenConnectingCoordinate =
      (a • 𝟙 (AddCommGrpCat.of ℤ)) ≫ frozenConnectingCoordinate := by
  rw [shearY_frozenConnectingCoordinate_naturality,
    frozenConnectingCoordinate_comp_overlapScalar]

/-- In the fixed integral top-class coordinate, the upper-triangular shear
acts on degree-two homology by multiplication by its first coefficient. -/
theorem shearY_H2 (a b : ℤ) :
    frozenTorusH2GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY a b)) 2 ≫
        frozenTorusH2GroupIsoInt.hom =
      a • 𝟙 (AddCommGrpCat.of ℤ) := by
  apply (cancel_mono frozenConnectingCoordinate).1
  exact shearY_frozenConnectingCoordinate_scalar a b

/-- Exchange the two circle coordinates of the frozen torus. -/
def swapTorus : C(FrozenTorus, FrozenTorus) :=
  ⟨fun p ↦ (p.2, p.1), by fun_prop⟩

@[simp] theorem swapTorus_comp_swapTorus :
    swapTorus.comp swapTorus = ContinuousMap.id FrozenTorus := by
  ext p <;> rfl

/-- Applying the coordinate swap twice acts trivially on degree-two
singular homology. -/
theorem swap_H2_square :
    HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            swapTorus) 2 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            swapTorus) 2 = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp,
    ConstructionTargets.SingularSubdivision.singularPostcomposition_comp,
    swapTorus_comp_swapTorus]
  exact ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 2).obj
    (AddCommGrpCat.of ℤ)).map_id (TopCat.of FrozenTorus)

noncomputable def swapH2Coordinate :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  frozenTorusH2GroupIsoInt.inv ≫
    HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition
        swapTorus) 2 ≫
    frozenTorusH2GroupIsoInt.hom

theorem swapH2Coordinate_square :
    swapH2Coordinate ≫ swapH2Coordinate = 𝟙 _ := by
  rw [swapH2Coordinate]
  calc
    _ = frozenTorusH2GroupIsoInt.inv ≫
        (HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              swapTorus) 2 ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              swapTorus) 2) ≫ frozenTorusH2GroupIsoInt.hom := by
      simp only [Category.assoc]
      slice_lhs 3 4 => exact frozenTorusH2GroupIsoInt.hom_inv_id
      slice_lhs 3 4 => exact Category.id_comp _
    _ = frozenTorusH2GroupIsoInt.inv ≫ 𝟙 _ ≫
        frozenTorusH2GroupIsoInt.hom := congrArg
      (fun k ↦ frozenTorusH2GroupIsoInt.inv ≫ k ≫
        frozenTorusH2GroupIsoInt.hom) swap_H2_square
    _ = 𝟙 _ := frozenTorusH2GroupIsoInt.inv_hom_id

/-- The determinant-one factor in the frozen linear torus map. -/
def lowerShear : C(FrozenTorus, FrozenTorus) :=
  ⟨fun p ↦ (p.1, p.2 - p.1), by fun_prop⟩

/-- The concrete determinant-three torus map, before adapting to the frozen
consumer declaration. -/
def frozenLbar : C(FrozenTorus, FrozenTorus) :=
  ⟨fun p ↦ (2 • p.1 + p.2, p.2 - p.1), by fun_prop⟩

theorem lowerShear_factorization :
    lowerShear = swapTorus.comp ((shearY 1 (-1)).comp swapTorus) := by
  ext p <;> simp [lowerShear, swapTorus, shearY, sub_eq_add_neg]

theorem frozenLbar_factorization :
    frozenLbar = (shearY 3 1).comp lowerShear := by
  ext p <;> simp [frozenLbar, lowerShear, shearY]
  module

/-- Functoriality of the concrete degree-two singular-homology map, exposed
without expanding the fixed integral coordinate. -/
theorem frozenH2Map_comp (g f : C(FrozenTorus, FrozenTorus)) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          (g.comp f)) 2 =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition f) 2 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition g) 2 := by
  rw [← ConstructionTargets.SingularSubdivision.singularPostcomposition_comp,
    HomologicalComplex.homologyMap_comp]

/-- Degree-two homology sees the determinant-one factor as the two swap maps
with the `(1,-1)` shear between them. -/
theorem lowerShear_H2_map :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          lowerShear) 2 =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            swapTorus) 2 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY 1 (-1))) 2 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            swapTorus) 2 := by
  rw [lowerShear_factorization, frozenH2Map_comp, frozenH2Map_comp]
  simp only [Category.assoc]

/-- The determinant-three factorization after applying degree-two singular
homology. -/
theorem frozenLbar_H2_map :
    HomologicalComplex.homologyMap
        (ConstructionTargets.SingularSubdivision.singularPostcomposition
          frozenLbar) 2 =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            lowerShear) 2 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            (shearY 3 1)) 2 := by
  rw [frozenLbar_factorization, frozenH2Map_comp]

/-- Conjugating a composite by the fixed top-class coordinate is the
composite of the conjugated maps. -/
theorem frozenH2Coordinate_comp
    (f g : SingularHomology 2 (TopCat.of FrozenTorus) ⟶
      SingularHomology 2 (TopCat.of FrozenTorus)) :
    (frozenTorusH2GroupIsoInt.inv ≫ f ≫
        frozenTorusH2GroupIsoInt.hom) ≫
      (frozenTorusH2GroupIsoInt.inv ≫ g ≫
        frozenTorusH2GroupIsoInt.hom) =
      frozenTorusH2GroupIsoInt.inv ≫ (f ≫ g) ≫
        frozenTorusH2GroupIsoInt.hom := by
  simp only [Category.assoc]
  slice_lhs 3 4 => exact frozenTorusH2GroupIsoInt.hom_inv_id
  slice_lhs 3 4 => exact Category.id_comp _

/-- The determinant-one factor acts trivially in the fixed top-class
coordinate. -/
theorem lowerShear_H2 :
    frozenTorusH2GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            lowerShear) 2 ≫
        frozenTorusH2GroupIsoInt.hom = 𝟙 _ := by
  rw [lowerShear_H2_map]
  let s := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularSubdivision.singularPostcomposition
      swapTorus) 2
  let h := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularSubdivision.singularPostcomposition
      (shearY 1 (-1))) 2
  change frozenTorusH2GroupIsoInt.inv ≫ (s ≫ h ≫ s) ≫
    frozenTorusH2GroupIsoInt.hom = 𝟙 _
  calc
    _ = (frozenTorusH2GroupIsoInt.inv ≫ s ≫
          frozenTorusH2GroupIsoInt.hom) ≫
        (frozenTorusH2GroupIsoInt.inv ≫ (h ≫ s) ≫
          frozenTorusH2GroupIsoInt.hom) :=
      (frozenH2Coordinate_comp s (h ≫ s)).symm
    _ = swapH2Coordinate ≫
        ((frozenTorusH2GroupIsoInt.inv ≫ h ≫
            frozenTorusH2GroupIsoInt.hom) ≫ swapH2Coordinate) := by
      change (frozenTorusH2GroupIsoInt.inv ≫ s ≫
          frozenTorusH2GroupIsoInt.hom) ≫
        (frozenTorusH2GroupIsoInt.inv ≫ (h ≫ s) ≫
          frozenTorusH2GroupIsoInt.hom) =
        (frozenTorusH2GroupIsoInt.inv ≫ s ≫
          frozenTorusH2GroupIsoInt.hom) ≫
        ((frozenTorusH2GroupIsoInt.inv ≫ h ≫
          frozenTorusH2GroupIsoInt.hom) ≫
        (frozenTorusH2GroupIsoInt.inv ≫ s ≫
          frozenTorusH2GroupIsoInt.hom))
      apply congrArg (fun k ↦
        (frozenTorusH2GroupIsoInt.inv ≫ s ≫
          frozenTorusH2GroupIsoInt.hom) ≫ k)
      exact (frozenH2Coordinate_comp h s).symm
    _ = swapH2Coordinate ≫ swapH2Coordinate := by
      change swapH2Coordinate ≫
        ((frozenTorusH2GroupIsoInt.inv ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              (shearY 1 (-1))) 2 ≫
          frozenTorusH2GroupIsoInt.hom) ≫ swapH2Coordinate) = _
      rw [shearY_H2]
      simp
    _ = 𝟙 _ := swapH2Coordinate_square

/-- The determinant-three factor acts by multiplication by three in the
fixed top-class coordinate. -/
theorem frozenLbar_H2 :
    frozenTorusH2GroupIsoInt.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularSubdivision.singularPostcomposition
            frozenLbar) 2 ≫
        frozenTorusH2GroupIsoInt.hom = 3 • 𝟙 _ := by
  rw [frozenLbar_H2_map]
  let l := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularSubdivision.singularPostcomposition
      lowerShear) 2
  let h := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularSubdivision.singularPostcomposition
      (shearY 3 1)) 2
  change frozenTorusH2GroupIsoInt.inv ≫ (l ≫ h) ≫
    frozenTorusH2GroupIsoInt.hom = 3 • 𝟙 _
  calc
    _ = (frozenTorusH2GroupIsoInt.inv ≫ l ≫
          frozenTorusH2GroupIsoInt.hom) ≫
        (frozenTorusH2GroupIsoInt.inv ≫ h ≫
          frozenTorusH2GroupIsoInt.hom) :=
      (frozenH2Coordinate_comp l h).symm
    _ = (𝟙 _) ≫ (3 • 𝟙 _) := by
      change (frozenTorusH2GroupIsoInt.inv ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              lowerShear) 2 ≫ frozenTorusH2GroupIsoInt.hom) ≫
        (frozenTorusH2GroupIsoInt.inv ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              (shearY 3 1)) 2 ≫ frozenTorusH2GroupIsoInt.hom) = _
      rw [lowerShear_H2, shearY_H2]
      rfl
    _ = 3 • 𝟙 _ := by simp

#print axioms frozenTorusH2GroupIsoInt
#print axioms frozenYCover
#print axioms frozenYCoverUHomeomorph
#print axioms frozenYCoverVHomeomorph
#print axioms frozenYCoverInterHomeomorph
#print axioms shearY
#print axioms frozenTorusCircleProd
#print axioms circleShearY
#print axioms frozenTorusCircleProd_shearY
#print axioms shearY_mem_U
#print axioms shearY_mem_V
#print axioms shearY_comp
#print axioms shearYShortComplexHom
#print axioms shearY_productionUnionMap
#print axioms shearY_productionIntersectionMap_range
#print axioms frozenOverlapH1IsoIntBiprod
#print axioms shearYOverlap
#print axioms overlapScalar
#print axioms boundaryOverlapShear
#print axioms twoCircleOverlapShear
#print axioms twoCircleOverlapShearLeft
#print axioms twoCircleOverlapShearRight
#print axioms twoCircleOverlapShearLeft_apply
#print axioms twoCircleOverlapShearRight_apply
#print axioms twoCircleOverlapShearLeft_H1
#print axioms twoCircleOverlapShearRight_H1
#print axioms twoCircleOverlapShearLeftFold
#print axioms twoCircleOverlapShearRightFold
#print axioms twoCircleOverlapShearLeft_eq_inl_fold
#print axioms twoCircleOverlapShearRight_eq_inr_fold
#print axioms twoCircleOverlapShearLeft_H1_eq_fold_inl
#print axioms twoCircleOverlapShearRight_H1_eq_fold_inr
#print axioms twoCircleOverlapShearLeftFold_H1
#print axioms twoCircleOverlapShearRightFold_H1
#print axioms overlapHomotopyEquivTwoCircles_inv_fst
#print axioms twoCircleFold_boolTimesCircle
#print axioms overlapHomotopyEquivTwoCircles_fold
#print axioms overlapCircleProd_fst
#print axioms boundaryOverlapShear_fst
#print axioms boundaryOverlapShear_snd
#print axioms overlapOrthogonalCoordinate_shear
#print axioms twoCircleBranch_boolTimesCircle
#print axioms overlapOrthogonalRetraction
#print axioms overlapModelOrthogonalRetraction
#print axioms twoCircleBranch_overlap_toFun
#print axioms overlapTwoCircles_inv_model
#print axioms twoCircleBranch_retraction
#print axioms twoCircleOverlapShear_branch
#print axioms twoCircleBranch_inl
#print axioms twoCircleBranch_inr
#print axioms twoCircleBranchFold_reconstruct
#print axioms twoCircleOverlapShear_fold_apply
#print axioms twoCircleOverlapShearLeftFold_eq_affine
#print axioms twoCircleOverlapShearRightFold_eq_affine
#print axioms circleZPow
#print axioms circleAffine
#print axioms circleAffineHomotopy
#print axioms circleAffine_H1_eq_zpow
#print axioms twoCircleOverlapShearLeftFold_H1_eq_zpow
#print axioms twoCircleOverlapShearRightFold_H1_eq_zpow
#print axioms liftBasedLoop_circleZPow
#print axioms liftBasedLoopEndpointInteger_circleZPow
#print axioms circleZPowPi1Map
#print axioms circleZPow_fundamentalGroup_coordinate
#print axioms circleZPowPi1Map_eq_zpow
#print axioms fundamentalGroupH1Hom_circleZPowPi1Map
#print axioms circleZPow_H1_apply
#print axioms circleZPow_H1
#print axioms circleZPow_H1_coordinate
#print axioms twoCircleOverlapShearLeftFold_H1_coordinate
#print axioms twoCircleOverlapShearRightFold_H1_coordinate
#print axioms shearY_coverRangeMap_naturality
#print axioms shearY_productionIntersectionMap_eq_overlap
#print axioms shearYOverlap_H1_boundary_transport
#print axioms boundaryOverlapShear_H1_twoCircle_transport
#print axioms twoCircleH1IsoIntBiprod
#print axioms circleSumInl_H1_coordinate
#print axioms circleSumInr_H1_coordinate
#print axioms shearYOverlapCoordinateMap
#print axioms shearYOverlapCoordinateMap_eq_twoCircle
#print axioms shearY_overlap_coordinate_components
#print axioms shearY_overlap_coordinate_of_injections
#print axioms inl_comp_overlapScalar
#print axioms inr_comp_overlapScalar
#print axioms shearY_overlap_coordinate_of_degree_components
#print axioms shearY_overlap_coordinate
#print axioms shearY_productionConnecting_naturality
#print axioms frozenConnectingCoordinate
#print axioms shearY_frozenConnectingCoordinate_naturality
#print axioms frozenConnectingCoordinate_comp_overlapScalar
#print axioms shearY_frozenConnectingCoordinate_scalar
#print axioms lowerShear_H2
#print axioms frozenLbar_H2

end ConstructionTargets.T97A04Closure

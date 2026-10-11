import ConstructionTargets.T97A04FrozenH1Coordinate
import ConstructionTargets.BoundaryTorusOpenCover
import ConstructionTargets.BoundaryTorusMayerVietoris
import ConstructionTargets.ProductionOpenCoverMayerVietoris

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

/-- The upper-triangular shear of the frozen torus.  Its second coordinate is
fixed, so it preserves the vertical cover literally. -/
def shearY (a b : ℤ) : C(FrozenTorus, FrozenTorus) where
  toFun p := (a • p.1 + b • p.2, p.2)
  continuous_toFun := by fun_prop

@[simp]
theorem shearY_apply (a b : ℤ) (p : FrozenTorus) :
    shearY a b p = (a • p.1 + b • p.2, p.2) :=
  rfl

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

/-- The left overlap-circle summand followed by the transported shear. -/
def twoCircleOverlapShearLeft (a b : ℤ) : C(Circle, Circle ⊕ Circle) :=
  (twoCircleOverlapShear a b).comp ⟨Sum.inl, continuous_inl⟩

/-- The right overlap-circle summand followed by the transported shear. -/
def twoCircleOverlapShearRight (a b : ℤ) : C(Circle, Circle ⊕ Circle) :=
  (twoCircleOverlapShear a b).comp ⟨Sum.inr, continuous_inr⟩

@[simp] theorem twoCircleOverlapShearLeft_apply (a b : ℤ) (z : Circle) :
    twoCircleOverlapShearLeft a b z = twoCircleOverlapShear a b (Sum.inl z) := rfl

@[simp] theorem twoCircleOverlapShearRight_apply (a b : ℤ) (z : Circle) :
    twoCircleOverlapShearRight a b z = twoCircleOverlapShear a b (Sum.inr z) := rfl

/-- The integer power map which remains on either overlap component after
the constant translation in the shear is removed. -/
def circleZPow (a : ℤ) : C(Circle, Circle) :=
  ⟨fun z ↦ z ^ a, by fun_prop⟩

/-- A translated integer power map on the circle. -/
def circleAffine (a : ℤ) (c : Circle) : C(Circle, Circle) :=
  ⟨fun z ↦ c * z ^ a, by fun_prop⟩

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

#print axioms frozenTorusH2GroupIsoInt
#print axioms frozenYCover
#print axioms frozenYCoverUHomeomorph
#print axioms frozenYCoverVHomeomorph
#print axioms frozenYCoverInterHomeomorph
#print axioms shearY
#print axioms shearY_mem_U
#print axioms shearY_mem_V
#print axioms shearY_comp
#print axioms shearYShortComplexHom
#print axioms shearY_productionUnionMap
#print axioms frozenOverlapH1IsoIntBiprod
#print axioms shearYOverlap
#print axioms overlapScalar
#print axioms boundaryOverlapShear
#print axioms twoCircleOverlapShear
#print axioms twoCircleOverlapShearLeft
#print axioms twoCircleOverlapShearRight
#print axioms twoCircleOverlapShearLeft_apply
#print axioms twoCircleOverlapShearRight_apply
#print axioms circleZPow
#print axioms circleAffine
#print axioms circleAffineHomotopy
#print axioms circleAffine_H1_eq_zpow
#print axioms liftBasedLoop_circleZPow
#print axioms liftBasedLoopEndpointInteger_circleZPow
#print axioms circleZPowPi1Map
#print axioms circleZPow_fundamentalGroup_coordinate
#print axioms circleZPowPi1Map_eq_zpow
#print axioms fundamentalGroupH1Hom_circleZPowPi1Map
#print axioms circleZPow_H1_apply
#print axioms circleZPow_H1
#print axioms circleZPow_H1_coordinate
#print axioms shearYOverlapCoordinateMap
#print axioms shearY_overlap_coordinate_of_injections
#print axioms inl_comp_overlapScalar
#print axioms inr_comp_overlapScalar
#print axioms shearY_overlap_coordinate_of_degree_components

end ConstructionTargets.T97A04Closure

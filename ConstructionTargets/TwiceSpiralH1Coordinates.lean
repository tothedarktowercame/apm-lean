import ConstructionTargets.FiniteFreeHurewiczNaturality
import ConstructionTargets.SolidTorusHomotopyAndHomology

/-!
# H1 coordinates determined by twice-spiral fundamental-group coordinates
-/

noncomputable section

namespace ConstructionTargets.TwiceSpiralH1Coordinates

open CategoryTheory
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.DegreeOneHurewiczSurjective
open ConstructionTargets.FiniteFreeHurewiczNaturality
open ConstructionTargets.CircleHurewiczIsomorphism
open ConstructionTargets.BoundaryTorusHurewiczIsomorphism
open ConstructionTargets.BoundaryTorusIntegralHomologyComplete
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.SolidTorusHomotopyAndHomology
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularSubdivision

/-- The product/integer-function coordinate used to apply finite-free
Hopficity to a supplied `ℤ × ℤ` fundamental-group coordinate. -/
def intProdMulEquivFinTwo :
    Multiplicative (ℤ × ℤ) ≃* Multiplicative (Fin 2 → ℤ) :=
  (AddEquiv.toMultiplicative
    (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ℤ)).symm.toAddEquiv)

def boundaryH1RawCoordinate :
    Multiplicative (IntegralH1 BoundaryTorus) ≃*
      Multiplicative (Fin 2 → ℤ) :=
  AddEquiv.toMultiplicative
    { toFun := boundaryTorusH1GroupIsoFinTwo.hom
      invFun := boundaryTorusH1GroupIsoFinTwo.inv
      left_inv := boundaryTorusH1GroupIsoFinTwo.hom_inv_id_apply
      right_inv := boundaryTorusH1GroupIsoFinTwo.inv_hom_id_apply
      map_add' := boundaryTorusH1GroupIsoFinTwo.hom.hom.map_add }

def solidTorusH1GroupIsoInt :
    SingularHomology 1 (TopCat.of SolidTorus) ≅ AddCommGrpCat.of ℤ :=
  singularHomologyIsoOfHomotopyEquiv solidTorusHomotopyEquivCircle 1 ≪≫
    circleH1GroupIsoInt

def solidH1RawCoordinate :
    Multiplicative (IntegralH1 SolidTorus) ≃* Multiplicative ℤ :=
  AddEquiv.toMultiplicative
    { toFun := solidTorusH1GroupIsoInt.hom
      invFun := solidTorusH1GroupIsoInt.inv
      left_inv := solidTorusH1GroupIsoInt.hom_inv_id_apply
      right_inv := solidTorusH1GroupIsoInt.inv_hom_id_apply
      map_add' := solidTorusH1GroupIsoInt.hom.hom.map_add }

local instance circlePathConnectedSpace : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

local instance solidTorusPathConnectedSpace : PathConnectedSpace SolidTorus :=
  ⟨⟨(1, 0)⟩, fun x y => by
    let hjoined := (convex_closedBall (0 : Plane) 1).isPathConnected (by simp) |>.joinedIn
      x.2.1 x.2.2 y.2.1 y.2.2
    let γ := hjoined.choose
    let γD : Path x.2 y.2 :=
      { toFun := fun t => ⟨γ t, hjoined.choose_spec t⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    exact ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1) γD⟩⟩

local instance boundaryTorusPathConnectedSpace : PathConnectedSpace BoundaryTorus :=
  ConstructionTargets.BoundaryTorusHurewiczIsomorphism.boundaryTorusPathConnectedSpace

/-- Rank-one Hurewicz after abelianization, with the explicit Hurewicz map as
forward function. -/
def rankOneAbelianizedFundamentalGroupH1MulEquiv
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X}
    (piCoord : FundamentalGroup X x ≃* Multiplicative ℤ)
    (raw : Multiplicative (IntegralH1 X) ≃* Multiplicative ℤ) :
    Abelianization (FundamentalGroup X x) ≃* Multiplicative (IntegralH1 X) :=
  MulEquiv.ofBijective (abelianizedFundamentalGroupToH1 x) (by
    constructor
    · intro a b hab
      apply (abelianizedFundamentalGroupIntCoordinate piCoord).injective
      have hi := (rankOneHurewiczCoordinate_bijective piCoord raw).1
      apply hi
      simpa [rankOneHurewiczCoordinate] using congrArg raw hab
    · exact abelianizedFundamentalGroupToH1_surjective x)

/-- Boundary H1 coordinates canonically determined by the supplied π1
coordinates. -/
def boundaryH1CoordinateFromPi {z : BoundaryTorus}
    (e : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ)) :
    Multiplicative (IntegralH1 BoundaryTorus) ≃* Multiplicative (ℤ × ℤ) :=
  let ef := e.trans intProdMulEquivFinTwo
  (finiteFreeAbelianizedFundamentalGroupH1MulEquiv ef
    boundaryH1RawCoordinate).symm.trans
    (e.abelianizationCongr.trans
      (commGroupAbelianizationMulEquiv (Multiplicative (ℤ × ℤ))))

/-- Solid-torus H1 coordinates canonically determined by the supplied π1
coordinate. -/
def solidH1CoordinateFromPi {z : SolidTorus}
    (c : FundamentalGroup SolidTorus z ≃* Multiplicative ℤ) :
    Multiplicative (IntegralH1 SolidTorus) ≃* Multiplicative ℤ :=
  (rankOneAbelianizedFundamentalGroupH1MulEquiv c solidH1RawCoordinate).symm.trans
    (abelianizedFundamentalGroupIntCoordinate c)

def secondCoordinateHom :
    Multiplicative (ℤ × ℤ) →* Multiplicative ℤ where
  toFun q := Multiplicative.ofAdd q.toAdd.2
  map_one' := rfl
  map_mul' _ _ := rfl

def boundaryHurewiczFromPi {z : BoundaryTorus}
    (e : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ)) :
    Abelianization (FundamentalGroup BoundaryTorus z) ≃*
      Multiplicative (IntegralH1 BoundaryTorus) :=
  finiteFreeAbelianizedFundamentalGroupH1MulEquiv (e.trans intProdMulEquivFinTwo)
    boundaryH1RawCoordinate

def solidHurewiczFromPi {z : SolidTorus}
    (c : FundamentalGroup SolidTorus z ≃* Multiplicative ℤ) :
    Abelianization (FundamentalGroup SolidTorus z) ≃*
      Multiplicative (IntegralH1 SolidTorus) :=
  rankOneAbelianizedFundamentalGroupH1MulEquiv c solidH1RawCoordinate

/-- Naturality becomes literal in H1 coordinates defined from the supplied
π1 coordinates. -/
theorem h1CoordinateFromPi_naturality
    {X Y A B : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] [CommGroup A] [CommGroup B]
    {x : X} (f : C(X, Y))
    (eX : FundamentalGroup X x ≃* A)
    (eY : FundamentalGroup Y (f x) ≃* B)
    (HX : Abelianization (FundamentalGroup X x) ≃*
      Multiplicative (IntegralH1 X))
    (HY : Abelianization (FundamentalGroup Y (f x)) ≃*
      Multiplicative (IntegralH1 Y))
    (hHX : HX.toMonoidHom = abelianizedFundamentalGroupToH1 x)
    (hHY : HY.toMonoidHom = abelianizedFundamentalGroupToH1 (f x))
    (g : A →* B)
    (hg : ∀ p, g (eX p) = eY (FundamentalGroup.map f x p))
    (q : A) :
    (HY.symm.trans
      (eY.abelianizationCongr.trans (commGroupAbelianizationMulEquiv B)))
      (Multiplicative.ofAdd
        ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
          (Multiplicative.toAdd
            ((HX.symm.trans
              (eX.abelianizationCongr.trans
                (commGroupAbelianizationMulEquiv A))).symm q)))) = g q := by
  let p := eX.symm q
  let abX := eX.abelianizationCongr.trans
    (commGroupAbelianizationMulEquiv A)
  let abY := eY.abelianizationCongr.trans
    (commGroupAbelianizationMulEquiv B)
  have hp : eX p = q := eX.apply_symm_apply q
  have habX : abX.symm q = Abelianization.of p := by
    apply abX.injective
    rw [abX.apply_symm_apply]
    change q = eX p
    exact hp.symm
  have habY : abY.symm (g q) =
      Abelianization.of (FundamentalGroup.map f x p) := by
    apply abY.injective
    rw [abY.apply_symm_apply]
    change g q = eY (FundamentalGroup.map f x p)
    exact (congrArg g hp.symm).trans (hg p)
  change abY (HY.symm (Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
        (Multiplicative.toAdd (HX (abX.symm q)))))) = g q
  apply abY.symm.injective
  rw [abY.symm_apply_apply]
  rw [habX, habY]
  apply HY.injective
  rw [HY.apply_symm_apply]
  have hxof := DFunLike.congr_fun hHX (Abelianization.of p)
  have hyof := DFunLike.congr_fun hHY
    (Abelianization.of (FundamentalGroup.map f x p))
  change Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
        (Multiplicative.toAdd
          (HX.toMonoidHom (Abelianization.of p)))) =
    HY.toMonoidHom
      (Abelianization.of (FundamentalGroup.map f x p))
  rw [hxof, hyof, abelianizedFundamentalGroupToH1_of,
    abelianizedFundamentalGroupToH1_of]
  exact congrArg Multiplicative.ofAdd
    (fundamentalGroupH1Hom_naturality f x p)

/-- In H1 coordinates determined by the supplied π1 coordinates, the actual
boundary inclusion is the second-coordinate projection. -/
theorem boundaryInclusion_H1_secondCoordinate
    (z : BoundaryTorus)
    (e : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ))
    (c : FundamentalGroup SolidTorus (boundaryInclusion z) ≃* Multiplicative ℤ)
    (hinc : ∀ p, c (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z p) =
        secondCoordinateHom (e p))
    (q : Multiplicative (ℤ × ℤ)) :
    solidH1CoordinateFromPi c (Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap
        (singularPostcomposition
          ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1)
        (Multiplicative.toAdd ((boundaryH1CoordinateFromPi e).symm q)))) =
      secondCoordinateHom q := by
  exact h1CoordinateFromPi_naturality
    ⟨boundaryInclusion, continuous_boundaryInclusion⟩ e c
    (boundaryHurewiczFromPi e) (solidHurewiczFromPi c) rfl rfl
    secondCoordinateHom (fun p => (hinc p).symm) q

/-- The π1 map of a boundary homeomorphism in supplied coordinates. -/
def boundaryCoordinateMap (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (z : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z) ≃* Multiplicative (ℤ × ℤ)) :
    Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ) :=
  e₂.toMonoidHom.comp ((FundamentalGroup.map ⟨h, h.continuous⟩ z).comp
    e₁.symm.toMonoidHom)

def twiceSpiralSecondCoefficient (h : BoundaryTorus ≃ₜ BoundaryTorus)
    (z : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z) ≃* Multiplicative (ℤ × ℤ)) : ℤ :=
  (boundaryCoordinateMap h z e₁ e₂ (Multiplicative.ofAdd (0, 1))).toAdd.2

theorem boundaryCoordinateMap_second_formula
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z) ≃* Multiplicative (ℤ × ℤ))
    (h10 : boundaryCoordinateMap h z e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2))
    (a b : ℤ) :
    (boundaryCoordinateMap h z e₁ e₂
      (Multiplicative.ofAdd (a, b))).toAdd.2 =
      2 * a + twiceSpiralSecondCoefficient h z e₁ e₂ * b := by
  have hdecomp : Multiplicative.ofAdd (a, b) =
      (Multiplicative.ofAdd (1, 0) : Multiplicative (ℤ × ℤ)) ^ a *
        Multiplicative.ofAdd (0, 1) ^ b := by
    change (a, b) = a • (1, 0) + b • (0, 1)
    simp
  rw [hdecomp, map_mul, map_zpow, map_zpow, h10]
  change (a • (1, 2) + b •
    (boundaryCoordinateMap h z e₁ e₂
      (Multiplicative.ofAdd (0, 1))).toAdd).2 = _
  simp [twiceSpiralSecondCoefficient]
  ring

/-- The actual H1 map obtained by first applying the boundary homeomorphism
and then including into the right solid torus has second coordinate
`2*a + d*b`. -/
theorem twistedBoundaryInclusion_H1_formula
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z) ≃* Multiplicative (ℤ × ℤ))
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z)) ≃*
      Multiplicative ℤ)
    (hinc₂ : ∀ p, c₂ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z) p) =
        secondCoordinateHom (e₂ p))
    (h10 : boundaryCoordinateMap h z e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2))
    (a b : ℤ) :
    solidH1CoordinateFromPi c₂ (Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap
        (singularPostcomposition
          ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1)
        ((HomologicalComplex.homologyMap
          (singularPostcomposition ⟨h, h.continuous⟩) 1)
          (Multiplicative.toAdd
            ((boundaryH1CoordinateFromPi e₁).symm
              (Multiplicative.ofAdd (a, b))))))) =
      Multiplicative.ofAdd
        (2 * a + twiceSpiralSecondCoefficient h z e₁ e₂ * b) := by
  let q : Multiplicative (ℤ × ℤ) := Multiplicative.ofAdd (a, b)
  let q' := boundaryCoordinateMap h z e₁ e₂ q
  have hh := h1CoordinateFromPi_naturality ⟨h, h.continuous⟩ e₁ e₂
    (boundaryHurewiczFromPi e₁) (boundaryHurewiczFromPi e₂) rfl rfl
    (boundaryCoordinateMap h z e₁ e₂) (by
      intro p
      simp [boundaryCoordinateMap]) q
  have hclass : Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap
        (singularPostcomposition ⟨h, h.continuous⟩) 1)
        (Multiplicative.toAdd ((boundaryH1CoordinateFromPi e₁).symm q))) =
      (boundaryH1CoordinateFromPi e₂).symm q' := by
    apply (boundaryH1CoordinateFromPi e₂).injective
    rw [(boundaryH1CoordinateFromPi e₂).apply_symm_apply]
    exact hh
  have hi := boundaryInclusion_H1_secondCoordinate (h z) e₂ c₂ hinc₂ q'
  change solidH1CoordinateFromPi c₂ (Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap
        (singularPostcomposition
          ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1)
        ((HomologicalComplex.homologyMap
          (singularPostcomposition ⟨h, h.continuous⟩) 1)
          (Multiplicative.toAdd
            ((boundaryH1CoordinateFromPi e₁).symm q))))) = _
  have hclass' := congrArg Multiplicative.toAdd hclass
  change ((HomologicalComplex.homologyMap
      (singularPostcomposition ⟨h, h.continuous⟩) 1)
      (Multiplicative.toAdd ((boundaryH1CoordinateFromPi e₁).symm q))) =
    Multiplicative.toAdd ((boundaryH1CoordinateFromPi e₂).symm q') at hclass'
  rw [hclass']
  exact hi.trans (congrArg Multiplicative.ofAdd
    (boundaryCoordinateMap_second_formula h z e₁ e₂ h10 a b))

/-- The signed degree-one Mayer--Vietoris coordinate arrow forced by a
twice-spiral first column; its remaining coefficient is intentionally left as
`d`. -/
def twiceSpiralSignedH1Arrow (d : ℤ) :
    (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun q := (q.2, -(2 * q.1 + d * q.2))
  map_zero' := by simp
  map_add' := by intro x y; ext <;> simp <;> ring

theorem twiceSpiralSignedH1Arrow_apply (d a b : ℤ) :
    twiceSpiralSignedH1Arrow d (a, b) = (b, -(2 * a + d * b)) := rfl

/-- The two actual induced H1 maps, with the Mayer--Vietoris minus sign on
the right component, assemble to `twiceSpiralSignedH1Arrow`. -/
theorem actual_signed_H1_pair_formula
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z) ≃* Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z)) ≃* Multiplicative ℤ)
    (hinc₁ : ∀ p, c₁ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z p) =
        secondCoordinateHom (e₁ p))
    (hinc₂ : ∀ p, c₂ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z) p) =
        secondCoordinateHom (e₂ p))
    (h10 : boundaryCoordinateMap h z e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2))
    (a b : ℤ) :
    ((solidH1CoordinateFromPi c₁ (Multiplicative.ofAdd
        ((HomologicalComplex.homologyMap
          (singularPostcomposition
            ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1)
          (Multiplicative.toAdd
            ((boundaryH1CoordinateFromPi e₁).symm
              (Multiplicative.ofAdd (a, b))))))).toAdd,
      -(solidH1CoordinateFromPi c₂ (Multiplicative.ofAdd
        ((HomologicalComplex.homologyMap
          (singularPostcomposition
            ⟨boundaryInclusion, continuous_boundaryInclusion⟩) 1)
          ((HomologicalComplex.homologyMap
            (singularPostcomposition ⟨h, h.continuous⟩) 1)
            (Multiplicative.toAdd
              ((boundaryH1CoordinateFromPi e₁).symm
                (Multiplicative.ofAdd (a, b)))))))).toAdd) =
      twiceSpiralSignedH1Arrow
        (twiceSpiralSecondCoefficient h z e₁ e₂) (a, b) := by
  rw [boundaryInclusion_H1_secondCoordinate z e₁ c₁ hinc₁
    (Multiplicative.ofAdd (a, b))]
  rw [twistedBoundaryInclusion_H1_formula h z e₁ e₂ c₂ hinc₂ h10 a b]
  rfl

#print axioms boundaryInclusion_H1_secondCoordinate
#print axioms boundaryCoordinateMap_second_formula
#print axioms twistedBoundaryInclusion_H1_formula
#print axioms twiceSpiralSignedH1Arrow_apply
#print axioms actual_signed_H1_pair_formula

end ConstructionTargets.TwiceSpiralH1Coordinates

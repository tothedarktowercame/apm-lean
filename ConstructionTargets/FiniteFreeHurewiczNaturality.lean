import ConstructionTargets.BoundaryTorusHurewiczIsomorphism

/-!
# Finite-free degree-one Hurewicz coordinates and naturality
-/

noncomputable section

namespace ConstructionTargets.FiniteFreeHurewiczNaturality

open CategoryTheory
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.DegreeOneHurewiczSurjective
open ConstructionTargets.CircleHurewiczIsomorphism
open ConstructionTargets.BoundaryTorusHurewiczIsomorphism
open ConstructionTargets.SingularSubdivision

/-- Abelianize a supplied finite-free fundamental-group coordinate. -/
def abelianizedFundamentalGroupCoordinate
    {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}
    (piCoord : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ)) :
    Abelianization (FundamentalGroup X x) ≃*
      Multiplicative (Fin n → ℤ) :=
  piCoord.abelianizationCongr.trans
    (commGroupAbelianizationMulEquiv (Multiplicative (Fin n → ℤ)))

/-- The abelianized Hurewicz map conjugated by arbitrary supplied finite-free
coordinates on its source and target. -/
def finiteFreeHurewiczCoordinate
    {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}
    (piCoord : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (h1Coord : Multiplicative (IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ)) :
    Multiplicative (Fin n → ℤ) →* Multiplicative (Fin n → ℤ) :=
  h1Coord.toMonoidHom.comp
    ((abelianizedFundamentalGroupToH1 x).comp
      (abelianizedFundamentalGroupCoordinate piCoord).symm.toMonoidHom)

theorem finiteFreeHurewiczCoordinate_surjective
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X} {n : ℕ}
    (piCoord : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (h1Coord : Multiplicative (IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ)) :
    Function.Surjective (finiteFreeHurewiczCoordinate piCoord h1Coord) :=
  h1Coord.surjective.comp
    ((abelianizedFundamentalGroupToH1_surjective x).comp
      (abelianizedFundamentalGroupCoordinate piCoord).symm.surjective)

theorem finiteFreeHurewiczCoordinate_injective
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X} {n : ℕ}
    (piCoord : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (h1Coord : Multiplicative (IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ)) :
    Function.Injective (finiteFreeHurewiczCoordinate piCoord h1Coord) :=
  multiplicative_finInt_monoidHom_injective_of_surjective _
    (finiteFreeHurewiczCoordinate_surjective piCoord h1Coord)

/-- Coordinate-parametric finite-free Hurewicz isomorphism.  Its forward map
is the explicit abelianized Hurewicz homomorphism. -/
def finiteFreeAbelianizedFundamentalGroupH1MulEquiv
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X} {n : ℕ}
    (piCoord : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (h1Coord : Multiplicative (IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ)) :
    Abelianization (FundamentalGroup X x) ≃* Multiplicative (IntegralH1 X) :=
  MulEquiv.ofBijective (abelianizedFundamentalGroupToH1 x) (by
    constructor
    · intro a b hab
      apply (abelianizedFundamentalGroupCoordinate piCoord).injective
      apply finiteFreeHurewiczCoordinate_injective piCoord h1Coord
      simpa [finiteFreeHurewiczCoordinate] using congrArg h1Coord hab
    · exact abelianizedFundamentalGroupToH1_surjective x)

/-- The conjugated Hurewicz endomorphism as an equivalence. -/
def finiteFreeHurewiczCoordinateMulEquiv
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X} {n : ℕ}
    (piCoord : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (h1Coord : Multiplicative (IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ)) :
    Multiplicative (Fin n → ℤ) ≃* Multiplicative (Fin n → ℤ) :=
  MulEquiv.ofBijective (finiteFreeHurewiczCoordinate piCoord h1Coord)
    ⟨finiteFreeHurewiczCoordinate_injective piCoord h1Coord,
      finiteFreeHurewiczCoordinate_surjective piCoord h1Coord⟩

/-- Naturality in arbitrary (possibly different-rank) coordinates.  A
calculation of the coordinate fundamental-group map determines the coordinate
integral-H1 map. -/
theorem h1_coordinate_eq_of_fundamentalGroup_coordinate_eq
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] {x : X} {n m : ℕ}
    (f : C(X, Y))
    (piCoordX : FundamentalGroup X x ≃* Multiplicative (Fin n → ℤ))
    (piCoordY : FundamentalGroup Y (f x) ≃* Multiplicative (Fin m → ℤ))
    (h1CoordX : Multiplicative (IntegralH1 X) ≃*
      Multiplicative (Fin n → ℤ))
    (h1CoordY : Multiplicative (IntegralH1 Y) ≃*
      Multiplicative (Fin m → ℤ))
    (coordinateMap : Multiplicative (Fin n → ℤ) →*
      Multiplicative (Fin m → ℤ))
    (hpi : ∀ p : FundamentalGroup X x,
      coordinateMap (piCoordX p) =
        piCoordY (FundamentalGroup.map f x p))
    (q : Multiplicative (Fin n → ℤ)) :
    h1CoordY (Multiplicative.ofAdd
        ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
          (Multiplicative.toAdd
            (h1CoordX.symm
              (finiteFreeHurewiczCoordinateMulEquiv piCoordX h1CoordX q))))) =
      finiteFreeHurewiczCoordinateMulEquiv piCoordY h1CoordY
        (coordinateMap q) := by
  let p : FundamentalGroup X x := piCoordX.symm q
  have hp : piCoordX p = q := piCoordX.apply_symm_apply q
  have hmap : piCoordY (FundamentalGroup.map f x p) = coordinateMap q := by
    rw [← hpi p, hp]
  have habX :
      (abelianizedFundamentalGroupCoordinate piCoordX).symm q =
        Abelianization.of p := by
    apply (abelianizedFundamentalGroupCoordinate piCoordX).injective
    rw [(abelianizedFundamentalGroupCoordinate piCoordX).apply_symm_apply]
    change q = piCoordX p
    exact hp.symm
  have habY :
      (abelianizedFundamentalGroupCoordinate piCoordY).symm
          (coordinateMap q) =
        Abelianization.of (FundamentalGroup.map f x p) := by
    apply (abelianizedFundamentalGroupCoordinate piCoordY).injective
    rw [(abelianizedFundamentalGroupCoordinate piCoordY).apply_symm_apply]
    change coordinateMap q = piCoordY (FundamentalGroup.map f x p)
    exact hmap.symm
  have habX' :
      (abelianizedFundamentalGroupCoordinate piCoordX).symm.toMonoidHom q =
        Abelianization.of p := habX
  have habY' :
      (abelianizedFundamentalGroupCoordinate piCoordY).symm.toMonoidHom
          (coordinateMap q) =
        Abelianization.of (FundamentalGroup.map f x p) := habY
  change h1CoordY (Multiplicative.ofAdd
      ((HomologicalComplex.homologyMap (singularPostcomposition f) 1)
        (Multiplicative.toAdd
          (h1CoordX.symm
            (finiteFreeHurewiczCoordinate piCoordX h1CoordX q))))) =
    finiteFreeHurewiczCoordinate piCoordY h1CoordY (coordinateMap q)
  simp only [finiteFreeHurewiczCoordinate, MonoidHom.comp_apply]
  rw [habX', habY', abelianizedFundamentalGroupToH1_of,
    abelianizedFundamentalGroupToH1_of]
  have hh : h1CoordX.symm
      (h1CoordX.toMonoidHom (fundamentalGroupH1Hom x p)) =
        fundamentalGroupH1Hom x p := h1CoordX.symm_apply_apply _
  rw [hh]
  exact congrArg h1CoordY (fundamentalGroupH1Hom_naturality f x p)

/-! Rank-one wrappers avoid choosing an identification `Fin 1 → ℤ ≃ ℤ`. -/

def abelianizedFundamentalGroupIntCoordinate
    {X : Type} [TopologicalSpace X] {x : X}
    (piCoord : FundamentalGroup X x ≃* Multiplicative ℤ) :
    Abelianization (FundamentalGroup X x) ≃* Multiplicative ℤ :=
  piCoord.abelianizationCongr.trans
    (commGroupAbelianizationMulEquiv (Multiplicative ℤ))

def rankOneHurewiczCoordinate
    {X : Type} [TopologicalSpace X] {x : X}
    (piCoord : FundamentalGroup X x ≃* Multiplicative ℤ)
    (h1Coord : Multiplicative (IntegralH1 X) ≃* Multiplicative ℤ) :
    Multiplicative ℤ →* Multiplicative ℤ :=
  h1Coord.toMonoidHom.comp
    ((abelianizedFundamentalGroupToH1 x).comp
      (abelianizedFundamentalGroupIntCoordinate piCoord).symm.toMonoidHom)

theorem rankOneHurewiczCoordinate_bijective
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X}
    (piCoord : FundamentalGroup X x ≃* Multiplicative ℤ)
    (h1Coord : Multiplicative (IntegralH1 X) ≃* Multiplicative ℤ) :
    Function.Bijective (rankOneHurewiczCoordinate piCoord h1Coord) := by
  have hs : Function.Surjective (rankOneHurewiczCoordinate piCoord h1Coord) :=
    h1Coord.surjective.comp
      ((abelianizedFundamentalGroupToH1_surjective x).comp
        (abelianizedFundamentalGroupIntCoordinate piCoord).symm.surjective)
  exact ⟨multiplicative_int_monoidHom_injective_of_surjective _ hs, hs⟩

#print axioms finiteFreeHurewiczCoordinate_injective
#print axioms finiteFreeAbelianizedFundamentalGroupH1MulEquiv
#print axioms h1_coordinate_eq_of_fundamentalGroup_coordinate_eq
#print axioms rankOneHurewiczCoordinate_bijective

end ConstructionTargets.FiniteFreeHurewiczNaturality

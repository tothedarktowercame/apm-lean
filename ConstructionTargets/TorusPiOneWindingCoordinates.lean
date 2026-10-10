import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.TwiceSpiralH1Coordinates
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism

noncomputable section
namespace ConstructionTargets.TorusPiOneWindingCoordinates

open ConstructionTargets.FundamentalGroupProduct
open ConstructionTargets.CircleUniversalCover
open ConstructionTargets.TwiceSpiralH1Coordinates
open ConstructionTargets.BoundaryTorusHurewiczIsomorphism

abbrev FrozenTorus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The two endpoint-winding coordinates on the based fundamental group of
the product torus. -/
def torusPi1Coord :
    FundamentalGroup (Circle × Circle) (1, 1) ≃*
      Multiplicative (Fin 2 → ℤ) :=
  (fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).trans
    ((circleFundamentalGroupMulEquivInt.prodCongr
      circleFundamentalGroupMulEquivInt).trans
        ((MulEquiv.prodMultiplicative ℤ ℤ).symm.trans
          intProdMulEquivFinTwo))

@[simp] theorem torusPi1Coord_apply_zero
    (p : FundamentalGroup (Circle × Circle) (1, 1)) :
    (torusPi1Coord p).toAdd 0 =
      (circleFundamentalGroupMulEquivInt (Path.Homotopic.projLeft p)).toAdd := by
  rfl

@[simp] theorem torusPi1Coord_apply_one
    (p : FundamentalGroup (Circle × Circle) (1, 1)) :
    (torusPi1Coord p).toAdd 1 =
      (circleFundamentalGroupMulEquivInt (Path.Homotopic.projRight p)).toAdd := by
  rfl

/-- Coordinate zero is the endpoint integer of the lifted left projection
of an explicit based product loop. -/
theorem torusPi1Coord_mk_apply_zero_eq_liftEndpoint
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 0 =
      liftBasedLoopEndpointInteger
        (gamma.map continuous_fst) (gamma.map continuous_fst).source
          (gamma.map continuous_fst).target := by
  change (circleFundamentalGroupMulEquivInt
      (Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk gamma))).toAdd = _
  rw [show Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk gamma) =
      Path.Homotopic.Quotient.mk (gamma.map continuous_fst) by
    exact (Path.Homotopic.Quotient.mk_map gamma ⟨Prod.fst, continuous_fst⟩).symm]
  rfl

/-- Coordinate one is the endpoint integer of the lifted right projection
of an explicit based product loop. -/
theorem torusPi1Coord_mk_apply_one_eq_liftEndpoint
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 1 =
      liftBasedLoopEndpointInteger
        (gamma.map continuous_snd) (gamma.map continuous_snd).source
          (gamma.map continuous_snd).target := by
  change (circleFundamentalGroupMulEquivInt
      (Path.Homotopic.projRight (Path.Homotopic.Quotient.mk gamma))).toAdd = _
  rw [show Path.Homotopic.projRight (Path.Homotopic.Quotient.mk gamma) =
      Path.Homotopic.Quotient.mk (gamma.map continuous_snd) by
    exact (Path.Homotopic.Quotient.mk_map gamma ⟨Prod.snd, continuous_snd⟩).symm]
  rfl

def frozenTorusHomeomorphCircleProd : FrozenTorus ≃ₜ Circle × Circle :=
  Homeomorph.prodCongr (AddCircle.homeomorphCircle one_ne_zero)
    (AddCircle.homeomorphCircle one_ne_zero)

@[simp] theorem frozenTorusHomeomorphCircleProd_base :
    frozenTorusHomeomorphCircleProd (0, 0) = ((1 : Circle), 1) := by
  simp [frozenTorusHomeomorphCircleProd, AddCircle.homeomorphCircle_apply]

noncomputable def frozenTorusPi1Coord :
    FundamentalGroup FrozenTorus (0, 0) ≃* Multiplicative (Fin 2 → ℤ) :=
  (fundamentalGroupMulEquivOfHomeomorph frozenTorusHomeomorphCircleProd (0, 0)).trans
    (by
      rw [frozenTorusHomeomorphCircleProd_base]
      exact torusPi1Coord)

def frozenLbar : C(FrozenTorus, FrozenTorus) :=
  ⟨fun p ↦ (2 • p.1 + p.2, p.2 - p.1), by fun_prop⟩

def circleMatrixMap : C(Circle × Circle, Circle × Circle) :=
  ⟨fun z ↦ (z.1 ^ (2 : ℕ) * z.2, z.2 * z.1⁻¹), by fun_prop⟩

theorem frozenTorusHomeomorphCircleProd_frozenLbar (p : FrozenTorus) :
    frozenTorusHomeomorphCircleProd (frozenLbar p) =
      circleMatrixMap (frozenTorusHomeomorphCircleProd p) := by
  ext <;>
    simp [frozenLbar, circleMatrixMap, frozenTorusHomeomorphCircleProd,
      AddCircle.homeomorphCircle_apply, sub_eq_add_neg,
      AddCircle.toCircle_add, AddCircle.toCircle_neg,
      AddCircle.toCircle_nsmul]

def circleMatrixLeftPath (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    Path (1 : Circle) 1 :=
  pointwiseMulPath (pointwiseMulPath (gamma.map continuous_fst) (gamma.map continuous_fst))
    (gamma.map continuous_snd)

def circleMatrixRightPath (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    Path (1 : Circle) 1 :=
  pointwiseMulPath (gamma.map continuous_snd)
    (pointwiseInvPath (gamma.map continuous_fst))

theorem circleMatrixLeftPath_endpointInteger
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    liftBasedLoopEndpointInteger (circleMatrixLeftPath gamma)
        (circleMatrixLeftPath gamma).source (circleMatrixLeftPath gamma).target =
      2 * liftBasedLoopEndpointInteger (gamma.map continuous_fst)
          (gamma.map continuous_fst).source (gamma.map continuous_fst).target +
        liftBasedLoopEndpointInteger (gamma.map continuous_snd)
          (gamma.map continuous_snd).source (gamma.map continuous_snd).target := by
  rw [circleMatrixLeftPath,
    liftBasedLoopEndpointInteger_pointwiseMulPath,
    liftBasedLoopEndpointInteger_pointwiseMulPath]
  ring

theorem circleMatrixRightPath_endpointInteger
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    liftBasedLoopEndpointInteger (circleMatrixRightPath gamma)
        (circleMatrixRightPath gamma).source (circleMatrixRightPath gamma).target =
      liftBasedLoopEndpointInteger (gamma.map continuous_snd)
          (gamma.map continuous_snd).source (gamma.map continuous_snd).target -
        liftBasedLoopEndpointInteger (gamma.map continuous_fst)
          (gamma.map continuous_fst).source (gamma.map continuous_fst).target := by
  rw [circleMatrixRightPath,
    liftBasedLoopEndpointInteger_pointwiseMulPath,
    liftBasedLoopEndpointInteger_pointwiseInvPath]
  ring

def circleMatrixMappedPath
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    Path ((1 : Circle), (1 : Circle)) (1, 1) where
  toFun t := circleMatrixMap (gamma t)
  continuous_toFun := circleMatrixMap.continuous.comp gamma.continuous
  source' := by simp [circleMatrixMap]
  target' := by simp [circleMatrixMap]

theorem circleMatrixMappedPath_projLeft
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (circleMatrixMappedPath gamma).map continuous_fst = circleMatrixLeftPath gamma := by
  ext t
  simp [circleMatrixMappedPath, circleMatrixLeftPath,
    ConstructionTargets.CircleUniversalCover.pointwiseMulPath, circleMatrixMap, pow_two]

theorem circleMatrixMappedPath_projRight
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (circleMatrixMappedPath gamma).map continuous_snd = circleMatrixRightPath gamma := by
  ext t
  simp [circleMatrixMappedPath, circleMatrixRightPath,
    ConstructionTargets.CircleUniversalCover.pointwiseMulPath,
    ConstructionTargets.CircleUniversalCover.pointwiseInvPath, circleMatrixMap]

theorem circleMatrixMap_base :
    circleMatrixMap ((1 : Circle), (1 : Circle)) = ((1 : Circle), (1 : Circle)) := by
  simp [circleMatrixMap]

def circleMatrixPi1Map :
    FundamentalGroup (Circle × Circle) ((1 : Circle), (1 : Circle)) →*
      FundamentalGroup (Circle × Circle) ((1 : Circle), (1 : Circle)) :=
  FundamentalGroup.mapOfEq circleMatrixMap circleMatrixMap_base

theorem circleMatrixPi1Map_mk
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    circleMatrixPi1Map (Path.Homotopic.Quotient.mk gamma) =
      Path.Homotopic.Quotient.mk (circleMatrixMappedPath gamma) := by
  rw [circleMatrixPi1Map, FundamentalGroup.mapOfEq_apply]
  rfl

theorem circleMatrixPi1Map_mk_coord_zero
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (torusPi1Coord (circleMatrixPi1Map (Path.Homotopic.Quotient.mk gamma))).toAdd 0 =
      2 * (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 0 +
        (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 1 := by
  rw [circleMatrixPi1Map_mk,
    torusPi1Coord_mk_apply_zero_eq_liftEndpoint,
    circleMatrixMappedPath_projLeft,
    circleMatrixLeftPath_endpointInteger,
    ← torusPi1Coord_mk_apply_zero_eq_liftEndpoint,
    ← torusPi1Coord_mk_apply_one_eq_liftEndpoint]

theorem circleMatrixPi1Map_mk_coord_one
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (torusPi1Coord (circleMatrixPi1Map (Path.Homotopic.Quotient.mk gamma))).toAdd 1 =
      (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 1 -
        (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 0 := by
  rw [circleMatrixPi1Map_mk,
    torusPi1Coord_mk_apply_one_eq_liftEndpoint,
    circleMatrixMappedPath_projRight,
    circleMatrixRightPath_endpointInteger,
    ← torusPi1Coord_mk_apply_zero_eq_liftEndpoint,
    ← torusPi1Coord_mk_apply_one_eq_liftEndpoint]

theorem circleMatrixPi1Map_coord_zero
    (p : FundamentalGroup (Circle × Circle) ((1 : Circle), (1 : Circle))) :
    (torusPi1Coord (circleMatrixPi1Map p)).toAdd 0 =
      2 * (torusPi1Coord p).toAdd 0 + (torusPi1Coord p).toAdd 1 := by
  induction p using Quotient.inductionOn with
  | _ gamma => exact circleMatrixPi1Map_mk_coord_zero gamma

theorem circleMatrixPi1Map_coord_one
    (p : FundamentalGroup (Circle × Circle) ((1 : Circle), (1 : Circle))) :
    (torusPi1Coord (circleMatrixPi1Map p)).toAdd 1 =
      (torusPi1Coord p).toAdd 1 - (torusPi1Coord p).toAdd 0 := by
  induction p using Quotient.inductionOn with
  | _ gamma => exact circleMatrixPi1Map_mk_coord_one gamma

theorem circleMatrixPi1Map_naturality
    (p : FundamentalGroup (Circle × Circle) ((1 : Circle), (1 : Circle))) :
    (torusPi1Coord (circleMatrixPi1Map p)).toAdd =
      fun i => Fin.cases
        (2 * (torusPi1Coord p).toAdd 0 + (torusPi1Coord p).toAdd 1)
        (fun _ => (torusPi1Coord p).toAdd 1 - (torusPi1Coord p).toAdd 0) i := by
  funext i
  fin_cases i
  · exact circleMatrixPi1Map_coord_zero p
  · exact circleMatrixPi1Map_coord_one p

def frozenCircleImagePath
    (gamma : Path ((0, 0) : FrozenTorus) (0, 0)) :
    Path ((1 : Circle), (1 : Circle)) (1, 1) where
  toFun t := frozenTorusHomeomorphCircleProd (gamma t)
  continuous_toFun := frozenTorusHomeomorphCircleProd.continuous.comp gamma.continuous
  source' := by simp
  target' := by simp

def frozenLbarCircleImagePath
    (gamma : Path ((0, 0) : FrozenTorus) (0, 0)) :
    Path ((1 : Circle), (1 : Circle)) (1, 1) where
  toFun t := frozenTorusHomeomorphCircleProd (frozenLbar (gamma t))
  continuous_toFun := frozenTorusHomeomorphCircleProd.continuous.comp
    (frozenLbar.continuous.comp gamma.continuous)
  source' := by simp [frozenLbar]
  target' := by simp [frozenLbar]

theorem frozenLbarCircleImagePath_eq_circleMatrixMappedPath
    (gamma : Path ((0, 0) : FrozenTorus) (0, 0)) :
    frozenLbarCircleImagePath gamma =
      circleMatrixMappedPath (frozenCircleImagePath gamma) := by
  ext t
  · exact congrArg Subtype.val
      (congrArg Prod.fst (frozenTorusHomeomorphCircleProd_frozenLbar (gamma t)))
  · exact congrArg Subtype.val
      (congrArg Prod.snd (frozenTorusHomeomorphCircleProd_frozenLbar (gamma t)))

end ConstructionTargets.TorusPiOneWindingCoordinates

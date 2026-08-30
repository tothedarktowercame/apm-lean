import ConstructionTargets.DegreeFourDiskBoundaryObstruction

/-! # The winding half of the degree-four disk obstruction -/

open scoped unitInterval
noncomputable section

namespace ConstructionTargets.DegreeFourCircleWinding

open ConstructionTargets.CircleWindingUniqueness
open ConstructionTargets.PeriodicCircleHomotopyWinding
open ConstructionTargets.DegreeFourDiskBoundaryObstruction

/-- The usual once-around parametrization of the unit circle. -/
def oneTurn : C(I, Circle) :=
  ⟨fun t ↦ Circle.exp ((2 * Real.pi) * (t : ℝ)), by fun_prop⟩

/-- The evident real lift of the fourth power of `oneTurn`. -/
def fourthPowerLift : C(I, ℝ) :=
  ⟨fun t ↦ 4 * (2 * Real.pi) * (t : ℝ), by fun_prop⟩

theorem exp_fourthPowerLift (t : I) :
    Circle.exp (fourthPowerLift t) = degreeFour (oneTurn t) := by
  apply Subtype.ext
  change Complex.exp (((4 * (2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
    Complex.exp ((((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) ^ 4
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem fourthPowerLift_endpointWinding :
    IsEndpointWinding (fourthPowerLift 1) (fourthPowerLift 0) 4 := by
  unfold IsEndpointWinding fourthPowerLift
  norm_num

private def squareOfHomotopy {q : Circle}
    (h : ContinuousMap.Homotopic degreeFour (ContinuousMap.const Circle q)) :
    C(I × I, Circle) :=
  ⟨fun p ↦ h.some.toContinuousMap (p.2, oneTurn p.1), by fun_prop⟩

private theorem squareOfHomotopy_zero {q : Circle}
    (h : ContinuousMap.Homotopic degreeFour (ContinuousMap.const Circle q)) (t : I) :
    squareOfHomotopy h (t, 0) = degreeFour (oneTurn t) := by
  exact h.some.map_zero_left (oneTurn t)

private theorem squareOfHomotopy_one {q : Circle}
    (h : ContinuousMap.Homotopic degreeFour (ContinuousMap.const Circle q)) (t : I) :
    squareOfHomotopy h (t, 1) = q := by
  exact h.some.map_one_left (oneTurn t)

/-- The fourth-power circle map is not freely homotopic to a constant. -/
theorem degreeFour_not_homotopic_const (q : Circle) :
    ¬ ContinuousMap.Homotopic degreeFour (ContinuousMap.const Circle q) := by
  intro h
  let Q := squareOfHomotopy h
  have hQ0 : Q (0, 0) = Circle.exp 0 := by
    rw [squareOfHomotopy_zero]
    apply Subtype.ext
    simp [oneTurn, degreeFour]
  have hloop : ∀ s : I, Q (1, s) = Q (0, s) := by
    intro s
    change h.some.toContinuousMap (s, oneTurn 1) =
      h.some.toContinuousMap (s, oneTurn 0)
    congr 2
    apply Subtype.ext
    simp [oneTurn]
  let L := liftedSquare Q 0 hQ0
  have hbottom : IsEndpointWinding (L (1, 0)) (L (0, 0)) 4 := by
    let d : I → ℝ := fun t ↦ L (t, 0) - fourthPowerLift t
    have hd : d 1 = d 0 := by
      apply Circle.isCoveringMap_exp.const_of_comp
      · dsimp [d]
        fun_prop
      · intro u v
        dsimp [d]
        rw [Circle.exp_sub, Circle.exp_sub, exp_liftedSquare, exp_liftedSquare,
          exp_fourthPowerLift, exp_fourthPowerLift,
          squareOfHomotopy_zero, squareOfHomotopy_zero]
        simp
    unfold IsEndpointWinding at ⊢
    dsimp [d] at hd
    change L (1, 0) - (4 * (2 * Real.pi) * (1 : ℝ)) =
      L (0, 0) - (4 * (2 * Real.pi) * (0 : ℝ)) at hd
    change L (1, 0) = L (0, 0) + (4 : ℝ) * (2 * Real.pi)
    norm_num at hd
    linarith
  have htop : IsEndpointWinding (L (1, 1)) (L (0, 1)) 0 := by
    unfold IsEndpointWinding
    have hc : L (1, 1) = L (0, 1) := by
      let e : C(I, ℝ) := L.comp
        ((ContinuousMap.id I).prodMk (ContinuousMap.const I (1 : I)))
      apply Circle.isCoveringMap_exp.const_of_comp e.continuous
      · intro u v
        change Circle.exp (L (u, 1)) = Circle.exp (L (v, 1))
        rw [exp_liftedSquare, exp_liftedSquare]
        rw [squareOfHomotopy_one, squareOfHomotopy_one]
    simpa using hc
  have : (4 : ℤ) = 0 :=
    uniqueEndpointWinding_agrees Q 0 hQ0 hloop hbottom htop
  norm_num at this

/-- A continuous disk map with fourth-power normalized boundary must vanish. -/
theorem exists_zero_of_degreeFour_normalizedBoundary
    (F : ComplexUnitDisk → ℂ) (hF : Continuous F)
    (hboundary : ∀ (hF0 : ∀ z, F z ≠ 0) (z : Circle),
      normalizedDiskMap F hF hF0 (circleToDisk z) = degreeFour z) :
    ∃ z, F z = 0 := by
  by_contra hz
  push_neg at hz
  exact degreeFour_not_homotopic_const _
    (degreeFour_homotopic_const_of_zeroFreeDiskExtension F hF hz (hboundary hz))

/-- It is enough that the normalized boundary be freely homotopic to the
fourth-power loop; literal boundary equality is not required. -/
theorem exists_zero_of_degreeFour_homotopic_normalizedBoundary
    (F : ComplexUnitDisk → ℂ) (hF : Continuous F)
    (hboundary : ∀ hF0 : ∀ z, F z ≠ 0,
      ContinuousMap.Homotopic degreeFour
        ((normalizedDiskMap F hF hF0).comp circleToDisk)) :
    ∃ z, F z = 0 := by
  by_contra hz
  push_neg at hz
  apply degreeFour_not_homotopic_const
    (normalizedDiskMap F hF hz diskZero)
  exact (hboundary hz).trans (normalized_boundary_homotopic_const F hF hz)

#print axioms exp_fourthPowerLift
#print axioms fourthPowerLift_endpointWinding
#print axioms degreeFour_not_homotopic_const
#print axioms exists_zero_of_degreeFour_normalizedBoundary
#print axioms exists_zero_of_degreeFour_homotopic_normalizedBoundary

end ConstructionTargets.DegreeFourCircleWinding

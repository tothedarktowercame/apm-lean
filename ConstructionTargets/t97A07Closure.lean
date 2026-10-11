import Mathlib

noncomputable section

namespace t97A07Closure

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Surjective continuous linear maps between finite-dimensional real normed spaces form an
open set. -/
theorem isOpen_setOf_surjective_clm [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  obtain ⟨R, hR⟩ := L.exists_right_inverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  let Φ : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ F E F).flip R
  have hΦ : Continuous Φ := Φ.continuous
  have hunit : Φ L ∈ {A : F →L[ℝ] F | IsUnit A} := by
    rw [show Φ L = ContinuousLinearMap.id ℝ F by simpa [Φ] using hR]
    exact isUnit_one
  filter_upwards [hΦ.continuousAt (Units.isOpen.mem_nhds hunit)] with L' hL'
  rcases hL' with ⟨u, hu⟩
  intro y
  refine ⟨R ((↑(u⁻¹) : F →L[ℝ] F) y), ?_⟩
  change Φ L' ((↑(u⁻¹) : F →L[ℝ] F) y) = y
  rw [← hu]
  simpa only [← ContinuousLinearMap.comp_apply, ← Units.val_mul] using
    congrArg (fun A : F →L[ℝ] F ↦ A y) (u.mul_inv)

open scoped Manifold ContDiff

abbrev EuclideanModel (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The fixed-chart representative supplied by manifold smoothness has a
continuous derivative within the model-with-corners range at the chart
centre.  This is the analytic continuity component of blueprint B2. -/
theorem continuousWithinAt_coordinate_fderivWithin
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    ContinuousWithinAt
      (fderivWithin ℝ
        (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
          (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
        (Set.range 𝓘(ℝ, EuclideanModel m)))
      (Set.range 𝓘(ℝ, EuclideanModel m))
      (extChartAt 𝓘(ℝ, EuclideanModel m) x x) := by
  have hcoord := (contMDiffAt_iff.mp (hf x)).2
  exact hcoord.continuousWithinAt_fderivWithin
    (ModelWithCorners.uniqueDiffOn 𝓘(ℝ, EuclideanModel m))
    (by simp) (by
      change 𝓘(ℝ, EuclideanModel m)
          ((extChartAt 𝓘(ℝ, EuclideanModel m) x) x) ∈
        Set.range 𝓘(ℝ, EuclideanModel m)
      exact Set.mem_range_self _)

/-- At the chart centre, the fixed-coordinate derivative is exactly the
manifold derivative.  The equality is well typed because the target is its
model vector space; no tangent spaces at distinct points are identified. -/
theorem coordinate_fderivWithin_eq_mfderiv
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    fderivWithin ℝ
        (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
          (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
        (Set.range 𝓘(ℝ, EuclideanModel m))
        (extChartAt 𝓘(ℝ, EuclideanModel m) x x) =
      mfderiv 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) f x := by
  have hd : MDifferentiableAt 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) f x :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv]
  simp only [hd, if_pos, writtenInExtChartAt]

end t97A07Closure

#print axioms t97A07Closure.isOpen_setOf_surjective_clm
#print axioms t97A07Closure.continuousWithinAt_coordinate_fderivWithin
#print axioms t97A07Closure.coordinate_fderivWithin_eq_mfderiv

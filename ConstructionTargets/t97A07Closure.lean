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

/-- At a nearby point lying in the fixed source and target charts, the
manifold derivative written in the tangent coordinates based at `x` is the
literal composite of the target chart derivative, `mfderiv f y`, and the
inverse source chart derivative.  This is the chart-transition equality
component of blueprint B2; no tangent fibers at distinct points are
identified directly. -/
theorem inTangentCoordinates_mfderiv_eq_chart_factors
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n) (x y : X)
    (hx : y ∈ (chartAt (EuclideanModel m) x).source)
    (hy : f y ∈ (chartAt (EuclideanModel n) (f x)).source) :
    inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x y =
      (mfderiv 𝓘(ℝ, EuclideanModel n) 𝓘(ℝ, EuclideanModel n)
          (extChartAt 𝓘(ℝ, EuclideanModel n) (f x)) (f y)) ∘L
        (mfderiv 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) f y) ∘L
          (mfderivWithin (I := 𝓘(ℝ, EuclideanModel m))
            (I' := 𝓘(ℝ, EuclideanModel m))
            (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm
            (Set.range 𝓘(ℝ, EuclideanModel m))
            (extChartAt 𝓘(ℝ, EuclideanModel m) x y)) := by
  exact inTangentCoordinates_eq_mfderiv_comp hx hy

/-- In fixed tangent coordinates based at `x`, the manifold derivative of a
smooth map varies continuously at `x`.  This packages the coordinate
transport needed before applying openness of surjective linear maps. -/
theorem continuousAt_inTangentCoordinates_mfderiv
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    ContinuousAt
      (inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x) x := by
  exact (hf.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt

/-- At its base point, the transported derivative reduces to the manifold
derivative followed by the inverse source-chart derivative. -/
theorem inTangentCoordinates_mfderiv_self_eq_sourceChartFactor
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n) (x : X) :
    inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x x =
      (mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f x) ∘L
        (mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel m)
          (chartAt (EuclideanModel m) x).symm
          ((chartAt (EuclideanModel m) x) x)) := by
  rw [inTangentCoordinates_eq_mfderiv_comp]
  · simp
  · exact mem_chart_source (EuclideanModel m) x
  · exact mem_chart_source (EuclideanModel n) (f x)

/-- At the chart centre of a Euclidean-model manifold, the derivative of the
inverse source chart is the identity on the model vector space. -/
theorem mfderiv_chartAt_symm_self_eq_id
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (x : X) :
    mfderiv 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel m)
        (chartAt (EuclideanModel m) x).symm
        ((chartAt (EuclideanModel m) x) x) =
      ContinuousLinearMap.id ℝ (EuclideanModel m) := by
  simpa using
    (mfderivWithin_range_extChartAt_symm
      (I := 𝓘(ℝ, EuclideanModel m)) (x := x))

/-- Consequently, the fixed tangent-coordinate family agrees with the
original manifold derivative at its centre. -/
theorem inTangentCoordinates_mfderiv_self_eq_mfderiv
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n) (x : X) :
    inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x x =
      mfderiv 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) f x := by
  rw [inTangentCoordinates_mfderiv_self_eq_sourceChartFactor,
    mfderiv_chartAt_symm_self_eq_id]
  exact ContinuousLinearMap.comp_id _

end t97A07Closure

#print axioms t97A07Closure.isOpen_setOf_surjective_clm
#print axioms t97A07Closure.continuousWithinAt_coordinate_fderivWithin
#print axioms t97A07Closure.coordinate_fderivWithin_eq_mfderiv
#print axioms t97A07Closure.inTangentCoordinates_mfderiv_eq_chart_factors
#print axioms t97A07Closure.continuousAt_inTangentCoordinates_mfderiv
#print axioms t97A07Closure.inTangentCoordinates_mfderiv_self_eq_sourceChartFactor
#print axioms t97A07Closure.mfderiv_chartAt_symm_self_eq_id
#print axioms t97A07Closure.inTangentCoordinates_mfderiv_self_eq_mfderiv

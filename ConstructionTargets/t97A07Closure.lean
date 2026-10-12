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

open scoped Manifold ContDiff Topology

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

/-- Near a fixed base point, both the source point and its image remain in
the fixed charts used by the tangent-coordinate derivative. -/
theorem eventually_mem_fixed_chart_sources
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    ∀ᶠ y in 𝓝 x,
      y ∈ (chartAt (EuclideanModel m) x).source ∧
        f y ∈ (chartAt (EuclideanModel n) (f x)).source := by
  filter_upwards [chart_source_mem_nhds (EuclideanModel m) x,
    hf.continuous.continuousAt.preimage_mem_nhds
      (chart_source_mem_nhds (EuclideanModel n) (f x))] with y hy hfy
  exact ⟨hy, hfy⟩

/-- On one neighbourhood of the base point, the transported derivative has
the explicit fixed-chart factorization at every point. -/
theorem eventually_inTangentCoordinates_mfderiv_eq_chart_factors
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    ∀ᶠ y in 𝓝 x,
      inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
          (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f z) x y =
        (mfderiv 𝓘(ℝ, EuclideanModel n) 𝓘(ℝ, EuclideanModel n)
            (extChartAt 𝓘(ℝ, EuclideanModel n) (f x)) (f y)) ∘L
          (mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f y) ∘L
            (mfderivWithin (I := 𝓘(ℝ, EuclideanModel m))
              (I' := 𝓘(ℝ, EuclideanModel m))
              (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm
              (Set.range 𝓘(ℝ, EuclideanModel m))
              (extChartAt 𝓘(ℝ, EuclideanModel m) x y)) := by
  filter_upwards [eventually_mem_fixed_chart_sources f hf x] with y hy
  exact inTangentCoordinates_mfderiv_eq_chart_factors f x y hy.1 hy.2

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

/-- At the common chart centre, the fixed-coordinate derivative and the
transported manifold derivative are the same continuous linear map. -/
theorem coordinate_fderivWithin_eq_inTangentCoordinates_mfderiv_self
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
      inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x x := by
  rw [coordinate_fderivWithin_eq_mfderiv f hf x,
    inTangentCoordinates_mfderiv_self_eq_mfderiv]

/-- At the common centre, the fixed-coordinate derivative is the same
three-factor chart expression used uniformly for nearby transported
derivatives. -/
theorem coordinate_fderivWithin_eq_chart_factors_self
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
      (mfderiv 𝓘(ℝ, EuclideanModel n) 𝓘(ℝ, EuclideanModel n)
          (extChartAt 𝓘(ℝ, EuclideanModel n) (f x)) (f x)) ∘L
        (mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f x) ∘L
          (mfderivWithin (I := 𝓘(ℝ, EuclideanModel m))
            (I' := 𝓘(ℝ, EuclideanModel m))
            (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm
            (Set.range 𝓘(ℝ, EuclideanModel m))
            (extChartAt 𝓘(ℝ, EuclideanModel m) x x)) := by
  rw [coordinate_fderivWithin_eq_inTangentCoordinates_mfderiv_self f hf x]
  exact inTangentCoordinates_mfderiv_eq_chart_factors f x x
    (mem_chart_source (EuclideanModel m) x)
    (mem_chart_source (EuclideanModel n) (f x))

/-- A single neighbourhood supports both fixed chart memberships and the
nearby chart-factor formula, while the fixed-coordinate derivative anchors
that family at the centre. -/
theorem exists_nhds_chart_factor_agreement
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    ∃ U ∈ 𝓝 x, (∀ y ∈ U,
        y ∈ (chartAt (EuclideanModel m) x).source ∧
        f y ∈ (chartAt (EuclideanModel n) (f x)).source ∧
        inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
            (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
              𝓘(ℝ, EuclideanModel n) f z) x y =
          (mfderiv 𝓘(ℝ, EuclideanModel n) 𝓘(ℝ, EuclideanModel n)
              (extChartAt 𝓘(ℝ, EuclideanModel n) (f x)) (f y)) ∘L
            (mfderiv 𝓘(ℝ, EuclideanModel m)
              𝓘(ℝ, EuclideanModel n) f y) ∘L
              (mfderivWithin (I := 𝓘(ℝ, EuclideanModel m))
                (I' := 𝓘(ℝ, EuclideanModel m))
                (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm
                (Set.range 𝓘(ℝ, EuclideanModel m))
                (extChartAt 𝓘(ℝ, EuclideanModel m) x y))) ∧
      fderivWithin ℝ
          (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
            (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
          (Set.range 𝓘(ℝ, EuclideanModel m))
          (extChartAt 𝓘(ℝ, EuclideanModel m) x x) =
        inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
          (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f z) x x := by
  let U := {y | y ∈ (chartAt (EuclideanModel m) x).source ∧
    f y ∈ (chartAt (EuclideanModel n) (f x)).source}
  have hU : U ∈ 𝓝 x := eventually_mem_fixed_chart_sources f hf x
  refine ⟨U, hU, ?_,
    coordinate_fderivWithin_eq_inTangentCoordinates_mfderiv_self f hf x⟩
  intro y hy
  exact ⟨hy.1, hy.2,
    inTangentCoordinates_mfderiv_eq_chart_factors f x y hy.1 hy.2⟩

/-- The coordinate-transported derivative is continuous at the base point
and is anchored there by the original manifold derivative.  This packages
the two facts needed before comparing it with the fixed representative after
precomposition by the fixed source chart. -/
theorem continuousAt_inTangentCoordinates_mfderiv_and_self
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
            𝓘(ℝ, EuclideanModel n) f z) x) x ∧
      inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
          (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f z) x x =
        mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f x := by
  exact ⟨continuousAt_inTangentCoordinates_mfderiv f hf x,
    inTangentCoordinates_mfderiv_self_eq_mfderiv f x⟩

/-- Precomposing the derivative of the fixed-chart representative with the
fixed source chart gives an operator-valued function on the manifold that is
continuous at the base point.  This is the domain bridge needed before its
pointwise comparison with the transported manifold derivative. -/
theorem continuousAt_coordinate_fderivWithin_comp_extChartAt
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    ContinuousAt
      (fun y ↦ fderivWithin ℝ
        (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
          (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
        (Set.range 𝓘(ℝ, EuclideanModel m))
        (extChartAt 𝓘(ℝ, EuclideanModel m) x y)) x := by
  have h := continuousWithinAt_coordinate_fderivWithin f hf x
  rw [ContinuousWithinAt] at h
  rw [ContinuousAt]
  apply h.comp
  rw [← map_extChartAt_nhds (I := 𝓘(ℝ, EuclideanModel m)) x]
  exact Filter.tendsto_map

end t97A07Closure

#print axioms t97A07Closure.isOpen_setOf_surjective_clm
#print axioms t97A07Closure.continuousWithinAt_coordinate_fderivWithin
#print axioms t97A07Closure.coordinate_fderivWithin_eq_mfderiv
#print axioms t97A07Closure.inTangentCoordinates_mfderiv_eq_chart_factors
#print axioms t97A07Closure.continuousAt_inTangentCoordinates_mfderiv
#print axioms t97A07Closure.eventually_mem_fixed_chart_sources
#print axioms t97A07Closure.eventually_inTangentCoordinates_mfderiv_eq_chart_factors
#print axioms t97A07Closure.inTangentCoordinates_mfderiv_self_eq_sourceChartFactor
#print axioms t97A07Closure.mfderiv_chartAt_symm_self_eq_id
#print axioms t97A07Closure.inTangentCoordinates_mfderiv_self_eq_mfderiv
#print axioms t97A07Closure.coordinate_fderivWithin_eq_inTangentCoordinates_mfderiv_self
#print axioms t97A07Closure.coordinate_fderivWithin_eq_chart_factors_self
#print axioms t97A07Closure.exists_nhds_chart_factor_agreement
#print axioms t97A07Closure.continuousAt_inTangentCoordinates_mfderiv_and_self
#print axioms t97A07Closure.continuousAt_coordinate_fderivWithin_comp_extChartAt

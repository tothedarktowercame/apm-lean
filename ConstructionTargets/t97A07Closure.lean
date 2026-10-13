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

/-- On the common fixed-chart neighbourhood, differentiating the fixed
representative at the source-chart image gives exactly the transported
manifold derivative. -/
theorem coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x y : X)
    (hx : y ∈ (chartAt (EuclideanModel m) x).source)
    (hy : f y ∈ (chartAt (EuclideanModel n) (f x)).source) :
    fderivWithin ℝ
        (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
          (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
        (Set.range 𝓘(ℝ, EuclideanModel m))
        (extChartAt 𝓘(ℝ, EuclideanModel m) x y) =
      inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x y := by
  rw [inTangentCoordinates_eq_mfderiv_comp hx hy]
  have hxe : y ∈ (extChartAt 𝓘(ℝ, EuclideanModel m) x).source := by
    simpa only [extChartAt_source] using hx
  have hz := (extChartAt 𝓘(ℝ, EuclideanModel m) x).map_source hxe
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, EuclideanModel m)
      (Set.range 𝓘(ℝ, EuclideanModel m))
      (extChartAt 𝓘(ℝ, EuclideanModel m) x y) :=
    𝓘(ℝ, EuclideanModel m).uniqueMDiffOn _ (Set.mem_range_self _)
  have hinv := mdifferentiableWithinAt_extChartAt_symm hz
  have hfy := (hf y).mdifferentiableAt (by simp)
  have A := mfderiv_comp_mfderivWithin_of_eq hfy hinv hU
    ((extChartAt 𝓘(ℝ, EuclideanModel m) x).left_inv hxe)
  rw [← A]
  have hcomp : MDifferentiableWithinAt 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n)
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
      (Set.range 𝓘(ℝ, EuclideanModel m))
      (extChartAt 𝓘(ℝ, EuclideanModel m) x y) :=
    MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
      (extChartAt 𝓘(ℝ, EuclideanModel m) x y) hfy hinv
      ((extChartAt 𝓘(ℝ, EuclideanModel m) x).left_inv hxe)
  have B := mfderiv_comp_mfderivWithin_of_eq
    (mdifferentiableAt_extChartAt hy) hcomp hU (by
      simp only [Function.comp_apply,
        (extChartAt 𝓘(ℝ, EuclideanModel m) x).left_inv hxe])
  rw [← B]
  simp only [mfderivWithin_eq_fderivWithin]

/-- The fixed-coordinate derivative and the transported manifold derivative
agree eventually at the base point. -/
theorem eventually_coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m) 𝓘(ℝ, EuclideanModel n) ∞ f)
    (x : X) :
    (fun y ↦ fderivWithin ℝ
        (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
          (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
        (Set.range 𝓘(ℝ, EuclideanModel m))
        (extChartAt 𝓘(ℝ, EuclideanModel m) x y)) =ᶠ[𝓝 x]
      inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x := by
  filter_upwards [eventually_mem_fixed_chart_sources f hf x] with y hy
  exact coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates
    f hf x y hy.1 hy.2

/-- B2 interface: in fixed tangent coordinates, both presentations of the
derivative are continuous, agree near the base point, and the transported
presentation has value `mfderiv f x` at the base point. -/
theorem continuousAt_coordinate_mfderiv
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
          (extChartAt 𝓘(ℝ, EuclideanModel m) x y)) x ∧
      ContinuousAt
        (inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
          (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f z) x) x ∧
      (fun y ↦ fderivWithin ℝ
          (extChartAt 𝓘(ℝ, EuclideanModel n) (f x) ∘ f ∘
            (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm)
          (Set.range 𝓘(ℝ, EuclideanModel m))
          (extChartAt 𝓘(ℝ, EuclideanModel m) x y)) =ᶠ[𝓝 x]
        inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
          (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f z) x ∧
      inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
          (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
            𝓘(ℝ, EuclideanModel n) f z) x x =
        mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f x := by
  exact ⟨continuousAt_coordinate_fderivWithin_comp_extChartAt f hf x,
    continuousAt_inTangentCoordinates_mfderiv f hf x,
    eventually_coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates
      f hf x,
    inTangentCoordinates_mfderiv_self_eq_mfderiv f x⟩

/-- Surjectivity of the fixed tangent-coordinate representative forces
surjectivity of the underlying manifold derivative.  Only injectivity of the
target chart derivative is needed; the source chart factor supplies a
preimage candidate. -/
theorem surjective_mfderiv_of_surjective_inTangentCoordinates
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n) (x y : X)
    (hx : y ∈ (chartAt (EuclideanModel m) x).source)
    (hy : f y ∈ (chartAt (EuclideanModel n) (f x)).source)
    (h : Function.Surjective
      (inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
        (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f z) x y)) :
    Function.Surjective
      (mfderiv 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) f y) := by
  let A := mfderiv 𝓘(ℝ, EuclideanModel n) 𝓘(ℝ, EuclideanModel n)
    (extChartAt 𝓘(ℝ, EuclideanModel n) (f x)) (f y)
  let B := mfderivWithin (I := 𝓘(ℝ, EuclideanModel m))
    (I' := 𝓘(ℝ, EuclideanModel m))
    (extChartAt 𝓘(ℝ, EuclideanModel m) x).symm
    (Set.range 𝓘(ℝ, EuclideanModel m))
    (extChartAt 𝓘(ℝ, EuclideanModel m) x y)
  have hA : Function.Injective A := by
    dsimp only [A]
    rw [(hasMFDerivAt_extChartAt hy).mfderiv]
    exact (mdifferentiable_chart (f x)).mfderiv_injective hy
  intro v
  obtain ⟨w, hw⟩ := h (A v)
  refine ⟨B w, hA ?_⟩
  rw [inTangentCoordinates_mfderiv_eq_chart_factors f x y hx hy] at hw
  exact hw

/-- B3: for a smooth map between the Euclidean-model manifolds used by
`t97A07`, the points where the manifold derivative is surjective form an open
set. -/
theorem isOpen_regularPoints
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) ∞ f) :
    IsOpen {x | Function.Surjective
      (mfderiv 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) f x)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let T := inTangentCoordinates 𝓘(ℝ, EuclideanModel m)
    𝓘(ℝ, EuclideanModel n) (fun z : X ↦ z) f
    (fun z ↦ mfderiv 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) f z) x
  have hB2 := continuousAt_coordinate_mfderiv f hf x
  have hTx : T x = mfderiv 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) f x := hB2.2.2.2
  have hopen : IsOpen {L : EuclideanModel m →L[ℝ] EuclideanModel n |
      Function.Surjective L} := isOpen_setOf_surjective_clm
  have hTsurj : Function.Surjective (T x) := by
    rw [hTx]
    exact hx
  have hsurj : ∀ᶠ y in 𝓝 x, Function.Surjective (T y) :=
    hB2.2.1.preimage_mem_nhds (hopen.mem_nhds hTsurj)
  filter_upwards [hsurj, eventually_mem_fixed_chart_sources f hf x] with y hTy hy
  exact surjective_mfderiv_of_surjective_inTangentCoordinates
    f x y hy.1 hy.2 hTy

/-- The image of the critical-point set is compact.  This is the reusable
compactness core of B4; the problem adapter identifies this image with its
frozen existential definition of critical values. -/
theorem isCompact_image_criticalPoints
    {m n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) ∞ f) :
    IsCompact (f '' {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) f x)}) := by
  have hclosed : IsClosed {x | ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) f x)} := by
    simpa only [Set.compl_setOf] using
      (isOpen_regularPoints f hf).isClosed_compl
  exact hclosed.isCompact.image hf.continuous

/-- If one target coordinate vanishes on the range of a continuous linear
map into Euclidean space, that map is not surjective.  This is the final
linear-algebra contradiction in blueprint B5. -/
theorem not_surjective_of_coordinate_eq_zero
    {m n : ℕ} (L : EuclideanModel m →L[ℝ] EuclideanModel n)
    (i : Fin n) (hzero : ∀ v, L v i = 0) :
    ¬ Function.Surjective L := by
  intro hsurj
  obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.single i 1)
  have hi := congrArg (fun w : EuclideanModel n ↦ w i) hv
  change L v i = (EuclideanSpace.single i 1 : EuclideanModel n) i at hi
  rw [hzero v] at hi
  simp at hi

/-- A global maximum of one target coordinate remains a local maximum after
passing to the fixed extended source chart. -/
theorem isLocalMax_coordinate_comp_extChartAt_symm
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n) (i : Fin n) (x : X)
    (hmax : IsMaxOn (fun z ↦ f z i) Set.univ x) :
    IsLocalMax
      (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z) i)
      (extChartAt 𝓘(ℝ, EuclideanModel m) x x) := by
  have hmax' : IsMaxOn
      (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z) i)
      Set.univ (extChartAt 𝓘(ℝ, EuclideanModel m) x x) := by
    rw [isMaxOn_univ_iff] at hmax ⊢
    intro z
    simpa using hmax
      ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z)
  exact hmax'.isLocalMax (by simp)

/-- Fermat's theorem applied after transferring a coordinate maximum to the
fixed source chart. -/
theorem fderiv_coordinate_comp_extChartAt_symm_eq_zero
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n) (i : Fin n) (x : X)
    (hmax : IsMaxOn (fun z ↦ f z i) Set.univ x) :
    fderiv ℝ
      (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z) i)
      (extChartAt 𝓘(ℝ, EuclideanModel m) x x) = 0 :=
  (isLocalMax_coordinate_comp_extChartAt_symm f i x hmax).fderiv_eq_zero

/-- The derivative of a selected coordinate after the inverse source chart is
the selected coordinate of the manifold derivative. -/
theorem fderiv_coordinate_comp_extChartAt_symm_apply
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) ∞ f)
    (i : Fin n) (x : X) (v : EuclideanModel m) :
    fderiv ℝ
      (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z) i)
      (extChartAt 𝓘(ℝ, EuclideanModel m) x x) v =
      (NormedSpace.fromTangentSpace (f x)
        (mfderiv 𝓘(ℝ, EuclideanModel m)
          𝓘(ℝ, EuclideanModel n) f x v)) i := by
  have hvec := coordinate_fderivWithin_eq_mfderiv f hf x
  have hd : DifferentiableAt ℝ
      (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z))
      (extChartAt 𝓘(ℝ, EuclideanModel m) x x) := by
    have hcoord := (contMDiffAt_iff.mp (hf x)).2
    rw [← differentiableWithinAt_univ]
    simpa using hcoord.differentiableWithinAt (by simp)
  rw [show (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z) i) =
      (EuclideanSpace.proj i : EuclideanModel n → ℝ) ∘
        (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanModel m) x).symm z)) by rfl,
    fderiv_comp _ (by fun_prop) hd, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]
  simpa [NormedSpace.fromTangentSpace, ContinuousLinearMap.fderiv] using
    congrArg (fun L : EuclideanModel m →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanModel n) (f x) ↦
      (NormedSpace.fromTangentSpace (f x) (L v)) i) hvec

/-- Blueprint B5: a global maximum of one target coordinate forces the
manifold derivative to be nonsurjective. -/
theorem not_surjective_mfderiv_of_isMaxOn_coordinate
    {m n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanModel m) X]
    [IsManifold 𝓘(ℝ, EuclideanModel m) ∞ X]
    (f : X → EuclideanModel n)
    (hf : ContMDiff 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) ∞ f)
    (i : Fin n) (x : X)
    (hmax : IsMaxOn (fun z ↦ f z i) Set.univ x) :
    ¬ Function.Surjective
      (mfderiv 𝓘(ℝ, EuclideanModel m)
        𝓘(ℝ, EuclideanModel n) f x) := by
  apply not_surjective_of_coordinate_eq_zero _ i
  intro v
  change (NormedSpace.fromTangentSpace (f x)
    (mfderiv 𝓘(ℝ, EuclideanModel m)
      𝓘(ℝ, EuclideanModel n) f x v)) i = 0
  rw [← fderiv_coordinate_comp_extChartAt_symm_apply f hf i x v]
  have hz := congrArg (fun L : EuclideanModel m →L[ℝ] ℝ ↦ L v)
    (fderiv_coordinate_comp_extChartAt_symm_eq_zero f i x hmax)
  simpa using hz

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
#print axioms t97A07Closure.coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates
#print axioms t97A07Closure.eventually_coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates
#print axioms t97A07Closure.continuousAt_coordinate_mfderiv
#print axioms t97A07Closure.surjective_mfderiv_of_surjective_inTangentCoordinates
#print axioms t97A07Closure.isOpen_regularPoints
#print axioms t97A07Closure.isCompact_image_criticalPoints
#print axioms t97A07Closure.not_surjective_of_coordinate_eq_zero
#print axioms t97A07Closure.isLocalMax_coordinate_comp_extChartAt_symm
#print axioms t97A07Closure.fderiv_coordinate_comp_extChartAt_symm_eq_zero
#print axioms t97A07Closure.fderiv_coordinate_comp_extChartAt_symm_apply
#print axioms t97A07Closure.not_surjective_mfderiv_of_isMaxOn_coordinate

import Mathlib
import ConstructionTargets.t00J02Closure

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace ConstructionTargets.T00J02Closure

/-- The fixed-target-chart Sard selector can be constrained to any open
neighborhood of the chart centre.  The chart-coordinate image of that
neighborhood is a nonempty open set, hence has positive additive Haar
measure, while the critical image is null. -/
theorem exists_mfderiv_surjective_fiber_mem_open_of_fixedTargetChart
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (g : M → N) (y : N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ g)
    (O : Set N) (hO : IsOpen O) (hyO : y ∈ O) :
    ∃ z ∈ O, ∀ x, g x = z → Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) g x) := by
  let bad : Set F := ((chartAt F y) ∘ g) ''
    {x | x ∈ targetChartDomain (F := F) g y hg.continuous ∧
      ¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
          ((chartAt F y) ∘ g) x)}
  have hbad : mu bad = 0 := targetChartCoordinate_ambientCriticalImage_null mu g y hg
  let T : Set F := (chartAt F y).target ∩ (chartAt F y).symm ⁻¹' O
  have hTopen : IsOpen T := (chartAt F y).isOpen_inter_preimage_symm hO
  have hyT : chartAt F y y ∈ T := by
    refine ⟨mem_chart_target F y, ?_⟩
    change (chartAt F y).symm (chartAt F y y) ∈ O
    rw [(chartAt F y).left_inv (mem_chart_source F y)]
    exact hyO
  have hT : mu T ≠ 0 := hTopen.measure_ne_zero mu ⟨_, hyT⟩
  have hnsub : ¬ T ⊆ bad := by
    intro hsub
    exact hT (MeasureTheory.measure_mono_null hsub hbad)
  rcases Set.not_subset.mp hnsub with ⟨v, hvT, hvbad⟩
  refine ⟨(chartAt F y).symm v, hvT.2, fun x hx ↦ ?_⟩
  have hxsource : g x ∈ (chartAt F y).source := by
    rw [hx]
    exact (chartAt F y).map_target hvT.1
  by_contra hcrit
  apply hvbad
  refine ⟨x, ⟨hxsource, ?_⟩, ?_⟩
  · intro hs
    exact hcrit ((mfderiv_targetChart_comp_surjective_iff_of_mem_source
      g x y (hg.mdifferentiableAt (by simp)) hxsource).mpr hs)
  · change chartAt F y (g x) = v
    rw [hx, (chartAt F y).right_inv hvT.1]

/-- Nonvanishing of the manifold derivative is stable near a point for a
smooth map.  The derivative is compared in the fixed tangent coordinates at
the base point, where both coordinate changes are identities. -/
theorem mfderiv_ne_zero_eventually
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (c : Circle → S)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (z₀ : Circle)
    (hz₀ : mfderiv (𝓡 1) SurfaceModelWithCorners c z₀ ≠ 0) :
    ∀ᶠ z in 𝓝 z₀,
      mfderiv (𝓡 1) SurfaceModelWithCorners c z ≠ 0 := by
  let D := inTangentCoordinates (𝓡 1) SurfaceModelWithCorners id c
    (mfderiv (𝓡 1) SurfaceModelWithCorners c) z₀
  have hDc : ContinuousAt D z₀ := by
    exact (hc.contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have hD0 : D z₀ ≠ 0 := by
    intro hzero
    apply hz₀
    ext v
    have heq := congrArg (fun L => L v) hzero
    simp only [D] at heq
    rw [inTangentCoordinates_eq id c _ (mem_chart_source _ _)
      (mem_chart_source _ _)] at heq
    simpa only [tangentCoordChange_self (I := 𝓡 1) (mem_extChartAt_source _),
      tangentCoordChange_self (I := SurfaceModelWithCorners) (mem_extChartAt_source _),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using heq
  filter_upwards [hDc.eventually_ne hD0] with z hz hcz
  apply hz
  simp [D, inTangentCoordinates, ContinuousLinearMap.inCoordinates, hcz]

#print axioms exists_mfderiv_surjective_fiber_mem_open_of_fixedTargetChart
#print axioms mfderiv_ne_zero_eventually


/-- An injective smooth circle has a point with nonzero derivative. -/
theorem exists_mfderiv_ne_zero
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (c : Circle → S)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (hcinj : Function.Injective c) :
    ∃ z : Circle, mfderiv (𝓡 1) SurfaceModelWithCorners c z ≠ 0 := by
  by_contra hall
  push_neg at hall
  let h : ℝ → S := fun t => c (Circle.exp t)
  have hexp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp := contMDiff_circleExp
  have hcd : ∀ z, MDifferentiableAt (𝓡 1) SurfaceModelWithCorners c z :=
    fun z => (hc z).mdifferentiableAt (by simp)
  have hed : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t :=
    fun t => (hexp t).mdifferentiableAt (by simp)
  have hhc : Continuous h := hc.continuous.comp hexp.continuous
  have hloc : IsLocallyConstant h := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    let x₀ := h t₀
    have hU : IsOpen (h ⁻¹' (chartAt SurfaceModel x₀).source) :=
      (chartAt SurfaceModel x₀).open_source.preimage hhc
    have ht₀ : t₀ ∈ h ⁻¹' (chartAt SurfaceModel x₀).source := mem_chart_source _ _
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU t₀ ht₀
    let F : ℝ → SurfaceModel := fun t => extChartAt SurfaceModelWithCorners x₀ (h t)
    have hFd : ∀ t ∈ Metric.ball t₀ r,
        MDifferentiableAt 𝓘(ℝ, ℝ) SurfaceModelWithCorners F t ∧
          mfderiv 𝓘(ℝ, ℝ) SurfaceModelWithCorners F t = 0 := by
      intro t ht
      have hsrc : h t ∈ (chartAt SurfaceModel x₀).source := hball ht
      have he := mdifferentiableAt_extChartAt (I := SurfaceModelWithCorners) hsrc
      have hh : MDifferentiableAt 𝓘(ℝ, ℝ) SurfaceModelWithCorners h t :=
        (hcd _).comp t (hed t)
      refine ⟨he.comp t hh, ?_⟩
      have h1 : mfderiv 𝓘(ℝ, ℝ) SurfaceModelWithCorners F t =
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners
            (extChartAt SurfaceModelWithCorners x₀) (h t)).comp
            (mfderiv 𝓘(ℝ, ℝ) SurfaceModelWithCorners h t) :=
        mfderiv_comp t he hh
      have h2 : mfderiv 𝓘(ℝ, ℝ) SurfaceModelWithCorners h t =
          (mfderiv (𝓡 1) SurfaceModelWithCorners c (Circle.exp t)).comp
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) :=
        mfderiv_comp t (hcd _) (hed t)
      have hh0 : mfderiv 𝓘(ℝ, ℝ) SurfaceModelWithCorners h t = 0 := by
        rw [h2, hall]; exact ContinuousLinearMap.zero_comp _
      rw [h1, hh0]; exact ContinuousLinearMap.comp_zero _
    have hconst : ∀ t ∈ Metric.ball t₀ r, F t = F t₀ := by
      intro t ht
      refine (Metric.isOpen_ball).is_const_of_fderiv_eq_zero (convex_ball t₀ r).isPreconnected
        (𝕜 := ℝ) ?_ ?_ ht (Metric.mem_ball_self hr)
      · intro s hs
        exact (mdifferentiableAt_iff_differentiableAt.mp (hFd s hs).1).differentiableWithinAt
      · intro s hs
        have := (hFd s hs).2
        rwa [mfderiv_eq_fderiv] at this
    filter_upwards [Metric.ball_mem_nhds t₀ hr] with t ht
    have hsrc : h t ∈ (chartAt SurfaceModel x₀).source := hball ht
    apply (extChartAt SurfaceModelWithCorners x₀).injOn
    · rw [extChartAt_source]; exact hsrc
    · rw [extChartAt_source]; exact ht₀
    · exact hconst t ht
  have h0pi := hloc.apply_eq_of_preconnectedSpace 0 Real.pi
  have hre := congrArg (fun w : Circle => (w : ℂ).re) (hcinj h0pi)
  simp [Circle.coe_exp] at hre
  norm_num at hre

/-- The Sard selection can be made at a regular point of an injective `c`. -/
theorem exists_regularCircleValue_locallyInjectiveAlongFiber
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S] [CompactSpace S]
    (mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 1)))
    [mu.IsAddHaarMeasure]
    (f : S → S) (c : Circle → S)
    (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c)
    (hcinj : Function.Injective c)
    (htrans : ∀ x z, f x = c z →
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ∃ z : Circle, mfderiv (𝓡 1) SurfaceModelWithCorners c z ≠ 0 ∧
      LocallyInjectiveAlongFiber f (c z) := by
  obtain ⟨z₀, hz₀⟩ := exists_mfderiv_ne_zero c hc hcinj
  obtain ⟨O, hOsub, hO, hz₀O⟩ := mem_nhds_iff.mp (mfderiv_ne_zero_eventually c hc z₀ hz₀)
  letI := circleIncidenceAtlas f c hf hc htrans
  letI : IsManifold (modelWithCornersSelf ℝ CircleIncidenceModel) ∞
      (CircleIncidence f c) := circleIncidence_isManifold f c hf hc htrans
  letI : SecondCountableTopology (CircleIncidence f c) :=
    circleIncidence_secondCountableTopology f c
  obtain ⟨z, hzO, hzreg⟩ := exists_mfderiv_surjective_fiber_mem_open_of_fixedTargetChart mu
    (circleIncidenceProjection (f := f) (c := c)) z₀
    (circleIncidenceProjection_contMDiff f c hf hc htrans) O hO hz₀O
  refine ⟨z, hOsub hzO, ?_⟩
  apply locallyInjectiveAlongFiber_of_circleDirection_lifts f c z hf (fun x hx ↦ htrans x z hx)
  intro x hx
  let p : CircleIncidence f c := ⟨(x, z), hx⟩
  have hp := hzreg p rfl
  have hkernel := (circleIncidenceProjection_surjective_iff_kernel_snd
    f c hf hc htrans p).mp hp
  exact direction_lifts_of_surjective_incidenceKernel_snd
    (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap
    (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap hkernel

#print axioms exists_regularCircleValue_locallyInjectiveAlongFiber

end ConstructionTargets.T00J02Closure

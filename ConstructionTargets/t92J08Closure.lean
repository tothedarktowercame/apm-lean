import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! # Uniform local flow input for t92J08 -/

open Set

noncomputable section

namespace t92J08Closure

open Classical

theorem exists_uniform_local_flow_in_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (x₀ : E) (hf : ContDiffAt ℝ 1 f x₀)
    (s : Set E) (hs : s ∈ nhds x₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧ ∃ α : E → ℝ → E,
      ∀ x ∈ Metric.closedBall x₀ r,
        α x 0 = x ∧
        α x '' Ioo (-ε) ε ⊆ s ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (f (α x t)) t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one hf
  have hr₀a : r₀ ≤ a := by
    have hnonneg : (0 : ℝ) ≤ (L : ℝ) * ε₀ := mul_nonneg L.coe_nonneg hε₀.le
    have hbound : (L : ℝ) * ε₀ ≤ (a : ℝ) - (r₀ : ℝ) := by
      simpa using (hpl 0).mul_max_le
    exact_mod_cast (sub_nonneg.mp (hnonneg.trans hbound))
  let b : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a b
  have ha' : 0 < a' := by
    apply lt_min (lt_of_lt_of_le hr₀ hr₀a)
    exact_mod_cast (half_pos hδ)
  let r' : NNReal := a' / 2
  have hr'a' : r' < a' := by simpa [r'] using half_lt_self ha'
  obtain ⟨ε, hε, hpl'⟩ :=
    (hpl 0).exists_shrink_radius hε₀ (show a' ≤ a from min_le_left _ _) hr'a'
  have htarget : Metric.closedBall x₀ (a' : ℝ) ⊆ s := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    exact lt_of_le_of_lt (show (a' : ℝ) ≤ (b : ℝ) by exact_mod_cast min_le_right a b)
      (by simpa [b] using half_lt_self hδ)
  have hfixed (x : E) (hx : x ∈ Metric.closedBall x₀ (r' : ℝ)) :=
    ODE.FunSpace.exists_isFixedPt_next hpl' hx
  choose φ hφ using hfixed
  set α : E → ℝ → E := fun x ↦
    if hx : x ∈ Metric.closedBall x₀ (r' : ℝ) then (φ x hx).compProj else 0 with hα
  refine ⟨ε, hε, r', by exact_mod_cast (half_pos ha'), α, ?_⟩
  intro x hx
  have hα0 : α x 0 = x := by
    rw [hα]
    beta_reduce
    rw [dif_pos hx, ODE.FunSpace.compProj_apply,
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc (0 - ε) (0 + ε) by constructor <;> linarith),
      ← hφ, ODE.FunSpace.next_apply₀]
  refine ⟨hα0, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    apply htarget
    rw [hα]
    beta_reduce
    rw [dif_pos hx]
    exact (φ x hx).compProj_mem_closedBall hpl'.mul_max_le
  · intro t ht
    have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by simpa using ht
    have hwithin : HasDerivWithinAt (α x) (f (α x t))
        (Icc (0 - ε) (0 + ε)) t := by
      rw [hα]
      beta_reduce
      rw [dif_pos hx, ODE.FunSpace.compProj_apply]
      apply ODE.hasDerivWithinAt_picard_Icc (t₀ := (0 : ℝ))
        (by simp [le_of_lt hε]) hpl'.continuousOn_uncurry
        (φ x hx).continuous_compProj.continuousOn
        (fun _ _ ↦ (φ x hx).compProj_mem_closedBall hpl'.mul_max_le) x
        (Ioo_subset_Icc_self ht') |>.congr_of_mem _ (Ioo_subset_Icc_self ht')
      intro t' ht'
      nth_rw 1 [← hφ]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    exact hwithin.hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

section ManifoldCoordinates

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The vector field in the single extended chart centred at `x₀`.  The
varying tangent-space coordinates are retained through the derivative of the
change from the chart at the represented point to the chart at `x₀`. -/
def localCoordinateField
    (v : (x : M) → TangentSpace I x) (x₀ : M) (z : E) : E :=
  let x := (extChartAt I x₀).symm z
  fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I x).symm)
    (Set.range I) (extChartAt I x x) (v x)

theorem localCoordinateField_contDiffAt
    [IsManifold I 1 M] [BoundarylessManifold I M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ContDiffAt ℝ 1 (localCoordinateField I v x₀) (extChartAt I x₀ x₀) := by
  have hv₀ : ContMDiffAt I I.tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀ := hv.contMDiffAt
  rw [contMDiffAt_iff] at hv₀
  obtain ⟨_, hv₀⟩ := hv₀
  have h := (hv₀.contDiffAt
    (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) : I.IsInteriorPoint x₀))).snd
  simpa [localCoordinateField, tangentCoordChange_def] using h

theorem exists_chart_nhds_uniform_isMIntegralCurveOn
    [CompleteSpace E] [T2Space M] [IsManifold I 1 M]
    [BoundarylessManifold I M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I I.tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ U ∈ nhds x₀, ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ U,
      ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  let c := extChartAt I x₀
  let z₀ := c x₀
  have htarget : interior c.target ∈ nhds z₀ :=
    isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) : I.IsInteriorPoint x₀))
  obtain ⟨ε, hε, r, hr, α, hα⟩ := exists_uniform_local_flow_in_nhds
    (localCoordinateField I v x₀) z₀
    (localCoordinateField_contDiffAt I v hv x₀) _ htarget
  let U := c.source ∩ c ⁻¹' Metric.ball z₀ r
  have hU : U ∈ nhds x₀ := by
    apply Filter.inter_mem (extChartAt_source_mem_nhds x₀)
    apply (continuousAt_extChartAt x₀).preimage_mem_nhds
    exact Metric.ball_mem_nhds _ hr
  refine ⟨U, hU, ε, hε, ?_⟩
  intro y hy
  have hy_source : y ∈ c.source := hy.1
  have hy_ball : c y ∈ Metric.closedBall z₀ r :=
    Metric.ball_subset_closedBall hy.2
  obtain ⟨hα0, hαtarget, hαderiv⟩ := hα (c y) hy_ball
  let γ : ℝ → M := c.symm ∘ α (c y)
  refine ⟨γ, ?_, ?_⟩
  · change c.symm (α (c y) 0) = y
    rw [hα0]
    exact c.left_inv hy_source
  · intro t ht
    let xₜ : M := c.symm (α (c y) t)
    have hcoord : HasDerivAt (α (c y))
        (fderivWithin ℝ (c ∘ (extChartAt I xₜ).symm) (Set.range I)
          (extChartAt I xₜ xₜ) (v xₜ)) t := by
      simpa [localCoordinateField, c, xₜ] using hαderiv t ht
    rw [← tangentCoordChange_def] at hcoord
    have hinside : α (c y) t ∈ interior c.target := hαtarget ⟨t, ht, rfl⟩
    have htarget' : α (c y) t ∈ c.target := interior_subset hinside
    have hsource : xₜ ∈ c.source := c.map_target htarget'
    have hxsource : xₜ ∈ (extChartAt I xₜ).source := mem_extChartAt_source (I := I) xₜ
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' htarget').comp hcoord.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt (((extChartAt I xₜ) ∘ c.symm) ∘ α (c y)) (v xₜ) t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ)
        (v := v xₜ) hxsource,
      ← tangentCoordChange_comp (x := x₀) ⟨⟨hxsource, hsource⟩, hxsource⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ hcoord
    apply HasFDerivWithinAt.hasFDerivAt (s := Set.range I) _ <|
      mem_nhds_iff.mpr ⟨interior c.target,
        Set.Subset.trans interior_subset (extChartAt_target_subset_range ..),
        isOpen_interior, hinside⟩
    rw [← c.right_inv htarget']
    exact hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hsource, hxsource⟩

end ManifoldCoordinates

open scoped ContDiff Manifold

abbrev euclideanModel (n : ℕ) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- The chart-local construction specialized to the Euclidean model used by
the consumer.  This formulation exposes one neighbourhood and one common
positive time around every centre. -/
theorem exists_nhds_uniform_isMIntegralCurveOn
    (n : ℕ) (M : Type*)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (euclideanModel n) ∞ M]
    [BoundarylessManifold (euclideanModel n) M]
    (v : (x : M) → TangentSpace (euclideanModel n) x)
    (hv : ContMDiff (euclideanModel n)
      (euclideanModel n).tangent 1
      (fun x ↦ (⟨x, v x⟩ :
        TangentBundle (euclideanModel n) M))) :
    ∀ x : M, ∃ U ∈ nhds x, ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ U,
      ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  intro x
  exact exists_chart_nhds_uniform_isMIntegralCurveOn
    (euclideanModel n) v hv x

end t92J08Closure

#print axioms t92J08Closure.exists_uniform_local_flow_in_nhds
#print axioms t92J08Closure.localCoordinateField_contDiffAt
#print axioms t92J08Closure.exists_chart_nhds_uniform_isMIntegralCurveOn
#print axioms t92J08Closure.exists_nhds_uniform_isMIntegralCurveOn

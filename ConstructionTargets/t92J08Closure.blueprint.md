# Uniform local time for integral curves on a compact manifold

This blueprint follows `~/notes/closer/t92j08-report.md`, specifically the
remaining chain “uniform local existence near initial data” followed by
“compact finite-subcover extraction”.  It supplies the sole remaining bridge
in `problems/t92J08/lean/Main.lean`.  The consumer route is t92J08 under the
shared area `manifold-uniform-local-flow`.

The construction builds on Mathlib
`IsPicardLindelof.of_contDiffAt_one`,
`IsPicardLindelof.exists_shrink_radius`,
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`,
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`,
the chart transport in
`exists_isMIntegralCurveAt_of_contMDiffAt`, and
`CompactSpace.elim_nhds_subcover`.  The representation is always Mathlib’s
extended chart `extChartAt I x₀`; no independent atlas or tangent-space
trivialization is introduced.

### B1. Uniform Euclidean solutions inside a prescribed target neighbourhood

lean: `t92J08Closure.exists_uniform_local_flow_in_nhds` : for a complete real
normed space `E`, `f : E → E`, `x₀ : E`, `ContDiffAt ℝ 1 f x₀`, and
`s ∈ 𝓝 x₀`, there exist `ε > 0`, `r > 0`, and `α : E → ℝ → E` such that for
every `x ∈ Metric.closedBall x₀ r`,
`α x 0 = x`, `α x '' Set.Ioo (-ε) ε ⊆ s`, and
`∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (α x) (f (α x t)) t`.

uses: Mathlib `IsPicardLindelof.of_contDiffAt_one`,
`IsPicardLindelof.exists_shrink_radius`,
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`

status: planned

Choose `a' > 0` with `closedBall x₀ a' ⊆ s` using `s ∈ 𝓝 x₀`.  Apply
`of_contDiffAt_one` to obtain Picard–Lindelöf data, then shrink its state radius
to at most `a'` and choose a strictly smaller positive initial radius `r`.
The closed-ball family theorem supplies all solutions with one time interval.
Its Picard bound keeps every solution in the shrunken state ball, hence in
`s`.  On the interior of the closed time interval, convert
`HasDerivWithinAt` to `HasDerivAt` using `Ioo_mem_nhds`.  Positivity of both
the time and initial radii is retained explicitly for B3.

### B2. The fixed-chart coordinate vector field

lean: `t92J08Closure.localCoordinateField` : for the manifold data of t92J08,
a vector field `v`, and `x₀ : M`, define the coordinate field on the model
space by
`z ↦ fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I ((extChartAt I x₀).symm z)).symm)
  (Set.range I) (extChartAt I ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z))
  (v ((extChartAt I x₀).symm z))`.

lean: `t92J08Closure.localCoordinateField_contDiffAt` : if
`hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))`, then
`ContDiffAt ℝ 1 (localCoordinateField I v x₀) (extChartAt I x₀ x₀)`.

uses: Mathlib `contMDiffAt_iff`, `range_mem_nhds_isInteriorPoint`, and the
coordinate expression used in
`exists_isMIntegralCurveAt_of_contMDiffAt`

status: planned

Unfold `contMDiffAt_iff` for the bundled vector field at `x₀`.  Its second
coordinate is exactly the displayed field after rewriting the tangent-bundle
chart and `tangentCoordChange_def`.  Boundarylessness supplies
`I.IsInteriorPoint x₀`, so `range I` is a neighbourhood of the chart centre
and the within differentiability becomes ordinary differentiability there.
This node records the exact coordinate representation used by B3 and prevents
silently replacing the varying tangent spaces by the model space.

### B3. Uniform manifold curves for a chart neighbourhood

lean: `t92J08Closure.exists_chart_nhds_uniform_isMIntegralCurveOn` : under
the complete-model, `IsManifold I 1 M`, `T2Space M`, and
`BoundarylessManifold I M` hypotheses, and the `hv` of B2, for every `x₀ : M`
there exist `U ∈ 𝓝 x₀` and `ε > 0` such that every `y ∈ U` admits
`γ : ℝ → M` with `γ 0 = y` and
`IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε)`.

uses: B1, B2, Mathlib `continuousAt_extChartAt_symm''`,
`hasFDerivWithinAt_tangentCoordChange`, `tangentCoordChange_comp`, and
`isMIntegralCurveAt_iff`

status: planned

Apply B1 to `localCoordinateField I v x₀` with prescribed neighbourhood
`interior (extChartAt I x₀).target`.  Let `U` be the chart-source points whose
coordinates lie in the open initial ball of B1; chart continuity and the
positive radius show `U ∈ 𝓝 x₀`.  For `y ∈ U`, take the B1 solution beginning
at `extChartAt I x₀ y` and set
`γ := (extChartAt I x₀).symm ∘ α`.  The target-control clause from B1 ensures
the inverse chart is valid for the entire common time interval.  Repeat the
coordinate-change calculation from `exists_isMIntegralCurveAt_of_contMDiffAt`
pointwise in time: use `tangentCoordChange_comp` and
`hasFDerivWithinAt_tangentCoordChange` to turn the coordinate derivative into
the required manifold derivative.  The initial-value equation follows from
the chart inverse law at `y`.

### B4. Public neighbourhood-uniform local-existence theorem

lean: `t92J08Closure.exists_nhds_uniform_isMIntegralCurveOn` : with
`E = EuclideanSpace ℝ (Fin n)` and `I = 𝓘(ℝ, E)`, under exactly the topology,
charted-space, manifold, boundaryless, vector-field, and `ContMDiff` hypotheses
of `apm_t92J08_bridge_1`,
`∀ x : M, ∃ U ∈ 𝓝 x, ∃ ε > 0, ∀ y ∈ U, ∃ γ : ℝ → M,
  γ 0 = y ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε)`.

uses: B3

status: planned

Instantiate B3 at every `x`.  The Euclidean model is complete, and
`hv.contMDiffAt` supplies B3’s pointwise hypothesis.  This node performs only
the specialization and binder bookkeeping; it repeats every hypothesis rather
than relying on an implicit ambient context.

### B5. Finite-subcover minimum of local existence times

lean: `t92J08Closure.exists_uniform_isMIntegralCurveOn_of_compact` : under
the exact hypotheses and conclusion family of B4, plus `CompactSpace M`,
`∃ ε : ℝ, 0 < ε ∧ ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
  IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε)`.

uses: B4, Mathlib `CompactSpace.elim_nhds_subcover`, `Finset.min'`

status: planned

Choose for each `x` an open neighbourhood contained in its B4 neighbourhood
and its positive time `εₓ`.  Compactness gives a finite nonempty set of chosen
neighbourhoods covering `M`.  Let `ε` be the minimum of their positive times.
For an arbitrary `y`, select a covering member, take its curve, and restrict
its integral-curve domain from `Ioo (-εₓ) εₓ` to `Ioo (-ε) ε` using
`IsMIntegralCurveOn.mono`.  Nonemptiness of the finite cover and positivity of
every `εₓ` prove `0 < ε`; the empty-manifold case may instead choose `ε = 1`
before invoking the nonempty finite minimum.

### B6. Frozen bridge adapter

lean: `apm_t92J08_bridge_1` : exactly the declaration already present in
`problems/t92J08/lean/Main.lean`.

uses: B5

status: planned

Apply B5 with the frozen `n`, `M`, `v`, and `hv`.  No additional conversion is
needed: B5’s conclusion is definitionally the bridge conclusion.  The already
proved `apm_t92j08` then consumes this bridge through
`exists_isMIntegralCurve_of_isMIntegralCurveOn`; no globalization theorem is
part of this blueprint.

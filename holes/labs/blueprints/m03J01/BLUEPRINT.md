# Blueprint for m03J01

## Triage

Verdict: **true and faithful**. The Lean statement uses `ContDiff ℝ ∞` and
repairs the printed typo `U ∈ H²(U)` to `u ∈ H²(Ω)`. The custom `H₀¹`
space, weak-solution existence/value uniqueness, gradient closability, and
weak-Hessian uniqueness are already proved. The two a.e.-invariance helpers
from `m03J01_H2bound.v1.lean` are copied in as proved lemmas; both use
`integral_congr_ae`.

## New leaves

### `apm_m03J01_weakSolution_H1size_le`

Tests the weak equation with `u` and bounds the value-plus-gradient `L²` size
by twice the forcing norm. Expected 50–90 lines. Rewrite integrals as `L²`
inner products with `L2.inner_def`, `MemLp.coeFn_toLp`, and
`integral_congr_ae`; apply `real_inner_le_norm`, then convert using
`Lp.enorm_toLp` and `enorm_le_iff_norm_le`.

Independent of every regularity/operator leaf. If `F = 0`, both norms vanish.
For `n = 0`, the gradient vanishes and
`apm_m03J01_zero_dim_eLpNorm_val_le` is sharper. The non-sharp factor `2`
avoids square-root edge cases.

### `apm_m03J01_hessianOperator_exists`

Constructs the solution-Hessian assignment as a linear map between the two
`Lp` spaces. Expected 100–150 lines. Use the coerced `Lp` representative and
`Lp.memLp`, `apm_m03J01_weakSolution_exists`, and `hregular`; return
`hH.1.toLp H`. Representative independence uses
`apm_m03J01_uniform_H2_bound_aux_weakSolution_congr`,
`apm_m03J01_weakSolution_unique_ae`,
`apm_m03J01_gradient_unique_of_val_ae`,
`apm_m03J01_uniform_H2_bound_aux_weakHessian_congr`,
`apm_m03J01_weakHessian_unique_ae`, and `MemLp.toLp_congr`. Establish
additivity/scalar compatibility using `apm_m03J01_H01_add_exists`,
`apm_m03J01_H01_smul_exists`, `integral_add`, `integral_smul`, `MemLp.add`,
and `MemLp.smul`.

Independent of closedness/boundedness. The realization predicate quantifies
over every representative, so this is not a vacuous restatement of
`hregular`. At zero the output is the zero class by uniqueness; for `n = 0`
the Hessian codomain is subsingleton.

### `apm_m03J01_hessianOperator_seq_closed`

Shows any realizing operator has sequentially closed graph. Expected 100–150
lines. Coerce sequence terms and limits to representatives with `Lp.memLp`.
Use the difference energy identity to get convergence of solution values and
gradients. Pass fixed-test-function weak-solution and weak-Hessian identities
to the limit with `L2.inner_def`, `Filter.Tendsto.inner`,
`L2.integrable_inner`, and `tendsto_nhds_unique`; identify the limit using the
three a.e.-uniqueness lemmas and `MemLp.toLp_congr`/`Lp.ext`.

Independent of operator construction because realization is an explicit
hypothesis. Empty coordinate types make the Hessian conclusion automatic;
zero forcing is handled without division.

### `apm_m03J01_hessianOperator_norm_bound`

Pure closed-graph leaf, expected 20–40 lines. Build
`ContinuousLinearMap.ofSeqClosedGraph hclosed`, take its operator norm, use
`norm_nonneg` and `ContinuousLinearMap.le_opNorm`, and simplify applications
with `ContinuousLinearMap.coeFn_ofSeqClosedGraph`. Equivalently start from
`LinearMap.continuous_of_seq_closed_graph`. `Lp` completeness is supplied by
`MeasureTheory.Lp.instCompleteSpace` (with `Fact (1 ≤ 2)`). This leaf depends
only on `T` and the explicit sequential-closedness hypothesis. The zero
operator gives `A = 0`.

### `apm_m03J01_H2_bound_of_hessianOperator_bound`

Translates the real operator norm into the exact registered `ENNReal` bound.
Expected 50–100 lines. Obtain `H,hH` from realization, rewrite the norm bound
using that equality and `Lp.enorm_toLp`, and combine it with
`apm_m03J01_weakSolution_H1size_le`. Choose
`C = 2 + ENNReal.ofReal A`; use `ENNReal.ofReal_lt_top`,
`ENNReal.ofReal_mul hA`, `enorm_le_iff_norm_le`, and distributivity.
`apm_m03J01_H2size_lt_top` handles any remaining finiteness side condition.

Independent of construction and closedness because both conclusions are
explicit hypotheses. At `F = 0`, the component estimates force the chosen
Hessian class to zero, so the required zero right-hand side is genuine.
Dimension zero and `A = 0` are harmless.

## Assembly and dependency layers

`apm_m03J01_uniform_H2_bound` is sorry-free: choose the operator, apply
sequential closedness, obtain a norm bound, and invoke the translation leaf.
The registered main theorem and everything copied from `Main.lean` remain
unchanged.

* **Layer 1 (parallel):** all five leaves above. Conclusions needed from other
  leaves are explicit hypotheses.
* **Layer 2 (sorry-free):** `apm_m03J01_uniform_H2_bound`.
* **Layer 3 (already compiled):** `apm_m03j01`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m03J01/Blueprint.lean
```

`#print axioms apm_m03j01` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; `sorryAx` enters only through
the five leaves above. The copied a.e.-invariance helpers and both assembly
theorems are proved.

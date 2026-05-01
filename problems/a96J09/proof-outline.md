# Proof Outline — a96J09

_Updated by Codex on 2026-05-01 after closing the Lean proof._

## Formal route actually used

The final Lean proof does **not** go through Cauchy-Hadamard or power-series radius.
It uses the shorter contradiction argument based on Cauchy's derivative estimate.

### Step 1

Assume `Metric.closedBall 0 1 ⊆ D`.

Because the closed unit disk is compact and `D` is open, use
`IsCompact.exists_cthickening_subset_open` to get some `δ > 0` with

```lean
Metric.cthickening δ (Metric.closedBall (0 : ℂ) 1) ⊆ D.
```

Then `cthickening_closedBall` upgrades this to

```lean
Metric.closedBall (0 : ℂ) (1 + δ) ⊆ D.
```

### Step 2

From analyticity on `D`, get `DiffContOnCl ℂ f (Metric.ball 0 (1 + δ))` using

```lean
hf.differentiableOn.diffContOnCl_ball hbigClosed
```

Then bound `‖f z‖` on the sphere `Metric.sphere 0 (1 + δ)` by compactness of the sphere.

### Step 3

Apply

```lean
Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
```

to obtain

```lean
‖iteratedDeriv n f 0‖ ≤ n.factorial * C / (1 + δ)^n.
```

After dividing by `n.factorial`, squeeze against the geometric sequence
`C / (1 + δ)^n → 0`.

This proves

```lean
Tendsto (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop (𝓝 0).
```

### Step 4

Use `Filter.Tendsto.limsup_eq` to conclude the limsup is `0`, contradicting the
hypothesis that it is positive.

## Lean theorems now present

```lean
theorem apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk
theorem apm_a96J09_main
```

## Bundle state

- `lean/Main.lean` has no `sorry`.
- The proof is closed with the direct Cauchy-estimate argument.

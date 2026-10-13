# Blueprint for m99A02

## Triage

Verdict: **true and faithful**.

The function is represented by zero at the origin, but this singleton has
Lebesgue measure zero and therefore does not affect either `H¹` membership or
the weak derivatives.  On the punctured disk, `‖x‖<1/2` makes
`-log ‖x‖>0`, so every real power in the formal statement is unambiguous.

I checked the principal borderline and degenerate cases:

* The function diverges at zero, so boundedness cannot be used accidentally;
  nevertheless its square has radial density
  `r * (-log r)^(2/3)`, which is integrable.
* The squared gradient has radial density
  `1 / (9 r (-log r)^(4/3))`; after `u=-log r` this is a constant multiple of
  `u^(-4/3)`, integrable because `4/3>1`.
* The comparison exponent one would diverge, confirming that the proof is
  using the correct side of the Bertrand threshold.
* The inner boundary flux is bounded by
  `C r (-log r)^(1/3)`, which tends to zero, so no Dirac mass appears at the
  origin.
* Either coordinate can vanish on an axis, but the sum-of-squares radial
  identity and coordinatewise domination remain valid.

The solve-loop obstruction records no counterexample.

## Reused completed work

The cached attempt is retained in full.  It already proves measurability of
the singular representative and both derivatives, positivity of the
logarithmic base, the exact summed-gradient radial identity, coordinatewise
domination, the Euclidean-plane radial integrability criterion, the relevant
almost-everywhere identities, integrability of the scalar power tail, and the
explicit Bertrand antiderivative together with its derivative and zero-endpoint
limit.

## Remaining lemmas

### `apm_m99A02_bridge_1`

**Statement in words.** The function and both displayed coordinate
derivatives belong to `L²` on the disk.

**Why true.** For the derivatives, extend

`A(r)=3*(-log r)^(-1/3)`

by zero at `r=0`.  The compiled endpoint limit gives continuity on
`[0,1/2]`, and `m99A02_log_antiderivative_hasDerivAt` identifies its
nonnegative derivative with the Bertrand density.  Apply
`intervalIntegral.integrableOn_deriv_of_nonneg`, then extend by zero outside
`(0,1/2)` and invoke the compiled
`m99A02_integrable_radial_iff`.  The almost-everywhere summed-gradient formula
and `m99A02_derivative_sq_le_radial` yield `MemLp` for each coordinate.

For the function, use the same radial criterion on
`r * (-log r)^(2/3)` over `(0,1/2)`.  Under `u=-log r` it becomes an
exponentially decaying factor times `u^(2/3)`; alternatively dominate the log
power near zero by `r^(-1/2)` and integrate a positive power of `r`.  Combine
this scalar integrability with `m99A02_function_sq_ae` and the already proved
measurability.

The names `intervalIntegral.integrableOn_deriv_of_nonneg`,
`MeasureTheory.integrable_fun_norm_addHaar`, and
`integrableOn_Ioi_rpow_of_lt` were checked in the pinned Mathlib tree; the
latter two already occur in compiling cached lemmas.

**Expected size:** 170–260 lines.

**Dependencies:** definitions and proved cached lemmas only.

**Truth check:** the antiderivative evaluates to a finite value at `1/2` and
tends to zero at the singular endpoint.  The transformed exponent `-4/3` is
strictly below `-1`, exactly Mathlib's integrable-power criterion.

### `apm_m99A02_bridge_2`

**Statement in words.** Each displayed coordinate function is the weak
derivative of the logarithmic function on the disk.

**Why true.** Fix a compactly supported smooth test function and integrate by
parts on the punctured annulus
`{ε < ‖x‖ < 1/2}`.  The outer boundary contributes nothing because the test
function's support lies inside the open disk.  On the inner circle, bound the
flux by the test-function sup norm times

`2π ε (-log ε)^(1/3)`.

This tends to zero.  The interior classical derivative is exactly
`m99A02Derivative i`; pass to the limit using dominated convergence, with
the `L²`/hence local `L¹` bounds established independently by the radial
estimates.  The puncture itself is null, so the resulting equality is exactly
`IsM99A02WeakDerivative`.

**Expected size:** 220–320 lines.

**Dependencies:** definitions and proved radial identities only.  Although
the final domination is also delivered by bridge 1, a seat can prove this
standalone using the same compiled scalar radial estimates, so the two
bridges can proceed in parallel.

**Truth check:** direct chain-rule differentiation away from zero gives
`-xᵢ/[3‖x‖²(-log ‖x‖)^(2/3)]`, including the negative sign.  The inner flux
limit rules out an additional delta distribution.

## Dependency layers

* **Layer 1 (parallel):** `apm_m99A02_bridge_1` and
  `apm_m99A02_bridge_2`.
* **Layer 2 (already proved):** `apm_m99a02` combines the `MemLp` and weak
  derivative clauses.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m99A02/Blueprint.lean
```

The final output was:

```text
'apm_m99a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings are exactly the two Layer 1 bridge declarations.  The main
theorem has no direct `sorry`.

## Doubt

I am convinced both bridge statements are true.  The weak-derivative bridge
may exceed one session if Mathlib lacks a convenient annular integration-by-
parts theorem; in that case the seat should first isolate a polar-coordinate
or cutoff approximation lemma rather than changing the statement.

# Blueprint for m99A06

## Triage

Verdict: **true and faithful**.

The source asks for an `L¹(ℝ)` solution for every sufficiently small positive
`ε`.  `Main.lean` encodes this as an integrable representative satisfying the
equation almost everywhere.  Since an `L¹` element only determines an
almost-everywhere equivalence class, this is the faithful interpretation of
the source rather than a weakening that loses meaningful pointwise data.

I tried the standard degeneracies before adopting the statement.  The ambient
measure space is the fixed, nonempty real line, the forcing is nonzero when
`ε > 0`, and the zero or constant functions do not spuriously satisfy the
equation.  At `ε = 0`, `f = 0` is a solution, but the theorem assumes `0 < ε`
and does not derive its positive case from that endpoint.  No counterexample
or statement objection was recorded in the available solve-loop material.

The cached attempt through 2026-09-29 was reused verbatim through the complete
`L¹` quotient construction, the representative/coercion lemmas, the quadratic
bound, and the polarized Lipschitz bound.  Thus the only admitted obligations
below are the two closed-ball facts.

## Constants and setup

Work in `Lp ℝ 1 volume`.  Let

* `F = ‖m99A06_forcingLp‖`,
* `ε₀ = 1 / (8 * (F + 1))`, and
* `s = Metric.closedBall 0 (1 / 4)`.

The intentionally conservative `ε₀` avoids evaluating the Gaussian norm.
Positivity follows from `F ≥ 0`.  On `s`, the cached estimates give the
quadratic size bound `1/16` and Lipschitz constant at most `1/2`.

## Remaining lemmas

### `m99A06_fixedPointLp_mapsTo_closedBall`

**Statement in words.** If `0 < ε < ε₀`, the quotient-level fixed-point map
sends the closed ball of radius `1/4` about zero into itself.

**Why true.** For `‖u‖ ≤ 1/4`, use the norm triangle inequality,
`norm_smul`, and `m99A06_quadraticLp_norm_le` to obtain

`‖T u‖ ≤ ε F + ‖u‖² < 1/8 + 1/16 ≤ 1/4`.

The forcing estimate follows from `ε < 1/(8(F+1))`, `F ≥ 0`, and
`F < F+1`; `nlinarith`/`positivity` can discharge the real arithmetic after
clearing the positive denominator.  Membership is rewritten with
`Metric.mem_closedBall` and `dist_zero_left`.

**Expected size.** 50–90 lines.

**Dependencies.** Only the definitions and already proved cached lemmas,
especially `m99A06_quadraticLp_norm_le`.

**Truth check.** I checked the worst boundary value `‖u‖ = 1/4`: its
quadratic contribution is exactly `1/16`; even the relaxed forcing bound
`1/8` leaves total `3/16 < 1/4`.  At the endpoint `ε = 0`, the same self-map
estimate is stronger, so no sign reversal is hidden in the smallness argument.

### `m99A06_fixedPointLp_contractingOn_closedBall`

**Statement in words.** For any proof that the fixed-point map preserves the
radius-`1/4` ball, its restriction to that ball is contracting with constant
`3/4`.

**Why true.** For subtype points `u,v` in the ball, unfold the restricted map
and use `m99A06_fixedPointLp_sub_norm_le`.  Their norms are each at most
`1/4`, hence

`dist (T u) (T v) ≤ dist u v * (1/4 + 1/4)
                  ≤ (3/4) * dist u v`.

Convert `dist` to norms with `dist_eq_norm`, and subtype distances with
`Subtype.dist_eq`.  The coefficient `(3/4 : NNReal)` is strictly below one,
as required by `ContractingWith`.

**Expected size.** 50–80 lines.

**Dependencies.** Only the definitions and the cached lemma
`m99A06_fixedPointLp_sub_norm_le`.  The `hmap` argument is merely the data
needed to form `Set.MapsTo.restrict`; this proof does not depend on the proof
of the preceding maps-to lemma.

**Truth check.** At the simultaneous boundary `‖u‖ = ‖v‖ = 1/4`, the cached
estimate gives the sharper factor `1/2`.  Choosing `3/4` leaves slack and is
strictly contracting.  If `u = v`, both sides reduce to zero.

## Assembly (already proved in `Blueprint.lean`)

`m99A06_fixedPointLp_exists` applies
`ContractingWith.exists_fixedPoint'` to the complete closed ball, starting at
zero.  `apm_m99A06_bridge_1` selects the raw representative of the fixed point
and uses `m99A06_fixedPointLp_coe` to obtain the equation almost everywhere.
Finally `apm_m99a06` rearranges that fixed-point equation into the exact
predicate from `Main.lean`.  None of these declarations contains `sorry`.

## Dependency layers

* **Layer 1 (parallel):**
  `m99A06_fixedPointLp_mapsTo_closedBall`,
  `m99A06_fixedPointLp_contractingOn_closedBall`.
* **Layer 2 (already compiled, no seat needed):**
  `m99A06_fixedPointLp_exists` and representative extraction, after both
  Layer 1 lemmas are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/solve-loop/blueprints/m99A06/Blueprint.lean
```

The final output of `#print axioms apm_m99a06` was:

```text
'apm_m99a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 lemmas.  The
main theorem and all assembly declarations have no direct `sorry`.

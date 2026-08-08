# Proof Outline: m94A04

## Hop 4 bridge statements

The remaining implementation is now isolated by three declarations above the
main theorem:

- `apm_m94A04_bridge_downgrade_eightThirds_to_two` states a linear,
  representative-preserving, norm-nonincreasing inclusion into `L²` for this
  measure-one interval.
- `apm_m94A04_bridge_operator_and_linearization` constructs the quotient
  operator and the bounded linear map `h ↦ 3f²h` with its a.e. formula.
- `apm_m94A04_bridge_remainder_estimate` states the exact epsilon–delta
  estimate obtained from `3fh²+h³` and mixed Hölder bounds.

Together their conclusions assemble the custom Fréchet-derivative predicate
and every conclusion of the frozen theorem. Their bodies intentionally remain
`sorry` under the statement-only instruction.

The frozen Lean theorem is present in `lean/Main.lean`. The exact cubic
remainder identity is now proved.
The `L⁸·L⁸ → L⁴` stage is also compiled: the quotient-level square has the
expected a.e. representative and satisfies `‖f²‖₄ ≤ ‖f‖₈²`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A04.md`

## Remaining boundary

- continue the compiled `L⁴` square through heterogeneous multiplication to
  construct `f³` and `f²h` at exponent `8/3`;
- downgrade `L^(8/3)` and `L^(8/3)` remainder terms to `L²` on the finite
  interval;
- package `h ↦ 3f²h` as a quotient-level `LinearMap`;
- combine the exact remainder identity with `Lp.norm_smul_le` and ENNReal
  arithmetic to prove the epsilon-delta estimate.

Mathlib's `MeasureTheory.Function.Holder` already handles quotient-level
representative independence and Hölder norm bounds. No searched sibling
assembles the required exponent chain and derivative package.

Closer hop 3 completes the second heterogeneous Hölder link by constructing
`f³ : L^(8/3)`, proving its representative is a.e. the pointwise cube, and
showing `‖f³‖_(8/3) ≤ ‖f‖₈³`. The remaining construction begins with the
finite-measure downgrade from exponent `8/3` to `2`.

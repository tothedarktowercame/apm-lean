# Proof Outline: b97A02

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves the two
finite-field coefficient identities used by the affine invariant calculation:

- embedded coefficients satisfy `a^q=a`;
- a nonzero embedded coefficient satisfies `a^(q-1)=1`.

Closer hop 2 finds and uses Mathlib's `FieldTheory/RatFunc/Luroth.lean`.
`apm_b97A02_finite_over_nontrivial_intermediate` proves the entire final
conjunct: `X` is algebraic over a non-bottom intermediate field, its simple
adjoin is finite dimensional, and `adjoinXEquiv` identifies that adjoin with
the whole rational-function field. The main theorem now discharges this
conjunct explicitly.

The same source provides the previously missed
`RatFunc.algEquivOfTranscendental` and `RatFunc.finrank_eq_max_natDegree`, so
the remaining affine/fixed-field route has substantially more infrastructure
than hop 1 recorded.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A02.md`

## Remaining boundary

- construct and invert the affine substitution `X ↦ aX+b` as an `AlgEquiv` of
  `RatFunc F`, and prove uniqueness from the image of `X`;
- combine characteristic-power additivity with the compiled coefficient lemmas
  to prove the displayed invariant is fixed;
- prove the invariant generates the complete fixed field, including the
  rational-function degree calculation;

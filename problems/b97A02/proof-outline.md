# Proof Outline: b97A02

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves the two
finite-field coefficient identities used by the affine invariant calculation:

- embedded coefficients satisfy `a^q=a`;
- a nonzero embedded coefficient satisfies `a^(q-1)=1`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A02.md`

## Remaining boundary

- construct and invert the affine substitution `X ↦ aX+b` as an `AlgEquiv` of
  `RatFunc F`, and prove uniqueness from the image of `X`;
- combine characteristic-power additivity with the compiled coefficient lemmas
  to prove the displayed invariant is fixed;
- prove the invariant generates the complete fixed field, including the
  rational-function degree calculation;
- establish finiteness of `RatFunc F` over every nontrivial intermediate field
  (the required Lüroth/degree bridge).

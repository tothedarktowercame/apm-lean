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

Closer hop 3 proves `apm_b97A02_exists_affineAlgEquiv`. The identity
`X = a⁻¹((aX+b)-b)` shows that the affine element generates the full rational
function field. It is nonconstant and hence transcendental, so
`RatFunc.algEquivOfTranscendental`, followed by the equivalence from its adjoin
to `⊤`, constructs the required automorphism with the exact image of `X`.

Hop 4 proves the missing extensionality result locally as
`apm_b97A02_ratFunc_algHom_ext`. `RatFunc.induction_on'` presents an arbitrary
rational function as a quotient of polynomial images; `mk_eq_div`,
`aeval_X_left_eq_algebraMap`, and `Polynomial.aeval_algHom_apply` show that two
algebra homomorphisms agreeing on `X` agree on that quotient. This closes the
entire uniqueness clause of the main theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A02.md`

## Remaining boundary

- count the now uniquely parameterized affine substitution automorphisms;
- combine characteristic-power additivity with the compiled coefficient lemmas
  to prove the displayed invariant is fixed;
- prove the invariant generates the complete fixed field, including the
  rational-function degree calculation;

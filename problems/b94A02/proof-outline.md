# Proof Outline: b94A02

The canonical Lean attempt is `lean/Main.lean`. Earlier work proves nonzero
generator/quotient facts and existence of coefficients for elements of the
principal ideal. Closer hop 1 proves the central well-definedness lemma:

- if `x=b*r=b*r'`, then `mk I (r*s) = mk I (r'*s)` for every `s`;
- the proof sends `b*(r-r')=0` through the annihilator hypothesis and uses
  ideal closure under multiplication.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b94A02.md`

## Remaining boundary

- define the quotient-valued coefficient map using a chosen witness and the
  compiled independence lemma;
- prove its additivity and scalar compatibility in both arguments, then bundle
  it as the required curried linear map;
- derive the tensor-product linear equivalence, either by its universal
  property or `tensorQuotEquivQuotSMul`;
- reuse the nonzero pure-tensor/map argument from sibling `b93A03` for the
  final failure of injectivity.

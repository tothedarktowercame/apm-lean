# Proof Outline: b94A02

The canonical Lean attempt is `lean/Main.lean`. Earlier work proves nonzero
generator/quotient facts and existence of coefficients for elements of the
principal ideal. Closer hop 1 proves the central well-definedness lemma:

- if `x=b*r=b*r'`, then `mk I (r*s) = mk I (r'*s)` for every `s`;
- the proof sends `b*(r-r')=0` through the annihilator hypothesis and uses
  ideal closure under multiplication.

Closer hop 2 avoids choice bookkeeping. Mathlib's
`Ideal.quotTorsionOfEquivSpanSingleton` canonically identifies `R/ann(b)` with
`bR`; the annihilator hypothesis induces `R/ann(b) → R/I` using
`Submodule.mapQ`. The resulting coefficient map has the expected formula.
Composing it with multiplication in `R/I` gives
`apm_b94A02_exists_balancedMap`, closing the theorem's entire first conjunct,
including surjectivity.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b94A02.md`

## Remaining boundary

- derive the tensor-product linear equivalence, either by its universal
  property or `tensorQuotEquivQuotSMul`;
- reuse the nonzero pure-tensor/map argument from sibling `b93A03` for the
  final failure of injectivity.

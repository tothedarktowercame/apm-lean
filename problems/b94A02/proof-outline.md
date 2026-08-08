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

Closer hop 3 applies `TensorProduct.lift` to that balanced map. The resulting
linear map from `bR ⊗ (R/I)` to `R/I` is proved surjective by turning each
preimage pair into a pure tensor, and its value on every witnessed
`x ⊗ mk(s)` is compiled. This constructs the forward half of the desired
linear equivalence directly, independently of quotient-submodule rewriting.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b94A02.md`

## Hop 4 completion

`apm_b94A02_exists_tensorEquiv` defines the inverse `q ↦ b ⊗ q` and proves
its left-inverse identity by `TensorProduct.induction_on`. On a pure tensor,
the first factor is written as `b*r`, the quotient factor as `mk(s)`, and the
claim follows from the compiled lift formula and `TensorProduct.smul_tmul`.

For the final conjunct, `b ⊗ 1` is nonzero because the tensor lift maps it to
the nonzero class of `1`. If `b ∈ I`, its image under the frozen tensor map is
zero by balancing the scalar `b` into the quotient factor. This supplies an
explicit kernel witness and completes the theorem without sorries.

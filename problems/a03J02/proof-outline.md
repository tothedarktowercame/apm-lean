# Proof Outline: a03J02

## Problem

Let f : ℝⁿ → ℝⁿ be a polynomial map. Show that every null set E ⊂ ℝⁿ
maps to a null set f(E).

## Formalisation Approach

### Statement repair

The informal proof proposes building `IsPolynomialMap` using `MvPolynomial`
and proving the result via the chain: polynomial ⟹ C¹ ⟹ locally Lipschitz ⟹
preserves null sets. Mathlib lacks calculus infrastructure for
`MvPolynomial.eval` as a map `(σ → R) → R`, making the polynomial ⟹ C¹ step
impractical to formalize following that route.

**Structural repair:** Mathlib's `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
(Gouëzel, in the Jacobian/change-of-variables theory) directly proves that
`Differentiable` maps on finite-dimensional real normed spaces send null sets
to null sets. We:

1. Prove `differentiable_image_null_of_null` (zero-sorry): a direct wrapper
   applying this theorem with `Differentiable.differentiableOn`.
2. Prove `MvPolynomial.eval_differentiable` (zero-sorry): the evaluation of
   a multivariate polynomial at `x : Fin n → ℝ` is `Differentiable`, using
   `eval_eq'` (which expresses eval as a finite sum of monomial products
   `∑ d ∈ support, coeff d * ∏ i, x_i^{d_i}`) and `fun_prop`.
3. Prove `IsPolynomialMap.differentiable` (zero-sorry): combines per-component
   `eval_differentiable` via `differentiable_pi`.
4. Prove `polynomial_map_image_null` (zero-sorry): the main theorem.

### Proven lemmas (all zero-sorry)

1. **`differentiable_image_null_of_null`**: Differentiable maps send null sets to null sets
2. **`MvPolynomial.eval_differentiable`**: Polynomial evaluation is differentiable
3. **`IsPolynomialMap.differentiable`**: Polynomial maps are differentiable
4. **`polynomial_map_image_null`**: Main theorem

## Lean state

- **Checked:** exit 0, 0 errors, 0 sorries
- **Classification:** complete
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a03J02/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a03J02.md`
- Key Mathlib theorem: `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
  (Mathlib.MeasureTheory.Function.Jacobian)

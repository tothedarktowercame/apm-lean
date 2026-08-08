# Proof Outline: a97J06

## Problem

Evaluate ∫₀^∞ cos(tx)/(x²+4) dx for all real t.
Answer: π/4 · e^{-2|t|}.

## Strategy

Contour integration:
1. Evenness: ∫₀^∞ = ½ Re ∫₋∞^∞ e^{itx}/(x²+4).
2. Close upper half-plane for t ≥ 0; pole at z=2i.
3. Residue: e^{-2t}/(4i); theorem gives π/2 · e^{-2t}.
4. ML estimate: arc → 0.
5. Combine: π/4 · e^{-2|t|}.

## Proved (exit 0, 1 sorry)

Statement compiles. 1 sorry: contour integral proof body.

The current bundle now contains compiled `Ioi`-form lemmas
`apm_a97J06_integral_zero` and `apm_a97J06_integral_neg`, recovered from prior
git history and adapted to the frozen encoding. Only `0 < t` remains.

## Phase-A hints used
- #1 `e-codexpilot-evaluate-a-rational-circle-integral-by-separating-interior-and-exterior-poles`: cited.
- #2 `e-j07-reuse-two-pole-partial-fraction-contour-pattern`: cited.
- #6 `math-informal/estimate-by-bounding`: cited (ML estimate).

## Mid-solve lookups

1. Mathlib `Probability/Distributions/Cauchy.lean`: found
   `integral_cauchyPDFReal_eq_one`, useful only for `t = 0`; no characteristic
   function theorem was found.
2. Repository and Mathlib searches for the Fourier transform of the Cauchy
   density (`exp (-γ|t|)`): no usable theorem found.
3. `problems/a92J06/lean/Main.lean`: found a compiled full-circle rational
   contour pattern using partial fractions, the interior-pole circle integral,
   and exterior-pole vanishing; retained as a residue sub-pattern.
4. Mathlib searches for semicircle, upper arc, and arc-integral APIs: no
   packaged semicircular contour theorem or Jordan lemma found.

## Remaining exact bridge

The full-circle rational pattern does not directly represent the Fourier
integral. The remaining direct route must define the upper semicircle as an
interval-parametrized path, combine it with the real diameter, prove the
single-pole residue identity, bound the arc uniformly, and take the improper
integral limit. The alternative probability route would close immediately if
a Cauchy characteristic-function theorem were added, but Mathlib currently
only supplies normalization of its density.

## Closer hop 2

Added the compiled lemma `cos_integral_eval_zero`. It derives the exact base
case from Cauchy-density normalization, uses `integral_comp_abs` for evenness,
and converts `Ioi` to `Ici`. Thus scaling, integrability, and half-line
symmetry are no longer speculative. The remaining obstacle is specifically
the oscillatory characteristic-function identity for `t ≠ 0`.

## Closer hop 3

Added compiled `cos_integral_even`, reducing negative frequencies to positive
ones. Combined with the proved zero-frequency case, the only remaining lemma
needed is the transform evaluation under `0 < t`. Repeated searches for a
Cauchy characteristic-function or Jordan-lemma theorem returned no match.

## Relay closer hop 2

The compiled lemma `apm_a97J06_integral_eq_half_standard` performs the exact
change of variables `x = 2u` and proves

`I(t) = (1/2) ∫₀∞ cos(u · 2t)/(1 + u²) du`.

Thus all scale and denominator bookkeeping is closed. The remaining theorem is
literally the positive-frequency assertion still open in sibling `a03J05`, not
a separate analytic obligation. Reusing that sibling is not possible while its
main transform theorem itself remains sorry-backed.

## Relay closer hop 3

Added `apm_a97J06_integrable`. It first scales Mathlib's global
`integrable_inv_one_add_sq` theorem to `(x²+4)⁻¹`, then dominates the cosine
kernel using `Real.abs_cos_le_one`. Thus absolute integrability and its
measurability bookkeeping are compiled; only the actual positive-frequency
transform evaluation remains open.

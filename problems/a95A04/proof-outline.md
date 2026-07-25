# Proof Outline: a95A04

## Problem

If f : [0,1] → ℝ is Lebesgue integrable and ∫_{x-h}^x f(t)dt = ∫_x^{x+h} f(t)dt
whenever [x-h, x+h] ⊆ [0,1], prove f(x) = ∫_0^1 f(t)dt for a.e. x ∈ [0,1].

## Proof strategy

1. **Symmetric splitting** (Step 2 of informal proof): For any [a,b] ⊆ [0,1]
   with midpoint m = (a+b)/2, ∫_a^m f = (1/2) ∫_a^b f. ✓ PROVED.

2. **Dyadic induction** (Step 3): By induction on j, ∫_{k/2^j}^{(k+1)/2^j} f = c/2^j
   where c = ∫_0^1 f. Uses symmetric_split at each level.
   ✗ SORRY — requires floor/division arithmetic for dyadic intervals.

3. **Lebesgue differentiation** (Step 4): For a.e. x, f(x) equals the limit of
   averages over shrinking dyadic intervals. Since all dyadic averages equal c,
   f(x) = c a.e. Uses Mathlib's `IntervalIntegrable.ae_hasDerivAt_integral`.
   ✗ SORRY — inherits from dyadic_integral_eq.

## Proved lemma

- `symmetric_split`: For [a,b] ⊆ [0,1] with midpoint m = (a+b)/2,
  ∫_a^m f = (1/2) ∫_a^b f. This is the key structural insight: the symmetric
  mean value property forces equal integrals on both halves of any interval.

## Checked Lean state

- `lake env lean problems/a95A04/lean/Main.lean`: exit 0
- Sorry count: 2
- Classification: partial

# Proof Outline: aunk03

## Result

The theorem is closed with Mathlib's exact zeta-value theorem and its canonical
natural-number series-shift equivalence.

## Proof

1. `hasSum_zeta_four` gives
   `HasSum (fun n : ℕ ↦ 1 / (n : ℝ)^4) (π^4 / 90)`.
2. The zero-index term is zero under Lean's division convention.
3. `(hasSum_nat_add_iff' 1).mpr` removes that first term and produces the
   shifted sequence `n ↦ 1 / ((n + 1 : ℕ) : ℝ)^4` with unchanged sum.
4. `HasSum.tsum_eq` yields the frozen theorem.

## Closer Hop 3

The prior boundary incorrectly concluded that no exact shift lemma existed.
Mathlib generates `hasSum_nat_add_iff'` as the additive counterpart of the
product-shift theorem in `Topology/Algebra/InfiniteSum/NatInt.lean`. Using its
forward implication avoids all manual finite-range decomposition.

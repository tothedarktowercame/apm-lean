# Proof Outline: b98J04

The canonical Lean attempt completes the semisimple reduction and obtains a
finite independent decomposition of `M` into simple submodules. One sorry
remains for transporting this decomposition to the requested quotient and CRT
data.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98J04.md`

## Formal progress

- The Artinian/Jacobson hypotheses yield `IsSemisimpleRing R`.
- `IsSemisimpleModule.finite_tfae` produces the finite simple decomposition.
- `rightAnnihilatorIdeal` bundles the frozen set-valued annihilator as an
  `Ideal R`; its membership predicate is definitionally the original set.

## Remaining bridge

Lift the simple summands from submodules of `M` to submodules of `R`. Prove
their annihilator ideals maximal and pairwise distinct using simplicity and
minimal faithfulness. Since `Ideal.quotientInfRingEquivPiQuotient` assumes a
commutative ring, establish the analogous finite two-sided CRT locally, relate
each quotient to the appropriate matrix ring, and prove the left-span claim.

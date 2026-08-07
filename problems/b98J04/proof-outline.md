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
- `rightAnnihilatorIdeal_isTwoSided` proves the bundled annihilator is a
  two-sided ideal, enabling noncommutative quotient rings and the injective
  simultaneous quotient map.
- `exists_simultaneous_residue_of_twoSided` proves the binary CRT construction
  for two comaximal two-sided ideals in a noncommutative ring. Given
  `1 = i + j`, the representative `b * i + a * j` realizes the two residues.

## Remaining bridge

Lift the simple summands from submodules of `M` to submodules of `R`. Prove
their annihilator ideals maximal and pairwise distinct using simplicity and
minimal faithfulness. Since `Ideal.quotientInfRingEquivPiQuotient` assumes a
commutative ring for its surjectivity half, establish that half of the finite
two-sided CRT by extending the compiled binary construction through finite
intersections, relate
each quotient to the appropriate matrix ring, and prove the left-span claim.
Mathlib's packaged `IsSimpleModule.annihilator_isMaximal` assumes a commutative
ring, so the required noncommutative maximality argument must also be local.

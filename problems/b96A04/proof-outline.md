# Proof Outline: b96A04

The formal proof now closes the elementary domain lemma, both free-module
claims, the free-embedding rigidity clause, and the projective fraction-field
clause.  The embedding proof clears an arbitrary fraction after showing every
nonzero denominator is a unit via a nonzero coordinate of the embedded `1`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b96A04.md`

## Remaining boundaries

1. For a proper ideal `I`, turn a projective splitting of `R ⧸ I` into a
   nontrivial idempotent decomposition, then use the domain hypothesis.
2. Unpack `M.FG` into a finite spanning set and apply the localization common
   denominator APIs uniformly, proving one nonzero scalar clears every element
   of `M` into the image of `R`.
3. Apply the preceding result to `M = ⊤` to close the final finite-module
   clause.

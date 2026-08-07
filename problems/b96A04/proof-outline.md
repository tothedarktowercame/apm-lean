# Proof Outline: b96A04

The formal proof now closes the elementary domain lemma, both free-module
claims, the free-embedding rigidity clause, the projective fraction-field and
projective quotient clauses, the common-denominator clause, and the final
finite-module clause.
The common-denominator helper extracts a finite spanning set, clears all its
denominators simultaneously, and extends the result by span induction.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b96A04.md`

## Projective quotient bridge

For a proper ideal `I`, projectivity gives a right inverse `s` of the canonical
linear quotient map `I.mkQ`.  The element `e = s 1` is nonzero because applying
the quotient map gives `1`.  Every `x ∈ I` has zero image in the quotient; by
linearity, applying `s` shows `x * e = 0`.  Since `R` is a domain and `e ≠ 0`,
we obtain `x = 0`, hence `I = ⊥`.

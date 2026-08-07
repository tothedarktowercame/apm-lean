# Proof Outline: t97J01

The Lean artifact proves that any covering map from a connected space onto a
preconnected space is surjective.  The proof uses the fact that a covering
map has open range and that an absent fiber has an evenly covered neighborhood
disjoint from the range, making the range clopen.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J01.md`

## Remaining bridge

The covering is consequently an open quotient map.  Mathlib's theorem
`t2Space_iff_of_isOpenQuotientMap` reduces the goal exactly to closedness of
the kernel relation `{q : X × X | p q.1 = p q.2}`.  It remains to combine the
finite fibers with local covering trivializations to prove this closedness,
or equivalently to prove that the finite covering map is closed/proper.

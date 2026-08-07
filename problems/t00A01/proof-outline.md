# Proof Outline: t00A01

The Lean encoding constructs the connected sum as the equivalence closure of
the boundary-sphere gluing relation.  The helper
`apm_t00A01_mk_inl_eq_mk_inr` proves that the quotient identifies the two
copies of every boundary point.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A01.md`

## Remaining boundary

The main theorem remains open.  Its two conclusions require precisely:

1. a Seifert--van Kampen theorem for the fundamental group of the supplied
   open cover, including basepoint/change-of-basepoint bookkeeping; and
2. a Mayer--Vietoris long exact sequence for Mathlib's singular homology
   functor, applied to the same cover.

Mathlib searches found only categorical Van Kampen colimit results and
sheaf-cohomology Mayer--Vietoris results, neither of which applies here.
Searches of `LEMMA-INDEX.md`, closed and partial sibling artifacts,
`ConstructionTargets/`, `YoungL2.lean`, and git history found no reusable
bridge.  The theorem statement is unchanged and appears mathematically sound.

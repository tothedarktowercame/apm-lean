# Proof Outline: t97A03

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97A03.md`

## Compiled progress

- `apm_t97A03_surjective_of_fiber_card_two` proves the cover map is onto from
  the frozen assertion that every fiber has cardinality two.
- The north and south attachment equalities in the concrete base quotient are
  now compiled directly from the generating relation.
- `apm_t97A03_fiber_equiv_fin_two` converts each numeric fiber-cardinality
  equation into finiteness and an actual equivalence with `Fin 2`.

## Hop 4 bridge contracts

- `apm_t97A03_bridge_classify_connected_double_cover` states the missing
  global monodromy classification directly: every connected two-sheeted cover
  satisfying the frozen hypotheses is homeomorphic to one of the two concrete
  quotient models.
- `apm_t97A03_bridge_invariants_of_model` states the common invariant package
  for a space homeomorphic to either model: singular homology of ranks
  `1,3,2`, vanishing above degree two, and fundamental group `F₃`.

Both declarations are intentionally unproved. Together they reduce the main
theorem to conjunction assembly while keeping its statement untouched.

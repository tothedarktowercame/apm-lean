# Proof Outline: b98A04

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98A04.md`

## Compiled progress

- Constructed the finite tuple's common annihilator directly as a left
  `Submodule R R`, proving the first conjunct without commutativity.
- Applied `IsArtinian.set_has_minimal` to finite common annihilators. A
  nonzero minimal annihilator is strictly decreased by adjoining a vector on
  which its nonzero element acts nontrivially, so a finite faithful tuple
  exists. This closes the second conjunct.
- Bundled the action map `R →ₗ[R] (Fin s → M)` and proved it injective when the
  common annihilator is zero, closing the third conjunct.

## Remaining bridge

Translate the raw strictly monotone submodule chain to Jordan–Hölder machinery,
then transport simple factors through the embedding of the regular module into
a finite power of `M`. The available Jordan–Hölder theorem compares series of
one module; the missing bridge is the submodule/refinement factor-occurrence
argument in the exact quotient representation of the frozen conclusion.

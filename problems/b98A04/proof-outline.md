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
- Proved every simple `R`-module is a quotient of the image of that embedded
  regular module inside `Fin s → M`.

## Remaining bridge

Prove that a simple quotient of a submodule of `Fin s → M` occurs among the
factors of the supplied composition series of `M`. The embedding and quotient
reduction are compiled; only the submodule/refinement factor-occurrence
argument in the frozen quotient representation remains. Hop 4 checked
`JordanHolderModule.instJordanHolderLattice`,
`CompositionSeries.jordan_holder`, and
`IsFiniteLength.iff_exists_compositionSeries`; none constructs the required
finite-power, submodule, and quotient series or normalizes its factor back to
the displayed quotient of successive `N` terms. The exact fully quantified
bridge proposition is recorded at the sorry boundary in `lean/Main.lean`.

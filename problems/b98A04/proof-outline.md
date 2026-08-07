# Proof Outline: b98A04

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98A04.md`

## Compiled progress

- Constructed the finite tuple's common annihilator directly as a left
  `Submodule R R`, proving the first conjunct without commutativity.
- Bundled the action map `R →ₗ[R] (Fin s → M)` and proved it injective when the
  common annihilator is zero. Thus the second conjunct implies the third.

## Remaining bridge

Use Artinian minimization to produce a finite tuple with zero common
annihilator. Separately translate the raw strictly monotone submodule chain to
Jordan–Hölder machinery and transport simple factors through the embedding of
the regular module into a finite power of `M`.

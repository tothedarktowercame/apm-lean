# Proof Outline: t97A02

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97A02.md`

## Compiled reduction

- Bundle the two coordinate maps from the torus to `Circle`.
- Use `ContinuousMap.Homotopic.prodMk` to prove that coordinate
  null-homotopies reassemble into a null-homotopy of the original torus map.

## Remaining bridge

It remains to prove that every continuous map `X → Circle` is
null-homotopic when the integral first singular-homology group of `X` is
finite. The standard proof uses `[X,S¹] ≅ H¹(X;ℤ)` (or a universal-cover
lifting criterion), neither of which is currently packaged with the required
hypotheses in Mathlib.

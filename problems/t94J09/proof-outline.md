# Proof Outline: t94J09

## Closer hop 1

The five concrete classification certificates now compile: there are two
vertex classes, seven edge labels, Euler characteristic `-4`, the orientation
pairing test fails, and the resulting nonorientable genus is `6`.

The homeomorphism and singular-homology tail remains open.  Neither Mathlib
nor `ConstructionTargets.Surfaces` supplies polygon moves/classification for
the actual `EqvGen` quotient, and the library has no cellular-to-singular
comparison or singular Mayer–Vietoris theorem capable of computing its
homology.  The exact searched boundary is recorded at the remaining `sorry`.

This bundle currently has a harvested informal solution but no imported
Lean proof attempt in this problem root.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J09.md`

## Follow-up Needed

- extract a formalization-oriented proof outline from the informal solution
- add or select the canonical Lean attempt for this problem

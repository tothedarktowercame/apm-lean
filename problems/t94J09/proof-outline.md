# Proof Outline: t94J09

## Closer hop 2

Both actual quotient presentations now expose their point-set universal
properties.  The canonical maps from the disk are continuous and surjective,
and `apm_t94J09_polygonDesc` / `apm_t94J09_n6Desc` continuously descend any
map respecting the respective generating relation.  Compiled computation and
uniqueness lemmas characterize both descended maps.

This reduces the positive topological comparison to constructing explicit
mutually inverse disk maps implementing the polygon moves.  No such
normalizing maps were found in the repository or Mathlib.  The singular
homology tail remains a separate missing invariant bridge: no searched source
computes these polygon quotients or connects their evident cellular boundary
calculation to singular homology.

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

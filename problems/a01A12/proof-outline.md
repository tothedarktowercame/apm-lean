# Proof Outline: a01A12

This proof outline was synthesized from legacy Lean files without a paired
proof-frame workspace.

Imported source: `lean-proofs/a01A12`

## Imported Lean Files

- `lean/Main.lean`

## Closer hop 1

The frozen theorem is still open. This hop recovered the earlier range-only
proof from commits `3ed025e`, `3fa3a92`, and `fddc86c`, and compiled three
reusable prerequisites in the repaired namespace:

- `1 - z^2` is nonzero throughout the upper half-plane;
- squaring sends the right half-plane away from the nonpositive real axis;
- the concrete positive-determinant Möbius family contains the identity.

The earlier artifact establishes only image containment. The remaining proof
must promote the principal fourth-root formula to a conformal bijection onto
the exact slit wedge (constructing and verifying its inverse), then prove that
every conformal automorphism of the upper half-plane is a real Möbius map with
positive determinant. Mathlib provides the `SL(2, ℝ)` action but not this
converse classification theorem.

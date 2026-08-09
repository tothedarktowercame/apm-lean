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

## Closer hop 2

The explicit map now has three further compiled properties:

- `apm_a01A12_conformalMap_pow_four` proves
  `apm_a01A12_conformalMap z ^ 4 = 1 - z ^ 2` using
  `Complex.cpow_nat_inv_pow`;
- `apm_a01A12_conformalMap_ne_zero` proves its values are nonzero throughout
  the upper half-plane;
- `apm_a01A12_conformalMap_injOn` proves injectivity: equality of images gives
  equality of squares, and positivity of both imaginary parts eliminates the
  sign ambiguity.

The explicit biholomorphism still needs surjectivity onto the exact wedge slit
and a compiled nonzero derivative. The separate converse classification of
all upper-half-plane conformal automorphisms as real Möbius maps also remains
absent from the searched corpus.

## Closer hop 3

The differential side of the explicit biholomorphism is now compiled:

- `apm_a01A12_one_sub_sq_mem_slitPlane` verifies the branch-domain condition
  for the principal complex power;
- `apm_a01A12_conformalMap_hasDerivAt` derives the exact derivative from
  `HasDerivAt.cpow_const`;
- `apm_a01A12_conformalMap_fderiv_ne_zero` proves the corresponding complex
  Fréchet derivative is nonzero throughout the upper half-plane.

The explicit-map bridge is therefore reduced to surjectivity onto the frozen
wedge slit. The separate automorphism-classification theorem remains absent:
the available upper-half-plane Möbius action constructs the forward family
but does not classify arbitrary conformal automorphisms.

## Hop 4 bridge statement

`apm_a01A12_bridge_automorphism_classification` states the missing
classification as a torsor theorem: conditional on the explicit map being a
conformal bijection, every conformal bijection from the upper half-plane onto
the same slit wedge is its precomposition by a positive-determinant real
Möbius map, and every such precomposition is a conformal bijection.

Its conclusion is verbatim the second conjunct of the frozen theorem. The
remaining surjectivity proof for the explicit map supplies its sole premise.

# Proof Outline: t95J06

The Lean formalization is partial, with one `sorry` remaining in the universal
surface-classification clause.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t95J06.md`

## Compiled explicit-torus clause

- Substitute the Hopf-flow identity `H(z,t) = exp(i t) • z`.
- If `z` has torus parameters `θ, φ`, use `θ, φ+t` for its image.
- `Complex.exp_add` and coordinate algebra prove the resulting vector equality,
  so the explicit torus is invariant.

## Remaining classification bridge

For an arbitrary compact orientable invariant surface:

1. Factor the real-parameter flow through a free circle action.
2. Construct the orbit space and prove it is a compact one-manifold.
3. View each connected component as a circle bundle and derive Euler
   characteristic zero.
4. Apply classification of compact orientable surfaces to construct an actual
   homeomorphism with `Circle × Circle`.

Mathlib currently packages neither the needed principal-circle-bundle theorem
nor compact-surface classification for these actual manifold subtypes.

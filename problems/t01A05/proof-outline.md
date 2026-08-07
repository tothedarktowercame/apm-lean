# Proof Outline: t01A05

The Lean encoding represents orientations and top forms through integral
singular homology, and retains actual carriers for oriented submanifolds.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A05.md`

## Formal progress

- `t01A05_pullback_integral_eq` proves the encoded pullback-integral identity.
- `t01A05_preimage_intersectionNumber_eq` proves the encoded numerical
  intersection identity.
- `t01A05_preimageSubmanifold_compact_of_t2` proves compactness of a lifted
  carrier when the base is Hausdorff and the total space is compact.

## Remaining boundary

The existence clause needs a concrete compact space with a compiled
`H₂ ≅ ℤ` computation and positive-degree finite covers. No sphere or torus
singular-homology computation was found in Mathlib. For the compact-preimage
claims, the frozen hypotheses omit `T2Space X`, while `Nat.card fiber = 0`
does not establish finiteness in the `k = 0` case. Thus the standard compact
source/Hausdorff target theorem cannot be applied to the statement as given.

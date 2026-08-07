# Proof Outline: t00J02

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J02.md`

## Compiled progress

- `apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero` proves that if the map
  induced by `f` on `H₂` is zero, then the integer specified by
  `apm_t00j02_hasDegree` is zero.  It evaluates the defining equation on the
  homology class corresponding to `1 ∈ ℤ`.

## Remaining boundary

- Construct the homological intersection class represented by the transverse
  inverse image of the essential embedded circle.
- Use the disk-bounding hypothesis to show that class vanishes.
- Formalize naturality/Poincaré duality to conclude that the induced map of
  `f` on top singular homology is zero.

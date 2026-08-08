# Proof Outline: t96J05

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t96J05.md`

## Compiled progress

- `apm_t96j05_exists_positive_nonempty_radialLevel` proves that a nonzero
  point of `X` supplies a positive radius and an inhabitant of its literal
  radial-level subtype.

## Remaining boundary

- Use positive manifold dimension to prove that `X` contains a nonzero point.
- Apply manifold Sard to the restricted norm or squared norm to choose a
  positive regular value.
- Turn derivative surjectivity into a global `ChartedSpace` and `IsManifold`
  instance of model dimension `m - 1` on the exact level subtype.

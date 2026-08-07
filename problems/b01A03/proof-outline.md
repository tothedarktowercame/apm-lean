# Proof Outline: b01A03

The frozen theorem is fully proved in `lean/Main.lean`.

For complementedness versus a free quotient:

1. A complement `T` is free as a submodule of the finite free PID-module
   `M`; `Submodule.quotientEquivOfIsCompl` identifies `M ⧸ S` with `T`.
2. If `M ⧸ S` is free, it is projective. The projective lifting theorem
   supplies a linear section `i` of `S.mkQ`. The proof directly verifies
   that `S` and `LinearMap.range i` have trivial intersection and span `M`.

For freeness versus saturation:

1. A free quotient is torsion-free. Applying torsion-freeness to
   `a • (y mod S) = 0` proves the custom saturation predicate.
2. Conversely, saturation constructs a `Module.IsTorsionFree R (M ⧸ S)`
   instance directly. Since the quotient is finite, Mathlib's
   `Module.free_iff_isTorsionFree` over a PID yields freeness.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01A03.md`

## Verification

- `lake env lean problems/b01A03/lean/Main.lean` exits successfully.
- The main theorem contains no `sorry`.

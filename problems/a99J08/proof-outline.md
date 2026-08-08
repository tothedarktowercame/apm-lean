# Proof Outline: a99J08

The canonical Lean attempt is `lean/Main.lean`. Closer hops 1–2 formalize:

- squaring a purely imaginary or purely real complex value produces a value
  with zero imaginary part;
- consequently `g²` is real-valued on the punctured diameter `(-1,1) \ {0}`.
- every point of the open real diameter belongs to the closure of the upper
  half-disk, using `Complex.closure_preimage_im` and `IsOpen.closure_inter`;
- continuity along the explicit sequences `1/(n+1)` and `-1/(n+1)` forces
  both coordinates of `g 0` to vanish, so `g 0 = 0`.
- `apm_a99J08_sq_real_on_diameter` removes the exceptional corner and proves
  `g²` is real on the full open diameter.
- `apm_a99J08_sq_regular` packages continuity of `g²` on the closed upper
  half-disk and holomorphicity in its interior.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J08.md`

## Remaining boundary

- construct the local Schwarz reflection of `g²` from the upper half-disk to
  the full disk (the construction library only proves symmetry for functions
  already entire);
- factor the reflected holomorphic function by `z` and bound the quotient on a
  smaller disk;
- combine the local square-root estimate with compactness away from zero.

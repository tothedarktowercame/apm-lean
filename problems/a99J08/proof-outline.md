# Proof Outline: a99J08

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 formalizes the
central algebraic reduction:

- squaring a purely imaginary or purely real complex value produces a value
  with zero imaginary part;
- consequently `g²` is real-valued on the punctured diameter `(-1,1) \ {0}`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J08.md`

## Remaining boundary

- use continuity to extend the real-boundary identity through zero and prove
  `g 0 = 0`;
- construct the local Schwarz reflection of `g²` from the upper half-disk to
  the full disk (the construction library only proves symmetry for functions
  already entire);
- factor the reflected holomorphic function by `z` and bound the quotient on a
  smaller disk;
- combine the local square-root estimate with compactness away from zero.

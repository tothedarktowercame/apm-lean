# Proof Outline: t93A03

The canonical Lean attempt is `lean/Main.lean`. Non-simple-connectivity is now
proved from the requested free-group equivalence.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t93A03.md`

## Compiled progress

- `apm_t93a03_not_simplyConnected_of_piOne_equiv` proves the second conjunct
  from the first using the nontrivial generator of `FreeGroup (Fin 2)`.

## Remaining boundary

- Compute the fundamental group of the concrete quotient wedge.
- This requires `π₁(Circle)=ℤ` and a topological Seifert--van Kampen or
  wedge/free-product theorem, neither currently packaged in Mathlib.

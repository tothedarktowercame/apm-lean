# Proof Outline: t93A03

The canonical Lean attempt is `lean/Main.lean`. Non-simple-connectivity is now
proved for the repaired connected-sum statement from the requested free-group
equivalence and the supplied homotopy equivalence.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t93A03.md`

## Compiled progress

- `apm_t93a03_spine_not_simplyConnected_of_piOne_equiv` proves that the spine
  is not simply connected using the nontrivial generator of `FreeGroup (Fin 2)`.
- `apm_t93a03_connectedSum_not_simplyConnected_of_piOne_equiv` transports a
  hypothetical simple-connectivity instance across `hspine` and derives the
  contradiction on the spine. Thus the theorem's second conjunct is fully
  discharged once the first conjunct's equivalence is available.

## Remaining boundary

- Compute the fundamental group of the concrete quotient wedge.
- This requires `π₁(Circle)=ℤ` and a topological Seifert--van Kampen or
  wedge/free-product theorem, neither currently packaged in Mathlib.

## Closer hop 3 (2026-08-08)

The quotient bookkeeping needed for a future Van Kampen proof is now fully
compiled. The canonical quotient map is continuous and surjective, the two
circle basepoints agree, and `apm_t93a03_spineDesc` plus its computation and
uniqueness lemmas proves the continuous pushout universal property.

The remaining gap is no longer point-set topology: it is the absent
fundamental-group computation for this pushout and for `Circle` itself.

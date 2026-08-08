# Proof Outline: b98A02

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98A02.md`

## Compiled progress

- Extracted the maximality universal property and proved uniqueness of a
  maximal abelian subextension.
- Proved `A(E ⊓ L) ≤ A(E) ⊓ A(L)` directly from maximality.
- Proved the intersection of the two finite Galois intermediate fields is
  Galois by installing the hypotheses as instances; this closes part (c).
- `apm_b98a02_maximal_iff` closes part (b) using
  `IsAbelianGalois.of_algHom` for subfields of the maximal abelian extension.
- `apm_b98a02_intersection_maximal_eq` closes part (d) by giving
  `A_E ⊓ A_L` the inherited abelian Galois structure and applying maximality.
- Three map/comap helpers close the exact order-theoretic transport between
  intermediate fields inside `E` and ambient fields below `E`.

## Remaining bridge

Construct the commutator fixed field inside `E`, map it through `E.val`, then
transport its Galois structure and automorphism quotient to the mapped field.
Finally prove its universal property using restriction and exact map/comap
recovery. This is the sole remaining conjunct, part (a).

# Proof Outline: t97A01

The Lean statement uses the actual polygon quotients, integral singular
homology objects, and fundamental group.  One `sorry` remains.

## Compiled quotient layer

- `apm_t97a01_quotientX` and `apm_t97a01_quotientTorusRP2` are the canonical
  disk projections; both are proved continuous and surjective.
- `apm_t97a01_quotientX_identifies_a` and
  `apm_t97a01_quotientTorusRP2_identifies_c` expose representative edge
  identifications as literal equalities in the quotients.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97A01.md`

## Formal route

- Give each quotient the one-vertex, three-edge, one-face CW structure.
- Compare cellular homology with the frozen singular-homology functor.
- Compute the two boundary maps; both have Smith normal form
  `diag(2, 0, 0)`, yielding `H₁ ≅ ℤ × ℤ × ZMod 2`, with `H₀ ≅ ℤ` and
  higher homology zero.
- Apply Seifert--van Kampen to the torus-minus-disk and Möbius-band
  decomposition, identifying the boundary loop with `[a,b]` and `c²`.

## Open boundary

Mathlib currently supplies neither a cellular-to-singular comparison theorem
for these concrete polygon quotients, a singular Mayer--Vietoris sequence, nor
a topological Seifert--van Kampen theorem.  Closed siblings `t01J03`, `t02A03`,
`t92J05`, and `t97J04` encounter the same missing bridge.  Formalizing only the
integer chain calculation would not establish any frozen conjunct because the
statement deliberately retains the actual quotient spaces.

Mathlib's generic quotient lifting can construct continuous descended maps
from relation-respecting functions, but supplies no induced computation of
singular homology or the fundamental group.

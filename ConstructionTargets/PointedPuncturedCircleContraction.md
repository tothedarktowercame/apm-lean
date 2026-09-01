# Pointed contraction of the punctured circle

`PointedPuncturedCircleContraction.lean` transfers the stereographic
coordinate model of the circle punctured at `-1` back to the literal subtype
encodings used by the frozen topology consumers.

The file owns three layers only:

- a generic `PointedContraction` structure, oriented from the identity map at
  time `0` to the constant map at the chosen basepoint at time `1`, together
  with the all-times fixed-basepoint law;
- the explicit punctured-circle contraction, defined by straight-line
  contraction in the orthogonal complement coordinates produced by
  stereographic projection from `-1`;
- the product contraction and the literal homeomorphism from the product
  punctured-circle subtype to the open neighborhood
  `{(z,w) : Circle × Circle | z ≠ -1 ∧ w ≠ -1}`.

The representation bridge is intentionally concrete. The file keeps the
stereographic formulas and inverse source checks visible instead of replacing
them by an abstract `ContractibleSpace` witness, because later quotient and
open-cover consumers need the exact subtype and evaluation formulas.

The module does not assert any wedge quotient descent, open-cover assembly,
Mayer--Vietoris computation, source reconstruction, or frozen uptake.

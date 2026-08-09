# Proof Outline: t00A01

The Lean encoding constructs the connected sum as the equivalence closure of
the boundary-sphere gluing relation.  The helper
`apm_t00A01_mk_inl_eq_mk_inr` proves that the quotient identifies the two
copies of every boundary point.

Closer hop 2 additionally packages the quotient as a continuous gluing
cocone: `apm_t00A01_continuous_inl`, `apm_t00A01_continuous_inr`, and
`apm_t00A01_inl_comp_iA_eq_inr_comp_iB` provide the two canonical maps and
their boundary compatibility.

Closer hop 3 proves the full mapping universal property of this concrete
quotient. Compatible piece maps descend through `apm_t00A01_glueLift`, the
lift computes on both canonical inclusions, continuity follows from continuity
on each piece, and `apm_t00A01_glueLift_unique` proves uniqueness. Thus the
point-set topological pushout layer is complete.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A01.md`

## Hop 4 bridge contracts

- `apm_t00A01_bridge_fundamentalGroup_coprod` states the missing
  Seifert--van Kampen comparison for the supplied cover. It includes the
  necessary change of basepoint and transport through the two given
  fundamental-group equivalences.
- `apm_t00A01_bridge_connectedSum_isHomology3Sphere` states the singular
  Mayer--Vietoris calculation for two homology balls glued along the standard
  sphere overlap.

Both contracts are intentionally unproved. They match the two conjuncts of
the main theorem exactly, reducing its completion to conjunction assembly
without changing the frozen statement.

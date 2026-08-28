# FiniteFreeHurewiczNaturality

This target packages degree-one Hurewicz in arbitrary supplied finite-free
integer coordinates.  If both the fundamental group and H1 are identified
with `Fin n → ℤ`, the conjugated abelianized Hurewicz map is surjective by the
direct singular-chain theorem and injective by finite-free Hopficity.  The
resulting `MulEquiv` retains the explicit abelianized Hurewicz homomorphism as
its forward map.

The naturality theorem accepts source and target coordinates and a proposed
coordinate homomorphism.  It proves that an equation for
`FundamentalGroup.map` forces the corresponding equation for the induced
integral H1 map, with the source and target Hurewicz coordinate automorphisms
shown explicitly.  They cannot honestly be omitted for arbitrary independent
coordinate choices.  It does not supply or assume a concrete matrix.  Separate
rank-one definitions use `ℤ` directly rather than imposing a `Fin 1`
representation.

No generic Hurewicz injectivity outside the finite-free equal-rank setting and
no twice-spiral calculation is claimed.

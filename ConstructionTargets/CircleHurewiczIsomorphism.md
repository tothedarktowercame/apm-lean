# CircleHurewiczIsomorphism

This target proves the degree-one Hurewicz comparison for the circle after
abelianization.  It uses the compiled winding-number equivalence for the
fundamental group, the compiled integral H1 coordinate, and the independently
proved path-connected Hurewicz surjectivity theorem.

The reusable algebraic ingredients are the equivalence between the
abelianization of an already commutative group and that group, and the theorem
that every surjective additive endomorphism of `ℤ` is injective.  Conjugating
the circle Hurewicz map by its two integer coordinates therefore makes it a
bijective endomorphism of `ℤ`, yielding
`circleAbelianizedFundamentalGroupH1MulEquiv`.

This is a Circle-specific rank-one result.  It does not assert generic
Hurewicz injectivity, a generic Hurewicz isomorphism, or any concrete map
calculation for the boundary torus.

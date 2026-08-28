# BoundaryTorusHurewiczIsomorphism

This target proves the degree-one Hurewicz isomorphism after abelianization
for the concrete boundary torus
`Circle × Sphere 1`, based at `(1, circleHomeomorphSphereOne 1)`.

The algebraic input is a reusable theorem that every surjective integral
linear endomorphism of `Fin n → ℤ` is injective.  Its proof invokes Mathlib's
finite-free projective endomorphism theorem, whose hypotheses are synthesized
for this module.  Additive and multiplicative wrappers are then derived.

On the topology side, the file proves that a homeomorphism induces an
equivalence of based fundamental groups, combines the product fundamental
group theorem with the two Circle winding coordinates, and normalizes the
result to `Multiplicative (Fin 2 → ℤ)`.  The compiled boundary-torus H1
coordinate gives the same codomain.  Path-connected Hurewicz surjectivity
makes the conjugated endomorphism surjective; finite-free Hopficity makes it
injective.

The final equivalence has the explicit
`abelianizedFundamentalGroupToH1 boundaryTorusBasepoint` as its forward map.
No generic Hurewicz injectivity theorem and no twice-spiral matrix calculation
is assumed or proved here.

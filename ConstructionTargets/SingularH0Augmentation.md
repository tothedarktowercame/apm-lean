# Integral singular H0 augmentation

`SingularH0Augmentation.lean` descends the coefficient-sum map on singular
zero-chains to a canonical map `H₀(X; ℤ) → ℤ` for every topological space.
No connectedness or nonemptiness assumption is used.

The key compiled identities say that the canonical projection of zero-chains
to zeroth homology, followed by this augmentation, is the original
coefficient sum, and that continuous maps commute with the augmentation.

For a nonempty space whose integral `H₀` object is isomorphic to `ℤ`, a
chosen vertex class splits the augmentation. Transporting it through the
given cyclic coordinate produces an epimorphic endomorphism of `ℤ`, hence a
monomorphism by the existing integer-group lemma. Thus the augmentation is an
isomorphism. Naturality then proves that every continuous map between two such
spaces induces an isomorphism on `H₀`.

This result does not infer topological connectedness from homology and does
not choose path-component representatives. It proves only the map-level fact
needed by the degree-zero end of t00A01's connected-sum Mayer--Vietoris
argument. It does not construct that Mayer--Vietoris sequence, compute the
remaining degrees, or prove t00A01's full homology-sphere bridge.

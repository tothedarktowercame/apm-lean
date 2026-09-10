# TorusFormTargets

The space is `(Fin 2 → AddCircle 1)`, the coordinatewise quotient R²/Z². `projection` is real reduction modulo 1 in each coordinate. `SmoothAtlas` must give this fixed topology its smooth structure and make this projection a local diffeomorphism. t93A06 asks for an inhabitant and the exact integer-lattice fiber relation.

The printed 2-form is a scalar multiple of the genuine determinant alternating map. Its explicit primitive is (x/2 − sin(4πx)/(8π)) cos²(2πy) dy. The torus integral is the integral of the pulled-back form on the positively oriented unit square; segment integrals evaluate the 1-form on the actual tangent b−a. The four segment endpoints are exactly those printed.

Construction targets: construct the quotient atlas; prove descent/uniqueness, the primitive identity and the two integral values; identify fundamental-domain integration with intrinsic integration under the quotient-induced orientation; prove nonexactness downstairs. There is no arbitrary integral operator or assumed integral value.

The module builds as a named Lake target and is imported by ConstructionTargets.lean. Its definitions contain no `sorry`; consumer theorems remain explicitly unproved. Independent mathematical review is pending.

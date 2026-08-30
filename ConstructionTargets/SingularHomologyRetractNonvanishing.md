# Singular-homology nonvanishing from retracts

`integralHomology_not_isZero_of_split_retract` applies the production integral
singular-homology functor to a section/retraction equation. If the ambient
homology object were zero, the section map would be zero, forcing the identity
of the retract's homology object to be zero.

`integralHomology_product_not_isZero` specializes this to the section
`x ↦ (x,y)` and projection `Prod.fst`. Together with
`positiveSphere_topHomology_not_isZero` and the off-degree sphere calculation
from `SphereHomology`, this proves:

- `sphereSix_not_homeomorphic_sphereTwo_product_sphereFour`;
- `sphereSix_not_homeomorphic_sphereThree_product_sphereThree`.

No product-homology decomposition is used. In particular, this target assumes
neither Eilenberg--Zilber nor Künneth. It does not compare `S² × S⁴` with
`S³ × S³`.

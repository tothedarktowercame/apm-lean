# Lipschitz parameterized flat Taylor remainder

`exists_lipschitz_parameterized_flat_taylor_remainder` transfers an ambient
flat Taylor estimate to a parameter subset. The ambient map is globally
C^(k+1), and its derivatives of orders 1 through k vanish on the image of
that subset. The image lies in a specified closed ball in a proper real
normed space. The parametrization need only be Lipschitz on the subset;
neither injectivity nor differentiability of the parametrization is assumed.

The observed dependency is `SardUniformFlatTaylorRemainder`, specifically
`exists_uniform_flat_taylor_remainder_on_bounded_set`. Its nonnegative
constant D gives the composite constant D*L^(k+1), where L is the supplied
nonnegative Lipschitz constant. Power monotonicity transfers the distance
bound and retains exponent k+1. The parameter space needs only a normed
additive commutative group, not finite dimension or a real vector structure.

This is a pairwise remainder bound, not a smoothness or image-nullity theorem.
In particular, it does not supply higher derivatives of the composite or
establish remaining-order Sard admissibility. Local Lipschitz chart
restrictions and parameter-space covers remain to be constructed. Covering
nullity requires the retained exponent times target dimension to exceed
parameter dimension; uncovered higher-jet cases still require analytic
repair before induction and exhaustion. No Morse-Sard refutation is claimed.

The intended consumer is t93A04; additional proposed consumers are t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is changed or closed here.
The source is byte-identical to the accepted fixture
`/tmp/SardLipschitzParameterizedFlatTaylorRemainderProbe.lean`, SHA-256
`ffb02082a64216d8bd3301c6c49f7576cfdcdcc17e6a73111edc32295d925e28`.
The declaration uses only propext, Classical.choice, and Quot.sound.

The stop boundary is failure of exponent preservation under the stated
Lipschitz bound, or a need for nonstandard axioms.

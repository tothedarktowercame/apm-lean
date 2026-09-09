# H0 augmentation with explicit ring coefficients

The coefficient ring `R : Type` has `[CommRing R]`; the spaces `X`, `Y : Type`
have arbitrary topologies. Ring and spaces are universe zero. Chains and
homology use the actual singular functors in `ModuleCat R` with coefficient
object `ModuleCat.of R R`.

The construction proves the alternating boundary formula for coefficient-
generic singular generators. The singular edge of a path has boundary equal
to endpoint minus startpoint, so its two point classes agree in H0.
Every singular zero-simplex is a vertex, and the coproduct generators show
that, on a path-connected space, every zero-chain class is its coefficient
sum times a chosen point class.

`zeroChainAugmentation` sums coefficients. Boundaries have sum zero, so the
homology cokernel property constructs `h0Augmentation`. Its naturality says
that the induced H0 map followed by the target augmentation equals the source
augmentation. This construction and naturality require no connectedness.
Some inherited Lean docstrings still say integral augmentation; the actual
types and constructions are over the explicit ring `R` throughout.

A point class followed by augmentation is the identity on `R`. Conversely,
with `[PathConnectedSpace X]` and an explicit `p : X`, augmentation followed
by that point class is the identity on H0. The latter equation follows by
cancelling the proved epimorphic zero-chain projection and using generation.
`h0Iso` packages these two constructed inverse maps.

`sphereH0` specializes to the literal Euclidean unit sphere in dimension
`n` with `[NeZero n]`. `rationalS2H0` explicitly has the actual rational
singular-homology type for the metric sphere in `EuclideanSpace ℝ (Fin 3)`;
`integralS2H0` uses the same construction over the integers. `identity_induced`
proves identity-map compatibility for the actual homology functor. Ordinary
S0 remains separate, with its reviewed two-coordinate H0 calculation.

The source exactly promotes `/tmp/CoefficientH0.lean`, SHA256
`3accdb80581f1167e758706b4a7e80503c413f835cf53f09d47b50dcc5cbb932`.
Validation includes fixture and canonical compilation, the focused build,
nine printed standard-only axiom audits, and placeholder and scope checks.

Rational H1 vanishing and H2 identification, coefficient-general sphere
suspension and endpoints, product homology and full t00J01 closure remain
downstream. No change-of-coefficients isomorphism or path-component
classification is assumed or proved here.

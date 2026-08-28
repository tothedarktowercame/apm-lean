# TwiceSpiralSignedArrowAlgebra

For every integer `d`, this target treats the actual signed degree-one arrow
as the categorical morphism

`(a,b) ↦ (b, -(2*a + d*b)) : ℤ² → ℤ²`.

Coordinate equations prove it injective, hence monic.  The normalized quotient
map is `q_d(x,y) = y + d*x` in `ZMod 2`.  The target proves directly that this
map kills the signed arrow and constructs its full cokernel universal
property.  Consequently the canonical cokernel is isomorphic to
`AddCommGrpCat.of (ZMod 2)`, with the canonical projection normalized to
`q_d`.

No determinant, Smith normal form, kernel/cokernel assumption, or frozen
bridge conclusion is used.

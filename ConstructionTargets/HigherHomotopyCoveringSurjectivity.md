# Higher-homotopy covering surjectivity

This target closes the topological step left in frozen `t01J02`.  Mathlib's
covering lift theorem produces a lift of a generalized cube loop after fixing
one boundary point.  The compiled path-connectedness of the finite cube
boundary and covering-map uniqueness then prove that this lift is constant on
the entire boundary.  It therefore defines a genuine `GenLoop` upstairs.

The quotient construction gives reusable surjectivity and injectivity theorems
for the induced map on `HomotopyGroup`, followed by the exact `Fin n`, `2 ≤ n`
bijection needed by the frozen model.  No boundary constancy, surjectivity, or
bijectivity is assumed.

The frozen file defines its postcomposition map locally rather than importing
a public construction target.  The remaining wiring is consequently a
definitional comparison between its `apm_t01j02_homotopyMap` and this target's
`homotopyMap`, plus its existing basepoint equality cast; there is no remaining
covering-lift or cube-boundary theorem.

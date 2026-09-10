# Product simplex reconstructed maximal path

This module applies `SSet.prodStdSimplex.objEquiv.symm` to the cumulative order
homomorphism of a balanced Boolean word.  The resulting
`reconstructedSimplex` is therefore exactly the product simplex whose ordered
grid vertices are its horizontal and vertical prefix counts.

`reconstructedSimplex_objEquiv` records the equivalence inverse law explicitly.
`reconstructedPath` packages that simplex as a maximal nondegenerate simplex:
`mem_maximalPath_iff` reduces nondegeneracy to the coordinate-sum condition,
which is supplied by `cumulativeOrderHom_coordinate_sum`.

The module does not prove either word/path inverse law and does not define
corner swaps, face cancellation, chain sums, or a singular cross product.

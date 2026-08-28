# DegreeOneHurewiczSurjectivityFinal

This target begins the final direct closing-path assembly.  It combines the
two compiled concatenation triangles with the explicit unnormalized
backtracking filler.  For every production singular edge it proves that its
closed based-loop chain differs from the edge chain plus the initial connector
minus the terminal connector by an actual production two-chain boundary.

The remaining step is finite assembly: weight this equation by the coefficients
on `oneChainSupport`, regroup connector chains by their endpoint zero-simplex,
use `cycle_vertex_balance`, and identify the remaining edge sum with the
original chain.  The target does compile the coefficient-weighted finite sum
of all individual defects as one production boundary; the unresolved part is
the endpoint-indexed regrouping of its connector terms.  Only after that can
the result be passed through `homologyπ` and
`fundamentalGroupH1Hom`.  Neither surjectivity nor injectivity is claimed here.

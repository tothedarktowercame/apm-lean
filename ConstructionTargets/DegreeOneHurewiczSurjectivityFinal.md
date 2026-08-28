# DegreeOneHurewiczSurjectivityFinal

This target begins the final direct closing-path assembly.  It combines the
two compiled concatenation triangles with the explicit unnormalized
backtracking filler.  For every production singular edge it proves that its
closed based-loop chain differs from the edge chain plus the initial connector
minus the terminal connector by an actual production two-chain boundary.

The endpoint layer is now complete.  It identifies the point represented by
each production face zero-simplex with the corresponding endpoint of the
recovered interval path, regroups both connector sums over a finite endpoint
support, and applies `cycle_vertex_balance` with the terminal-minus-initial
sign convention.  Thus the connector sums cancel for every production
one-cycle.

The target reconstructs the original chain from its canonical coefficients,
builds the weighted closed-loop chain and boundary witness, and proves that
the original cycle and the finite weighted sum of directly closed edge loops
have equal production H1 classes.

The remaining step toward surjectivity is algebraic realization of that
weighted sum as the image under `fundamentalGroupH1Hom` of a finite product of
integer powers of the closed-edge loops, followed by choosing a cycle
representative for an arbitrary homology element.  Neither surjectivity nor an
`Epi` instance is claimed here.

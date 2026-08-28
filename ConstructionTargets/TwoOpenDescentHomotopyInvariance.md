# Representative-level homotopy invariance

`castSubdivision` explicitly transports a subdivision certificate across an
equality of underlying paths, and `evaluate_castSubdivision` records that this
transport does not alter its common-coordinate morphism.

Using the uniform subordinate grid, the finite time telescope, and arbitrary
subdivision independence, `evaluate_eq_of_pathHomotopy` proves that arbitrary
subdivisions of relatively homotopic paths have equal evaluations.
`evaluate_eq_of_homotopic` exposes the same result from an actual
`Path.Homotopic` witness, ready for later quotient descent.

No quotient function, descent functor, or van Kampen universal property is
constructed here.  The next step is to choose subdivisions for path
representatives coherently enough to define the morphism map on
`Path.Homotopic.Quotient`, using this theorem for well-definedness.

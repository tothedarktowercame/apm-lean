# Finite coordinates for actual singular chains

`coordinates` constructs an R-linear equivalence from the actual degree-n
singular-chain object with coefficient object `ModuleCat.of R R` to finitely
supported functions from actual singular n-simplices to R. The ring R and
topological space X are universe zero; R is a commutative ring. Every natural
number degree is supported, without nonemptiness, connectedness or cover
hypotheses. Coefficients range over all of R.

The equivalence composes `ModuleCat.coprodIsoDirectSum` with the inverse of
`finsuppLEquivDirectSum`. `coordinates_generator` identifies a simplex
generator evaluated at r with the singleton coordinate r. `inverse_single`
proves the reverse equation. `finite_expansion` reconstructs every actual
chain as the finite sum of its generators evaluated at these coordinates;
`exists_finite_expansion` exports the resulting finite presentation.

Imports reuse `CoefficientFiniteRealization` and Mathlib's module coproduct
and direct-sum APIs. The interval-edge examples use coefficient 3 over the
integers and coefficient 1/2 over the rationals. Four printed axiom audits
cover the coordinate and reconstruction equations.

The Lean file is an exact promotion of `/tmp/CoefficientChainSupport.lean`,
SHA256 `925af120ead4db53582b302b9975249e0a32364a595a82f99bb619b11a3e3cc8`.

Iterate-realization compatibility, geometric subordinate support at a common
exponent and actual preimages for every larger exponent remain downstream.
This module does not establish eventual smallness, homology comparison,
excision or frozen consumer closure.

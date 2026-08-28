# CircleUniversalCover

This target packages Mathlib's existing quotient cover
`Real → AddCircle (2 * pi)` through `AddCircle.homeomorphCircle'`.

It proves that `Circle.exp` is a covering map and a local homeomorphism,
identifies each fiber by integral multiples of `2 * pi`, constructs Mathlib's
canonical continuous lift of a based loop starting at zero, and proves that a lifted
loop's endpoint is a unique integral period.  The chosen integer coordinate is
proved invariant under homotopies relative to the two endpoints, using
Mathlib's covering homotopy lifting theorem.  Explicit constant-speed loops
realize every integer, and their canonical lifts are computed literally.  A
translated-lift uniqueness calculation and Mathlib's literal `Path.trans`
lifting theorem prove that concatenation adds endpoint integers.  A separate
corollary records Mathlib's reversed `CategoryTheory.End` multiplication order
explicitly; commutativity of integer addition gives the required orientation.

The endpoint coordinate descends to the actual based-loop homotopy quotient.
Explicit integer loops prove surjectivity.  For injectivity, equal coordinates
give equal lifted endpoints; the two lifts are joined by the explicit affine
homotopy in `Real`, which projects to a based homotopy in `Circle`.  This gives
the axiom-clean classification
`FundamentalGroup Circle 1 ≃* Multiplicative Int`.

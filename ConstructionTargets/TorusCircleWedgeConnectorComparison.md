# Torus–circle wedge connector comparison

This target fixes explicit connector systems for the fundamental groupoids of
`Unit`, `Circle × Circle`, and `Circle`.  It proves that the two coordinate
functors respect those connectors and packages the resulting comparison cells
against the induced vertex homomorphisms.

The endpoint groups are identified as `PUnit`, `Multiplicative (ℤ × ℤ)`, and
`Multiplicative ℤ`.  The torus coordinates are ordered by the product
fundamental-group equivalence, then the first and second circle winding
equivalences, followed by `(MulEquiv.prodMultiplicative ℤ ℤ).symm`.  This file
does not construct a pseudococone, reconstruct a source, or modify a frozen
problem.

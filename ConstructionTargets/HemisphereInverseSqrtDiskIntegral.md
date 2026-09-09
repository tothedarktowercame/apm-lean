# Hemisphere inverse-square-root disk integral

This leaf compiles the part of the t03J06 hemisphere calculation that does not
require a missing polar-integration theorem.

It proves that the square-root denominator is strictly positive on the open
disk, identifies the literal `x/sqrt` and `y/sqrt` formulas there, proves that
the closed disk is invariant under the two coordinate reflections, and proves
pointwise cancellation of each odd term with its reflected value. These
statements remain valid independently of how the measure-zero boundary circle
is represented.

The exact remaining standard analytic input is isolated as
`RadialInverseSqrtIntegrable`: integrability of
`(1-x²-y²)⁻¹ᐟ²` on the unit disk. The current Mathlib checkout contains general
polar-coordinate change-of-variables infrastructure, but no ready theorem for
this disk singularity. Proving that estimate, then applying reflection
invariance of planar Lebesgue measure, is still needed to turn the compiled
pointwise cancellations into zero disk integrals. Consequently this leaf does
not claim the hemisphere value `3π`, use Stokes, or claim the final bullet
integral.

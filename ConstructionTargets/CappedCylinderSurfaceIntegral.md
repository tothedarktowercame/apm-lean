# Capped-cylinder scalar surface integral

This leaf evaluates the full cylindrical contribution in frozen `t03J06`.
After expanding the compiled cylinder integrand it is the sum of `1` and two
angular cancellation terms.  The first changes sign under
`θ ↦ 2π - θ`; the second changes sign under `θ ↦ θ + π`.  Two reusable
interval-integral lemmas formalize those cancellations.

`angular_integral_cylinderIntegrand` proves that every fixed-height angular
integral is `2π`.  The joint integrand is continuous on the compact parameter
rectangle, so Fubini is applicable, and `cylinder_surface_integral` proves the
frozen nested cylinder integral is `4π`.
`cylinder_surface_integral_of_pointwise` is the direct adapter consuming the
already-compiled frozen cylinder-integrand equality.

The hemisphere remains separate.  Its expected contribution is `3π`, but the
compiled formula contains the boundary quotients `x / sqrt (1-x²-y²)` and
`y / sqrt (1-x²-y²)`.  Proving their integrability and their disk-symmetry
cancellations is the next measure-theoretic seam.  This file assumes neither
that seam, Stokes' theorem, nor the final `7π` surface integral.

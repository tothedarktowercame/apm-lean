# Capped-cylinder hemisphere integral

The frozen hemispherical pullback is expanded into two reflection-odd terms
and the radial expression `1 + (1-x²-y²)⁻¹ᐟ²`.  The odd terms are integrable
because their remaining coefficients are continuous on the compact unit disk;
the existing coordinate reflections make their integrals zero.

For the even term, the substitution `u = 1-r²` proves
`∫₀¹ r / sqrt(1-r²) dr = 1`.  Mathlib's additive-Haar polar formula therefore
gives `2π` for the inverse-square-root kernel.  The disk's constant term gives
another `π`, so `hemisphere_surface_integral` is `3π`.

`hemisphere_surface_integral_of_pointwise` is the adapter for the frozen
pointwise pullback formula.  No Stokes theorem, bullet value, or final frozen
theorem is assumed.

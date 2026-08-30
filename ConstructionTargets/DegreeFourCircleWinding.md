# Degree-four circle winding

This target supplies the missing winding half of
`DegreeFourDiskBoundaryObstruction`.

`fourthPowerLift` is the explicit real lift `t ↦ 4 (2π)t` of the
fourth-power once-around circle path.  Its endpoint equation is computed as
the integer `4`.  For a hypothetical free homotopy to a constant, the target
lifts the homotopy square.  Covering-space uniqueness makes the difference
between its bottom edge and `fourthPowerLift` constant, while its constant top
edge has winding zero.  Homotopy invariance would therefore give `4 = 0`.

Consequently `degreeFour_not_homotopic_const` completes the topological
obstruction, and `exists_zero_of_degreeFour_normalizedBoundary` combines it
with the previously compiled radial disk contraction.  The latter keeps the
normalization hypothesis dependent on the proposed zero-free proof, matching
the actual construction without postulating a degree invariant.

`exists_zero_of_degreeFour_homotopic_normalizedBoundary` is the stronger
adapter needed by the frozen problem: a zero-free homotopy on the boundary can
be normalized to supply its hypothesis.  The remaining frozen-specific work
is only the radius-`r` rescaling and normalization of its complex-valued
cylinder homotopy.

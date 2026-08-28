# TwiceSpiralGluingHomologyTable

This target completes the integral singular-homology calculation for the
reusable solid-torus gluing model.  It uses the actual production
Mayer--Vietoris connecting map rather than a product or Künneth computation.

`gluingH3GroupIsoInt` proves that the degree-three connecting map is an
isomorphism.  Both solid-torus cover pieces have zero homology in degrees two
and three, so the two adjacent production exactness statements identify
`H₃(Gluing h)` with `H₂(BoundaryTorus)`, which is already identified with
`ℤ`.  `gluingH3ModuleIsoInt` transports this result to `ModuleCat ℤ`.

For `k > 3`, `gluingGroupHomology_isZero_of_three_lt` uses exactness to make
the connecting map from degree `k` monic.  Its target is degree `k - 1`
homology of the boundary-torus intersection, which vanishes.  The corresponding
module result is `gluingModuleHomology_isZero_of_three_lt`.

These degree-three and higher declarations are independent of the twice-spiral
coordinate hypotheses.  `gluing_complete_module_homology` combines them with
the unconditional H0 computation and the conditional H1 and H2 computations
from `TwiceSpiralGluingHomologyConsequences`.  Its result has the homology-table
shape needed by the frozen `t01J03` bridge, but it makes no fundamental-group
claim and does not close that bridge.

The remaining frozen seam is therefore the fundamental group of the glued
space, together with a small adapter unpacking the frozen `hasTwiceSpiral`
predicate into the three coordinate hypotheses consumed here.

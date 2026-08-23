# EmbeddedCirclePreimage

This module isolates the categorical middle layer of the `t00J02` preimage
argument. Given circle parametrizations covering the inverse image of an
embedded circle, with each parametrization sent to zero by a functor from
`TopCat`, it produces compatible lifts to the target circle and proves those
lifts are also sent to zero whenever the embedded circle is sent to a mono.

The strongest theorem is `exists_component_lift_eq_zero_and_range`. Besides
the lift and its functorial vanishing, it retains the fact that the source
circle lies in the inverse image; this is the geometric input needed by a
later orientation or intersection argument. The projection
`exists_component_lift_eq_zero` remains available to purely homological
consumers.

The module deliberately leaves the differential-topological
transverse-preimage/Poincaré-duality step to its consumer.

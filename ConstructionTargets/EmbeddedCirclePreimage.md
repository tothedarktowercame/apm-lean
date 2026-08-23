# EmbeddedCirclePreimage

This module isolates the categorical middle layer of the `t00J02` preimage
argument. Given circle parametrizations covering the inverse image of an
embedded circle, with each parametrization sent to zero by a functor from
`TopCat`, it produces compatible lifts to the target circle and proves those
lifts are also sent to zero whenever the embedded circle is sent to a mono.

The main theorem is `exists_component_lift_eq_zero`. The module deliberately leaves the
differential-topological transverse-preimage/Poincaré-duality step to its
consumer.

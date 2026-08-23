# Disk boundary homology

`DiskBoundaryHomology.lean` packages the coefficient-independent fact that the
boundary of a continuous map from the closed complex unit disk is
nullhomotopic, and consequently induces zero on positive-degree singular
homology. It was extracted for `t00J02`, whose disk-bounded inverse-image
components need precisely this input before the missing intersection-duality
bridge can be applied.

The module also provides the consumer-depth interface
`ComponentsBoundByDisks` and two coefficient-generic consequences. The first
produces a boundary circle whose range is the selected connected component;
the second produces, through every point of the set, a circle contained in the
set whose positive-degree singular-homology map is zero. This pointwise form
feeds directly into `EmbeddedCirclePreimage.hasNullWindingPreimage_of_components`
and avoids rebuilding the disk-boundary and connected-component argument in
each geometric consumer.

Axiom audit (2026-08-23):
`exists_homology_trivial_circle_through_point` depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The still-open geometric bridge in the
keying problem is not the library terminal and is tracked separately by that
problem's sorry audit.

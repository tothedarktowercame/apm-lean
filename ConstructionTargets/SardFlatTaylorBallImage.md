# Flat Taylor remainder ball-image containment

`flatTaylor_image_inter_closedBall_subset` converts a pointwise order-`k + 1`
remainder estimate on a subset of a real normed space into the target-ball
containment needed by a scale-cover argument.  Intersecting the source subset
with the closed ball of radius `r` about `a` gives an image contained in the
closed ball of radius `C * r ^ (k + 1)` about `f a`.

The theorem performs only this metric adapter step.  It does not obtain the
remainder estimate from smoothness, construct the scale-wise source cover, or
deduce target-measure nullity.  The next Sard obligation is therefore the
scale-wise smooth flat-locus remainder-and-null-cover theorem, before local
rank reduction.

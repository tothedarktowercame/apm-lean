# Local flat Taylor remainder ball-image containment

`flatTaylor_image_inter_closedBall_subset_local` converts an order-`k + 1`
Taylor remainder estimate on the localized set `s ∩ closedBall a r` into the
target-ball containment used by finite-cover arguments. The image lies in the
closed ball about `f a` of radius `C * r ^ (k + 1)`.

Unlike the earlier global adapter, this theorem requests the remainder bound
only at points belonging to the source ball whose image is being bounded. This
matches compact uniform little-o control after a sufficiently small cover scale
has been selected. Localized finite-cover aggregation and construction of the
endpoint small-coefficient cover data remain.

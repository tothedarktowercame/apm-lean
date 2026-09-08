# Projected-slice local image-nullity witness

`local_image_null_of_subset_projectedSlice` packages the pointwise witness
consumed by exact-rank-piece local aggregation.  It retains an open
neighborhood and its base-point membership while proving that the local source
piece has null image.

The proof assumes that this local image is contained in the image of a smooth
lower-dimensional slice.  A surjective projected coordinate with zero
derivative makes the whole slice image null by the compiled induction theorem;
measure monotonicity transfers that conclusion to the restricted source-piece
image.

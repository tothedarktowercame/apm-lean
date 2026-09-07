# Local rank-coordinate normal form

`localRankNormalForm_of_complemented_minor` specializes Mathlib's
`ImplicitFunctionData` interface to the coordinate form needed by the local
rank step in Sard's theorem.  The resulting `OpenPartialHomeomorph` maps a
source point to the regular output coordinates paired with complementary source
coordinates, contains the base point in its source, and satisfies the two local
inverse coordinate equations near the base image.

The selected invertible derivative minor and complementary source block are
represented by the input `ImplicitFunctionData`; this theorem does not select
that data from an abstract rank equality.  It also does not prove flat-locus
image nullity or perform the rank/source-dimension induction.  Those remain the
two separate obligations before rectangular local Sard assembly, and no
manifold chart assembly is begun here.

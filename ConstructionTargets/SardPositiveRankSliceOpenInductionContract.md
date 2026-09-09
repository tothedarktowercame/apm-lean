# Positive-rank residual slices with open-domain induction

The fixture constructs the actual projected rank chart using
`SardGenuineSmoothRankUpperResidualZero`, retaining its source membership,
first-coordinate identity, and genuine-infinity smoothness in both directions.
Rank-nullity gives strict source dimension drop, and orthogonal dimension
addition gives a nontrivial complementary target.

`exists_positive_rank_slice_image_null` assumes critical-image nullity only
for maps smooth on an explicitly open domain in each strictly smaller
finite-dimensional complete real inner-product source. Zero-dimensional
sources are included. For each first coordinate r, the open domain is exactly
`{z | (r,z) ∈ e.target}`. The rank-bounded subset lies in that domain.
The banked regularity producer yields ContDiffOn infinity there; its zero
derivative conclusion makes every point of the rank-bounded subset critical.
Applying the open-domain premise proves the actual complementary image null.

`open_induction_of_global` obtains precisely this premise from smaller-source
global smooth critical-image nullity using
`SardGenuineSmoothOpenDomainLocalization.local_image_null_of_global` (in its
Probe namespace). `exists_positive_rank_slice_image_null_of_global_induction`
composes both theorems for the actual complementary target, deriving its
inherited Borel instance with the existing derivative-range producer.

No chart, dimension drop, extension, derivative identity, or residual nullity
is assumed. No positive lower bound on the smaller source dimension is used.
No pointwise-to-neighborhood infinity assertion is used. Existing APIs remain
unchanged. This repairs only the positive-rank slice contract. Propagation
through compact/open/stratum/global assembly, the analogous rank-zero
first-nonzero-jet contract, induction discharge and manifold transport remain.

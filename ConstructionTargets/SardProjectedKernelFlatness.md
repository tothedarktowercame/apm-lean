# Projected-kernel derivative flatness

This module promotes two compiled linear-algebra interfaces for local rank reduction.

If `P ∘ L` is surjective and the full range of `L` has dimension at most the dimension of the projected target, rank-nullity forces `ker (P ∘ L) = ker L`. The pointwise theorem then states that the full derivative kills every vector tangent to a projected-coordinate fibre.

The next consumer step is to instantiate this result throughout the local rank-at-most locus where the projected block stays surjective, transport the kernel direction through the local normal-form coordinates, and prove residual target-coordinate derivative flatness before applying Taylor-cover nullity.

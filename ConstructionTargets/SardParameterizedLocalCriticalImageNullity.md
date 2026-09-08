# Parameterized local critical-image nullity

This module gives the local-on-local form of critical-image nullity transfer needed by source-dimension induction.

Let `t` be a localized critical set of `f` contained in the image of a parameter set `s` under `g`. If both maps are differentiable at the relevant points and the image of the critical set of `f ∘ g` restricted to `s` is null, then `f '' t` is null. No global critical-image nullity or differentiability away from `s` is required.

The downstream Sard argument must apply its lower-dimensional induction hypothesis to each restricted kernel composite, transfer the result with this theorem, and aggregate the local refined loci.

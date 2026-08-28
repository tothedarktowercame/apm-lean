# FundamentalGroupoidTwoOpenRefinement

This target proves the local refinement identity downstream of
`FundamentalGroupoidTwoOpenDescent`.

`pathInPiece_trans` makes the subtype-path concatenation equation explicit,
and `mapPath_trans` transports functorial composition through the common object
coordinates and their `eqToHom` terms.

`subpathSplitHomotopyInPiece` lifts Mathlib's
`Path.Homotopy.subpathTransSubpath` into the selected cover subtype.  Its range
certificate comes from the original path's membership in that cover member.
`mapPath_subpath_split` then proves that the mapped whole segment equals the
categorical composite of the two mapped subsegments.

`subpath_mem_of_mem_ordered_segment` is the first localized layer: membership
of `p.subpath t₀ t₂` restricts to every ordered subsegment `[a,c] ⊆ [t₀,t₂]`.
In particular it supplies the two chart-membership proofs for `[t₀,t₁]` and
`[t₁,t₂]` without assuming anything about `p` outside `[t₀,t₂]`.

The remaining localized split step is an explicit range theorem for
`Path.Homotopy.subpathTransSubpath`: under `t₀ ≤ t₁ ≤ t₂`, every point of that
homotopy lies in `Set.range (p.subpath t₀ t₂)`. Mathlib's definition composes
`subpathTransSubpathRefl` with `transRefl`; after unfolding, the second branch
is a cast of a reparameterized homotopy, and no range lemma for that composite
is currently exposed.  Until that range theorem is proved, lifting the
homotopy into `twoChart U V b` from segment-only membership would be an
unsupported step.

No refinement invariance, descent functor, or van Kampen conclusion is
assumed. The next exact seam is the range-preservation theorem for
`Path.Homotopy.subpathTransSubpath` described above; it will permit the
segment-local homotopy lift and the crossing refinement square.

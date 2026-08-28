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

`subpathTransSubpath_mem_range` now proves the required structural range
theorem. It unfolds Mathlib's composition of `subpathTransSubpathRefl` and
`transRefl`: the moving-split branch uses the bounds on `Icc.convexCombo`, and
the reparameterized/cast branch is reduced to an actual value of the unsplit
subpath.

`subpathSplitHomotopyInPiece_of_subpath_mem` lifts that homotopy into the cover
subtype from whole-segment membership alone.
`mapPath_subpath_split_of_subpath_mem` gives the localized categorical split
identity. It does not require the ambient path outside `[t₀,t₂]` to lie in
the selected cover member.

No refinement invariance, descent functor, or van Kampen conclusion is
assumed. The next exact seam is to instantiate the localized split identity
at the inserted crossing segment and normalize its side, membership, and
endpoint transports into the crossing refinement square.

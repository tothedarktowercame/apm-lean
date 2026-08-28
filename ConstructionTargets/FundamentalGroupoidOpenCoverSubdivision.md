# FundamentalGroupoidOpenCoverSubdivision

This target supplies the path-generation input for an open-cover
Seifert--van Kampen theorem.  It uses Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval` through the finite `Fin`
wrapper already compiled in `SimplyConnectedOpenCover`.

`PathTwoOpenSubdivision p U V` contains:

* a finite ordered list of interval vertices from `0` to `1`;
* a `Bool` label selecting `U` or `V` for every consecutive segment;
* a certificate that the entire closed segment maps into that selected set.

The associated `piece` is the explicit `Path.subpath` between consecutive
vertices.  `piece_mem` proves its full range lies in the selected cover member.
`concat_piece_homotopic` uses the existing finite `Path.concat` subdivision
homotopy to reconstruct the original path, with endpoint casts explicit.
`quotient_concat_eq` records the resulting equality of fundamental-groupoid
morphisms.  `exists_pathTwoOpenSubdivision` constructs this data for every path
when `U` and `V` are open and cover the ambient space.

No van Kampen statement or pushout conclusion is assumed.  The next exact
seam is independence of subdivision and construction of the descent functor:
given functors from the two piece fundamental groupoids that agree on the
intersection (with object/basepoint transports), send a subdivided path to the
composite of the selected piece morphisms and prove that this is independent
of subdivision and path homotopy.

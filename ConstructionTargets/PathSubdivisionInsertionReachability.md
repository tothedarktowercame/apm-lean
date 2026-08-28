# PathSubdivisionInsertionReachability

This target defines `InsertionReachable S R` as an actual finite sequence of
`SingleVertexInsertion`s.  The constructors retain the full refined
subdivision at each step, so vertex coordinates, membership proofs, and exact
Boolean side labels cannot drift.  `InsertionReachable.evaluate_eq` proves by
induction that every `TwoOpenDescentDatum` evaluates the endpoint subdivisions
equally, using `evaluate_refined_eq` at each step.

`SingleInsertionPresentation S R` is the one-step recognition interface: it
contains an insertion and an equality between its produced refinement and
`R`.  This is intentionally stronger than merely listing compatible vertex
coordinates.

The current `commonSubdivision S T` is not claimed reachable from `S` or
`T`.  There are two concrete reasons.  Its common vertex enumeration removes
duplicates, while insertion can only add a vertex and cannot delete repeated
vertices already in the source.  Moreover, insertion duplicates the exact
Boolean label of the segment it splits, while `commonSubdivision` chooses a
containing left segment independently for every common interval.  A proof of
reachability therefore needs either duplicate-free source data together with
a coherent inherited-label construction, or a separate proof that changing a
label is harmless whenever the common interval lies in the overlap.  Neither
condition is assumed here.

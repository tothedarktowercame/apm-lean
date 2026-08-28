# PathSubdivisionLabelChangeInvariance

This target isolates the label obstruction in common path refinements.
`relabelSubdivision` changes only the Boolean chart labels while retaining the
subdivision number and vertex function definitionally.

`mappedPiece_relabel_eq` applies the existing overlap compatibility when a
label changes, requiring explicit proofs that the affected path lies in both
`U` and `V`.  `evaluate_relabel_eq` lifts these pointwise equalities through
the finite ordered composite.

The theorem does not infer overlap membership from unequal labels.  To compare
the two source-labelled common refinements, the remaining geometric step is to
show that any common segment receiving different inherited labels is contained
in both corresponding original segments, and hence in both cover pieces.

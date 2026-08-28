# PathSubdivisionEvaluationIndependence

This target proves that `TwoOpenDescentDatum.evaluate` is independent of the
chosen `PathTwoOpenSubdivision` of a fixed path.  It compares the left and
right multiplicity-preserving reconstructions, transports their segment index
types using the proved size equalities, and identifies both vertex functions
with the same merged tuple.

When the inherited labels disagree, `InheritedSegmentOrigin.piece_mem_source`
derives membership from each reconstruction's actual source segment and its
interval-containment witness.  Boolean case analysis therefore supplies both
`U` and `V` membership without inferring overlap merely from unequal labels.
The right reconstruction is then an explicit relabeling of the left;
`evaluate_relabel_eq` compares them, and insertion reachability transports the
result back to the original subdivisions.

The next topology step is path-homotopy invariance and descent of this value to
the fundamental-groupoid quotient, followed by construction of the actual
two-open descent functor and its universal property.

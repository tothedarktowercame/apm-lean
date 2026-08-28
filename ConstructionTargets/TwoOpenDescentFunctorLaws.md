# Functor laws for quotient two-open descent

This target constructs a genuine one-segment subordinate subdivision of a
constant path and proves that both its evaluation and `quotientEvaluation` of
the identity path class are categorical identities.

The composition law is not assumed here.  Its exact remaining prerequisite is
a generic concatenation operation on `PathTwoOpenSubdivision`: given
certificates for `p` and `q`, it must construct a certificate for `p.trans q`
whose ordered mapped pieces are the two original lists in traversal order,
and prove the corresponding `composeFin` append formula.  No such operation is
currently banked; constructing it is the next packet before a descent functor
can be defined.

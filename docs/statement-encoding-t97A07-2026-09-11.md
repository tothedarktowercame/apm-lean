# t97A07: a remaining source issue encoded explicitly

[The Lean file](../problems/t97A07/lean/Main.lean) defines critical values using
failure of surjectivity of the actual manifold derivative. It retains the
nonempty, compact, connected, smooth, boundaryless manifold assumptions and
the original nonconstant-map hypothesis for part (b).

The source does not explicitly require positive target dimension. The encoding
therefore states a labelled corrected version: critical values are compact for
all n, nonempty for n>0, empty for n=0, and infinite if n>1 and f is nonconstant.
The source file has not been changed. Acceptance of positive dimension as the
intended source convention remains a review question, not an implicit edit.

Two accompanying lemmas prove that the critical-value set of every map into
R⁰ is empty and hence not nonempty. These proofs contain no `sorry`, and their
axiom reports contain only standard Lean axioms. The final problem theorem
has one deliberate `sorry`; its compactness, positive-dimensional nonemptiness
and infinitude claims are not proved here.

Construction/proof targets are now concrete: closedness of the locus where the
derivative is nonsurjective; compactness of its image; the open-image obstruction
for submersions from compact manifolds to positive-dimensional Euclidean space;
and the connectedness argument for infinitude in dimension greater than one.
No Sard theorem, arbitrary critical-value set or desired conclusion is assumed.

This is evidence that a source convention need not leave the entire problem
without Lean material. It is not evidence that missing conclusions or diagrams
can be reconstructed without their sources. Independent review remains pending.

The source-stem material census is now 478/491, with 13 without Lean material.
That material count explicitly includes this corrected, unproved statement;
it is not a count of 478 verified faithful source encodings or solved problems.

Validation: `lake env lean -DautoImplicit=false problems/t97A07/lean/Main.lean`
and `python3 -u scripts/check_statement_quality.py t97A07`. Exact final outputs
are recorded in the companion validation JSON. No construction-library root
or global gate was changed in this unit of work.

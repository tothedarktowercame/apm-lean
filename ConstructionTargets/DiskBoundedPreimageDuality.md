# Disk-bounded preimage duality

`DiskBoundedPreimageDuality.lean` packages the complete reusable homological
part of a transverse embedded-circle preimage argument.

The first theorem converts disk-bounded inverse-image components into
`HasNullWindingPreimage` for positive-degree singular homology.  It combines
the disk boundary calculation with cancellation along a homologically
essential embedded circle.  The second theorem immediately feeds that result
to `DetectsTopMap`, so a manifold-specific consumer need only construct the
geometric duality principle.

For `t00J02`, take degree-one integral singular homology for the circle functor
and degree-two integral singular homology for the top functor.  The remaining
problem obligation is precisely the construction of `DetectsTopMap` from the
smoothness and transversality hypotheses; no disk-component or categorical
cancellation bookkeeping remains in the problem file.

## Axiom audit

Both exported theorems are sorry-free.  Direct standalone elaboration reports
exactly `[propext, Classical.choice, Quot.sound]` for each.  The unfinished
consumer theorem still has its separately audited geometric `sorry`; that hole
is not part of this library module or its axiom set.

# Genuine smooth manifold source, vector target Sard

Extract the exact `T93A04ManifoldWork.null_critical` producer from reviewed
consumer commit a49c84764968d8286ff05d87e5d218018505f50c. Preserve its name
and proof; replace the embedded producer in t93A04 Main with an import of
ConstructionTargets.SardGenuineSmoothManifoldVector. This is extraction of
an existing theorem, not an additional mathematical advance or new closure.

For a second-countable genuine-infinity manifold modeled on a complete
finite-dimensional real inner-product space, the theorem proves nullity of
the actual nonsurjective-mfderiv critical image in the supplied Borel Haar
measure on a finite-dimensional inner-product target. No Hausdorff source
hypothesis is needed; the requested Hausdorff case is included. No nonempty
or nontrivial source or target hypothesis is imposed.

At each critical point use chartAt and its actual open target. The manifold
smooth inverse chart and the global ContMDiff map give ContDiffOn infinity
of their composition. Apply unconditional Euclidean open-domain Sard.
The mfderiv chain rule shows that surjectivity of the chart representative's
derivative would force surjectivity of the original derivative. Chart
inverse identities give the required image inclusion, in the original target
measure. Existing pointwise-open aggregation derives countable coverage from
second countability; no coverage or local nullity assumption remains.

The companion /tmp/T93A04ManifoldReuse.lean is the full closed consumer using
the extracted module. Preserve every existing consumer declaration and its
statement. Consumer placeholders remain zero. Standard axioms only; the
consumer retains its inherited unnecessarySimpa warning.

Next edge: general target-manifold chartwise critical-value transport, or
regular-value/transversality uptake in t01A08, t01J04, t92J07 and t96J05.
No general target-manifold measure theorem is claimed. t93A04 is already
reviewed closed and this extraction must not count it as a second closure.

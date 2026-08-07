# Proof Outline: m98A04

The concrete periodic convolution identity is compiled.  Closer hop 1 also
constructs the translated reflection `y ↦ φ (x-y)` as a genuine bundled test
function.  Compact support is transported through `Homeomorph.subLeft x`, and
the resulting canonical pairing with a distribution satisfies the custom
`IsConvolution` predicate.

Closer hop 2 also bundles every iterated coordinate derivative of a test
function using `TestFunction.fderivCLM` and `postcompCLM`, with a compiled
pointwise equality to the statement's custom `partialList` recursion.

The remaining analytic bridge is to prove that the parameterized translated
test function is smooth into Mathlib's LF test-function topology.  That yields
smoothness after composition with the distribution.  The resulting identities
must then be combined with the now-bundled iterated test derivatives and a
bundled iterated distributional derivative.

# Proof Outline: m98A04

The concrete periodic convolution identity is compiled.  Closer hop 1 also
constructs the translated reflection `y ↦ φ (x-y)` as a genuine bundled test
function.  Compact support is transported through `Homeomorph.subLeft x`, and
the resulting canonical pairing with a distribution satisfies the custom
`IsConvolution` predicate.

The remaining analytic bridge is to prove that the parameterized translated
test function is smooth into Mathlib's LF test-function topology.  That yields
smoothness after composition with the distribution and permits induction with
`TestFunction.fderivCLM` for the derivative identities.

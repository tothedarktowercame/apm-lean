# Target-equivalence critical-image equality

`criticalImage_eq_of_target_continuousLinearEquiv` identifies the localized
ambient derivative-critical images under a continuous linear target change.
The source and both targets are arbitrary real normed spaces. The source set
`s` is arbitrary, and `f` is differentiable at every point of `s`.

## Representation and direction

Source representation: `e '' (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)}))`.

Target representation: `(e ∘ f) '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ (e ∘ f) x)})`.

The theorem states exact equality from the target composite critical-image
representation to the source equivalence-image representation, both subsets
of `H`. It does not equate subsets of different target types directly.

## Proof and dependencies

The chain rule identifies the composite derivative with `e` composed with
the derivative of `f`. Invertibility of `e` gives surjectivity equivalence;
the two image inclusions then use the same source points.

The observed import is `ConstructionTargets.SardSourceEquivCriticalImage`.
No invocation of its source-equivalence theorem is needed: this proof uses
the imported Mathlib derivative and continuous-linear-equivalence interfaces
directly, including `HasFDerivAt.comp` and `ContinuousLinearEquiv.hasFDerivAt`.

## Evidence and residual

The Lean file is byte-identical to the compiled acceptance fixture
`/tmp/SardTargetEquivCriticalImageProbe.lean`, SHA-256
`9c98bd45342769a7962dc0642fcbd1983ee4d2c339f814c7189489c4d5085c53`.
Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
There are no measure, finite-dimensionality, or measurability assumptions.

Intended consumers are `t93A04`, `t01A08`, `t01J04`, `t92J07`, and `t96J05`;
no frozen consumer is closed by this increment. Next combine this equality
with target nullity transport and model construction. Borel-compatible
dimension induction, complementary analytic ranges, and remaining regularity
cases are still open. The frozen `t93A04` theorem and its one placeholder
remain unchanged.

Stop only if the chain rule and invertible target derivative fail to preserve
criticality in both directions, the localized image equality fails under the
stated hypotheses, or nonstandard axioms are required.

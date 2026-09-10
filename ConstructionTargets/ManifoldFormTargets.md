# ManifoldFormTargets

Smooth differential forms on boundaryless manifolds are tangent alternating covectors. `inChart` pulls each covector through the derivative of the chart inverse; `IsSmooth` tests every chart. `pullback` uses the actual manifold derivative. `exteriorDerivative` computes Mathlib's Euclidean exterior derivative in the chosen chart and transports it back. A smooth nowhere-zero top form supplies its induced orientation.

Construction targets: prove independence from the chosen chart on smooth manifolds; equivalence of this smoothness condition with smooth sections of the exterior cotangent bundle; pullback composition and smoothness; naturality of exterior differentiation and d²=0. For t97A06, extension by partitions of unity and the closed-form obstruction remain open. No operator or theorem is postulated as an axiom.

Consumers: t97A06, t98J06, t93A06 and ManifoldIntersectionTargets. Models are finite-dimensional in these consumers. This module does not provide arbitrary manifold integration or manifolds with boundary.

The module builds as a named Lake target and is imported by ConstructionTargets.lean. Its definitions contain no `sorry`; consumer theorems remain explicitly unproved. Independent mathematical review is pending.

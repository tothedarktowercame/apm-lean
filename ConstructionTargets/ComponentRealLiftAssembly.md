# Component real lift assembly

This module assembles supplied continuous real lifts on connected components
into a continuous lift on the whole space, then constructs its Circle
null-homotopy. It also proves naturality for the actual component inclusion
on fundamental groups. It does not yet apply the finite-H1 diagnostic to
construct the component lifts required by t97A02.

For a locally connected space `X`, `componentFiber c` is the fiber of
`X → ConnectedComponents X` over `c`. The component quotient is discrete,
so its fibers are open. The canonical sigma-fiber equivalence is continuous
and open, giving the actual homeomorphism
`componentDecomposition : (Σ c, componentFiber c) ≃ₜ X`.

Given continuous maps `F c : C(componentFiber c, ℝ)`, `assembledLift F`
is the continuous sigma evaluation map composed with the inverse of this
homeomorphism. Its pointwise formula is

```lean
assembledLift F x = F (x : ConnectedComponents X) ⟨x, rfl⟩
```

Consequently, componentwise equations `Circle.exp (F c y) = f y.val`
give `Circle.exp (assembledLift F x) = f x` everywhere. The theorem
`exists_global_lift` chooses component lifts from their existence hypotheses.
`nullhomotopic_of_component_lifts` contracts the assembled lift by the
explicit homotopy

```text
(t, x) ↦ Circle.exp ((1 - t) * assembledLift F x).
```

Its endpoints are `f` and the constant map with value `1`. No nonempty-domain
hypothesis enters this construction. `empty_domain_lift` additionally checks
the empty case explicitly, using the constant zero real map.

`component_loop_naturality` proves that the fundamental-group map of
`f.comp (componentInclusion c)` equals the composite of the actual induced
maps. Thus ambient loop triviality implies component loop triviality in
`component_loop_trivial`. These theorems neither assume nor establish
finiteness of the fundamental group.

`componentFiber_eq` identifies a fiber over the class of `x` with
`connectedComponent x`. The banked classical local-contractibility
conversion then supplies path connectivity of these fibers.
`classical_component_lifts_nullhomotopic` uses that same conversion to
obtain local connectivity and apply the assembly theorem. Path connectivity
of the whole space is not required.

The next consumer step must construct the supplied lifts by combining the
finite-H1 diagnostic, component normalization, inclusion naturality, and
the covering-lift theorem. Only after that application compiles can this
assembly establish the frozen t97A02 conclusion. This module alone makes
no frozen consumer closure claim.

The Lean source is an unchanged promotion of
`/tmp/ComponentRealLiftAssemblyProbe.lean`, SHA-256
`c79a403303887e39689f2a787d278f478c93165772721545a4cc199fd9d6633d`.
The classical local-connectivity dependency was independently reviewed PASS
at commit `f8d3d38156369e16f70d38f9991ffaf88b957263`.
The source retains all nine printed axiom audits. Validation compiles both
the fixture and canonical source and builds this module with
`ClassicalLocalPathConnectivity` and `CircleUniversalCover`; the permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

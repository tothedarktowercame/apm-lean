# Classical local contractibility and component lifting

This target derives local path connectivity from classical local
contractibility, establishes the covering-lift domain hypotheses for each
connected component, and constructs a normalized real lift of a Circle map
on a component when its actual induced loop map is trivial.

## Classical hypothesis and paths

`locPathConnected_of_classical` accepts `hX : LocallyContractibleSpace X`,
the same classical hypothesis used by frozen `t97A02`. It does not replace
that hypothesis by a basis of contractible neighborhoods.

For a point `x` in an open set `U`, classical local contractibility supplies
a smaller neighborhood `V` whose inclusion into `U` is null-homotopic.
Evaluating that homotopy at `x` and any `y ∈ V` gives paths from their images
to the same constant point in `U`. Concatenating the first with the reverse
of the second joins `x` to `y` inside `U`. Thus `V` lies in the path component
of `x` within `U`, proving that this path component is a neighborhood and
establishing local path connectivity.

`component_locPathConnected` uses openness of connected components in a
locally path-connected space to give the component subtype the same local
property. `component_pathConnected` combines it with connectedness of the
component subtype to obtain path connectivity. Neither theorem assumes that
the whole space is path connected.

## Conditional component lift

`componentMap f x` is the actual restriction of `f : C(X, Circle)` to
`connectedComponent x`, composed with subtype inclusion.
`component_real_lift` assumes `f x = 1` and that every based fundamental-group
element of this component maps to the identity under
`FundamentalGroup.map (componentMap f x)`.

With the proved local path connectivity and path connectivity, it applies
the actual exponential covering's range criterion. Triviality of the loop
map supplies the required subgroup inclusion. The result is

```text
∃ F : C(connectedComponent x, ℝ),
  F ⟨x, mem_connectedComponent⟩ = 0 ∧
  ∀ y : connectedComponent x, Circle.exp (F y) = f y.val.
```

The loop-triviality condition remains an explicit premise. It is not derived
from finite ambient homology in this packet.

## Evidence and next consumer steps

The Lean file is a byte-for-byte promotion of
`/tmp/ClassicalLocalPathConnectivityProbe.lean`, SHA-256
`16a99e9bcff7464eb85dfca8eb59a05ca592b0710c18ebcc1694791c1e10b89e`.
All four retained axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`. The row has no ledger dependencies and uses the banked
`CircleUniversalCover` API.

The observed consumer is the conditional component-lift theorem. Its named
consumer is `t97A02-component-lifting`; other intended uses are
`circle-valued-map-lifting` and `covering-lift-component-assembly`.
No frozen problem is edited and the placeholder delta is zero.

Next prove component-inclusion naturality to obtain the component loop
premise from the ambient homological result. Then assemble component lifts
into a continuous global lift, including the empty-domain case, and construct
its explicit null-homotopy. This packet claims neither global component
assembly nor full `t97A02` closure.

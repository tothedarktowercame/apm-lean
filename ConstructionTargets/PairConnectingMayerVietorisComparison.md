# Pair connecting map versus Mayer–Vietoris

This target compares two chain-level presentations attached to simplicial
subcomplexes `P` and `Q`:

* the signed Mayer–Vietoris short exact sequence for `P ∩ Q`, `P ⊕ Q`,
  and `P ∪ Q`;
* the cokernel short exact sequence for `P ∩ Q → Q`.

`unionToRightRelative` is defined by the actual pushout universal property. It
kills the `P` summand and restricts to the cokernel projection on `Q`.
`mayerVietorisToRightRelative` is therefore a morphism of short complexes; its
first component is `-𝟙`, which is the source of the sign. The two connecting
map theorems are consequences of Mathlib's connecting-map naturality, not
assumptions.

The resulting theorem says that the union-to-relative projection followed by
the relative connecting map is the negative of the Mayer–Vietoris connecting
map. The remaining topological seam is representation transport: identify
this SSet-chain cokernel connecting map with `singularPairConnecting` for the
topological pair, and then compose it with the already compiled excision map.
That comparison involves the singular-complex/subspace chain isomorphisms and
is not asserted here. No sphere antipodal recurrence or frozen `t94J08`
conclusion follows from this file; the frozen statement is also false at
dimension zero.

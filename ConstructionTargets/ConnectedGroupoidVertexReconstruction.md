# Connected groupoid vertex reconstruction

`ConnectorSystem` records a base object and a chosen isomorphism from that
base to every object.  For `f : X ⟶ Y`, `normalForm f` is the explicit
vertex-group element

```text
connector(X).hom ≫ f ≫ connector(Y).inv.
```

The target proves normalization of identities and composites, reconstruction
of `f` from its normal form, and injectivity on every hom-set.  The shared
connector in the composition proof is cancelled explicitly.

`constantObjectFunctor` extends a monoid homomorphism from the chosen vertex
group to the automorphism group of an object in another groupoid.  It is
constant on objects and maps arrows through `normalForm`.

No connectedness instance is inferred and no connectors are chosen from mere
existence: callers must supply the connector system.  No pushout or
twice-spiral fundamental-group identification is asserted.  The next needed
layer is a connector-compatible comparison between pseudococones of groupoids
and cocones of their chosen vertex groups.

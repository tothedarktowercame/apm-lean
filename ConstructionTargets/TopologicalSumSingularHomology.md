# Singular homology of a topological sum

For arbitrary spaces `X` and `Y`, this target uses the ranges of `Sum.inl`
and `Sum.inr` as a clopen two-set cover of `X ⊕ Y`.  It gives explicit
homeomorphisms of the two piece subtypes with `X` and `Y`, and an explicit
homeomorphism of their intersection with `Empty`.

The banked empty-space homology theorem makes the intersection homology zero
in every degree. Production Mayer–Vietoris exactness therefore makes the
actual reassembly morphism an isomorphism: exactness at the pieces gives
monicity, while degree-zero reassembly epicity or exactness at the union gives
epicity. Transport through the piece homeomorphisms yields

```
H_k(X ⊕ Y; ℤ) ≅ H_k(X; ℤ) ⨞ H_k(Y; ℤ).
```

The isomorphism is constructed from the actual production inclusion-induced
reassembly arrow; no splitting or Künneth theorem is assumed.  Its two
components are normalized against the actual homology maps of `Sum.inl` and
`Sum.inr`: postcomposition with `sumHomologyIsoBiprod.hom` gives the categorical
`biprod.inl` and `biprod.inr`.  Equivalently, those homology maps are the two
injections followed by `sumHomologyIsoBiprod.inv`, and that inverse is exactly
their `biprod.desc`.

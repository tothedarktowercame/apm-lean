# Higher-dimensional punctured-disk local homology

For every `k : ℕ`, this target computes integral relative homology in degree
`k+2` of the open `(k+2)`-disk modulo its deleted origin. Thus it covers every
dimension at least two. It constructs an integer isomorphism, its normalized
generator, and the generator's boundary under actual radial normalization.

## Representation and forward maps

The source is
`(RelativeSingularChains (puncturedOpenDiskSet (k+2))).homology (k+2)`.
Coefficients are integers in production `AddCommGrpCat` singular chains.
The intermediate target is integral `H(k+1)` of the unit `(k+1)`-sphere;
the final target is `AddCommGrpCat.of ℤ`.

`connectingIso` uses contractibility of the open disk and vanishing of its
absolute homology in both degrees `k+2` and `k+1`. Production pair exactness
therefore makes the actual connecting map an isomorphism from relative
`H(k+2)` to puncture `H(k+1)`.

`radialIso` is the inverse of the homology isomorphism induced by the banked
sphere-to-punctured-open-disk homotopy equivalence. Its forward map is induced
by `radialNormalizeMap`, from the puncture to the sphere.

`localIsoInt` composes these with `sphereTopHomologyIsoInt (k+1)`.
`comparison` proves the exact forward-map equation: its homomorphism is the
actual pair connecting map, followed by the induced radial-normalization map,
followed by the banked sphere normalization. The construction uses these
geometric maps rather than an unrelated abstract group isomorphism.

## Generator and concrete equations

`generator k` is `(localIsoInt k).inv 1`. `normalization` proves that it maps
to `1`, and `generates` proves every relative class is an integer multiple
of it. `boundary_radial_generator` identifies the geometric boundary image:

```text
radialNormalizeMap_*(singularPairConnecting (generator k))
  = (sphereTopHomologyIsoInt (k+1)).inv 1.
```

The proof applies the sphere normalization inverse to the generator's
normalization equation after rewriting by the exact composite comparison.
`dimension_two_generates` specializes to `k=0`, and
`dimension_four_generates` specializes to `k=2`.

## Evidence and boundary

The Lean file is a byte-for-byte promotion of
`/tmp/HigherModelLocalHomologyProbe.lean`, SHA-256
`b1ff5b97ed848a02ca923f385c8d4be2b4a39197567c0eddbb6c83b650ffd65b`.
All nine retained axiom audits permit only `propext`, `Classical.choice`, and
`Quot.sound`. The portfolio checkpoint was independently reviewed PASS by
`codex-11` in `invoke-1788974101248-16672-6375d624`.

Observed consumers are the boundary/radial generator equation and the
dimension-two and dimension-four generation instances. The named consumer
is `euclidean-higher-model-local-homology`, with proposed downstream uses in
`t98A02`, `t01A02`, and `t01A05`. No frozen problem is changed and the
placeholder delta is zero.

This is a model calculation only. Higher-dimensional coordinate-change
signs, geometric orientation compatibility, manifold chart transport, global
localization, and `t98A02` gluing remain separate obligations. No
arbitrary-manifold fundamental class, localization monicity, or frozen
consumer closure is claimed.

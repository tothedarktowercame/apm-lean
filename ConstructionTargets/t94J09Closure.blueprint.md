# t94J09 closure blueprint

## Verdict and frozen target

The registered statement is true.  Its fourteen-edge word has two vertex
classes, seven edge classes, and one face, hence Euler characteristic `-4`.
The two positive occurrences of `a` make the surface nonorientable, so the
normal form is the nonorientable genus-six surface `N6`.  The old harvested
`N3` claim is inconsistent with the stipulated vertex count and is not used.

The implementation must preserve the definitions and theorem statement in
`problems/t94J09/lean/Main.lean`.  The executable specification is
`holes/labs/blueprints/t94J09/Blueprint.lean`; its five finite certificates
and final conjunction assembly already compile.  Only the two declarations
marked `LIBRARY` there may require new mathematics.

## B1: finite certificates

Copy the following proved declarations from the executable blueprint into the
consumer when assembling the final result:

* `apm_t94J09_vertexCount_eq`
* `apm_t94J09_edgeCount_eq`
* `apm_t94J09_eulerCharacteristic_eq`
* `apm_t94J09_not_oppositeOrientationPairing`
* `apm_t94J09_nonorientableGenus_eq`

They are closed computations over the frozen word and vertex-class function.
They must not be replaced by assumptions or changes to those definitions.

## B2: polygon normalization

Prove the literal interface

```lean
theorem apm_t94J09_polygon_normalization :
    Nonempty (apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6)
```

by normalizing the concrete fourteen-edge polygon to the standard twelve-edge
presentation of `N6`.  The intended route is a finite chain of polygon
cut-and-paste moves, each realized as a homeomorphism of quotient spaces, then
composition.  A single disk self-map is not assumed: cutting and regluing can
change the polygon presentation in a way not induced by one self-map.

Reusable inputs include the quotient universal properties in the consumer and
the signed-polygon, boundary, and radial machinery in
`ConstructionTargets.PolygonSurfacePiOne`.  Any new general lemma must be no
more general than the concrete normalization requires and remain in the row's
scope.

Milestone:

```text
apm_t94J09_polygon_normalization
area: polygon-cut-and-paste
depends-on: none
```

## B3: polygon homology

Prove the literal interface

```lean
theorem apm_t94J09_polygon_homology :
    Nonempty (apm_t94J09_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t94J09_H 1 ≅
      ModuleCat.of ℤ ((Fin 5 → ℤ) × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t94J09_H k))
```

Use the reviewed polygon-surface homology foundation.  Specialize its pairing
data to the frozen fourteen-edge word and identify its orbit-coordinate
boundary map.  The cellular data are two vertices, seven edges, and one face;
Smith reduction gives free rank five and one `ZMod 2` summand in degree one.
The top boundary is injective, so degree two vanishes, and the foundation's
high-degree result supplies every `k ≥ 3`.

The adapter must transport the foundation's quotient and module
representations to the exact frozen types.  It must not infer the homology
from B2 unless all required homeomorphism-induced maps and the homology of the
literal `N6` model are already available.

Milestone:

```text
apm_t94J09_polygon_homology
area: polygon-surface-homology
depends-on: polygonQuotient_homology
```

B2 and B3 are independent and may be developed separately.

## B4: final assembly

After B2 and B3 compile, copy the blueprint's conjunction proof verbatim:

```lean
exact ⟨apm_t94J09_vertexCount_eq, apm_t94J09_edgeCount_eq,
  apm_t94J09_eulerCharacteristic_eq,
  apm_t94J09_not_oppositeOrientationPairing,
  apm_t94J09_nonorientableGenus_eq,
  apm_t94J09_polygon_normalization, apm_t94J09_polygon_homology⟩
```

Completion requires a placeholder-free `Main.lean`, unchanged registered
statement fingerprints, and only `propext`, `Classical.choice`, and
`Quot.sound` among axioms.

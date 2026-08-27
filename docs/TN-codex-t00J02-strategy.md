# t00J02 strategy after the method surveys

Date: 2026-08-27

This note records the result of four bounded surveys of possible methods for
`t00J02`.  It is intentionally a strategy note, not a claim that the remaining
bridge has been proved.

## Summary

The current explicit geometric-chain route should not be continued as a
bounded attempt to close `t00J02`.  It does not eliminate the missing
differential-topological and homological theory; instead, it expresses that
theory as a long collection of triangulation, incidence, orientation, and
fundamental-cycle compatibility proofs.

The most promising reusable program is:

1. extract and review the experimental low-degree integral cap construction;
2. develop oriented-manifold fundamental classes and their localization;
3. separately develop boundaryless finite-dimensional regular-preimage
   geometry;
4. add Thom/Poincare-duality comparison only after those foundations exist;
5. then reconsider `t00J02`, preferring the local-homology route if
   point-avoidance surgery is available.

## Survey outcomes

| Method | Classification | Main missing work |
|---|---|---|
| General transversality | C: foundational stop | Manifold regular-preimage/transverse-pullback construction, tangent identification, compactness, and orientations |
| Poincare-duality comparison | B: useful algebra, premature comparison theorem | Singular cochains and general cap products, manifold fundamental classes, Thom classes, and geometric naturality |
| Local homology | B: viable alternative | Point-avoidance surgery and localization of the oriented fundamental class |
| Explicit geometric chains | B: substantial infrastructure, poor closure route | Oriented vertex-link topology, incidence assembly, coefficient transport, survivor comparison, and global fundamental-cycle identification |

### Transversality substrate

Mathlib has finite-dimensional calculus, implicit-function machinery, smooth
bump functions, partitions of unity, and an immersion API.  It does not have a
generic manifold regular-value theorem, submersion construction,
transverse-preimage manifold, tubular-neighborhood theory, or relative and
parametric transversality theorem.

The existing project results are honest linear and consumer-side adapters:

- `TransverseLinearPair.IsTransversePair`;
- `isTransversePair_iff_surjective_coprod`;
- `TransversePreimageGeometry.holdsAlong_surjective_coprod_of_range_sup_eq_top`;
- `TransversePreimageGeometry.surjective_coprod_of_range_sup_eq_top`.

They turn the frozen range-sum condition into a surjectivity statement.  They
do not construct the inverse-image manifold, its orientation, or its
fundamental class.

The smallest useful foundational theorem is a boundaryless,
finite-dimensional transverse-pullback or regular-preimage construction with
tangent-space identification.  This would also serve `t93A04`, `t94J05`,
`t94A06`, `t96J05`, `t02A07`, `t92J07`, and `t95J04`.

### Intersection and Poincare-duality comparison

The repository already has reusable singular-homology components:

- coefficient-category comparison;
- relative singular chains and pair exact sequences;
- relative maps and their naturality;
- excision;
- concrete circle and sphere homology;
- disk-boundary nullhomology;
- component-lift and disk-bounded cancellation consumers.

Canonical Mathlib and canonical project master do not yet contain the general
cohomology, cap-product, manifold fundamental-class, or Thom-class theory
needed for the comparison

```text
i_* [f^{-1}(Z)] = [M] cap f^*(PD_N(j_*[Z])).
```

The predicates in `TransversePreimageDuality` and
`OrientedSurfacePreimageDuality` specify consequences of this missing theorem;
they do not construct it.

### Local-homology route

There is a clean alternative argument.  If `f` is homotopic to a map `g` that
avoids a point `q`, and

```text
H_n(M) -> H_n(M, M \ {q})
```

is injective, then naturality makes the localized map induced by `g` zero, so
the global top-homology map is zero as well.

The project already contains much of the relative-chain and excision algebra
needed to state this argument.  Two independent geometric producers remain:

1. point-avoidance surgery from the relevant inverse-image hypotheses;
2. localization of the global oriented fundamental class, or at least
   monicity of the top-homology-to-local-homology map.

This localization layer would also serve `t00A01`, `t98A02`, `t00A04`, and
`t01A05`, with related uses in `t03J05` and `t96J06`.

### Geometric-chain route

Canonical master already contains a mature reusable subdivision and excision
trunk in `ConstructionTargets/SingularSubdivision.lean`, including affine and
vertex subdivision, boundary compatibility, prism identities, iteration,
naturality, diameter control, and small-chain comparison.  It is already used
by `SingularExcision`, `T02A06HomologyScaffold`, `T02A06DiskPairShift`, and
`SphereOneH1Concrete`.

The experimental solver branch
`qualification/library-loop-t00J02-solver` at `03df9978` additionally contains
a coherent low-degree integral cap construction embedded in
`SingularSubdivision.lean`:

- `SingularOneCocycle` and pullback;
- `singularCapOneOne`, `singularCapOneTwo`, and `singularCapOneThree`;
- chain identities and cycle preservation;
- `capCycles` and `capHomologyOneTwo`;
- homology projection and Alexander-Whitney edge naturality results.

This material is the best bounded extraction candidate.  It should be moved
into a dedicated generic module and reviewed independently; the entire solver
branch or its expanded `SingularSubdivision.lean` should not be merged as a
unit.

By contrast, structures such as `ChartwiseCapAssignment`,
`InteriorBackEdgePairing`, `FiniteSharedFaceData`,
`RegularFiberFanRealization`, `OrientedFaceOccurrenceLedger`, and the survivor
component records already contain much of the missing geometry.  Their
consumer theorems are valid conditional results, but they are not producers
derived from the frozen hypotheses.

The genus-two polygon sectors, tagged triangle systems, annular
retriangulations, radial cycles, and explicit quotient-boundary enumerations
are useful for validating one chosen representative.  They should not be
treated as generic transverse-preimage or fundamental-class theory.

## Recommended library program

### 1. Extract the low-degree cap module

Create a standalone generic module containing only the cocycle definition,
pullback, the dimension-one through dimension-three cap operations, chain
identities, and homology descent.  Give it independent consumers and an axiom
audit before considering any t00J02 integration.

### 2. Build fundamental classes and localization

Develop oriented-manifold fundamental classes, local homology at a point, and
the theorem identifying the localized global class with the local orientation
generator.  This is the most widely shared missing homological layer found by
the survey.

### 3. Build regular-preimage geometry separately

Start with boundaryless finite-dimensional manifolds and regular values or
submersions.  Establish the inverse-image manifold and tangent kernel before
attempting general transverse fibre products, relative perturbation, or
parametric transversality.

### 4. Add geometric comparison later

Only after fundamental classes, cap operations, and regular-preimage
orientations exist should the project attempt the generic transverse-preimage
fundamental-class formula or a Thom-class formulation.

### 5. Revisit t00J02 at a clear interface

Prefer the local-homology proof if point-avoidance surgery and localization
are then available.  Otherwise use the direct transverse-preimage comparison
once its generic theorem exists.  Do not resume the representation-specific
geometric-chain loop merely to replace one missing interface with further
conditional incidence structures.

## Banking policy

No new theorem was banked as a result of these read-only surveys.  Any cap
extraction must be reviewed and committed into canonical
`/home/joe/code/apm-lean` as an independently compiled reusable module, rather
than being retained only on the experimental solver branch.

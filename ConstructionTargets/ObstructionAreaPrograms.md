# Obstruction areas to construction programs

This map turns the structured obstruction-area census into candidate library
programs and representative APM problems.  It complements the detailed
checklists in `SingularHomologyConcrete.md` and
`FundamentalGroupConcrete.md`.

The census includes only unresolved structured records whose `areas_are` value
is `necessary`.  Counts describe recorded blockers at the 2026-08-24 master
snapshot.  They do not estimate cost, and a problem can occur in several rows
because its proof can require several jointly necessary layers.

## Program map

| Recorded area | Problems | Construction program | Representative problem |
|---|---:|---|---|
| singular homology | 23 | Relative chains, excision, Mayer--Vietoris, concrete circle/sphere/torus computations, cellular comparison, Künneth | `t02A06` for the proven trunk; `t96J06` for the product frontier |
| fundamental group | 14 | Circle computation, based products, van Kampen, presentations, surface groups, cover/subgroup bridge | `t91A05`, then `t93A03`, `t03J02`, and `t03J03` |
| covering space | 13 | Concrete cover construction, lifting and deck transformations, subgroup/monodromy classification, finite surface covers | `t00A02`, `t03J03`, `t98A03`, `t94J04` |
| orientation | 9 | Homological orientations and degree, orientation covers/characters, manifold and surface orientation transport | `t02A08`, `t94J08`, `t03J03`, `t99J03` |
| transversality | 7 | Regular values, manifold Sard, parametric transversality, transverse-preimage geometry and duality | `t02A07`, `t94A06`, `t00J02` |
| differential forms | 6 | Bundled forms/extDeriv, parameter integration and homotopy, weak derivatives, compact-support primitives, surface integration | `t96J08`, `t94J07`, `m02J01`, `t03J06` |
| van Kampen | 5 | A subprogram of the fundamental-group trunk | `t93A03` for the open/wedge gate; `t03J02` for closed gluing |
| Mayer--Vietoris | 5 | A subprogram of the singular-homology trunk | `t96A03`, followed by `t98A02` |
| cellular homology | 3 | Finite CW chains and cellular-to-singular comparison | `t96A03`, followed by `t97A01` |
| intersection theory | 2 | Mod-two fundamental classes, intersection pairing, self-intersection, geometric/dual comparison | `t03J05`, then `t96J06` |
| Stokes | 2 | A subprogram of differential forms and oriented integration | `t94A10`, then `t03J06` |
| cohomology | 2 | Circle representability of integral `H¹`, primitive classes, relative adjustment | `t97A02`, then `t03J01` |
| complex analysis | 2 | Rouché/argument-principle zero counting and disk automorphism rigidity | `a92J05` for Rouché; `a94A09` for integration |
| measure/integral | 2 | Endpoint-singular FTC and variation/absolute-continuity approximation | `a02J07` and `a93A04` |
| Künneth | 1 | A subprogram of singular homology: chain cross product, Eilenberg--Zilber, integral Tor sequence | `t96J06` |
| Fourier analysis | 1 | `L¹` convolution theorem, derivative rule, concrete transform pair, injectivity | `a01A03` |
| excision | 1 | Already the central trunk of the singular-homology program | `t98A02` as the remaining connected-sum gate |
| degree theory | 1 | Integer degree of circle maps and homotopy classification | `t91A08` |

## Covering-space program

The thirteen covering-space records split into four materially different
construction layers.

### Concrete covers and local charts

- Construct quotient and product covers with explicit local trivializations.
- Compute fibers and sheet numbers without relying only on an opaque
  `IsCoveringMap` witness.
- Package products, compositions, and pullbacks of finite covers.
- Expose deck transformations and their action on fibers.

Representatives:

- `t00A02` is the smallest local-chart gate: its antipodal quotient and exact
  two-point fibers already compile, leaving the covering charts.
- `t01A02` exercises a product cover, deck group, and a downstream lifting
  consequence.
- `t98A01` exercises a circle cover already proved locally and asks for the
  product-torus package.

### Lifting, subgroups, and characters

- State the based lifting criterion in terms of induced-map range.
- Relate connected covers to conjugacy classes of subgroups.
- Classify double covers by characters to `ZMod 2`.
- Connect orientation characters to the orientable double cover.

Representatives:

- `t03J03` is the best double-cover/character gate.
- `t01A04` checks that the exact parity kernels equal induced ranges, rather
  than merely producing abstract covers.
- `t97A03` tests transport from the classification to concrete total-space
  invariants.

### Finite monodromy

- Package a finite cover's monodromy action.
- Relate connectedness to transitivity and regularity to the action/kernel.
- Construct covers back from transitive finite actions.

Representative: `t98A03`, which distinguishes regular and nonregular
three-sheet covers of a wedge.

### Surface-cover classification

- Construct polygonal surface covers and verify their covering charts.
- Prove Euler-characteristic multiplicativity under finite covers.
- Combine orientability parity and surface classification to identify total
  spaces and genera.
- Realize finite-index surface subgroups geometrically.

Representatives:

- `t97J02` for explicit five- and six-sheet polygon covers.
- `t94J04` for the subgroup-to-cover and genus theorem.
- `t95J06` for a principal circle action and quotient classification.

## Orientation program

The orientation label currently conflates three layers which should remain
separate in implementation and promotion tests.

### Homological orientations and degree

- Compute top singular homology of the concrete sphere models.
- Package a generator as an integral orientation.
- Define induced degree and prove identity, composition, and homotopy laws.
- Compute antipodal degree and construct sphere maps of arbitrary integer
  degree.

Representatives:

- `t02A08` is the integer-degree construction gate.
- `t94J08` is the sphere orientation and antipodal-action gate.

This layer depends on `SingularHomologyConcrete.md`; it is not an independent
replacement for the sphere-homology work there.

### Orientation characters and covers

- Define the orientation character with usable functoriality.
- Identify its kernel with the orientable double cover.
- Transport orientation through covering maps and cylinders.

Representative: `t03J03`.

### Manifold and surface orientation transport

- Orient boundaries, punctures, products, and connected sums.
- Relate polygon normal forms to orientability.
- Make Euler characteristic compatible with the homeomorphisms used in
  surface classification.

Representatives:

- `t98A02` for connected-sum/boundary orientation interfaces.
- `t99J03` for orientable and nonorientable polygon normal forms.
- `t97J02` for orientation parity in finite surface covers.

## Transversality program

### Regular values and manifold Sard

- Prove Sard for finite-dimensional second-countable manifolds in the exact
  smoothness vocabulary used by the corpus.
- Turn a regular value into the required subtype manifold instance.
- Package regular-level compactness and dimension calculations.

Representatives:

- `t93A04` is the smallest nonempty-domain Sard gate.
- `t96J05` adds globalization of radial regular levels.
- `t94J05` checks that Sard produces the nonsurjectivity needed by a compiled
  punctured-sphere contraction.

### Parametric transversality

- Construct the incidence submanifold.
- Prove almost-everywhere/dense transversality for parameterized families.
- Package the derivative linear algebra used to discharge regularity.

Representatives:

- `t94A06` for translated slices and the incidence argument.
- `t02A07` for a concrete constraint family and explicit gradient
  independence.

### Transverse-preimage geometry and duality

- Promote transverse inverse images to oriented compact submanifolds.
- Relate their fundamental classes or intersection pairings to induced maps
  in homology.
- Compose with the already-landed preimage geometry/duality construction
  targets without hiding their remaining producer obligations.

Representative: `t00J02`.  It is a stronger end-to-end gate than the Sard
problems because its remaining bridge joins geometry to homology.

## Differential-forms and Stokes program

The six differential-form records divide into four relatively independent
increments.

- **Bundling/extDeriv:** prove coordinate formulas agree with Mathlib's bundled
  exterior derivative.  Representative: `t96J08`.
- **Parameter integration/homotopy:** tangency, mixed derivatives, and
  differentiation under a parameter integral.  Representative: `t94J07`.
- **Weak and compact-support calculus:** normalized primitives, weak curl,
  volume transport, Fubini, and compact-support integration by parts.
  Representatives: `m02J01` and `m94J04`.
- **Oriented surface integration and Stokes:** local `extDeriv` calculations,
  boundary integrals, sphere periods, and non-exactness.  `t94A10` is the
  cleaner foundational gate; `t03J06` is the harder curved-surface integral
  validation.

## Intersection and cohomology programs

### Intersection theory

- Define mod-two fundamental classes for the relevant compact manifolds and
  submanifolds.
- Prove an intrinsic boundary maps to zero in ambient homology.
- Construct intersection and self-intersection pairings.
- Compare geometric transverse intersections with the homological pairing.
- Prove the product formula needed for projective-line factors.

`t03J05` is the geometric parity gate.  `t96J06` is the full homological
self-intersection gate and also validates Künneth.

### Degree-one cohomology

- Relate integral `H¹` to homotopy classes of maps into the circle.
- Construct a circle map from a primitive integral class.
- Provide a relative adjustment that fixes the map on a specified embedded
  circle or subspace.

`t97A02` is the clean representability gate; `t03J01` adds the relative
retraction adjustment.

## Cellular homology and Mayer--Vietoris

These are not competing area programs.  Both feed the singular-homology
checklist:

- `t96A03` is the first cellular/Mayer--Vietoris comparison gate: two spheres
  glued along an equator.
- `t98A02` is the excision and connected-sum gate.
- `t97A01` is the polygon-cell and surface-presentation gate shared with van
  Kampen.

Promotion should therefore extend `SingularHomologyConcrete.md` rather than
create disconnected one-problem modules for each label.

## Analytic singleton and small-area programs

These areas have too little structured evidence to justify a large slate, but
their representative problems give exact promotion tests:

- **Complex analysis:** `a92J05` requires the reusable Rouché zero-counting
  theorem.  `a94A09` tests its use inside a larger compactness/rigidity proof.
- **Measure/integral:** `a02J07` requires FTC with a one-sided singular
  endpoint; `a93A04` requires the variation characterization and Lipschitz
  approximation of absolutely continuous functions.  These are distinct
  programs despite sharing a coarse area label.
- **Fourier analysis:** `a01A03` is the sole recorded gate and requires the
  `L¹` convolution theorem, Fourier differentiation, a concrete interval
  transform pair, and injectivity.
- **Degree theory:** `t91A08` is the sole gate and requires the integer-degree
  classification of additive-circle self-maps.

## Candidate representative slate

No small slate can cover every construction program.  A topology-focused
Library Loop slate should maximize distinct reusable layers and use exact
residual obligations:

| Problem | Primary layer | Secondary layers |
|---|---|---|
| `t91A05` | circle fundamental group | retraction obstruction |
| `t93A03` | van Kampen for a wedge | free groups, circle computation |
| `t03J03` | cover/subgroup classification | orientation character, fundamental group |
| `t02A08` | homological orientation and degree | sphere homology |
| `t94A06` | parametric transversality | manifold Sard |
| `t00J02` | transverse-preimage duality | singular homology, orientation |
| `t96J06` | intersection/self-intersection | Künneth, singular homology |

If five slots are a hard limit, the recommended initial set is `t91A05`,
`t03J03`, `t02A08`, `t00J02`, and `t96J06`.  It sacrifices the clean wedge
van-Kampen gate and the pure parametric-transversality gate; those should be
the first alternates, not silently treated as covered.

Before adopting this slate, each row still needs a state-bound checkpoint with
the frozen statement, exact residual obligation, expected reusable increment,
and a promotion test.  This map supplies the coverage rationale but is not
that checkpoint evidence.

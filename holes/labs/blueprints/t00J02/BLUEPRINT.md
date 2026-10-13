# Blueprint for t00J02

## Triage

Verdict: **true and faithful**.  No statement repair is needed.

The registered theorem formalizes the source faithfully: `CompactSpace`,
`T2Space`, `PathConnectedSpace`, and the two-dimensional manifold structure
encode a closed connected surface; `hasGenusTwo` supplies its integral
homology; `wrapsHandle c` says the embedded circle has nonzero integral
`H₁` class; `transverse` is the derivative range-sum condition; and
`componentsBoundDisks` supplies an embedded filling disk for every connected
component of the inverse image.  `hasDegree` pins the claimed integer to the
actual endomorphism of `H₂(S; ℤ)`.

The topology audit found no counterexample to the registered statement.  It
did find that the current proof's intermediate obligation
`ConstructionTargets.OrientedSurfacePreimageDuality.Producer S` is false:
the predicate hidden inside that interface permits an arbitrary surjective
degree-zero parametrization of a component, rather than a genuine component
parametrization.  The blueprint therefore bypasses `Producer` entirely.

Degenerate checks:

* The empty surface is excluded by `PathConnectedSpace S`.
* For a constant map whose value misses `range c`, the inverse image is empty
  and the disk condition is vacuous, but its top-homology map and degree are
  zero, as claimed.
* If the constant value lies on `c`, transversality fails: both derivative
  ranges have total dimension at most one and cannot span the surface tangent
  space.
* For the identity map and an essential handle circle, the inverse image is
  the handle circle itself; it cannot bound a disk because its `H₁` map is
  nonzero.  Thus the hypothesis correctly rules out this degree-one test.
* A separating circle would invalidate the informal argument, but it is
  excluded by `wrapsHandle c`, which is exactly nonvanishing of its induced
  `H₁` morphism.

## Remaining lemma

### `t00J02_transverse_diskBounded_topHomologyMap_eq_zero` — LIBRARY

**Statement in words.**  Let `f` be a smooth self-map of a compact connected
charted surface, transverse to a smoothly embedded circle `c`.  If `c` is
nonzero in integral first homology, the surface has genus-two integral
homology, and every connected component of `f ⁻¹(range c)` bounds an embedded
disk, then the map induced by `f` on integral `H₂` is zero.

**Why true.**  Choose a regular value on `c`.  Local fundamental-class
naturality identifies the action on top homology with the signed sum of local
degrees over its finite fiber.  Transversality organizes that fiber into the
compact one-manifold components of `f ⁻¹(c)`.  The contribution of each
component is, up to the component orientation sign, the degree of its lift to
`c`.  A component bounding an embedded disk is null-homologous.  Functoriality
and the nonzero map `H₁(c) → H₁(S)` then force the lift's `H₁` map, hence its
circle degree, to vanish.  Every component contributes zero, so the signed
local-degree sum and therefore `H₂(f)` vanish.

Equivalently, this is the integral Poincare-duality identity
`PD[f⁻¹(c)] = f* PD[c]`: the disk hypothesis makes the left side zero, while
nondegeneracy of the surface intersection form turns the vanishing pullback of
the nonzero class `PD[c]` into degree zero.  The signed-count route is the one
for which the repository already contains the most infrastructure.

**Repository status and estimate.**  This is a genuine library program, not a
30--150-line seat.  The audit splits its implementation into:

1. `surfaceTopHomology_localFundamentalClassIso` (250--500 lines), shared with
   `t98A02` and built on the sorry-free
   `ConstructionTargets.ManifoldFundamentalClass` infrastructure;
2. `regularValue_topHomologyMap_signedCount` (500--900 lines);
3. `transverseCircle_preimage_component_signedCount` (350--700 lines), using
   the banked transverse-preimage geometry modules; and
4. `circleDegree_eq_homologyMap` (180--350 lines), followed by an 80--160-line
   consumer assembly.

These stages share representation-sensitive local-homology and orientation
data and exceed the lemma-seat size individually.  Following the batch rule,
the blueprint states their combined deliverable once rather than hiding the
same work in several fake adapters.  The closest sorry-free modules are
`ConstructionTargets.ManifoldFundamentalClass`,
`ConstructionTargets.TransversePreimageGeometry`,
`ConstructionTargets.TransversePreimageDuality`,
`ConstructionTargets.DiskBoundedPreimageDuality`,
`ConstructionTargets.DiskBoundaryHomology`, and
`ConstructionTargets.CircleHomology`.  All ConstructionTargets modules
imported by `Blueprint.lean` were checked to contain no `sorry`, `admit`, or
custom `axiom` declaration.

**Dependencies.**  None within this blueprint.  The external implementation
depends on the four library stages above.

**Truth check.**  Besides the constant-map and identity-map tests in triage, a
hand calculation with a symplectic basis
`a₁,b₁,a₂,b₂` takes `[c]=a₁`.  Vanishing of the transverse inverse-image class
gives `f* PD(a₁)=0`; pairing with `PD(b₁)` gives
`degree(f) · (a₁ · b₁)=0`.  Since `a₁ · b₁=1`, the degree is zero.  The same
calculation is exactly what the signed local-degree proof encodes.

## Assembly

The already compiled elementary lemma
`apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero` evaluates the defining
degree equation on the class corresponding to `1 ∈ ℤ`.  The registered
theorem `apm_t00j02` applies that adapter to the LIBRARY lemma, with no direct
`sorry`.  Its type is identical to the theorem in
`problems/t00J02/lean/Main.lean`.

## Dependency layers

* **Layer 1 (LIBRARY program):**
  `t00J02_transverse_diskBounded_topHomologyMap_eq_zero`.
* **Layer 2 (already compiled):** the degree adapter and `apm_t00j02`.

There is one admitted lemma.  Honest parallelism belongs inside the named
library program after its local-fundamental-class representation boundary is
fixed; there are no independent 30--150-line missing consumer lemmas now.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00J02/Blueprint.lean
```

The output of `#print axioms apm_t00j02` was:

```text
'apm_t00j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole `sorryAx` enters through
`t00J02_transverse_diskBounded_topHomologyMap_eq_zero`; the main theorem and
the degree adapter contain no `sorry`.

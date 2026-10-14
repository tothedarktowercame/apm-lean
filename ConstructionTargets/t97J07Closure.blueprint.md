# t97J07 closure blueprint

The frozen consumer is `problems/t97J07/lean/Main.lean`.  Its space
`T97J07CP2` is the quotient-topological complex projective plane
`ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 2`.  The final conjunct
is the honest rational-singular-homology predicate
`ConstructionTargets.RationalLefschetz.HasEulerCharacteristic T97J07CP2 3`.
The registered statement and every definition it mentions remain unchanged.

This plan is copied from the reviewed blueprint
`holes/labs/blueprints/t97J07/BLUEPRINT.md`.  That review found an earlier
statement unfaithful because its last arithmetic equality did not compute an
Euler characteristic; the registered repaired statement already contains the
predicate above.  The repaired statement is not refuted.

## C1. Elementary projective fixed-point calculation — blueprint-proved

Copy the sorry-free definitions and proofs from
`holes/labs/blueprints/t97J07/Blueprint.lean` into
`ConstructionTargets/t97J07Closure.lean`:

- the projectivization of `diag(1,1,3)` and its fixed line and isolated point;
- both affine chart formulas;
- exclusion of the isolated point from the line;
- the two derivative computations and determinant signs;
- both local indices, the line contribution, and `2 + 1 = 3`;
- final assembly of `apm_t97j07` after the two remaining inputs below.

These are adapter proofs, not library obligations, and must retain the exact
definitions used by the registered theorem.

## C2. Exact fixed-set classification — bounded adapter

Prove `t97J07_fixed_set`: the fixed locus is precisely the projective line
whose third coordinate is zero together with the third coordinate axis.

For a fixed class `p`, use `Projectivization.mk_rep`,
`Projectivization.map_mk`, and `Projectivization.mk_eq_mk_iff'` to obtain the
nonzero scalar relating `t97J07Linear p.rep` to `p.rep`.  Coordinate 2 either
vanishes, putting the class on the line, or forces the scalar to be 3; then
coordinates 0 and 1 vanish and `mk_eq_mk_iff'` identifies the class with the
isolated point.  The converse is direct projective equality.  This node is
independent of C3.

## C3. Rational homology of CP² — LIBRARY

Prove `t97J07_eulerCharacteristic`:

```lean
ConstructionTargets.RationalLefschetz.HasEulerCharacteristic T97J07CP2 3
```

Compute actual rational singular homology of the literal quotient-topological
space: it is one-dimensional in degrees 0, 2, and 4 and zero otherwise.  Then
the identity has trace one in those three degrees, and the finite alternating
sum is `1 + 1 + 1 = 3`.

Use the standard filtration
`CP⁰ ⊂ CP¹ ⊂ CP²`, with one cell in dimensions 0, 2, and 4.  Build the needed
coefficient open-cover Mayer–Vietoris/cellular comparison against the existing
`ProjectiveSpaceTopology` and `RationalLefschetz` infrastructure.  Reuse the
rational projective-space and sphere-homology results being built for t96A06
and t99J05; do not create a second incompatible homology model and do not
replace the exact quotient topology by an abstract CP².

The construction must establish finite dimensionality and finite degree
support required by `HasEulerCharacteristic`; a default trace on an
infinite-dimensional module is not sufficient.  Boundary checks are CP⁰ with
Euler characteristic 1 and CP¹ with Euler characteristic 2.

## C4. Final assembly

After C2 and C3 compile, copy the already-proved assembly from
`Blueprint.lean`.  It combines the exact fixed-set theorem, chart and index
calculations, the contribution equality, and `t97J07_eulerCharacteristic`.
Only here does the sole placeholder in `Main.lean` change from one to zero.

## Dependency order and milestones

1. Blueprint (this file).
2. C1 declarations and C2 fixed-set classification; C2 may proceed in
   parallel with C3.
3. C3 should be split only at genuine reusable homology interfaces: exact
   CP filtration/quotient pairs, rational relative groups and connecting maps,
   the CP² homology table, then the Euler-characteristic adapter.
4. C4 consumer assembly.

Each program job commits one compiled, sorry-free milestone and records the
next mathematical node.  The final gates are:

```text
lake env lean problems/t97J07/lean/Main.lean
python3 scripts/statement-registry.py check
```

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.  No
registered statement, registry file, or definition used by the statement may
change.

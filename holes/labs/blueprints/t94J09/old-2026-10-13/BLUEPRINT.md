# Blueprint for t94J09

## Triage

Verdict: **true and faithful**.

The problem specifies a fourteen-edge polygon, seven paired edge labels, and
exactly two vertex classes.  Hence its displayed CW structure has
`V = 2`, `E = 7`, `F = 1`, so `χ = -4`.  The occurrences of `a` have the same
orientation, making the surface nonorientable.  The classification formula
`χ(N_g) = 2 - g` therefore gives `g = 6`.  This agrees with `Main.lean`; the
harvested old claim `N₃` is explicitly marked untrusted and contradicts the
problem's stipulated vertex count.

I tried the relevant degeneracies.  The polygon is nonempty (its centre lies
in the closed disk), all seven labels occur exactly twice, and the exceptional
corner test in `vertexClass` has both values: position `3` maps to `1`, while
position `0` maps to `0`.  Direct kernel computation (`decide`) verifies the
vertex count, edge count, Euler characteristic, and genus.  Specializing the
orientation predicate to `a` computes a contradiction, since `a` occurs twice
positively and never negatively.  The topology-loop audit independently
identifies the same two missing foundations and no counterexample.

The five finite certificates and the quotient definitions are reused from
`Main.lean` with their complete proofs.  The two remaining obligations are
honestly library-scale; splitting either into artificial seat-sized statements
would conceal rather than remove its shared topological dependency.

## Definitions and available infrastructure

`Blueprint.lean` reproduces all definitions needed to state either obligation:
the signed word, its finite invariants, the two concrete `EqvGen` disk
quotients, and integral singular homology `apm_t94J09_H`.

The imports include the original imports and the closest sorry-free banked
infrastructure:

* `ConstructionTargets.Surfaces` defines the standard nonorientable polygon
  quotient (the target presentation used here).
* `ConstructionTargets.SurfaceClassification` develops finite two-complex and
  planar perturbation infrastructure, but does not yet classify these polygon
  quotients.
* `ConstructionTargets.PolygonSurfacePiOne` provides extensive signed-polygon
  quotient, boundary, radial-cover, and fundamental-group machinery.  It does
  not provide the required cut-and-paste homeomorphism or integral homology.
* `ConstructionTargets.SingularHomologyConcrete` supplies concrete access to
  Mathlib singular homology, but no cellular-to-singular comparison for this
  presentation.

All four files are sorry-free (checked by a source search), and the blueprint
compiles against them.

## Remaining lemmas

### `apm_t94J09_polygon_normalization` — LIBRARY

**Statement in words.** The quotient of the disk by the concrete fourteen-edge
word is homeomorphic to the standard twelve-edge presentation of `N₆`.

**Why true.** Apply the classical polygon cut-and-paste normalization: edge
slides and cancellations transform the signed pairing word into six twisted
pairs.  Each elementary polygon move must be realized as a homeomorphism of
the corresponding quotients; composing those homeomorphisms yields the stated
one.  The already proved quotient universal-property assembly in `Main.lean`
is useful when a move is induced by compatible maps, but the audit warns that
a complete cut-and-paste sequence is generally not induced by a single disk
self-map.  A robust implementation should use the signed-polygon quotient and
radial/boundary machinery imported through
`ConstructionTargets.PolygonSurfacePiOne`.

**Expected size.** 500–1000 lines (one library program, 1–3 weeks).

**Dependencies.** Definitions only; independent of the homology lemma.

**Truth check.** The target genus is forced independently by `χ = -4` and
nonorientability.  It is not `N₃`, whose Euler characteristic is `-1`.
The concrete standard target relation is definitionally the `false, 6`
presentation pattern in `ConstructionTargets.Surfaces`.

### `apm_t94J09_polygon_homology` — LIBRARY

**Statement in words.** The concrete quotient has integral singular homology
`H₀ ≅ ℤ`, `H₁ ≅ ℤ⁵ × ℤ/2`, and zero homology in every degree at least two.

**Why true.** Give the polygon quotient its finite CW/relative-chain model.
There are two 0-cells, seven 1-cells, and one 2-cell.  Compute the cellular
boundary maps from the endpoint identifications and signed attaching word,
put the resulting integer matrices into Smith normal form, and transport the
calculation to Mathlib singular homology through a cellular-to-singular or
Mayer–Vietoris comparison.  The Smith calculation yields one torsion factor
of order two and free rank five in degree one; the top boundary is injective,
so degree two and above vanish.  The topology audit records that the missing
part is precisely this comparison/production theorem, not the arithmetic.

**Expected size.** 800–1800 lines (one library program, 2–5 weeks).

**Dependencies.** Definitions only; independent of normalization.  This is
deliberate: giving it the normalization conclusion as a hypothesis would still
leave the absent homology computation of `N₆` and would serialize two programs
that can be developed in parallel.

**Truth check.** The standard formula for a closed nonorientable genus-six
surface is `H₀ = ℤ`, `H₁ = ℤ^(6-1) ⊕ ℤ/2`, `H₂ = 0`.  The displayed groups are
exactly `ℤ`, `ℤ⁵ × ZMod 2`, and zero.  The degree-two vanishing is consistent
with nonorientability; the Euler ranks give `1 - 5 + 0 = -4`, matching the
independent cell count.  Degree `k ≥ 3` vanishes for a two-dimensional CW
model.

## Assembly

The main theorem combines the five already proved finite certificates with
the two library lemmas.  Its body contains no `sorry`, and neither obligation
is smuggled into a definition or a hypothesis.

## Dependency layers

* **Layer 1 (parallel library programs):**
  `apm_t94J09_polygon_normalization`, `apm_t94J09_polygon_homology`.
* **Layer 2 (already compiled):** conjunction assembly in `apm_t94j09`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t94J09/Blueprint.lean
```

The final output of `#print axioms apm_t94j09` is:

```text
'apm_t94j09' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 library
lemmas.  The main theorem has no direct `sorry`.

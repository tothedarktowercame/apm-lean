# Blueprint for t94A08

## Triage

Verdict: **true and faithful**. No statement repair is needed.

The first locus is the nonsingular complex conic
`z₀² + z₁² + z₂² = 0`; the second is the union of the two
distinct projective lines `z₁ + i z₂ = 0` and `z₁ - i z₂ = 0`, meeting at
`[1:0:0]`. The registered theorem says exactly that the first locus is locally
homeomorphic to open subsets of `ℝ²` and the second is not. Its separate
regular-level conjunct is also true and is already proved without placeholders.

Degenerate cases checked:

* Projective space has no zero-vector point, so the only common zero of the
  gradient `(2z₀,2z₁,2z₂)` does not create a singular projective point.
* The explicit vector `(1,0,0)` is nonzero and its projective class belongs to
  `sigma2`; the compiled lemma `apm_t94a08_node_mem_sigma2` checks this despite
  the noncanonical `Projectivization.rep`.
* The two factors are genuinely distinct over `ℂ`: for example `(0,i,1)` is
  on one branch and not the other. Their simultaneous vanishing forces
  `z₁=z₂=0`, hence their projective intersection is only `[1:0:0]`.
* At the node there are **two**, not four, punctured branches. Each branch is
  real two-dimensional, and a punctured disk in it is connected; the union of
  the two punctured disks is disconnected. This is enough to contradict a
  punctured planar disk.
* In the manifold predicate, `p ∈ U ∩ S` makes the chart domain nonempty, so
  choosing an empty target open set cannot make the definition vacuous.

The informal statement has a typographical `Sigma1` in its second item but
then asks about `Sigma2`; the Lean file already applies the intended repair.
The batch note also records the registered statement as graded faithful.

## Reused sorry-free infrastructure

`Blueprint.lean` imports:

* `ConstructionTargets.T94A08AffineChartHomeomorph`, which supplies actual
  affine `OpenPartialHomeomorph`s for the frozen coinduced projective topology;
* `ConstructionTargets.T94A08AffineSmoothConicParametrization`, which supplies
  an explicit homeomorphism from the normalized affine conic
  `1 + u² + v² = 0` to `ℂˣ`.

Both imported files and their dependency chain were checked with a
comment-stripped `sorry`/`admit` search and contain no placeholders. They are
also exercised by compiling the blueprint. The derivative proof, node
construction, factorization, branch union, and node-in-both-branches results
from `Main.lean` are copied with their complete proofs.

The most recent topology STOP did **not** refute the problem. It refuted a
discarded comparison contract whose `Fin.cases z.1 (fun _ => z.2)` inserted
`z.2` at both affine indices and lost `z.1`. A future implementation should
case-split the two members of `{j : Fin 3 // j ≠ 0}`, sending index `1` to the
first pair component and index `2` to the second. This blueprint imports the
valid chart and affine-parametrization modules, but does not import or restate
the malformed contract.

## Remaining lemmas

### `apm_t94a08_sigma1_isRealTwoManifold` — LIBRARY

**Statement in words.** Every point of the smooth projective conic has an
ambient-open neighborhood whose intersection with the conic is homeomorphic
to an open subset of the real plane.

**Why true.** Choose a nonzero homogeneous coordinate and use
`ConstructionTargets.T94A08ProjectiveConic.affineChartConstruction`. In the
`z₀ ≠ 0` chart, normalize to the affine equation `1+u²+v²=0`, using the
correct two-coordinate insertion described above. The imported
`T94A08AffineSmoothConicParam.affineConicHomeomorphCstar` identifies this with
`ℂˣ`, an open subset of `ℂ`; compose with the standard real-linear
homeomorphism `ℂ ≃ₜ EuclideanSpace ℝ (Fin 2)`. The other affine charts are
the same after permuting homogeneous coordinates. Restrict the ambient affine
chart to the conic and compose these homeomorphisms.

The projective-affine restriction and correct coordinate insertion are the
remaining implementation work. Because this is a coherent local-chart
construction rather than several independent facts, splitting it into tiny
contracts would only duplicate the same normalization proof. It is marked
LIBRARY in accordance with the batch instructions.

**Expected size.** 180–300 lines, using the banked chart and parametrization
modules. The older audit's 250–450-line affine-chart foundation is already
banked, so it is not part of this estimate.

**Dependencies.** Definitions and proved lemmas in `Blueprint.lean`, plus the
two imported `ConstructionTargets` modules. Independent of the nodal lemma.

**Truth check.** In the `z₀` chart the test points `(u,v)=(i,0)` and
`(-i,0)` both satisfy `1+u²+v²=0` and must remain distinct under the corrected
coordinate insertion. The imported affine parametrization sends them to `i`
and `-i`, respectively. At a point with `z₀=0`, some other coordinate is
nonzero, so the three affine sources cover every projective point.

### `apm_t94a08_nodal_not_manifold_at` — LIBRARY

**Statement in words.** `sigma2` is not locally homeomorphic to an open subset
of `ℝ²` at the node `[1:0:0]`.

**Why true.** Use the imported `z₀ ≠ 0` affine chart. There the two branch
equations become two distinct complex lines through `(0,0)`. Intersect with a
small ball. Removing the origin leaves the disjoint union of two nonempty
punctured complex disks. Thus every sufficiently small punctured neighborhood
inside the nodal locus is disconnected. If a manifold chart existed, shrink
its open target around the image of the node to a Euclidean ball; its
punctured preimage would be connected because a punctured open disk in
`ℝ²` is path connected. Homeomorphisms preserve connectedness, a
contradiction.

This is the missing local-separation theorem named by the solve loop. Mathlib
has transport lemmas such as `Homeomorph.map_punctured_nhds_eq`, but no
packaged theorem for the complex nodal cross. The chart, branch separation,
shrinking argument, and punctured-plane connectivity form one substantial
topological result, so it is stated once rather than divided into fake small
lemmas.

**Expected size.** 300–500 lines. This is intentionally marked LIBRARY: the
topology loop should build it as a program. The closest sorry-free foundation
is `ConstructionTargets.T94A08AffineChartHomeomorph`; the missing addition is
the local connectedness/component obstruction for the union of the two
branches.

**Dependencies.** Definitions and proved branch lemmas in `Blueprint.lean`,
and the imported affine projective chart. Independent of the smooth-conic
lemma.

**Truth check.** On the ball of any positive radius, each branch contains a
nonzero point and their intersection is only the origin. Removing the origin
therefore separates the locus into exactly two nonempty relatively open
pieces. By contrast, `ℝ² \ {0}` and every punctured open disk are path
connected. Radius zero is never chosen, and the chart neighborhood contains
the node by construction.

## Assembly

The main theorem has no `sorry`. It combines the already proved regular-level
result with `apm_t94a08_sigma1_isRealTwoManifold`; for the negative conjunct it
applies a hypothetical global manifold witness to the compiled node-membership
proof and contradicts `apm_t94a08_nodal_not_manifold_at`.

## Dependency layers

* **Layer 1 (parallel, both LIBRARY):**
  `apm_t94a08_sigma1_isRealTwoManifold`,
  `apm_t94a08_nodal_not_manifold_at`.
* **Layer 2 (already compiled):** main-theorem assembly after both Layer 1
  contracts are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t94A08/Blueprint.lean
```

The final output of `#print axioms apm_t94a08` was:

```text
'apm_t94a08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 LIBRARY
lemmas. The main theorem and every other declaration are proved without
placeholders.

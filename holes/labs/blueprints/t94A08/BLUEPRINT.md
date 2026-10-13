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

### Nodal obstruction split (four parallel LIBRARY leaves)

The auxiliary predicate
`apm_t94a08_HasConnectedPuncturedNeighborhood S p` says that some ambient-open
neighborhood `U` of `p` has preconnected `(U ∩ S) \ {p}`.  It is deliberately
weaker than being a manifold, and strong enough to distinguish the node.

#### `apm_t94a08_plane_punctured_neighborhood` — LIBRARY

**Statement.** If `W` is open in `EuclideanSpace ℝ (Fin 2)` and `x ∈ W`, there
is an open `V`, with `x ∈ V ⊆ W`, whose puncture is preconnected.

**Proof route / Mathlib tools.** Use `Metric.isOpen_iff` (or
`Metric.mem_nhds_iff`) to choose `0 < r` with `Metric.ball x r ⊆ W`, and take
that ball.  The useful existing results are
`isPathConnected_compl_singleton_of_one_lt_rank`, `isPathConnected_ball`,
`IsPathConnected.isPreconnected`, and `Module.finrank_fin`; alternatively give
the standard two-segment path, choosing an intermediate point not collinear
with the puncture.  Expected size: **60–110 lines**.

**Truth/degenerate checks.** Openness and `x ∈ W` force a strictly positive
radius, so the chosen ball is neither empty nor `{x}`. `Fin 2` has real rank
two, which is exactly why removing one point remains connected.

#### `apm_t94a08_chart_transport_punctured_neighborhood` — LIBRARY

**Statement.** Given a homeomorphism `e : ↥(U ∩ S) ≃ₜ ↥W`, openness of `U`,
membership `p ∈ U ∩ S`, and an explicit connected punctured plane
neighborhood of `e(p)`, produce
`apm_t94a08_HasConnectedPuncturedNeighborhood S p`.

**Proof route / Mathlib tools.** Restrict `e.symm` to `V`; use
`e.isOpenMap`, `IsOpen.isOpenEmbedding_subtypeVal`, and
`isOpen_induced_iff` to express its preimage as `U' ∩ (U ∩ S)` for an
ambient-open `U'`. Replace `U'` by `U' ∩ U`. Transport preconnectedness with
`IsPreconnected.image` (using `Homeomorph.continuous`) after proving the image
is precisely the punctured slice; `Homeomorph.injective` handles deletion of
the distinguished point. Expected size: **80–140 lines**.

**Independence.** The plane conclusion is an explicit hypothesis; this lemma
does not refer to the preceding LIBRARY lemma. Empty-domain and wrong-basepoint
loopholes are excluded by the explicit `hpU` and `hpS` arguments.

#### `apm_t94a08_complexCross_punctured_not_preconnected` — LIBRARY

**Statement.** For the cross
`{z : ℂ × ℂ | z.1 = 0 ∨ z.2 = 0}`, every open neighborhood `V` of `(0,0)` has
a non-preconnected punctured intersection with the cross.

**Proof route / Mathlib tools.** Separate the punctured cross by the relatively
clopen sets `z.1 = 0` and `z.2 = 0`. Use
`isPreconnected_iff_subset_of_disjoint`, continuity of `Prod.fst`/`Prod.snd`,
`isClosed_singleton`, and `isOpenMap_fst`/basic product-open lemmas.
Nonemptiness of both sides follows by choosing positive-radius balls
inside `V` and the points `(r/2,0)` and `(0,r/2)` (coerce real numbers to
`ℂ`); `Metric.isOpen_iff`, `Prod.dist_eq`, and `norm_real` discharge the
bounds. Expected size: **70–130 lines**.

**Truth/degenerate checks.** The origin is deleted, hence the two axes are
disjoint. Strictly positive radius makes both pieces nonempty. There are two
complex branches (not four real rays), but two nonempty separated pieces are
all the contradiction requires.

#### `apm_t94a08_node_has_no_connected_punctured_neighborhood` — LIBRARY

**Statement.** Assuming the preceding cross obstruction explicitly, the node
of `sigma2` has no connected punctured ambient neighborhood.

**Proof route / Mathlib tools.** Use the imported
`ConstructionTargets.T94A08ProjectiveConic.affineChartConstruction 0` and its
`source`, `target`, `toPartialEquiv`, and continuity/open-source facts. In the
`z₀ ≠ 0` chart, apply the complex-linear homeomorphism
`(u,v) ↦ (u + I*v, u - I*v)`; its inverse is
`(a,b) ↦ ((a+b)/2, (a-b)/(2*I))`. Rewrite membership using
`apm_t94a08_quadratic2_factor`, `mul_eq_zero`, and the chart coordinate
formulas `coordinates_chartInverse` / `chartInverse_coordinates`. Pull any
hypothetical connected punctured neighborhood into the cross and contradict
the supplied `hcross`. Expected size: **110–150 lines**.

**Independence.** The cross theorem is an explicit hypothesis, so this leaf can
be proved before it lands. The chart source contains the node because its
zeroth homogeneous coordinate is nonzero. The linear change of variables has
nonzero determinant (`I ≠ 0`), so neither branch is collapsed.

### `apm_t94a08_nodal_not_manifold_at` — assembly (proved)

The theorem now contains no `sorry`: unpack a hypothetical manifold chart,
obtain the plane neighborhood from the first leaf, transport it with the
second, and contradict the fourth leaf instantiated by the third. Thus all
four LIBRARY leaves are siblings and can be assigned simultaneously.

## Assembly

The main theorem has no `sorry`. It combines the already proved regular-level
result with `apm_t94a08_sigma1_isRealTwoManifold`; for the negative conjunct it
applies a hypothetical global manifold witness to the compiled node-membership
proof and contradicts `apm_t94a08_nodal_not_manifold_at`.

## Dependency layers

* **Layer 1 (four parallel nodal LIBRARY leaves):**
  `apm_t94a08_plane_punctured_neighborhood`,
  `apm_t94a08_chart_transport_punctured_neighborhood`,
  `apm_t94a08_complexCross_punctured_not_preconnected`, and
  `apm_t94a08_node_has_no_connected_punctured_neighborhood`.
* **Layer 2 (already compiled):** `apm_t94a08_nodal_not_manifold_at` assembles
  the four leaves; the main theorem then uses it directly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t94A08/Blueprint.lean
```

The final output of `#print axioms apm_t94a08` was:

```text
'apm_t94a08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings identifying `sorry` are exactly the four nodal Layer 1
leaves. The former nodal LIBRARY theorem is now a sorry-free assembly. The
main theorem and every other declaration are proved without placeholders.

# Statement-encoding progress — 2026-09-10

Later on September 10, [the second tranche](statement-encoding-progress-round2-2026-09-10.md) added five more statements: the current count is 477/491, with 14 remaining. The report below records the first tranche.

Twelve of the original 31 missing bundles now have compiled, concrete Lean
statements. The source-stem material count is **472/491**, with **19** still
missing. Each new problem has exactly one explicit `sorry`; this is statement
and construction-specification progress, not twelve solved problems.

The [backlog JSON](statement-construction-backlog-2026-09-10.json) retains the
initial census and source hashes and now records the twelve encodings. Each
problem's status.json records its source-clause mapping, source/Lean hashes,
open proof and review status. Independent mathematical review is still pending.

## Statements written

- [t93J03](../problems/t93J03/lean/Main.lean): Presentation of the actual Klein-bottle fundamental group; inclusion-induced subgroup condition; plane embedding for the specified locally connected subspace.
- [t95A04](../problems/t95A04/lean/Main.lean): Construct quotient-compatible smooth RP2 atlas; descend the six-coordinate sphere polynomial; smoothness, embedding and immersion onto a submanifold.
- [t96A01](../problems/t96A01/lean/Main.lean): Closed connected orientable genus-four surface; actual subgroup of its fundamental group with finite index n; explicit genus-(3n+1) presentation.
- [t96A02](../problems/t96A02/lean/Main.lean): Construct the point wedge of two actual projective planes; every continuous self-map has a fixed point.
- [t96A06](../problems/t96A06/lean/Main.lean): Descend the exact quadratic map from every nonzero vector; compute actual rational-homology Lefschetz number -3; nonhomotopy to identity.
- [t96A07](../problems/t96A07/lean/Main.lean): Construct quotient smooth atlas and descend (yz,xz,xy); negate z-axis transversality; infinitely many intersecting horizontal planes transverse to the original sphere map.
- [t96J02](../problems/t96J02/lean/Main.lean): All finite-index subgroups of the actual Klein-bottle fundamental group are isomorphic to it or Z2; both alternatives occur.
- [t98A06](../problems/t98A06/lean/Main.lean): Every smooth target tangent field lifts through the submersion; the actual regular fibers over +1 and -1 are diffeomorphic.
- [t98J01](../problems/t98J01/lean/Main.lean): The precise sphere/circle product map has Lefschetz number 8 and is not homotopic to identity.
- [t98J02](../problems/t98J02/lean/Main.lean): Nonseparation lifts through connected finite covers; a disconnected-cover counterexample to unrestricted part (a); a connected-cover counterexample to part (b).
- [t99J01](../problems/t99J01/lean/Main.lean): Positive-degree connected covers exist; every connected degree-n cover has free group rank 2n+1; arbitrary disconnected covers have componentwise ranks from actual sheet counts.
- [t99J06](../problems/t99J06/lean/Main.lean): Literal exterior derivative; cone as the actual parameter image; single-cover and immersion interior certificates; positive dx-wedge-dy orientation; pullback integral 9pi/2.

## Five reusable construction modules

- [StatementSurfaceModels](../ConstructionTargets/StatementSurfaceModels.lean):
  concrete projective-plane/Klein-bottle polygons, circle wedges and surface
  group relators, reusing existing quotient constructions.
- [ProjectiveSpaceTopology](../ConstructionTargets/ProjectiveSpaceTopology.lean):
  projectivization with the coinduced topology from nonzero vectors, including
  proved continuity and surjectivity of its projection.
- [RealProjectiveSmoothTarget](../ConstructionTargets/RealProjectiveSmoothTarget.lean):
  the actual sphere projection and a precise required smooth atlas. An atlas
  must make that projection a local diffeomorphism. Its existence is requested
  in the two consumer theorem conclusions; no inhabitant is postulated.
- [RationalLefschetz](../ConstructionTargets/RationalLefschetz.lean): alternating
  traces of actual rational singular-homology maps. The number predicate
  explicitly requires finite dimensionality and eventual vanishing, preventing
  default traces of infinite modules from masquerading as a Lefschetz number.
- [CoordinateSurfaceForms](../ConstructionTargets/CoordinateSurfaceForms.lean):
  continuous alternating coordinate forms and pullback integration over an
  oriented parameter rectangle. The cone statement supplies image, coverage,
  immersion and orientation certificates as open construction obligations.

All five are in the ConstructionTargets library and its root imports, build
with Lake, and have `.olean` files. Their definitions and elementary proofs
contain no `sorry`. This does not mean the requested smooth atlas has been
constructed, or that arbitrary manifold integration/intersection theory exists.

## Source fidelity decisions

The source text itself was not edited. No hypothesis was discarded to obtain
a simpler theorem. The mathematical meanings and the open work are recorded
next to each declaration.

- `t98J02`: a disconnected finite cover invalidates unrestricted part (a).
  The encoding states the connected-cover theorem and a disconnected-cover
  counterexample, as well as the connected counterexample to (b).
- `t99J01`: both connected and arbitrary covers are represented, with the
  latter's fundamental groups computed per path component.
- `t99J06`: `dz ∧ dz` stays exactly as printed. Integration is of the actual
  form on derivatives of the specified cone parametrization; the apex is not
  incorrectly treated as a smooth manifold point.
- `t95A04`/`t96A07`: the missing smooth quotient is an explicit existential
  construction requirement. It is not replaced by an arbitrary manifold, a
  free proposition, or a structure field asserting the desired answer.
- `t98A06`: smooth tangent sections and the existing regular-fiber atlases
  suffice to state the requested lift and fiber diffeomorphism. No flow or
  partition-of-unity theorem had to be proved first.
- The prior assertion that CW complexes were simply absent was too broad:
  this pinned Mathlib has `Topology/CWComplex/Classical/Basic.lean` and its
  abstract counterpart. Concrete attachments and comparison maps still need
  to be supplied for the remaining CW problems.

## Remaining nineteen

The remaining bundles were not filled with partial substitutes merely to
raise the material counter. Their source-specific obligations remain in the
backlog. The next constructions are larger shared definitions, or require
resolving the printed source, rather than proving the twelve theorems above.

| Problems | Next requirement |
|---|---|
| `a98J05` | Recover the missing conclusion. |
| `lts-derived-induction-lem3`, `lts-monadic-integration` | Recover source definitions and build the intended spectrum/measure-monad models. |
| `t00J05`, `t99J02` | Concrete disk attachments, the actual universal-cover description / CW and connected-sum presentations and comparison maps. Reuse existing CW definitions. |
| `t93A05`, `t97A05`, `t98J06` | Actual oriented/mod-2 submanifold intersection definitions connected to tangent geometry. Projective topology/smooth-target vocabulary now exists. |
| `t93A06`, `t95A05`, `t97A06` | Smooth forms on manifolds with pullback, exterior derivative, boundary orientation and integration. Euclidean forms alone do not supply these. |
| `t95A01` | Geometric nonorientability and actual surface self-cover witnesses, retaining all three existence questions. |
| `t93J05` | Resolve the unbounded printed cylinder versus the informal closed-surface argument. |
| `t97A07` | Resolve the n=0/positive-target-dimension convention before claiming nonempty critical values. |
| `t98J04` | Recover the knot diagram or a precise parametrization for part (b). |
| `t98J05` | Specify the genus-two action and its orbit quotient, then descend manifold forms; the printed relation needs explicit reflexive/equivalence closure. |
| `t99A05`, `t99A06` | Resolve compactness/properness conventions; then define geometric degree/intersection or Euler-characteristic obstruction. |
| `t99J05` | Complex-projective smooth affine charts and local fixed-point index connected to them. Quotient topology and rational invariants now exist. |

## Validation and existing gate conflict

- All twelve problem files compile under `lake env lean -DautoImplicit=false`.
  Each emits exactly one unproved-declaration warning; axiom inspection records
  `sorryAx` for every final theorem, as expected for this milestone.
- The existing statement-quality screen was run over all twelve. Its first
  pass found one constructor-name compilation error in t98A06; that was fixed
  and the affected check rerun. The final result is **12/12 pass** (eleven unchanged passes plus the corrected
  t98A06 rerun). The warnings about signatures without named hypotheses were
  reviewed against their concrete spaces and existential construction clauses.
- All five new modules build as named Lake library targets. Their public
  construction declarations were inspected with `#print axioms`.
- The global `check_construction_targets.sh` is **not green**: it reports 762
  modules absent from the root imports. Running the same script on HEAD's
  tracked module set and root (`98ce43c1069994d2a76d4e8dee88a29ee2f7810a`)
  reproduces the identical failing module set: **zero new failures**. The
  script and root policy were not relaxed; all five new modules satisfy the
  existing reachability requirement.

The root-import discrepancy needs a separate reconciliation of production and
explicitly partial modules with the gate. Blindly importing all 762 modules
would ignore the policy that the root excludes deliberately partial targets;
changing the check to ignore missing imports would weaken it. This sweep does
neither, and does not claim a clean repository-wide construction gate.

Detailed compiler/axiom outputs and quality-screen results are saved in the
[validation record](statement-encoding-validation-2026-09-10.json). The 22
audited construction declarations use only `propext`, `Classical.choice` and
`Quot.sound`; none uses `sorryAx`.

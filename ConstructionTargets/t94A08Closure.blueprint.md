# Blueprint for t94A08 closure

## Triage

The registered theorem is true and needs no statement repair. The first locus
is the nonsingular complex conic `z₀² + z₁² + z₂² = 0`. The second is the
union of the distinct projective lines `z₁ + i z₂ = 0` and
`z₁ - i z₂ = 0`, meeting at `[1:0:0]`.

Projective space excludes the zero vector, so the conic gradient has no
projective zero. The explicit nonzero vector `(1,0,0)` gives the node in
`sigma2`. At that node the punctured locus has two complex branches, whereas
a punctured real two-disc is connected.

## Reused sorry-free infrastructure

The implementation starts from `holes/labs/blueprints/t94A08/Blueprint.lean`.
It imports:

* `ConstructionTargets.T94A08AffineChartHomeomorph`, providing affine
  `OpenPartialHomeomorph`s for the frozen coinduced projective topology;
* `ConstructionTargets.T94A08AffineSmoothConicParametrization`, providing a
  homeomorphism from `1 + u² + v² = 0` to `ℂˣ`.

The derivative proof, node construction, factorization, branch union, and
node-in-both-branches proofs are already compiled in the source blueprint and
will be copied rather than re-derived. The discarded comparison contract that
used `Fin.cases z.1 (fun _ => z.2)` must not be reused: it sends both affine
indices to `z.2`. Correct insertion case-splits the two members of
`{j : Fin 3 // j ≠ 0}`, sending index `1` to the first pair component and
index `2` to the second.

## Milestone B1 — smooth conic manifold chart (LIBRARY)

### `apm_t94a08_sigma1_isRealTwoManifold`

Every point of the smooth projective conic has an ambient-open neighborhood
whose intersection with the conic is homeomorphic to an open subset of the
real plane.

Choose a nonzero homogeneous coordinate and use
`ConstructionTargets.T94A08ProjectiveConic.affineChartConstruction`. In the
`z₀ ≠ 0` chart, normalize to `1 + u² + v² = 0` with the correct two-coordinate
insertion. Compose
`T94A08AffineSmoothConicParam.affineConicHomeomorphCstar` with the standard
real-linear homeomorphism `ℂ ≃ₜ EuclideanSpace ℝ (Fin 2)`. Handle the other
charts by permuting homogeneous coordinates, then restrict the ambient chart
to the conic.

Dependencies: the definitions and proved lemmas in the source blueprint and
the two imported ConstructionTargets modules. It is independent of B2.

Truth check: `(u,v) = (i,0)` and `(-i,0)` both satisfy the affine equation and
remain distinct under correct coordinate insertion. A point with `z₀ = 0`
has another nonzero coordinate, so the three affine charts cover the conic.

Expected implementation size: 180–300 lines.

## Milestone B2 — nodal nonmanifold obstruction (LIBRARY)

### `apm_t94a08_nodal_not_manifold_at`

`sigma2` is not locally homeomorphic to an open subset of `ℝ²` at the node
`[1:0:0]`.

Use the imported `z₀ ≠ 0` affine chart. The two branch equations become two
distinct complex lines through `(0,0)`. Their intersection is only the origin.
Inside any sufficiently small positive-radius ball, removal of the origin
therefore separates the locus into two nonempty relatively open punctured
complex discs. If a manifold chart existed, shrink its open target around the
node image to a Euclidean ball. Its punctured preimage would be connected
because a punctured disc in `ℝ²` is path connected. A homeomorphism preserves
connectedness, giving a contradiction.

Dependencies: the definitions and proved branch lemmas in the source
blueprint and `ConstructionTargets.T94A08AffineChartHomeomorph`. It is
independent of B1.

Truth check: every positive-radius ball meets both branches away from the
origin, and the branches meet only at the origin. Radius zero is never chosen.

Expected implementation size: 300–500 lines.

## Assembly

After B1 and B2 compile without placeholders, copy the source blueprint's
proved definitions and lemmas into the scoped implementation. The main
theorem combines the proved regular-level result with B1. For the negative
conjunct, apply a hypothetical global manifold witness at the compiled node
and contradict B2.

## Dependency layers

* Layer 1, parallel: B1 and B2, both LIBRARY milestones.
* Layer 2: already compiled main-theorem assembly after both milestones.

The final implementation must compile `problems/t94A08/lean/Main.lean`, pass
the statement registry unchanged, contain no `sorry` or `admit`, and use only
standard axioms.

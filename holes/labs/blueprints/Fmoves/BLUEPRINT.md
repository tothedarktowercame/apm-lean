# Foundation blueprint: moves on signed polygon words

## Concrete model

`Signed Label = Label × Bool`.  For a nonempty even list `w`,
`PolygonSurface w` is `ConstructionTargets.Surfaces.Disk` modulo the relation
which pairs the `i`th and `j`th arcs exactly when `i ≠ j` and `w[i]` and
`w[j]` have the same label.  The common parametrisation is
`Surfaces.edgePoint w.length`.  Equal signs use the same parameter and unequal
signs use `1-t`.  `IsPolygonWord w` says that the length is positive and even
and every occurring label occurs exactly twice.

This replaces `QuotientMove` completely.  No theorem below receives maps on
quotients, a homeomorphism, or a relation-comparison certificate as input.

## Geometric word moves

- `rotation u v`: `PolygonSurface (u ++ v) ≃ₜ PolygonSurface (v ++ u)`.
  Radially extend the rotation carrying the first `u.length` sectors past the
  last `v.length` sectors.  Expected proof: 35–55 lines.
- `relabelInvert w e flip`: rename labels through `e`, and toggle both
  occurrences selected by `flip`.  The disk map is the identity; only the
  finite relation calculation changes.  Expected proof: 30–45 lines.
- `inversePairCancellation u v x`: delete the displayed adjacent
  `[x, inv x]`, assuming the residual word is a nonempty polygon word.  Split
  the PL proof into the two triangles incident to their common vertex and the
  complementary polygon.  Expected proof: 70–110 lines.
- `mergeRepeatedBlock u v t y z a`: replace
  `[y,z] ... [inv z,inv y]` by `[a] ... [inv a]`, with explicit freshness and
  occurrence hypotheses.  The pieces are the quadrilateral swept by the two
  consecutive sides and its complement.  Expected proof: 90–140 lines.
- `cutAndPaste u v t x`: the normal-form diagonal slide
  `u x v x t  ↦  u x x (inverseWord v) t`.  Cut between the two occurrences
  of `x`; define affine maps on the two closed triangles on opposite sides of
  the new diagonal, prove agreement on the diagonal, then descend them to the
  quotients.  Expected proof: 110–150 lines.

For the last three moves, if the implementation reaches 150 lines, split it
into: (1) affine formulas and boundary values, (2) quotient descent and
continuity, and (3) inverse identities.  Those helper lemmas must retain the
source and target words in their statements.

## Bridges

The bridge leaves are separate from the reusable moves.

1. `kleinSquare_bridge`: the radial square-to-disk homeomorphism, checked on
   each of four sides, identifies the closed-square Klein quotient with
   `PolygonSurface kleinWord`.
2. `crosscapTwo_bridge`: compare `aabb` directly with `SurfaceRel false 2`.
3. `t02A02_bridge`: compare the literal octagon relation with the list
   `a a b c c⁻¹ d⁻¹ b d⁻¹`.
4. `fourteenGon_bridge`: compare the literal t94J09 fourteen-gon relation with
   its displayed signed list.  The tunk01 bridge is obtained by its label
   equivalence, not by repeating the geometric proof.

The current file gives these bridge seats explicit names.  When moved into
the consumer modules, their `F`, label type, and word parameters are fixed to
the corresponding definitions; they are not extra hypotheses of the final
consumer theorem.

## Assemblies

All assembly lemmas are proved and contain no `sorry`:

- `kleinSquare_assembly` composes square bridge → word slide → `aabb` bridge.
- `t02A02_assembly` composes octagon bridge → cancellation stage → merge/slide
  stage.
- `fourteenGon_assembly` is the same three-link composition used independently
  for t94J09 and tunk01.

The only open declarations are the five geometric word moves and the four
consumer bridge leaves.  `homeomorph_trans` and all three assemblies are
closed proofs.

## Seat split: cancellation and cut-and-paste

The two formerly monolithic boundaries are now sorry-free assemblies.  Their
leaves do not call one another: any information shared between leaves is an
explicit hypothesis.

### Cancellation

- `inversePairCancellation_aux_zip_map` is the **LIBRARY** PL leaf (130--180
  lines after a prescribed-boundary fan triangulation tool exists): it constructs the honest
  slit-sector PL zip and proves `CancellationZipSpec`: continuity,
  surjectivity, preservation of boundary/interior, and injectivity on the
  interior, together with the boundary relation calculation.  These cannot
  soundly be separated until the explicit affine chart is a named definition:
  continuity/interior injectivity alone do not determine its boundary action.
  Do **not** use a radial extension of a folding circle map; that
  identifies whole radii.  Suggested Mathlib route: triangulate convex fans,
  use `Continuous.piecewise` (or `Continuous.if_le`) on closed half-planes,
  `continuous_const`, `continuous_subtype_val`, and affine-map continuity.
- `inversePairCancellation_aux_zip_interior` (45--70 lines, independent given
  `hc`) uses `wordRel_eqvGen_interior`, `hc.interior_iff`, and
  `hc.interior_injective`.  This also handles mixed boundary/interior pairs:
  such a relation is impossible unless both points coincide, contradicting
  the norm split.
- `inversePairCancellation_aux_zip_relation` (30--45 lines, independent given
  the two comparisons) splits on norm `< 1`; every disk point has norm `≤ 1`,
  so `¬ norm < 1` gives `norm = 1` by `le_antisymm`.

Degenerate checks: the target word cannot be empty because `hrest.1`; hence
the target fan has positive length.  The source has two extra edges.  At slit
endpoints the two affine formulas agree, and the endpoint equivalences are
already included by `EqvGen`; interior points have singleton classes.

### Cut-and-paste

- `cutAndPaste_aux_triangle_charts` is currently the single **LIBRARY** leaf
  (100--150 lines once a polygon/triangle PL toolkit is available).  It
  constructs both maps from `Fin 2 × Disk`, proves continuity and coverage,
  and performs the two directed boundary-fibre checks.  The natural reusable
  missing foundation is a theorem that a closed Euclidean triangle (and a
  finite convex polygon triangulated from a diagonal) is a quotient image of
  `Disk`, with prescribed oriented boundary arcs.  Mathlib tools to try are
  `Convex`, `AffineMap`, `ContinuousMap.piecewise`,
  `IsClosed.isClosedEmbedding_subtypeVal`, and
  `IsQuotientMap.of_surjective_continuous`; no SphereCap/LinearGraphMeasure
  import is permitted.
- `cutAndPaste_aux_relation_iff` (25--40 lines, independent) combines the two
  directed fibre statements.  `cutAndPasteParameterRel` names the old-picture
  pullback relation so the two direction proofs can be developed separately
  inside the library leaf without depending on each other.

The two copies of `Disk` are essential even when one of `u,v,t` is empty: a
zero-width boundary block merely collapses a run of polygon vertices and does
not remove either closed triangle.  Along the cutting diagonal the two chart
orientations are opposite.  On the new picture this accounts exactly for
`inverseWord v`; at diagonal endpoints all incident edge relations must be
taken in `EqvGen`, not just `WordRel`.  `hw.1` rules out an empty old polygon,
and `cutAndPaste_aux_span_aux_target_polygon` supplies the corresponding
nonempty/even target check.

Review (claude-14, 2026-10-14): `CancellationZipSpec.interior_iff` was unsatisfiable (zipped arcs map to an interior slit, so boundary ↛ boundary); replaced by `interior_maps` (interior → interior) and a one-sided `interior_injective` (p interior, c p = c q → p = q), which is what zip_interior needs.

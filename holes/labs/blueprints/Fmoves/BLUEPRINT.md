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

# Embedded circles in surfaces: triage of 2026-11-03

Every row below takes an arbitrary topological circle, so no smoothness may be added.
Blueprints from October call all of them blocked on one collar or Schoenflies foundation.
That is a claim about the blueprint's route, not about the problem.  t03J02 needs no homeomorphism
in its conclusion, which is why it escaped.

| row | state | what the conclusion really needs |
|---|---|---|
| t91J03 | closed 10-31 | planar crossing lemma on lifts to the strip |
| a96A07 | closed 11-03 | zero count and Borsuk's logarithm criterion |
| t98J02 | closed 11-03 | fibre count on one side of the lift; Klein bottle model |
| t03J02 | closed 11-03 | a homotopy pushout, via a cylinder in `X × ℝ` |
| t03J01 | open | global: a separating circle bounds; a nonseparating circle has a dual class |
| t01J01 | open | a homeomorphism to an annulus: Schoenflies-strength |
| t00A03 | open | homeomorphisms to pants: Schoenflies-strength plus classification |
| t00J05 | open | a homeomorphism to the standard cell: Schoenflies-strength |

The closed rows share one move: find a quantity that is locally constant off the curve and
control how it jumps at the curve.  That needs no information about the shape of the curve
beyond injectivity, so wildness never enters.

## t03J02 without a collar

An arbitrary curve gives no cheap open neighbourhood homotopy equivalent to a circle: the
neighbourhood deformation below moves points out of the neighbourhood.  So the cover is not on `X`.
Take `Cyl ⊆ X × ℝ`, the left torus at height -1, the right at 1, and the glued circle at every height
between.  The cover is `s < 1/2`, `s > -1/2`, and all its homotopies are linear in `s`.  `X` and
`Cyl` are homotopy equivalent by `x ↦ (E (x,1), B x)` and `fst`, where `E` is the glued deformation
and `B` a height function, in two linear stages.  This is a cofibration argument with the awkward
continuity case removed, since no reparametrisation by distance occurs.  About 2,300 lines in all, of
which about 1,200 were the existing van Kampen and Mayer-Vietoris consumers.

## t03J01 (no route found)

A count of this kind sees only local data.  Whether a retraction exists depends on whether the
curve bounds, which is a global fact about the fundamental class, so I found no count that decides it.

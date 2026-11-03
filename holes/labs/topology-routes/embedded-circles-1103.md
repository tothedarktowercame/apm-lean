# Embedded circles in surfaces: triage of 2026-11-03

Every row below takes an arbitrary topological circle, so no smoothness may be added.
Blueprints from October call all of them blocked on one collar or Schoenflies foundation.
That is a claim about the blueprint's route, not about the problem.

| row | state | what the conclusion really needs |
|---|---|---|
| t91J03 | closed 10-31 | planar crossing lemma on lifts to the strip |
| a96A07 | closed 11-03 | zero count and Borsuk's logarithm criterion |
| t98J02 | closed 11-03 | fibre count on one side of the lift; Klein bottle model |
| t03J02 | open | a homotopy pushout; see below |
| t03J01 | open | global: a separating circle bounds; a nonseparating circle has a dual class |
| t01J01 | open | a homeomorphism to an annulus: Schoenflies-strength |
| t00A03 | open | homeomorphisms to pants: Schoenflies-strength plus classification |
| t00J05 | open | a homeomorphism to the standard cell: Schoenflies-strength |

The closed rows share one move: find a quantity that is locally constant off the curve and
control how it jumps at the curve.  That needs no information about the shape of the curve
beyond injectivity, so wildness never enters.

## t03J02 without a collar (not started)

The current certificate asks for an open neighbourhood homotopy equivalent to a circle.  An
arbitrary curve does not give that cheaply, but the homology and fundamental group only need
the inclusion to be a cofibration.  Tietze into the plane and normalise gives a retraction
`r : N → J` from an open `N`; straight lines in the flat torus give a homotopy in `T` from the
inclusion of a smaller neighbourhood to `r`, fixing `J`.  With Urysohn that is an NDR pair, so
the glued space is homotopy equivalent to the double mapping cylinder, which has the open cover
the existing consumers want.  The homotopy stays in `T`, not in `N`, so `CompatibleOpenCover`
must move to the cylinder rather than be built on the quotient.  Estimate 800–1500 lines; this
is a guess, untested.

## t03J01 (no route found)

A count of this kind sees only local data.  Whether a retraction exists depends on whether the
curve bounds, which is a global fact about the fundamental class, so I found no count that decides it.

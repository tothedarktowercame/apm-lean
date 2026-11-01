# Proposal: embedded-circle normal forms on compact surfaces

This is a proposed shared foundation, not an implementation.  It is needed by
t00J05 and overlaps the missing geometric input recorded by t00A03, t01J01,
t03J01, t03J03, t03J05, t95J06, t97J02, t98J02, and t99J03.

The reusable API should not assume smoothness or tameness.  Its input is a
topological embedding `j : C(Circle, M)` into a topological 2-manifold.  It
should provide:

1. an annular collar of `Set.range j`, compatible with the given
   parametrisation;
2. a cut-surface construction with a quotient homeomorphism back to `M`;
3. connectedness/separation and boundary data for the cut surface;
4. classification of the compact cut components; and
5. extension across a disk of every circle reparametrisation used when
   transporting an attached-cell quotient.

For t00J05 the first consumer theorem is:

> If `j : C(Circle, Circle × Circle)` is an embedding and is not homotopic to
> a constant, then `AttachTwoCell.Cell j` is homeomorphic to
> `AttachTwoCell.Cell (fun z => (z, 1))`.

The intended proof first shows that the embedded essential curve is primitive,
cuts the torus to an annulus, classifies that annulus, and reglues.  The
homeomorphism must remember the boundary parametrisation so that the induced
homeomorphism of attached cells is an actual quotient-space map, not merely a
homotopy equivalence.

`ConstructionTargets/SurfaceSchoenflies.lean` currently proves closedness,
compact finite subcovers, and transport properties for an already supplied
local-flat structure.  It neither proves arbitrary embedded circles locally
flat nor constructs a global annular collar or cut surface.  Those are the
first missing layers of this proposal.

An alternative cover-theoretic API may lift an essential circle to an annular
or universal cover, but it still needs the planar theorem that the lifted line
separates and can be straightened equivariantly.  It is therefore another
presentation of the same foundation, not a route around Jordan--Schoenflies.

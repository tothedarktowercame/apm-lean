# Topology foundational programs

Date: 2026-08-27

This note defines bounded entry points for the shared topology projects found
by the dependency survey.  A program is not authorized to assume its final
consumer theorem; every milestone must compile and have independent consumers.

## Oriented-manifold fundamental classes and localization

Goal: connect the existing relative singular-chain and excision machinery to
local and global orientation classes of finite-dimensional manifolds.

First milestones:

1. compute local homology of the model pair at the origin (the
   one-dimensional case is banked in `3c96f98e`);
2. transport that computation through a homeomorphism of pairs (banked in
   `707efa05`), then construct the restricted boundaryless manifold chart pair
   and its deleted-point equivalence;
3. define a local orientation generator and prove overlap compatibility;
4. define the global fundamental class for compact connected oriented
   manifolds;
5. prove that its localization is the local orientation generator, hence that
   the top-homology localization map is monic in the required setting.

Do not begin with `t00J02`.  Initial consumers should be a sphere or Euclidean
model pair, followed by a punctured-manifold calculation.

## Manifold Sard and regular preimages

Goal: turn Mathlib's finite-dimensional Euclidean calculus and Jacobian
nullity results into reusable boundaryless-manifold statements.

Keep four interfaces separate:

1. chart invariance of coordinate-null sets;
2. Euclidean dimension-drop image nullity;
3. regular-value/submersion preimage manifolds with tangent kernel;
4. incidence projections for parametric and relative transversality.

The product-complement Euclidean dimension-drop theorem is banked in
`1f0a8882`, and arbitrary strict-finrank transport is banked in `20191b38`.
One-chart dimension-drop nullity and coordinate-change transport are banked in
`ce5839a7`; countable source/target chart-pair selection, exact range
decomposition, and local coordinate equations are banked in `fb05ffe9`.  The
`DifferentiableOn` dimension-drop theorem is banked in `7c2f83a6`, and
transport of countably many varying-chart null patches into a fixed target
chart is banked in `b4d6065f`.  Their composition for `C¹` manifold maps is
banked in `7e531b1d`, and the boundaryless fixed-chart positivity contradiction
is banked in `0193d098`.  The first consumer, frozen `t94J05`, is closed in
`3348f833` without changing its statement.  This branch applies only under
strict model-dimension drop; it does not address critical-value Sard.  The
first geometric milestone for that separate program remains a boundaryless
regular-preimage theorem, not full parametric transversality.

This program was the first strategy-informed build test.  The method survey
successfully separated an already-supported Euclidean nullity theorem from
four missing generic interfaces: subset differentiability, countable chart
selection, overlap transport, and the chart-local positivity contradiction.
Each became an independently compiled theorem, and their first consumer then
closed with a short specialization.  The result supports continuing to elect
small reusable interfaces before starting a monolithic foundational proof.

## Covering constructors

Goal: fill small closure gaps around Mathlib's `IsEvenlyCovered` and
fibre-bundle APIs.

Milestones:

1. product covering maps (banked in `935fc228`);
2. pullback/base-change covering maps using fibre-bundle pullbacks;
3. transport of quotient-cover data across action equivalences;
4. only later, equivariant gluing and classification.

The first three are generic constructors.  Gluing requires descent and cocycle
data and should not be disguised as a small adapter.

## Manifold integration and Stokes

Goal: support the concrete differential-form and sphere/ball integral
problems without adding assumed integral-value interfaces.

Milestones:

1. normalize Hausdorff measure on concrete unit spheres;
2. prove reusable sphere/ball coordinate moment formulas;
3. identify frozen tangent-projection surface integrals with a standard
   manifold or Hausdorff integration interface;
4. prove the required Stokes theorem and locality/naturality adapters.

Coordinate symmetry and polynomial exterior-derivative calculations already
exist.  The missing work is measure and integration theory, not more scalar
algebra.

## Cap, Thom, and intersection comparison

Goal: relate geometric transverse inverse images to homology and cohomology.

The experimental low-degree integral cap construction has been extracted as
the standalone canonical module `SingularCapLowDegree` in `408be02b`.  General
comparison work must still wait for:

- manifold fundamental classes;
- regular-preimage orientations;
- singular cochains and general cup/cap naturality;
- Thom or coorientation classes.

The desired eventual theorem identifies the fundamental class of a transverse
preimage with the cap of the ambient fundamental class and a pulled-back dual
or Thom class.  Conditional `Producer` structures are specifications of this
theorem, not implementations.

## Election rule

A foundational program is ready for sustained implementation only when:

1. its first theorem is independent of every final problem;
2. at least two concrete consumers are identified;
3. the required Mathlib substrate has been inspected;
4. the first milestone has an explicit stop condition;
5. canonical ownership, review, and axiom-audit procedures are assigned.

In addition, every sustained program should aim to certify its infrastructure
by closing at least one named problem or frozen branch.  The reusable theorem
must remain independent of that consumer, but the program is not considered
successful merely because a sequence of ConstructionTargets compiles.

If immediate closure is impossible, the program note must record:

- the intended first consumer;
- the exact remaining specialization or missing theory;
- why that remainder is not equivalent to the final theorem;
- the condition under which work stops instead of producing another adapter.

The dimension-gap program is the reference example: its generic chain closed
`t94J05` in `3348f833`.  A full t00J02 producer, critical-value manifold Sard
theorem, or generic covering-space gluing theorem is not yet a bounded first
milestone until a comparable consumer path is identified.

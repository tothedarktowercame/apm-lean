# t97A03 closure blueprint

Reviewed source: `holes/labs/blueprints/t97A03/BLUEPRINT.md` and its compiled
companion `Blueprint.lean`.

## Frozen target

Close the registered theorem `apm_t97a03` without changing its statement or
the definitions it uses.  The source theorem concerns connected two-sheeted
covers of the quotient obtained by attaching the north and south poles of a
sphere to two distinct points of a circle.  Its total space must be one of two
literal quotient models and must have integral homology ranks `1, 3, 2`, zero
higher homology, and fundamental group `FreeGroup (Fin 3)`.

The hypotheses `A ≠ B`, connectedness, and fiber cardinality two exclude the
degenerate and disconnected cases.  The proved source helpers
`apm_t97A03_surjective_of_fiber_card_two` and
`apm_t97A03_fiber_equiv_fin_two` provide surjectivity and labeled fibers.

## Reused foundations

Move the blueprint's already proved definitions, attachment equalities, fiber
lemmas, and final conjunction assembly into `t97A03Closure.lean` unchanged in
meaning.  Reuse these compiled modules:

* `ConstructionTargets.SuppliedCoverAlgebra` for the supplied cover's induced
  fundamental-group range;
* `ConstructionTargets.FiniteIndexFreeGroupSchreierRank` for the index-two
  subgroup rank calculation;
* `ConstructionTargets.PointWedgeVanKampen` for point-wedge fundamental groups;
* `ConstructionTargets.ProductionOpenCoverMayerVietoris`,
  `ConstructionTargets.SphereHomology`, and
  `ConstructionTargets.CircleSingularHomology` for model homology.

Do not reconstruct covers from arbitrary subgroups: this theorem classifies a
cover supplied in its hypotheses.

## Library milestone 1: cover classification

`apm_t97A03_classify_connected_double_cover` states that every connected
two-sheeted cover of the literal base is homeomorphic to either
`OneCircleCover` or `TwoCircleCover`.

Split the inverse image of the simply connected sphere into two sheets, label
the sheets over one pole, and lift the two complementary circle arcs.  Each
lift either preserves or swaps the label.  Connectedness excludes the
simultaneously trivial pair.  The patterns `(1,0)` and `(0,1)` differ by
interchanging the arcs and yield the one-circle model; `(1,1)` yields the
two-circle model.  Descend the piecewise equivalences through the literal
`EqvGen` quotients and prove the resulting bijective local homeomorphism is a
homeomorphism.

This milestone depends only on the frozen definitions and proved fiber
helpers.  Expected size: 800--1600 lines.

## Library milestone 2: model invariants

`apm_t97A03_invariants_of_model` takes a homeomorphism to either literal model
and returns the required homology groups and pointed fundamental group.

Construct quotient-compatible neighborhoods of the two sphere sheets and
lifted circle pieces.  Mayer--Vietoris reduces homology to the cellular count:
four vertices, six edges, and two null-boundary two-cells.  Hence the connected
one-skeleton has cycle rank three, the two cells give two independent
degree-two classes, and higher homology vanishes.  Van Kampen, equivalently a
deformation to two spheres wedged with three circles, gives `FreeGroup (Fin 3)`.
Transport both calculations across the supplied homeomorphism and change the
basepoint using connectedness.

This milestone depends on the frozen definitions and the reused foundations,
not on the classification milestone.  Expected size: 1500--3000 lines.

## Assembly order and checks

The two library milestones may be developed independently.  Once both are
proved, copy the blueprint's compiled assembly: classify the supplied cover,
feed that disjunction to the invariant theorem, and assemble the registered
conjunction in `problems/t97A03/lean/Main.lean`.

Every implementation job must remain within the row scope, introduce no
axioms beyond `propext`, `Classical.choice`, and `Quot.sound`, preserve the
statement registry, and pass the closure build plus the registered Main file.

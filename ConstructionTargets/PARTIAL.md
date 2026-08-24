# Partial construction targets

These modules are landed deliberately so later work can resume from their
exact boundary, but they are not imported by `ConstructionTargets.lean`.
Importing the roll-up therefore exposes only sorry-free construction targets.

`ConstructionTargets.CircleSingularHomology` is production rather than
partial: it is imported by the roll-up, and its paired seam document and
`problems/t01A03/targets.edn` record the concrete circle audit boundary.

| Module | Lean `sorry` count | Remaining boundary |
|---|---:|---|
| `ConstructionTargets.T02A06HomologyScaffold` | 3 | The file is “deliberately exploratory.” Its theorem-layer holes are the positive-degree sphere suspension shift, the circle base-class isomorphism, and degree-one vanishing above the sphere dimension. |
| `ConstructionTargets.T02A06SphereShiftStandalone` | 0 | The file “deliberately contains no axiom, theorem placeholder, or `sorry`.” It records the target type and checks the available algebraic inputs; the missing boundary is the geometric hemisphere/subdivision comparison needed to construct the shift. |

The counts above count Lean `sorry` commands, not occurrences of the word in
comments. In particular, the standalone module's only textual occurrence says
that it contains no `sorry`.

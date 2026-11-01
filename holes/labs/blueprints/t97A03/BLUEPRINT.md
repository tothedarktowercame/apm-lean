# Blueprint for t97A03

## Reconciliation and triage

Verdict: **true and faithful; `Main.lean` was the authoritative advanced
state**.

The registered `problems/t97A03/lean/Main.lean` had 1,847 lines and three
admissions.  The old blueprint had 184 lines and two library-scale admissions,
so this blueprint was first replaced by the registered file.  That preserves
the already-proved literal quotient geometry, complementary arc loops,
two-generator normal forms, aligned fundamental-group equivalences, covering
monodromy algebra, and finite model selector.  The registered declarations and
the statement of `apm_t97a03` are unchanged; only new declarations and proof
assemblies were added.

The source asks for all connected two-fold covers of the sphere/circle
adjunction and their invariants.  The frozen statement gives the two literal
`EqvGen` models, integral singular homology ranks `1,3,2`, higher
vanishing, and fundamental group `F₃`.  The hypotheses `A ≠ B`, connected
total space, covering map, and two-element fibres exclude the collapsed-pole,
empty, disconnected trivial-cover, and wrong-degree cases.

## Cheapest existing route

The copied registered file already does most of the algebraic classification:
it fixes two literal loops, proves their signed-word generation through an
aligned `F₂` presentation, defines their covering transports, and imports the
sorry-free finite two-permutation classifier in
`ConstructionTargets.t97A03Closure`.  The remaining classification work is
therefore geometric: turn the selected endpoint permutations into a
homeomorphism of the supplied cover with the matching literal quotient.

For invariants, a fresh cellular/Mayer–Vietoris calculation on each quotient is
unnecessary.  Both models collapse a contractible connecting arc and have the
homotopy type of the same nested point wedge: two copies of `S²` and the
existing `ThreeCircles`.  The bank already contains:

* `PointWedgeVanKampen.genericPointWedgeLegCoordinatesEquiv` and
  `PointWedgeVanKampen.threeCirclesFundamentalGroupEquiv`;
* `PolygonSurfaceHomology.pointWedgeHigherHomologyIsZero` and the generic
  point-wedge Mayer–Vietoris infrastructure;
* `SphereHomology.sphereModuleTopHomologyIsoInt` and off-degree vanishing;
* the finite-circle-wedge homology and path-connectedness results.

Thus only the two literal quotient collapses are model-specific.  Every
homology degree and `π₁` is computed once on `apm_t97A03_modelWedge`.

## Leaf table

All leaves are top-level theorems whose complete body is `sorry`.  The two
old bridge names and `apm_t97a03` are assemblies.

| Order | Leaf | Work / tools | Lines | Depends on |
|---:|---|---|---:|---|
| 1 | `apm_t97A03_classify_aux_oneCircleMonodromy` | Finite `Fin 2` permutation normalization using `finTwoPerm_bool_normalForm`; exactly one nontrivial transport becomes the one-circle pattern. | 35–60 | nontrivial literal transport; negated both-swap predicate |
| 2 | `apm_t97A03_classify_aux_literal_transport_nontrivial` | Use connected-cover moved monodromy, the proved aligned literal `F₂` normal form, and `literal_transport_moved_of_generated`. | 80–120 | cover hypotheses |
| 3 | `apm_t97A03_invariants_aux_modelWedge_h0` | Path connectedness plus `CoefficientH0.h0Iso`, or point-wedge H₀ MV. | 35–60 | fixed wedge |
| 4 | `apm_t97A03_invariants_aux_modelWedge_high` | Repeated `pointWedgeHigherHomologyIsZero`, sphere and finite-circle-wedge vanishing. | 60–90 | fixed wedge |
| 5 | `apm_t97A03_invariants_aux_modelWedge_piOne` | Two applications of generic point-wedge van Kampen, sphere simple connectivity, `threeCirclesFundamentalGroupEquiv`, and basepoint change. | 80–120 | fixed wedge |
| 6 | `apm_t97A03_invariants_aux_modelWedge_h1` | Point-wedge MV/Hurewicz; only the three-circle summand contributes, with its fixed `Fin 3` basis. | 80–120 | fixed wedge |
| 7 | `apm_t97A03_invariants_aux_modelWedge_h2` | Two sphere top classes via `sphereModuleTopHomologyIsoInt` and point-wedge MV. | 90–130 | fixed wedge |
| 8 | `apm_t97A03_invariants_aux_transport` | Transport homology through `singularHomologyIsoOfHomotopyEquiv`; transport based `π₁` using the equivalence homotopy and basepoint path. | 70–110 | all fixed-wedge invariant facts |
| 9 | `apm_t97A03_invariants_aux_oneCircle_homotopyEquiv` | Collapse the contractible connector using `PointWedgePointedContractionDescent` and quotient homotopy descent. | 120–150 | one-circle quotient |
| 10 | `apm_t97A03_invariants_aux_twoCircle_homotopyEquiv` | Collapse one spanning arc and identify the remaining three loops and two sphere sheets with the fixed wedge. | 120–150 | two-circle quotient |
| 11 | `apm_t97A03_classify_aux_oneCircle_homeomorph` | Trivialize sphere sheets, lift normalized complementary arcs, descend through `OneCircleRel`, and use covering-lift uniqueness for inverse laws. | 120–150 | one-circle monodromy |
| 12 | `apm_t97A03_classify_aux_twoCircle_homeomorph` | The analogous two-circle quotient descent when both literal transports swap. | 120–150 | two-circle monodromy |

Estimated total: **1,010–1,410 proof lines**.  No leaf is estimated above 150,
and the whole remaining program is below 2,000 lines.  The classification
realization leaves are at the upper bound and are the least certain estimates.

## Dependency layers

* **Layer 1, parallel:** literal-transport nontriviality; both model-wedge
  homotopy equivalences; all five fixed-wedge invariant computations.
* **Layer 2, parallel:** one-circle monodromy normalization; invariant transport
  (it takes all invariant results as explicit inputs).
* **Layer 3, parallel:** one-circle and two-circle homeomorphism realizations.
* **Layer 4:** sorry-free classification and invariant bridge assemblies.
* **Layer 5:** sorry-free `apm_t97a03` conjunction assembly.

The model-homeomorphism leaves receive exact monodromy predicates; they do not
re-run the finite selector.  The transport leaf receives every computed
invariant explicitly and does not depend on sibling sorries through a
definition.

## C1–C10 record

* **Literal transport nontrivial:** C1 connected two-sheet monodromy is
  transitive; C2 nontriviality is derived, not assumed; C3 only generation to
  the two fixed loops remains; C4 the two loops generate all signed words; C5
  uses the exact registered transports; C6 retains all cover hypotheses; C7
  transports are permutations of the literal fibre; C8 disconnected zero
  monodromy is excluded by `ConnectedSpace Y`; C9 is strictly below the old
  classification bridge; C10 matches.
* **One-circle monodromy:** C1 every nonidentity `Fin 2` permutation is swap;
  C2 conclusion is not among hypotheses; C3 finite algebra only; C4
  nontrivial-and-not-both partitions the cases; C5 exact literal transports
  are retained; C6–C7 no topology or cast is weakened; C8 identity/identity is
  excluded; C9 not the ancestor; C10 matches.
* **One-circle homeomorphism:** C1 the exactly-one-swap gluing is the literal
  one-circle model; C2 the hypothesis records monodromy, not a homeomorphism;
  C3 only geometric realization remains; C4 handles both choices of swapped
  arc; C5 sheet labels and exact loops reach quotient attachments; C6 keeps
  `A ≠ B` and cover degree; C7 coinduced quotient topologies are used; C8
  pole and arc endpoints are included; C9 not the old full classifier; C10
  matches.
* **Two-circle homeomorphism:** C1 both swaps give the crossed two-circle
  attachment; C2–C3 as above; C4 all four endpoint identifications occur; C5
  exact sheet labels reach `TwoCircleRel`; C6–C7 retain the literal cover and
  topology; C8 both poles and both sheets checked; C9 not the ancestor; C10
  matches.
* **One-circle collapse:** C1 collapsing a contractible connector preserves
  homotopy type; C2 no invariant is assumed; C3 only one quotient homotopy;
  C4 all attachment points map to the wedge point; C5 the target is the fixed
  wedge used downstream; C6 no stronger source assumption; C7 actual
  `EqvGen` topology; C8 connector endpoints remain fixed; C9 not the old
  invariant bridge; C10 matches.
* **Two-circle collapse:** C1 one spanning arc is a tree edge; C2–C3 as above;
  C4 the three remaining cycles are all represented; C5 exact fixed wedge;
  C6–C7 literal quotient retained; C8 both sheet vertices remain connected;
  C9 not the ancestor; C10 matches.
* **Wedge H₀:** C1 connected nonempty wedge has H₀ = ℤ; C2 no connectedness
  result is passed as the answer; C3 one degree only; C4 nested wedge handled
  twice; C5 exact homology carrier; C6 integral coefficients; C7 degree zero;
  C8 explicit wedge point prevents emptiness; C9 not ancestor; C10 matches.
* **Wedge H₁:** C1 two spheres contribute zero and three circles contribute
  rank three; C2 basis is computed; C3 one degree; C4 both wedge stages;
  C5 fixed `Fin 3` target; C6 integral coefficients; C7 no natural
  subtraction; C8 sphere simply-connectedness includes the standard S²;
  C9 not ancestor; C10 matches.
* **Wedge H₂:** C1 each S² contributes one class; C2 classes are not assumed;
  C3 one degree; C4 both sphere summands included; C5 exact `Fin 2` target;
  C6 integral coefficients; C7 degree two; C8 circle summands vanish here;
  C9 not ancestor; C10 matches.
* **Wedge higher:** C1 all summands vanish above two; C2 no restated
  conclusion; C3 one generic degree; C4 induction has both nested wedge
  stages; C5 exact carrier; C6 integral coefficients; C7 hypothesis `3 ≤ n`
  avoids subtraction errors; C8 boundary degree three checked; C9 not
  ancestor; C10 matches.
* **Wedge π₁:** C1 free product of two trivial groups and `F₃` is `F₃`;
  C2 group is computed; C3 van Kampen only; C4 both wedge stages; C5 arbitrary
  consumer basepoint is handled; C6 exact based fundamental group; C7
  `FreeGroup (Fin 3)`; C8 wedge point and arbitrary point both covered; C9
  not ancestor; C10 matches.
* **Invariant transport:** C1 homotopy equivalence preserves singular homology
  and π₁; C2 computed facts are explicit inputs, not bundled as the conclusion;
  C3 transport only; C4 all five outputs supplied; C5 the supplied equivalence
  is the one assembled from the literal model; C6 no new hypotheses; C7
  orientation of the equivalence is `Y ≃ₕ modelWedge`; C8 arbitrary
  basepoint `y`; C9 strictly below the old invariant bridge; C10 matches.

## Verification

`python3 scripts/statement-registry.py check t97A03` reports:

```text
1 registered statements match, 0 do not
```

The required locked compile was queued, but did not acquire the lock: the
preceding `t98A04` Lean process remained the lock holder for more than nine
minutes (about 6.5 GB RSS and mostly sleeping).  It was not terminated because
it belongs to another seat.  Consequently no compiler error count,
sorry-warning count, or fresh `#print axioms` output is claimed here.

## Review (claude-14, 2026-11-01)

Skeleton by codex-6, compiled by me after fixes: `modelWedge` needed `abbrev` for its topology, and the `rcases` pattern needed a second level. 12 leaves, 0 errors, registry matches.

Doubt on `_oneCircle_homotopyEquiv`, `_twoCircle_homotopyEquiv`: each sphere carries two attachment points, N and S. Collapsing arcs alone does not give a one-point wedge: an attachment point has to slide along the sphere, which is a homotopy of the attaching map, not a quotient. Expect these two to exceed 150 lines and to need splitting. The ranks check: 4 edges over 2 sphere vertices gives rank 3 in both models.

## Held leaves (claude-14, 2026-11-01)

`_classify_aux_literal_transport_nontrivial` came back with a real gap: the docstring's "aligned literal fundamental-group equivalence" does not exist. `apm_t97A03_collapsePiOneHom` is not known injective, so nothing shows the two literal loops generate the monodromy. The honest routes are (a) direct: if both literal transports are trivial, glue a sphere lift and two arc lifts into a global section through the `EqvGen` quotient, whose clopen image contradicts connectedness and degree two; or (b) van Kampen for the base. Route (a) is the same gluing the two `_homeomorph` leaves need, so those three leaves share one construction that should be written first as a sheet-data lemma. Together with the two `_homotopyEquiv` leaves (attachment-point sliding), this is the expensive part, likely well above the skeleton's 1010-1410 line total.

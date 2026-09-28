# Topology routes (2026-09-28) — the loops' guide

Replaces `TOPOLOGY-DEPENDENCY-DAG.md` as the source of elections. That file named 31 of the
open problems and let two chains grow for weeks without touching a `sorry`
(`/home/joe/topo-watch/dag-audit.md`). Every row below is a problem whose statement is in the
approved registry (`problems/STATEMENTS.json`) and still has a `sorry`.

Per-problem routes (what each `sorry` needs, reusable banked declarations, ordered steps,
doubts) are in `holes/labs/topology-routes/routes-{1,2,3}.md`, written by read-only Claude
reviewers who compiled probes where they could. Seventeen problems they found closable were
landed directly on 2026-09-28.

## Election rules (each strategy checkpoint)

1. Only the problems in this loop's own list below (Joe, 2026-09-28: topo1 = the 12 DIRECT/ADAPTER
   problems, topo2 = the 15 FOUNDATION problems; the 33 HEAVY problems are not assigned to a loop).
2. topo1: DIRECT first, then ADAPTER, closing problems one at a time. topo2: infrastructure steps
   shared by two or more of its problems first (by the routes' shared tags), then each problem's
   remaining steps; build a step only at the generality its named problems use. Never elect generality beyond what the named
   route step needs.
3. Every work row names the problem, the `sorry` and the route step it supplies. A row that
   does not shorten a route in `routes-*.md` is not elected.
4. Apply the stop-after-two rule per problem: two consecutive rows that do not reduce that
   problem's `sorry` count or complete a listed route step end work on it until a Claude
   reviewer re-routes it; record that in the finding.
5. If a route step turns out false or unbuildable, STOP with the evidence (a compiled
   counterexample where possible). Never change a registered statement.

## Problems


### topo1 — DIRECT and ADAPTER (12)

| id | class | shared tags |
|---|---|---|
| t01A01 | ADAPTER | projective-quotient-descent, sphere-lift-to-circle (maps from simply connected spaces to Circle lift to ℝ), nullhomotopic-trivial-pi1 |
| t02A05 | ADAPTER (statement fixed to μHE[2], daa1d8ad; re-graded faithful) | euclidean-hausdorff-normalisation (i.e. the isodiametric constant). The same issue affects `t01J06, which also integrates against `μH[2]` on a sphere. |
| t91J06 | ADAPTER | — |
| t92J08 | ADAPTER | manifold-uniform-local-flow |
| t93J06 | DIRECT | — |
| t94A07 | ADAPTER | — |
| t94A09 | DIRECT | in ConstructionTargets, and import it from t93J06 and t94A09) |
| t94A10 | ADAPTER | periodic-stokes-square |
| t95J02 | ADAPTER | — |
| t97A07 | ADAPTER | regular-points-open` (t92J07 and t98A06 also state `Surjective (mfderiv …)` conditions; I did not check whether they need steps 1–2) |
| t99J04 | ADAPTER | manifold-inverse-function-theorem |
| t99J06 | ADAPTER | — |

### topo2 — FOUNDATION (15)

| id | class | shared tags |
|---|---|---|
| t00J01 | FOUNDATION | klein-bottle-homology, circle-reflection-degree-H1, quotient-surface-charts` (shared with t00A02's action quotient), mayer-vietoris-open-cover` (banked) |
| t00J07 | FOUNDATION | van-kampen-two-open-cover, rp2-fundamental-group, rp2-homology, circle-power-degree-H1, disk-attachment-punctured-retraction, quotient-by-finite-free-action-covering` (t00A02), mayer-vietoris-open-cover` (banked) |
| t00J08 | FOUNDATION | nielsen-schreier-rank-formula |
| t01A02 | FOUNDATION | punctured-torus-H2-vanishing, torus-map-integer-matrix-lift, planar-bounded-perturbation-surjective |
| t01A04 | FOUNDATION | eqvgen-quotient-covering-map (with t00A02), two-sheet-monodromy-character (with t97A03), wedge-pi1-inclusion-naturality, cut-point-count-invariant |
| t02A02 | FOUNDATION | polygon-quotient-t2, polygon-word-quotient-classes, polygon-cut-paste-homeomorph |
| t02A03 | FOUNDATION | explicit-r3-tube-deformation-retraction, homotopy-equiv-gluing-lemma |
| t91J03 | FOUNDATION | planar-crossing-lemma, circle-h1-degree |
| t93A06 | FOUNDATION | torus-quotient-smooth-atlas, periodic-stokes-square |
| t94A08 | FOUNDATION | projective-affine-chart-homeomorph |
| t95A04 | FOUNDATION | rp-smooth-atlas, immersion-from-injective-mfderiv |
| t96A07 | FOUNDATION | rp-smooth-atlas |
| t96J02 | FOUNDATION | polygon-surface-open-cover, polygon-puncture-retract, wedge-of-circles-pi1, van-kampen-simply-connected-piece, polygon-boundary-word (all together = polygon-surface-pi1; shared with t97A01, t92J05, t94J04, t97A03) |
| t97A04 | FOUNDATION | mv-connecting-naturality` (would also give induced maps on H₂ for t96J06-style torus and product problems), torus-pi1-winding-coordinates |
| t98A03 | FOUNDATION | rp2-double-cover-and-pi1, wedge-covering-construction, wedge-van-kampen-instance (template: TorusCircleWedge), wedge-point-not-manifold, wedge-basepoint-homogeneity |

### Unassigned — HEAVY (33)

| id | class | shared tags |
|---|---|---|
| t00A02 | HEAVY | quotient-by-finite-free-action-covering` (steps 1–3; also t00J01 Klein charts), wedge-cover-gluing, surface-classification, euler-characteristic-covering-multiplicativity, homology-orientability |
| t00A03 | HEAVY | schoenflies-2d, surface-classification, simple-curve-homotopy-isotopy` (Baer–Epstein), homology-orientability, euler-characteristic-cut-additivity, mayer-vietoris-open-cover` (banked) |
| t00J02 | HEAVY | manifold-fundamental-class` (t98A02), local-degree-signed-count, transverse-preimage-submanifold, circle-degree-signed-count, sard-regular-value` (partly banked) |
| t01A03 | HEAVY | circle-wedge-van-kampen, torus-pi1-abelian, surface-curve-collar (Schoenflies-type tameness; also cited by the audit for t00A03 and t98A02) |
| t01A08 | HEAVY | manifold-sard-general-model, sard-convex-domain (corners part only; possibly shared with t01J04/t96J05, which the DAG lists as Sard uptake) |
| t01J01 | HEAVY | surface-schoenflies-tameness, surface-mod2-intersection-pairing, surface-cut-and-classify, orientation-from-top-homology, invariance-of-domain-dim2 (overlaps with t00A03/t99J03 surface rows, which the audit already flags as needing Schoenflies) |
| t02A04 | HEAVY | lefschetz-fixed-point-compact-polyhedron, cell-attachment-open-cover-mv, coefficient-q-mayer-vietoris |
| t03J02 | HEAVY | embedded-circle-collar-surface (jordan-schoenflies), van-kampen-open-cover, mayer-vietoris-open-cover (exists), torus-fundamental-group, connected-h0 |
| t03J03 | HEAVY | covering-trivial-over-disk, polygon-cover-descent, polygon-cut-and-paste-homeomorph, polygon-surface-homology, covering-monodromy-character, surface-local-homology-orientation, invariance-of-domain-dim2 |
| t91A02 | HEAVY | covering-trivial-over-disk, polygon-cover-descent, polygon-complex-euler-characteristic (≈ polygon-surface-homology) |
| t91J05 | HEAVY | surface-classification, polygon-quotient-covering, covering-euler-characteristic, polygon-cut-and-paste-homeomorphism |
| t92J05 | HEAVY | antipodal-sphere-cover (with t00A02), simply-connected-cover-fiber-bijection, surface-classification, surface-singular-homology, seifert-van-kampen-cell-attachment, wedge-of-circles-free-group |
| t92J06 | HEAVY | wedge-quotient-covering-gluing (with t01A04, t98A03, t97A03), graph-cut-point-invariant, infinite-tree-simply-connected, wedge-of-circles-free-group (only on the alternative route to (a)) |
| t93J03 | HEAVY | deck-group-fundamental-group, covering-lifting-criterion, polygon-quotient-identification |
| t94J04 | HEAVY | surface-classification, covering-subgroup-correspondence, euler-characteristic-covers |
| t94J09 | HEAVY | polygon-surface-homology, polygon-cut-and-paste |
| t95J06 | HEAVY | free-circle-action-slice, surface-homology-invariants |
| t96A01 | HEAVY | van-kampen-amalgamated, surface-classification, covering-subgroup-correspondence, euler-characteristic-covers |
| t96A02 | HEAVY | lefschetz-fixed-point-theorem, polygon-quotient-identification, rp-rational-homology |
| t96A06 | HEAVY | rp-rational-homology, sphere-map-degree, projective-covering-sphere |
| t96J06 | HEAVY | manifold-fundamental-class-mod2-with-boundary, kunneth-cross-product, projective-plane-homology-mod2, intersection-pairing |
| t97A01 | HEAVY | polygon-surface-open-cover, polygon-puncture-retract, wedge-of-circles-pi1, wedge-of-circles-homology, van-kampen-simply-connected-piece, polygon-boundary-word, polygon-surface-mv-homology |
| t97A03 | HEAVY | covering-classification-explicit` (also named by t94J04, t01A04, t93A03, t00J08), van-kampen-iterated-free-rank, quotient-deformation-retraction, quotient-space-mayer-vietoris |
| t97A05 | HEAVY | tubular-neighbourhood, hypersurface-separation-bounds, transversality-perturbation, compact-one-manifold-classification, manifold-with-boundary, intersection-homotopy-invariance |
| t97A06 | HEAVY | manifold-form-calculus` (also t98J06, t93A06, ManifoldIntersectionTargets), form-extension-partition-of-unity, smooth-homotopy-approximation, de-rham-homotopy-formula, manifold-top-form-integration, stokes-compact-manifold |
| t97J02 | HEAVY | polygon-quotient-manifold-charts, surface-classification, surface-triangulation, euler-characteristic-finite-cover, orientation-double-cover, polygon-permutation-cover |
| t98A02 | HEAVY | manifold-homology-local-to-global, manifold-fundamental-class, mayer-vietoris-open-cover, ball-complement-collar, wild-embedding-anr |
| t98A06 | HEAVY (part b) / ADAPTER (part a) | smooth-flow-initial-condition-dependence, compact-manifold-complete-flow, submersion-local-right-inverse |
| t98J01 | HEAVY (part a) / ADAPTER (part b) | circle-product-mayer-vietoris (or rational-kunneth), trace-additivity-short-exact, rational-sphere-homology-with-reflections, circle-map-degree |
| t98J02 | HEAVY (conjunct 1) / ADAPTER (conjuncts 2, 3) | surface-curve-collar (Schoenflies/Jordan for topological curves; shared with t00A03 per the audit), surface-charts-from-covering-quotient |
| t99J01 | HEAVY | fundamental-group-wedge-of-circles, van-kampen-two-open-group, covering-subgroup-index, schreier-index-formula, explicit-graph-cover-construction |
| t99J05 | HEAVY | rational-homology-cpn, coefficient-open-cover-mayer-vietoris, rational-sphere-homology, projective-quotient-charts (step 1–2 also useful to t96A06's RP3 map), lefschetz-trace-bookkeeping (t98J01, t96A06 use the same `HasLefschetzNumber`) |
| tunk01 | HEAVY | polygon-cut-and-paste-homeomorphism, polygon-quotient-hausdorff (shared with t94J09, t98A01, t97J02 and any polygon-surface classification problem) |

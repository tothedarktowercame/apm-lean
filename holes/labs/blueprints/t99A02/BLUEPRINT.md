# Blueprint for t99A02: universal covers of RP²∨RP² and S¹∨RP²

The statement was repaired and admitted on 2026-10-15 (d4eafe905, 9f0831d08) and
graded faithful and TRUE (`statement-registry/t99A02-cover-grade.md`).
`Blueprint.lean` has the frozen definitions and theorem, byte-identical to
`problems/t99A02/lean/Main.lean`. The assembly is sorry-free and rests on
31 leaves. The earlier attempts, which stated π₁ and presentations, are in
`old-2026-10-15/` and are background only.

## Verdict

The statement is true. I checked by hand that the leaves hold (see "Checks"
below).

## Route

1. **RP² cover.** `rp2Proj : S² → Surface false 1` is an explicit map:
   `diskOf x = x₀ + i x₁` when `x₂ ≥ 0`, and `-(x₀ + i x₁)` otherwise.
   Leaf `rp2Proj_factor` builds a homeomorphism `S²/± ≃ₜ Surface false 1`
   from two lifts. The antipodal quotient map is a covering; that proof is
   copied, already proved, from the t00A02 blueprint. From these follow,
   all proved: `rp2Proj_isCoveringMap`, `_eq_iff`, `_neg`, `_surjective`,
   `_north`, `_south` and `_eq_base_iff`.
2. **Covering maps.** Both covers are quotient maps by a deck group acting
   upstairs:
   - `D∞ = DihedralGroup 0` acts on `ℤ × S²`. `r i` translates by `2i`;
     `sr i` sends `(n, x)` to `(-2i - n, -x)`.
   - `G` acts on `(G × I) ⊕ (G × S²)` by left multiplication.

   The generic leaf `isCoveringMap_quotLift_of_deck` uses Mathlib's
   `IsQuotientCoveringMap`. Its inputs are:
   - an upstairs quotient map;
   - fibres that are orbits modulo the relation;
   - for every point, an open saturated neighbourhood whose translates are
     disjoint.

   No Hausdorff or proper-discontinuity hypothesis is needed.
3. **Simple connectivity.** Both spaces get a `TreeCover`: an open cover by
   simply connected sets whose intersection pattern is a rooted tree.
   - The pieces are "stars": images of saturated opens that contract
     upstairs. The generic leaf is `isSimplyConnected_image_of_contraction`;
     the contraction is the explicit `spherePush`, plus a linear shrink on
     edges.
   - The chain uses stars `sphere n \ {S} ∪ sphere n+1 \ {N}`, and the tree
     is a path.
   - The tree uses vertex stars (two half-open edges plus a sphere minus the
     far pole). The tree is the Cayley graph of `ℤ * ℤ/2` on `{a, a⁻¹, b}`.
   - `TreeCover.simplyConnectedSpace` adds stars depth by depth, gluing
     along path-connected overlaps (two-set van Kampen), and then takes a
     directed union.
   - S² being simply connected is not needed. It exists anyway as
     `euclideanSphere_simplyConnected 2` in `SimplyConnectedSphereProducts`.

## Leaves

The 10 leaves marked G are generic and reusable. Sizes are estimated lines
of proof.

| leaf | content | size |
|---|---|---|
| `sphere_compl_poles_isPathConnected` (G) | S² minus both poles is path connected (stereographic; copy the `hoverlap` step of `simplyConnectedSpace_sphere_of_pole`) | 50 |
| `rp2Proj_factor` (G) | `S²/± ≃ₜ Surface false 1`, compatible with `rp2Proj` | 150 |
| `isCoveringMap_quotLift_of_deck` (G) | deck-group criterion for coverings out of `RelationQuotient` | 120 |
| `isSimplyConnected_image_of_contraction` (G) | a saturated open set that contracts upstairs has a simply connected image | 130 |
| `isSimplyConnected_union` (G) | ambient two-open van Kampen (from `simplyConnectedSpace_of_union_eq_univ`) | 70 |
| `isSimplyConnected_iUnion_of_directed` (G) | directed unions of open simply connected sets | 80 |
| `isSimplyConnected_union_iUnion_of_pairwiseDisjoint` (G) | attaching a disjoint family | 80 |
| `TreeCover.simplyConnectedSpace` (G) | trees of simply connected opens | 110 |
| `spherePush_continuousOn` (G) | push toward `p` is continuous off `-p` | 50 |
| `spherePush_spec` (G) | push identities (endpoints, fixes `p`, avoids `-p`, odd under negation) | 90 |
| `chainF_rel` | `chainF` respects `ChainRel` | 25 |
| `chainF_smul` | `chainF` is `D∞`-invariant | 25 |
| `chainF_isQuotientMap` | open surjection composed with the wedge quotient | 60 |
| `chainF_fiber` | fibres are orbits (parity case analysis) | 130 |
| `chain_local_junction` | disjoint-translate neighbourhood at a junction | 90 |
| `chain_local_regular` | the same at a non-pole point | 80 |
| `chainPiece_open_saturated` | chain star open and saturated | 35 |
| `chainPiece_isSimplyConnected` | chain star contracts | 100 |
| `chainPiece_inter` | stars meet only when adjacent; adjacent overlap is an annulus | 80 |
| `treeF_rel` | `treeF` respects `TreeRel` | 25 |
| `treeF_isQuotientMap` | sum of quotient maps composed with the wedge quotient | 80 |
| `treeF_fiber` | fibres are `G`-orbits | 150 |
| `G_facts` | `a ≠ 1`, `b ≠ 1`, `b² = 1`, `a² ≠ 1`, `a ≠ b`, `a⁻¹ ≠ b`, `ab ≠ 1` | 40 |
| `tree_local_edge` | neighbourhood of an edge interior point | 40 |
| `tree_local_vertex` | neighbourhood of a vertex | 110 |
| `tree_local_sphere` | neighbourhood of a non-pole sphere point | 100 |
| `treeStar_open_saturated` | tree star open and saturated | 60 |
| `treeStar_isSimplyConnected` | tree star contracts | 130 |
| `treeStar_inter` | stars meet only along Cayley edges; edge and sphere overlaps are path connected | 120 |
| `G_normalForm` (G-ish), **LIBRARY-borderline** | reduced-word normal form for `ℤ * ℤ/2` (van der Waerden action) | ~200 |
| `G_cayleyTree` | depth/parent from the normal form: the Cayley graph is a tree | 120 |

## Proved in the blueprint

These are not leaves:
- the antipodal covering (copied from t00A02);
- the quotient tools (`Saturated`, `quotLift`, open images, image of an
  intersection);
- the action instances and their continuity, and relation invariance under
  the action;
- the case splits `chain_local` and `tree_local`, and the covers
  `chainPiece_cover` and `treeStar_cover`;
- `chainTreeCover` (depth `natAbs`, parent toward 0);
- the tree `TreeCover` assembly;
- the main theorem.

## Checks

- **Compile.** `Blueprint.lean` has 0 errors. There are 31
  `declaration uses sorry` warnings, exactly the 31 leaves. In a /tmp copy,
  `#print axioms apm_t99a02` gives
  `[propext, sorryAx, Classical.choice, Quot.sound]`, with `sorryAx` coming
  only from the leaves. The frozen definitions and the theorem statement
  were diffed against Main: identical.
- **Quotient topology.** Every quotient (`RelationQuotient`, `Wedge`,
  `Surface`) is coinduced. Every open set used downstairs is the image of a
  saturated open set, so its preimage is that set. The contraction leaf
  restricts the quotient map to an open saturated set
  (`IsQuotientMap.restrictPreimage_isOpen`) and crosses with `I`, which is
  locally compact. No leaf claims Hausdorffness of a quotient.
- **Relation directions.** `ChainRel` is directional, and reflections reverse
  it. That is why the deck leaf only asks for `EqvGen R (g•z) (g•w)`.
- **`rp2Proj`.** Continuity holds because the two hemisphere formulas agree
  after `surfaceQuotient`: `SurfaceRel false 1` identifies `z` with `-z` on
  the whole unit circle, since `edgePoint 2 1 t = -edgePoint 2 0 t`. Both
  composite identities were checked, including `x₂ < 0`.
- **Freeness and saturation.** These were checked case by case:
  - junction classes `{(n,N), (n+1,S)}`;
  - vertex classes `{(g,0), (g a⁻¹,1), (g,N), (g b,S)}`;
  - pair classes `{(g,x), (g b,-x)}`.

  The stars and neighbourhoods need only the facts in `G_facts`, not the
  word problem. The word problem enters only through `G_cayleyTree`, for the
  tree-shaped intersection pattern.
- **Contractions respect the relation.** `spherePush (-p) (t,-x) =
  -spherePush p (t,x)`, and vertex and junction points stay fixed.

## Risks

- `G_normalForm` is the largest leaf. If it overruns, split it into
  (i) the `Equiv.Perm` action of the letters on reduced words, and
  (ii) injectivity of `wordEval`.
- `treeF_fiber` and `chainF_fiber` are long case analyses. `ZMod 0 = ℤ` is
  handled through `zOf` and the `rfl` lemmas `zOf_add`, `zOf_sub` and
  `zOf_zero`.
- `treeF_isQuotientMap` needs "a sum of quotient maps is quotient". I found
  no Mathlib name for this, so the seat proves it with `isOpen_sum_iff`.

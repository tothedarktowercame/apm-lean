# Blueprint for t91J05

## Triage

Verdict: **true and faithful**.

The source asks which spaces are finite covers of the connected sum of three
tori.  The registered theorem makes the standard implicit convention explicit:
the covering space is connected.  Without `[ConnectedSpace X]`, finite disjoint
unions of the listed surfaces would also be covers, so the registered version is
the faithful connected classification described by `informal-solution.md`.

I checked the principal degeneracies.  The empty source cannot acquire a
`ConnectedSpace` instance compatible with the intended inhabited connected
cover, and in any event cannot map surjectively to the nonempty polygon quotient.
The identity cover is the `n = 1` endpoint and gives genus `3`.  The theorem
requires `0 < n`, so no zero-sheet/genus-one artifact occurs.  Constant maps
cannot be surjective onto the genus-three surface.  The solve-loop records no
counterexample; the batch registration independently marks the statement
faithful.

The already compiled source-homeomorphism transport lemma and the integer
Euler-characteristic calculation were copied from `Main.lean` with their
proofs.  The main theorem is fully assembled from the two obligations below.

## Remaining lemmas (re-split 2026-10-26, claude-14)

The 2026-10-13 version had two LIBRARY leaves. Both are now handled from
sorry-free modules that did not exist then.

### `apm_t91J05_connected_finite_cover_classification` — PROVED

Proved on `lemmas` in 966e033f8 (`holes/labs/lemmas/t91J05/`, about 110
lines). The proof is inlined in `Blueprint.lean`. It is a bridge to
`StandardSurfaceFiniteCover.connectedFiniteCover_homeomorph_standardSurface`
(`g = 3`, so `n·(3-1)+1 = 2n+1`), with two aux lemmas:
`_aux_locPath` (the source of a local homeomorphism onto a locally
path-connected space is locally path-connected; the base is a quotient of the
disk, `LocPathConnectedSpace.coinduced`), so the connected `X` is
path-connected; and `_aux_sheets` (fibre cardinality of a covering is locally
constant, hence constant over the connected base). `n > 0` comes from a
nonempty finite fibre. Axioms: propext, Classical.choice, Quot.sound.

### `apm_t91J05_cyclic_surface_cover` — sorry-free assembly over 8 leaves

**Route.** Not the polygon cyclic gluing proposed in 2026-10-13. That would
need a converse to the module, namely that a polygon complex's quotient map is
a covering, and that is local analysis at the vertex. Not the subgroup route
(`CoveringSubgroupCorrespondence.connectedCover`) either: it needs
`SemilocallySimplyConnected (Surface true 3)`, and nothing in the library gives
charts on the polygon surfaces. Instead, pull back the `n`-fold circle cover:

* `φ : Disk → ℝ` is `‖z‖ · profile (arg z)`. The profile is `0` for angles
  `≤ 0`, rises with slope `6/π` to `1` at `π/6`, is `1` up to `π/3`, falls to
  `0` at `π/2`, and is `0` beyond. On the 12-gon this is `t` on side 0, `1` on
  side 1, `1 - t` on side 2, and `0` on sides 3–11.
* Across each `SurfaceRel true 3` identification, `φ` changes by an integer
  (side 0 at `t` and side 2 at `1-t` both give `t`; sides 1 and 3 give `1` and
  `0`; sides ≥ 4 give `0`). So `f = Circle.exp (2πφ)` descends to a continuous
  `f : Surface true 3 → Circle` that winds once along side 0.
* `E = LiteralPullbackCover.Pullback (· ^ n) f` covers `Surface true 3`
  (`LiteralPullbackCover.isCoveringMap`, `Circle.isQuotientCoveringMap_npow`)
  with `n` points in every fibre (`sheet_card`,
  `CirclePowerFiberCard.circlePower_fiber_card`).
* `E` is path-connected: the side-0 loop lifts to a path from `(s₀, w)` to
  `(s₀, w·e^{2πi/n})`, and Mathlib's path lifting carries any point to the
  fibre over `s₀`.
* The module theorem gives `E ≃ₜ Surface true (2n+1)`, and
  `apm_t91J05_isFiniteCover_of_homeomorph` transports the cover.

The assembly (`apm_t91J05_cyclic_surface_cover`, about 40 lines) is written
and compiles.

**Leaves** (queue order, easiest first):

| # | leaf | in words | sketch / tools | est. lines | deps |
|---|---|---|---|---|---|
| 1 | `_aux_vertex` | `[edgePoint 12 0 0] = [edgePoint 12 0 1]` in `Surface true 3` | chain π/6 ~ π/3 ~ π/2 ~ 0: three `SurfaceRel` steps with `j = 0` and equalities `edgePoint 12 k 1 = edgePoint 12 (k+1) 0` (same `Complex.exp`) | 40–80 | none |
| 2 | `_aux_phi_rel` | for any `ψ` with the boundary values, `SurfaceRel true 3 x y → ∃ m : ℤ, ψ y = ψ x + m` | unfold `SurfaceRel` (`4*3 = 12`), cases `j < 3` and the two disjuncts | 40–80 | edge values as hypotheses |
| 3 | `_aux_circleMap` | a continuous `ψ` that changes by integers across identifications descends to `C(Surface true 3, Circle)` with `f [x] = Circle.exp (2πψ x)` | `Quotient.lift` over `EqvGen` (`Relation.EqvGen` induction), periodicity of `Circle.exp`, `continuous_coinduced_dom` | 40–80 | none |
| 4 | `_aux_phi_edge_low` | `φ` on sides 0, 1, 2 is `t`, `1`, `1 - t` | `‖edgePoint‖ = 1`; `Complex.arg_exp_mul_I` / `arg_cos_add_sin_mul_I` for angles in `[0, π/2]`; min/max arithmetic | 60–120 | none |
| 5 | `_aux_phi_edge_high` | `φ = 0` on sides 3–11 | angle `π(k+t)/6 ∈ [π/2, 2π]`; its `arg` is the angle, or the angle minus `2π`; profile `0` on both ranges | 60–120 | none |
| 6 | `_aux_pathConnected` | if any two points over some `s₀` are joined, `E` is path-connected | `IsCoveringMap.liftPath` (Mathlib `Topology/Homotopy/Lifting`); base path-connected as the image of the disk; `E` nonempty since `n > 0` | 60–120 | `hjoin` as hypothesis |
| 7 | `_aux_phi_continuous` | `φ` is continuous | `Complex.continuousAt_arg` on the slit plane; profile `0` near `arg = ±π`; `|φ| ≤ ‖z‖` at `0` | 80–150 | none |
| 8 | `_aux_vertexFibre_joined` | over the vertex, any two points of `E` are joined | path `t ↦ ([edgePoint 12 0 t], w · Circle.exp (2πt/n))`; `hv` at `t = 1`; every root of unity is a power of `e^{2πi/n}` | 100–150 | `hf`, `hv` as hypotheses |

No leaf is LIBRARY. All leaves are independent: each takes its siblings'
conclusions as explicit hypotheses (2, 6, 8), so all eight can go to seats at
once.

**Checks (C1–C10).**
* C1: angles checked by hand for every side. `edgePoint 12 k t` has angle
  `π(k+t)/6`. The profile gives `t, 1, 1-t` on sides 0–2. On sides 3–11 the
  angle is `≥ π/2` (profile `0`), or its `arg` lies in `(-π, 0]` (profile `0`).
  The shared corners agree: `0` at angle `π/2` and at `0 ≡ 2π`. Leaf 2 is
  stated for every `ψ` with these values, and is true there because the
  integer differences depend only on the values. Leaf 6 is stated for any
  `s₀`; it is true because every fibre is nonempty and lifting reaches any
  fibre.
* C2: no hypothesis restates a conclusion. `hjoin` (leaf 6) concerns one
  fibre, the conclusion the whole space. `hv` (leaf 8) is leaf 1's conclusion,
  passed in.
* C3: the largest leaf is 8, which only needs one explicit path family and
  roots of unity.
* C4: the assembly compiles against the leaves as stated.
* C7: `4 * genus` in `SurfaceRel` versus the literal `12` in the leaves: the
  leaf seats need `norm_num` for this; it is not a mismatch. `Circle.exp t =
  exp (t·I)`, so `2π` appears explicitly. No natural subtraction: the module's
  `n * (3 - 1) + 1` is rewritten by `omega` in the assembly.
* C8: `n = 1` gives `E ≅ Surface true 3` (`w = f s` is forced); all leaves hold
  at `n = 1`. Leaves 6 and 8 assume `0 < n`.
* C9: no leaf repeats an ancestor; the old LIBRARY statement is now the
  assembly.
* C10: this section replaces the 2026-10-13 LIBRARY text; the triage above is
  unchanged.

## Dependency layers

* Layer 1 (all parallel): the 8 leaves above.
* Layer 2 (compiled): `apm_t91J05_cyclic_surface_cover`; then `apm_t91j05`
  from it, the proved classification, and the transport lemma.

## Compilation and axioms

```text
flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=12G \
  lake env lean holes/labs/blueprints/t91J05/Blueprint.lean
```

0 errors; 8 `declaration uses sorry` warnings, one per leaf.
`'apm_t91j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`.
`scripts/statement-registry.py check t91J05`: 1 registered statement matches.

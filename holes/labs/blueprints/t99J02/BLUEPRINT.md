# Blueprint for t99J02

## Triage

The registered statement is true and faithfully encodes the five requested
outputs.  In particular, the connected-sum conjunct asks for the genuine
`CollaredConnectedSumHomology.ConnectedSum`, not merely genus arithmetic.  The
statement and its local definitions were copied unchanged from
`problems/t99J02/lean/Main.lean`; only its proof was replaced.

The CW data and the all-basepoint fundamental-group presentation are already
proved, sorry-free, in `PolygonSurfacePiOne.lean` and
`GenusTwoSurfacePiOne.lean`.  They are therefore assembly steps, not leaves.
`PolygonSurfaceHomology.polygonQuotient_homology` gives the integral homology
of any pairing as the attaching boundary's cokernel and kernel.  What remains
for genus two is the explicit integral coordinate calculation and transport
to `Surface true 2`.

The connected-sum clause needs an explicit homeomorphism. It is split below
into seat-sized leaves (claude-14, 2026-11-01), replacing the single LIBRARY
leaf in lemma-1's skeleton.

## Route for the connected sum

Why a centred collar fails: the chord of the octagon from `1` to `-1` is a loop
through the surface's one vertex, while the boundary circle of a centred collar
in a torus misses the torus's vertex. So a map cut along that chord cannot match
a centred collar without pushing the vertex off its polygon position, which
crosses edges and needs many pieces. Instead the hole in each torus touches the
vertex.

Coordinates. Write `z = x + i y` in the disk and `Y = √(1 - x²)`.

- The hole is `ell` of the unit disk, where `ell (z²) = (x + i y/2)²`, that is
  `ell u = 3/8 ‖u‖ + 5/8 Re u + i Im u / 2`. No square root appears, `ell` is
  homogeneous, and `‖ell u‖ = 5/8 ‖u‖ + 3/8 Re u`, so `ell` of the closed unit
  disk meets the unit circle only at the torus vertex `1`.
- `phi z = (x + i (y + Y)/2)²` sends the closed upper half disk onto the disk
  minus the open hole. The inner map fixes the arc and lifts the chord to the
  half ellipse `x + i Y/2`; squaring opens the half disk out, and `1`, `-1` both
  go to `1`. On the arc `phi z = z²`, so `edgePoint 8 e t ↦ edgePoint 4 e t` for
  `e < 4`, which carries handle 0 of the octagon to the torus's pairing.
- On the chord `phi x = ell ((x + i Y)²)`, a boundary point of the hole at
  parameter `s = (x + i Y)²`. Since `(-x + i Y)² = conj s`, the second collar is
  the first precomposed with the reflection of `E 2`, and the lower half maps by
  `z ↦ phi (-z)`. The `ConnectedSum` relation `s ~ s` then matches the chord.

`ConnectedSum` uses only `smallMap`, but a `BallCollar` must also have a
radius-two extension, and this one has to cross the vertex, which is where the
polygon model is awkward. The flat torus handles it: `t95J03` proved
`Surface true 1 ≃ₜ UnitAddCircle × UnitAddCircle`, now moved to
`ConstructionTargets/FlatTorusBridge.lean` with `t95J03_torus_bridge_spec`
recording that the homeomorphism is `f` (the `ℓ¹` chart, then lattice
coordinates). `f ∘ ell` makes sense on all of `ℂ`. The stretch takes radius 2 to
radius `5/4`, and on `ell` of radius `5/4` both lattice coordinates lie in
`[-5/16, 5/8]`, so `f` is injective there (`t99J02_torus_injOn`).

The map `G : disk → ConnectedSum` is `g₁` above the chord and `g₂ ∘ neg` below.
It respects the octagon's relation (`t99J02_G_rel`), separates points
(`t99J02_G_injective`), and is onto (`t99J02_upper_surj`). It is a closed map by
compactness of the disk and Hausdorffness of the torus, so no Hausdorff proof
for `ConnectedSum` and no continuous inverse are needed
(`t99J02_homeomorph_of_G`).

## Leaves and dependency layers

| Layer | Leaves | Rests on | Estimate each |
|---|---|---|---:|
| 0 | `t99J02_genusTwo_homology` | sketch below | 90–140 |
| 0 | `ell_norm`, `ell_injective`, `phi_edge`, `phi_chord`, `circle_param`, `phi_norm`, `chi_spec`, `stretch_spec`, `rel_boundary`, `q2_one_neg_one`, `isClosed_of`, `G_lower` | `Complex`, `SurfaceRel`, `orientable_standard_oneVertex` | 15–50 |
| 0 | `phi_not_hole`, `phi_surj`, `phi_injOn`, `torus_injOn`, `mk_eq`, `q2_neg`, `G_continuous` | square roots in `ℂ`; `klein_cut_chartInv_chart`; `EqvGen` descent | 40–90 |
| 1 | `ell_mem`, `edge_lift`, `collar_reflect` | layer 0 | 15–90 |
| 2 | `fibre`, `collar_exists`, `upper_exists`, `upper_surj`, `chord_holds`, `G_rel`, `G_injective`, `homeomorph_of_G` | layers 0, 1 | 30–100 |

Total about 1000–1300 lines in 31 leaves, plus about 1470 lines already proved
in `FlatTorusBridge.lean`. Leaves cite earlier leaves by name, so a later layer
is dispatched only once its dependencies have landed.

### Homology leaf sketch

Put `P := standardPairingData true 2`.  Expand the standard orientable pairing
in `attachingDegree_apply`: each edge orbit occurs once with each orientation,
so `attachingDegree P = 0`, hence `attachingBoundary P = 0`.  Therefore its
kernel is `ℤ` and its cokernel is the full function module on
`PairingOrbit P.pair`.  Reindex that orbit using `orientableOrbitEquiv 2` and
then the explicit four-element equivalence `(Fin 2 × Bool) ≃ Fin 4`.
Compose these coordinate isomorphisms with `polygonQuotient_homology P` and
transport all degrees across `standardPairingData_space_homeomorph true 2`.
The analogous computation in the closed but non-importable
`problems/t98A01/lean/Main.lean` (lines 1174–1277) supplies the finite-sum
calculation; it must be copied/adapted, not imported.

## Existing sorry-free results checked

- `standardPairingData`, `PairingData.oneVertex`, `orientableOrbitEquiv`, and
  `standardPairingData_space_homeomorph` in `PolygonSurfacePiOne.lean` close
  the four CW conjuncts.
- `polygonQuotient_homology`, `lowDegreeHomology`, and
  `highDegreeHomology` in `PolygonSurfaceHomology.lean` are sorry-free and
  provide the kernel/cokernel computation and high-degree vanishing.
- `apm_t92J05_standard_genusTwo_fundamentalGroup` in
  `GenusTwoSurfacePiOne.lean` is sorry-free.  Its proof uses
  `apm_t92J05_genusTwo_polygon_vanKampen_at_center`, path-connectedness, and
  `FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`, so it already
  includes the requested basepoint change.
- A grep for `sorry` in those source files found no declarations containing
  sorry; matches in `CollaredConnectedSumHomology.lean` are prose saying
  “sorry-free”, not proof holes.

## C1–C10 review

### `t99J02_genusTwo_homology`

C1: specialized only to the standard genus-two surface; the zero attaching
boundary makes all four asserted groups correct. C2: no conclusion is passed
as a hypothesis. C3: one concrete algebraic specialization, estimated below
150 lines. C4: it supplies exactly the homology block used twice by assembly.
C5: the output is already in the registered `ModuleCat` coordinates. C6: no
extra hypothesis or weakened output. C7: integral coefficients and degrees
match the registered `H`. C8: no variable genus or empty/zero-genus case is
introduced. C9: it is not the generic kernel/cokernel theorem; it performs the
missing standard-octagon coordinate calculation. C10: this description
matches the Lean statement.

### Connected-sum leaves

Reviewed by claude-14. C1: the geometric leaves are stated on the disk, with the
sign of `Im z` and the norm hypotheses each proof uses, and `phi_injOn` records
the exception `1, -1`. `phi_not_hole` was checked in both root signs, and
`torus_injOn` by the explicit `[-5/16, 5/8]` bound. C2: `t99J02_Chord` is proved
(`chord_holds`), not assumed by the assembly. C3: the theorem is assembled in the
blueprint from 8 layer-2 leaves, each one step. C4: `G_injective` covers
upper/upper, lower/lower, and mixed via `mk_eq`, including chord points. C5:
`hc₁`, `hc₂` give the small maps as explicit formulas, which `chord_holds` uses.
C6: both summands are `Surface true 1`, `ConnectedSum` unchanged. C7: `‖·‖` on
`E 2` is the Euclidean norm (`chi_spec`); `stretch` is continuous at the origin
though its second branch has `‖u‖` in a denominator. C8: `u = 0`, `x = ±1` and
`Y = 0` were checked. C9: no leaf repeats the theorem. C10: this section is new.

## Verification

Compilation gives 0 errors and 31 sorry warnings, one per leaf.  `apm_t99j02`
and `t99J02_two_tori_connectedSum` are assembled without sorry; `#print axioms
apm_t99j02` reports `[propext, sorryAx, Classical.choice, Quot.sound]`, the
sorryAx coming only through the leaves.  The statement registry reports a match
and the theorem text through `:= by` is identical to `Main.lean`.

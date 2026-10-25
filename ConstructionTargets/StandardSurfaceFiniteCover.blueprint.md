# StandardSurfaceFiniteCover blueprint

## Triage and boundary

The theorem is true for `g,n >= 1`. The cell-structure route avoids recognition
of an arbitrary compact surface. The repository has the single-polygon quotient
(`PolygonSurfacePiOne`) and geometric elementary word moves (`PolygonMoves`),
but no multi-polygon datatype/dual-tree reduction and no terminating word
normalizer. Thus the honest split has two LIBRARY leaves.

## Leaves

### `standardCover_pairingData` — LIBRARY, 1800–3500 lines, independent

Lift the standard `4g`-gon through `IsCoveringMap`; use
`IsCoveringMap.monodromy`, `monodromy_bijective`, path lifting, and connectedness
to make the face-dual graph connected. Glue the `n` disks along a spanning tree,
then reduce the `n` lifted vertex classes to one `PairingData`. Counts
`V=n,E=2gn,F=n` give `4*(n*(g-1)+1)` boundary arcs.

C1 Euler count and lifted cells; C2 no homeomorphism witness is assumed; C3
marked LIBRARY because the multi-polygon layer is absent; C4 connectedness
supplies the spanning tree; C5 returns pairing and homeomorphism; C6 only cover,
sheet, connectivity hypotheses; C7 subtraction safe from `1<=g`; C8 `n=1`
returns the base polygon and `g=1` gives four sides; C9 below the old ancestor;
C10 matches Lean.

### `orientablePairing_normalForm` — LIBRARY, 1200–2500 lines, independent

Normalize a one-vertex pairing with opposite paired signs to the standard
commutator word. Use `PolygonMoves.rotation`, cancellation, merge, and
`cutAndPaste`. Those already prove each geometric homeomorphism; the missing
foundation is the terminating finite combinatorial normalizer.

C1 classical orientable polygon normal form; C2 orientability is a sign
equation, not the conclusion; C3 marked LIBRARY because normalizer is absent;
C4 one vertex is built into `PairingData`; C5 composes directly; C6 no surface
classification; C7 exact `4*h` count; C8 `h=1` is the torus and `hh` excludes
zero; C9 not the cover theorem; C10 matches Lean.

The sorry-free assembly composes the leaves. Layer 1 is the two independent
LIBRARY leaves, layer 2 the shared assembly, and layer 3 consumer adapters.
Truth checks: `n=1` gives genus `g`; `g=1` gives a torus; zero cases are
excluded. The sign convention matches `standardSign_orientable_pair`.

### Split of `orientablePairing_normalForm_aux_cutPaste` (2026-10-24)

lemma-1 found that `PolygonMoves.cutAndPaste` is the crosscap move (`x … x`)
and cannot reach orientable words. The orientable move reuses its convex-piece
geometry with `p = 0`: both pictures cut the disk along the same chord (vertex
`0` to vertex `q = |α₁|+1+|α₂|`), so the old charts `cutOldA`/`cutOldB` serve
both words. Only the boundary labels change, by circle homeomorphisms `ρA`
(`α₁ y α₂ c⁻¹ ↦ α₂ c⁻¹ α₁ y`) and `ρB` (`β₁ y⁻¹ β₂ c ↦ β₂ c β₁ y⁻¹`). Proved in
the file: `_aux_length` (banked by lemma-1), `_aux_lift`, `_aux_package`
(the proof of `cut_charts_package` with the words abstracted), and the parent.
Leaves, all parallel: `_aux_reparamA`, `_aux_reparamB` (piecewise-linear
circle maps; junction angles and the `n₁ = 0`, `n₂ = 0`, `m₁ = 0`, `m₂ = 0`
cases were checked by hand), `_aux_forward`, `_aux_reverse`,
`_aux_fibreForward`, `_aux_fibreReverse` (combinatorics from the edge formulas
in `_aux_Data`; models `cut_forward_generators`, `cut_reverse_generators`,
`cut_forward_fibre`, `cut_reverse_fibre`). Signs: the `y` pair has opposite
signs and lands on the chord read in opposite directions by the two pieces;
the old chord becomes the `c⁻¹`/`c` sides at positions `|α₂|` and `q+|β₂|`
with parameters `s` and `1-s`.

### Split of `standardCover_pairingData_aux_contractStep_aux_isolate` (2026-10-25)

Massey's corner-moving induction, done with the glue machinery that is already
proved (`_aux_glueStep_aux_mergeExists`, `_aux_glueStep_aux_homeomorph`,
`_aux_glueStep_aux_vertexCount`), used in both directions. The measure is
`_aux_isolate_aux_classCard C u`, the number of corners at the vertex of `u`.
Proved in the file: `_aux_classCard_congr`, `_aux_move0`, `_aux_move`, and the
parent (strong induction on the count). Leaves, all parallel:
`_aux_single` (count one gives `nextCorner (pair u) = u`), `_aux_entry` (one
face, two vertices: some corner `a` outside the vertex of `u` is followed by
one inside), `_aux_rotate_aux_homeomorph` (face rotation, from
`PolygonMoves.rotation_aux_disk_homeomorph`), `_aux_rotate_aux_corners`
(rotation adds `k` mod `n` and carries `CornerRel`), `_aux_transport` (generic:
a side bijection carrying `CornerRel` carries vertex count, `EqvGen` and
corner counts), `_aux_cut` (a one-face complex is the triangle `a b c` glued to
the rest along the chord `c`, as a `GlueData D C c` with `D.sides c.1 = 3`,
`c.2 = 2`), `_aux_cutFacts` (`b` and `pair b` lie in different faces of `D`,
and the vertex of `b` has a third corner), `_aux_classCard_glue` (generic: a
glue along `s` removes the corners among `s, pair s` from each vertex),
`_aux_count` (at the vertex `Q` of `b`, `c, pair c` give one corner fewer than
`b, pair b`: `c` meets `pair b`, `pair c` meets `a`, which is not at `Q`).
Checks: the move needs `P ≠ Q` (`hPQ`); with `P = Q` the count at `Q` does not
change. `pair b = a` is excluded by `hab` (otherwise `pair b` would be in the
triangle and `mergeExists` would not apply); `b → b` loops (`R = Q`) are
covered, since then both `pair b` and `c` are at `Q`. `_aux_cut` needs
`3 ≤ totalSides` so the second face has two sides.

Split of `_aux_cut` (2026-10-25, after the lemma-1 PARTIAL, which banked
`_aux_cut_aux_face_eq` and `_aux_cut_aux_sides_eq`). `D` is the def
`_aux_cut_aux_complex C n hn E`: faces `![3, n - 1]`, its pairing is
`C.pair ⊕ swap 0 1` transported along a side matching
`E : D.Side ≃ C.Side ⊕ Fin 2`, and its signs are those of `C`, plus `true`/`false` on the
two chord sides. The assembly proves `D.IsOrientable`, `2 ≤ D.sides f` and
`D.sides c.1 = 3` itself. Leaves:
`_aux_cut_aux_equiv` (Fin bookkeeping, ~60 lines: an `E` meeting `_aux_cut_aux_spec`,
which sends side `j` of `C` to triangle side `j` for `j < 2`, else to side
`j - 1` of the other face, and the chords to triangle side `2` and side `0`
of the other face) and `_aux_cut_aux_glue` (~100 lines: the `GlueData` with
`c = E.symm (inr 0)`, `old` constant, `toOld = E.symm ∘ inl`; the merged-side
fields reduce to `(3 + m) % 3 = m` for `m < 2` and `(m - 1) % (n - 1) = m - 1`).
Checks: C1, the counts match (`3 + (n - 1) = n + 2`) and the spec is injective
(the images are distinct); C8, at `n = 3` the second face is a 2-gon
`[pair c, side 2]`; C9, neither leaf restates `_aux_cut` or `_aux_isolate`.

**`_aux_rotate_aux_homeomorph` split (claude-14, 2026-10-25, lemma-3 PARTIAL).** lemma-3 banked
`_aux_shift_val` (`((finRotate n)^k i).val = (i + k) % n`), `_aux_edge_mod` and `_aux_edge`
(the facewise rotation sends `edgePoint _ s.2 t` to `edgePoint _ (shift s).2 t`). The
assembly is proved: `_aux_disks C k := Equiv.sigmaCongrRight (rotation_aux_disk_equiv ·)`
is continuous and bijective, and `_aux_glueStep_aux_homeomorph_aux_span` with `a = id`,
`b = _aux_disks` gives the homeomorphism once the generators match. One leaf:
`_aux_rel` (`C.Rel x y ↔ (rotate C k).Rel (e x) (e y)`, ~30 lines). Checks: C1, the
rotated pairing at `shift s` is `shift (pair s)` and its sign is `C.sign s`, so
`pairedParameter` agrees and the iff holds in both directions (backwards via
`s = shift.symm s'` and injectivity of `e`); C9, the leaf is a generator-level
statement, not the homeomorphism.

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

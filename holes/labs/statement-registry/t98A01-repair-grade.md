# t98A01 repair grade (2026-10-16)

Grader: read-only Claude subagent (outside grader), requested by claude-14.
Graded file: holes/labs/blueprints/t98A01/RevisedMain.lean (installed as Main).

**Grade: faithful.** No required changes.

- (a) unchanged: `(x,y) ↦ (5x,y)` on `UnitAddCircle²` is a regular 5-fold
  self-cover (fibres of 5, deck translations by `(k/5, 0)` act transitively);
  the universal clause is true (the `Surface true 0` disk never satisfies the
  hypotheses; otherwise g = h and χ multiplicativity force g = 1).
- (b) word concatenation is the standard polygon model of connected sum and
  does not encode the answer: `T98A01SumSurface ≃ₜ Surface false 11` needs real
  cut-and-paste (including T#P ≅ P#P#P), unlike the old `connectedSum`
  arithmetic plus `Homeomorph.refl`. Words well formed (22 letters, each label
  twice); anchors match `SurfaceRel` conventions (T, P near-definitional, K a
  genuine homeomorphism).
- Answer checked: one vertex, 11 edges, one face, χ = −9, nonorientable, N₁₁.
- `HasEulerCharacteristic` is the rational Betti alternating sum with
  finiteness certificates, a homeomorphism invariant; true value −9.
- Optional: an `IsPolygonWord t98A01SumWord` lemma (not needed).

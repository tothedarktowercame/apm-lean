# Reopened statements, round 2 — fidelity grades (2026-09-28)

Repo: /home/joe/code/apm-lean (HEAD for these files: 8ec6539c; t00A04 statement last changed in 4489e960). Graded the current `theorem apm_<id>`; `apm_<id>_previous_encoding` ignored. Read-only; nothing built. No STATEMENT-REPAIR.md exists for any of the six; PRELIM-DEFECT.md exists only for t00A04.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A04 | narrower | `apm_t00a04` | `IsManifold I (⊤ : WithTop ℕ∞)` and `ContMDiff … ⊤` are C^ω (analytic), not C^∞; also adds `PathConnectedSpace X`, which the prelim does not assume (drops orientation and compactness of Y, which widens the statement) | YES, real (a one-point X is a counterexample; empty X is another), but the PRELIM-DEFECT.md text is stale: it describes an "infinite, path connected" fix that the Lean no longer uses. The minimal fix is "X nonempty of positive dimension"; path-connectedness goes beyond it, and the analytic regularity has no justification |
| t01A03 | faithful | `apm_t01a03` | real genus-2 manifold (pinned by integral singular homology), concrete wedge in `Circle × Circle`; subsets fixed by homeomorphism type of their complements, not by algebraic hypotheses; answer "no retraction" ×3 is correct | no |
| t02A02 | faithful | `apm_t02a02` | real quotient of the disk by the signed 8-edge word; the pairing and orientations check out by hand; conclusion `≃ₜ Surface false 2` (Klein bottle = RP²#RP²) is correct | no |
| t91A02 | faithful | `apm_t91a02` | concrete N₁₆ → N₈; "covering map with constant finite nonzero fibre" is equivalent to "covering map" here (compact total space, connected base) | no |
| t95J03 | faithful | `apm_t95j03` | real covering maps plus a homeomorphism of total spaces; answer {T, K} for even k, {K} for odd k is correct. Encoding note: `.orientable 0` / `.nonorientable 0` denote the closed disk, not S², so S² is missing from the domain. This does not change the answer set | minor: reading "surface" as connected closed is needed (for disconnected F, K⊔K ∈ S₂) and is declared in the file |
| t97J06 | faithful | `apm_t97j06` | concrete map on `Circle × Circle` with a lift identity; degree is the actual H₂ map (0); non-nullhomotopy uses Mathlib's `Homotopic`; both claims are true | minor typo (literal periodicity is false; the second coordinate shifts by n+m), handled by using the descended map; no content lost |

## Evidence notes

### t00A04 — narrower
Lean (Main.lean:41-53):
```lean
theorem apm_t00a04 :
    ∀ (E F : Type*) … (I : ModelWithCorners ℝ E E) (J : ModelWithCorners ℝ F F)
      (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [CompactSpace X] [PathConnectedSpace X]
      [ChartedSpace E X] [IsManifold I (⊤ : WithTop ℕ∞) X]
      [ChartedSpace F Y] [IsManifold J (⊤ : WithTop ℕ∞) Y],
      0 < Module.finrank ℝ E →
      ∀ (ι : C(X, Y)) (r : C(Y, X)),
      ContMDiff I J (⊤ : WithTop ℕ∞) ι → ContMDiff J I (⊤ : WithTop ℕ∞) r →
      (∀ x, r (ι x) = x) → ¬ apm_t00a04_NullHomotopic ι
```
- **Regularity.** In the pinned Mathlib, `(⊤ : WithTop ℕ∞)` is `ω`: FTaylorSeries.lean:112 has `notation3 "ω" => (⊤ : WithTop ℕ∞)`, and smooth is `∞ => ((⊤ : ℕ∞) : WithTop ℕ∞)`. So the statement requires analytic manifolds and an analytic ι and r, which is narrower than the prelim's "smooth". The problem wants C^∞ (`∞`), and the proof only needs continuity. Compare t01A03, which correctly writes `IsManifold … ∞ S` under `open scoped ContDiff`.
- **Extra hypothesis.** `PathConnectedSpace X` is not in the prelim. The prelim does need X nonempty: empty X makes the inclusion vacuously null-homotopic, which is a second prelim counterexample, and `PathConnectedSpace` excludes it. But for a nonempty, disconnected, positive-dimensional X the claim holds trivially, because a null-homotopy of ι gives one of id_X = r∘ι, which forces X to be path connected. So path-connectedness is more than the defect requires. The cases it drops are easy ones, but they are dropped.
- **Wider in other respects (harmless).** Orientation of X and Y, and compactness and Hausdorffness of Y, are dropped. ι only needs to be a map with a left inverse, not an inclusion. The statement stays true: a null-homotopic ι makes X contractible, and a closed n-manifold with n>0 has H_n(X;ℤ/2) ≠ 0. The model `ModelWithCorners ℝ E E` with `H = E` rules out boundary.
- **PRELIM-DEFECT.md.** The defect is real: for a one-point X, ι is constant. But the file describes the wrong fix ("X is compact, Hausdorff, path connected, and infinite"), which matches 30f76adb and not the current 4489e960 statement (manifold charts plus `0 < finrank`). The minimum departure is "X nonempty and dim X > 0" (or "X is not a single point and nonempty"). The current Lean adds path-connectedness and analyticity on top of that, and neither is justified by the defect.
- **Suggested repair:** change `(⊤ : WithTop ℕ∞)` to `∞` (with `open scoped ContDiff`), change `PathConnectedSpace X` to `Nonempty X`, and update PRELIM-DEFECT.md to match.

### t01A03 — faithful
- Surface: `∀ S … [T2Space S] [CompactSpace S] [PathConnectedSpace S] [ChartedSpace apm_t01a03_E2 S] [IsManifold apm_t01a03_I2 ∞ S], apm_t01a03_hasGenusTwo S →`. Here `hasGenusTwo` requires H₀≅ℤ, H₁≅ℤ⁴ and H₂≅ℤ in integral singular homology. For a closed connected surface, H₂≅ℤ forces orientability and H₁≅ℤ⁴ forces genus 2, so the surface is pinned down.
- (a) `IsMiddleCircle`: an embedding whose complement is `≃ₜ PuncturedTorus ⊔ PuncturedTorus`. This matches "separates into two once-punctured tori", since the interior of a torus with one boundary circle is homeomorphic to the torus minus a point.
- (b) `IsTypicalWedge`: an embedding of the quotient `S¹ ∨ S¹` into `Circle × Circle` whose complement is `≃ₜ` the open unit disk. That is the standard a∨b.
- (c) `IsSeparatingTwoCircles`: an embedding of `Circle ⊔ Circle` whose complement is `≃ₜ S² \ {4 distinct points}`.
- Conclusion: `¬HasRetraction` in all three parts, where `HasRetraction i := ∃ r : C(X, A), ∀ a, r (i a) = a`. This is the correct answer: (a) the circle is null-homologous, so H₁(i) = 0 while H₁(S¹) ≠ 0; (b) F₂ → ℤ² is not injective; (c) the image of a connected space is connected. All hypotheses are geometric, so none of them supplies the obstruction, and all are satisfiable. The three parts are bundled under one ∀ with joint hypotheses. That is logically equivalent to stating them separately, because the genus-2 surface with both configurations exists.

### t02A02 — faithful
- Word `![a, a, b, c, c⁻¹, d⁻¹, b, d⁻¹]` matches `aabcc⁻¹d⁻¹bd⁻¹`. Pairing `![1,0,6,4,3,7,2,5]` is correct.
- `gluingRel` glues edge i at parameter t to edge `pair i` at t when the two edges have the same direction and at 1−t otherwise. That is the correct rule for boundary edges traversed counterclockwise (`edgePoint 8 i t` = exp(2πi(i+t)/8)).
- Independent vertex count: {v0,v1,v2,v6}, {v3,v5,v7}, {v4} gives V=3, E=4, F=1, so χ=0. The repeated `aa` makes it nonorientable. So the surface is the Klein bottle.
- `Surface false 2` in ConstructionTargets/Surfaces.lean is the disk with edges 0~1 and 2~3 glued in the same direction, i.e. a₁a₁a₂a₂ = N₂. The conclusion `Nonempty (apm_t02a02_F ≃ₜ Surface false 2)` is the correct identification. It names the answer, which is appropriate for "identify".

### t91A02 — faithful
```lean
theorem apm_t91a02 :
    ¬ ∃ (p : Surface false 16 → Surface false 8) (sheets : ℕ),
      IsCoveringMap p ∧ 0 < sheets ∧
      ∀ x : Surface false 8, Nat.card {e : Surface false 16 // p e = x} = sheets
```
Both surfaces are the concrete polygon quotients N₁₆ and N₈. Any covering map N₁₆ → N₈ has finite fibres, because they are discrete and closed in a compact space. The image is open and compact, so p is surjective onto the connected base, and the fibre size is constant and nonzero. So the extra conjuncts cost nothing, and the statement is equivalent to "N₁₆ does not cover N₈". It is true because χ(N₁₆) = −14 is not a multiple of χ(N₈) = −6. No Euler-characteristic equation is assumed.

### t95J03 — faithful
```lean
theorem apm_t95j03 (k : ℕ) (hk : 1 < k) :
    {F | T95J03SharesKFoldCover k F t95J03KleinBottle} =
      if Even k then {t95J03Torus, t95J03KleinBottle} else {t95J03KleinBottle}
```
`SharesKFoldCover` requires actual `IsCoveringMap`s from `TopCat` spaces onto the concrete `Surface` quotients, all fibres of size k, and a homeomorphism `E ≃ₜ K`. There are no hypothesis parameters, no Prop stand-ins, and covers may be disconnected.

The answer is correct:
- χ(E) = kχ(F) = kχ(K) = 0 forces F ∈ {T, K}.
- For odd k, some component of a cover of K has odd degree and is therefore nonorientable, while every cover of T is orientable. So T is excluded.
- For even k, T k-fold covers K, so T is included.

Encoding caveat: `.orientable 0` and `.nonorientable 0` both map to `Surface _ 0`. Its relation is empty (`j < 0`), so the space is the closed disk, and S² is absent from the domain. Neither S² (χ=2) nor the disk belongs to S_k, so the set equation is unaffected. Reading "surface" as connected and closed is declared in the file. It is necessary: with disconnected F, K⊔K ∈ S₂.

### t97J06 — faithful
- `t97J06Map (z₁, z₂) = (exp(2πi·Im(z₁z₂²)), z₁z₂)`. The first conjunct, a proved lemma, pins its lift to (sin(2πx+4πy), x+y).
- Degree: `t97J06HasDegree f 0 := ∃ e : H₂(T²;ℤ) ≅ ℤ, e.hom (f_* (e.inv 1)) = 0`. This uses the actual induced map on singular H₂, and degree does not depend on the choice of e. The value 0 is correct: f is homotopic to (1, z₁z₂), which factors through S¹.
- Non-nullhomotopy: `∀ q, ¬ ContinuousMap.Homotopic t97J06Map (const q)`. This is true because the second coordinate is nontrivial on π₁.
- Prelim typo: f̂(x+n, y+m) = f̂(x, y) is literally false, since the second coordinate shifts by n+m. The encoding uses the descended map, which is the only sensible reading, so no content is lost.

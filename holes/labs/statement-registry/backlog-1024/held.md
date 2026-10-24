# Backlog grading 2026-10-24: reviewer decisions on held rows (claude-14)

## Grader errors on smoothness order, overridden to faithful

The packets for batches 00–11 said "a bare ⊤ as a smoothness order is analytic".
Some graders applied that to `(⊤ : ℕ∞)`, which is C^∞. Checked against the
pinned Mathlib: `TestFunction`/`Distribution` take `n : ℕ∞`
(`Mathlib/Analysis/Distribution/TestFunction.lean:87`), and
`statement-registry.py fingerprint` reports no bare-⊤ flag for these statements.

- m99J02 (batch 07, graded vacuous): test functions are `ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ`, i.e. C_c^∞. The grader gave no other objection. Admitted faithful.
- m99J03 (batch 08, graded narrower): same test-function class; the grader says the three limits are correct. Admitted faithful.
- m03J03 (batch 04, graded narrower): `Distribution (⊤ : Opens ℝ) ℂ ⊤` is order ∞, the ordinary distributions. The grader says the four claims are represented. Admitted faithful.

## Held rows, regenerated over all 32 batches

`held-raw.txt` is now the complete list: `admit-batch.py NN` for NN = 00–31,
HELD lines only, prefixed by batch. 40 rows: 34 narrower, 4
hypothesis-carries-core, 1 vacuous (m00A04), 1 admit refused (a01A03, bare ⊤).
They stay unregistered; per the no-narrower-stand-ins rule they are open
statement repairs, not admissions.

## Batch 06 spot-checks (all grades upheld)

- m95J01 (hypothesis-carries-core): `[InnerProductSpace ℝ H]` plus `hinner`
  (Main.lean:290-297) assume the integral is a positive-definite inner product;
  part (a) asks to prove it. Upheld. `hT` correctly encodes (d/dx)² on
  e^{-x}p as p'' - 2p' + p.
- m95J02 (narrower): `hn : 2 ≤ n` (line 2101); the prose allows n = 1
  (fundamental solution |x|/2). Upheld. Test functions are C^∞ via
  `((⊤ : ℕ∞) : WithTop ℕ∞)`.
- m96J05 (hypothesis-carries-core): `hD`/`hT` (lines 193-201) posit D_ε and T
  as Fourier multipliers acting on f ξ directly; the physical-space difference
  and shift operators and the Fourier transform never appear. Upheld.
- Faithful check, m96J03: unit-ball indicator (33-34), C_c^∞ tests (77-79),
  ∫ 1_B Δφ = ∫_S Dφ(ω)ω d(volume.toSphere) (1899-1905), correct sign
  (divergence theorem) and unnormalised sphere area.

## Batch 30 (admitted 2026-10-24 during the final sweep)

Nine faithful rows admitted. Held m97A05 (narrower) checked: the theorem
(Main.lean:100-105) gives T, ∂x T = ∂y T and the wave equation but nothing for
part (b), the Fourier transform. Faithful check, m99A04: unique continuous
extension from a dense set (19-25), matches.

## Batch 05 spot-checks (all grades upheld)

Batch 05 was admitted in the earlier sweep (seven faithful rows registered);
these checks came after its late reply. Two of the three held rows narrow a
source claim that is false, so they belong on the false-problem.md list, not
the ordinary narrower list.

- m94J02 (narrower): lines 1107-1110 prove `‖fg‖ ≤ (5/4)‖f‖‖g‖`; part (c)
  asks for constant 1. The source is false: f = g = 1 + z gives ‖f‖ = 3 and
  ‖f²‖ = 1 + 2·2 + 5 = 10 > 9. The file says so (lines 8-10), and 5/4 is the
  sharp constant: max over k, m of ((k+m)²+1)/((k²+1)(m²+1)) is 5/4, at
  k = m = 1. Held; false source, repaired.
- m94J05 (narrower, correction 8cf4ec3ee): uniqueness only in a sup-norm
  ball. The file (lines 8-10) says unrestricted uniqueness is false at zero
  forcing; a negative solution of (t²x')' = x² with x(1) = x(2) = 0 exists
  beside x = 0 (superlinear Lane-Emden type). Held; false source, repaired.
- m95A04 (hypothesis-carries-core): `regular`/`hregular`, `Dtest`/`hDtest`,
  `Ddist`/`hDdist` (lines 645-654) are parameters, so parts (a) and (b), the
  embedding and the definition of the derivative, are assumed rather than
  constructed. Upheld.
- m94A04 (faithful): `IsFrechetDerivative` (lines 109-122) is a bounded
  L⁸→L² linear map with the o(‖h‖₈) remainder in L², and the theorem
  (364-372) gives a derivative at every f. Upheld.

## Batch 04 spot-checks (all grades upheld)

Batch 04 was admitted in the earlier sweep (seven rows registered: five
faithful, m03J02 stronger, m03J03 overridden to faithful above). These checks
came after its late reply. One of the three held rows narrows a false source.

- m93J03 (narrower): uniqueness only among solutions of size < η
  (Main.lean:689-698). The source is false: any solution has the form
  x = ε + A sin t + B cos t, and at ε = 0 the nonzero solution
  x = R sin(t + φ) needs R e^{2iφ} = -2π J₁(R). With φ = π/2 that is
  R = 2π J₁(R), which has a root R > 0 (2π J₁(R) ≈ πR > R near 0, and
  2π J₁(R) < R for R > 4). The file says so (lines 6-12). Held; false
  source, repaired.
- m93J02 (narrower): `hUnontrivial` and `0 < α < 1` (lines 689-693). The
  source is underspecified rather than false: for a singleton Ω, or for α = 1
  on an interval, (d) holds, while for 0 < α < 1 it fails (f(x) = x on [0,1]
  has local seminorm 0 and global 1). The file names both restrictions
  (lines 9-13). Held; not on the false-source list.
- m93J06 (narrower): part (c) adds a global Lipschitz hypothesis
  (lines 1815-1818) that the source does not need (continuity plus
  |f| ≤ C|y| gives global existence). The negated uniqueness clause for (d)
  is a fair repair, since without uniqueness the map y₀ ↦ y(t) is not
  defined, but (c) is an unforced narrowing. Held; not on the false-source
  list.
- m03J02 (stronger, admitted): uniqueness on all of ℝ (lines 20-21,
  501-504). f(u) = cos u - u is globally Lipschitz, so the backward solution
  exists, and a forward solution on t > 0 extends uniquely to ℝ. Upheld.
- m93J01 (faithful): κ = 1/12, the expansions with O(h⁶) and O(h⁴) in place
  of the false o(·) (lines 166-183), and the Numerov residual
  (1 - h²V₊/12)y₊ - (2 + 5h²V/6)y + (1 - h²V₋/12)y₋ = O(h⁶) (184-190). I
  rederived the h²(Ly) identity: the + sign on κh⁴y⁽⁴⁾ is right. Upheld.

## Batch 07 spot-checks

Batch 07 was admitted in the earlier sweep (eight rows registered: six
faithful, m96J06 stronger, m99J02 overridden to faithful above). These checks
came after its late reply. One held row is overridden; the other stays held.

- m97A04 (graded narrower, overridden to faithful): the theorem assumes
  `∀ t ∈ Set.Icc 0 1, b t < 0` (Main.lean:569). The source says "if
  b(t)<0 for all t", not "for 0<t<1", so the closed interval is within what
  problem.md states. (The open-interval version is also true, because the
  stencil only evaluates b at interior mesh points, but the problem does not
  ask for it.) The stencil identity (552-568) is the correction from 541f88367.
  Admitted faithful with this file as evidence. This leaves 39 held rows,
  33 of them narrower; `held-raw.txt` still lists m97A04 as raw output.
- m98A05 (narrower): confirmed. The only declaration is `lemma
  apm_m98a05_ift` (line 17), the generic IFT; the perturbation claim (b)
  and the H²(0,π) existence claim (c) were deleted in 93c400876. Not a false
  source: (b) is false for arbitrary ε₀, but the bank already repaired that
  with ε₀ = 0, and (c) is true. Held; not on the false-source list.
- m99J02 (graded vacuous, already overridden): rechecked against the pinned
  Mathlib: `((⊤ : ℕ∞) : WithTop ℕ∞) = ∞` is `rfl` and `≠ ω` by `decide`. The
  jump term is right: g' jumps by u₁(y)u₂'(y) − u₁'(y)u₂(y) = W(y), and
  under the ODE W is constant, so c = W(0) (lines 278-290). Upheld faithful.
- m96J06 (stronger, admitted): the extra conclusion |x| ≤ 1/12 on the ball
  |y| < 1/48 is added to the exact equation. Upheld.
- m99J01 (faithful): ODE imposed only for t ≥ 0 (lines 19-21), uniqueness on
  t ≥ 0, unique ξ = cos ξ with every solution tending to ξ (502-512). Upheld.

## Batch 08 spot-checks

Batch 08 was admitted in the earlier sweep (eight rows registered: six
faithful by the grader, a00J06 stronger, m99J03 overridden to faithful above).
These checks came after its late reply. One admission is revoked; both held
rows are now admitted.

- a00J06 (graded stronger, admission revoked): `f a := (p a).sum`, and
  `FormalMultilinearSeries.sum` is a `tsum`, which Lean sets to 0 where the
  series is not summable. So `f a x = 0` for every x > 1, and the theorem
  `¬ ∃ ρ, 0 < ρ ∧ AnalyticAt ℝ (f a) 1` (Main.lean:93-96) follows from
  "positive just left of 1, zero just right of 1". The proof's own docstring
  takes that route. Pringsheim's theorem is never used, and `ρ` is unused.
  The problem asks that no analytic g near 1 agree with f on the part of the
  disk |z| < 1 near 1; a real form that would be faithful is: no g with
  `AnalyticAt ℝ g 1` and g = f on (1 - r, 1) for some r > 0. Held as
  vacuous (junk-value statement); a repair needs a real proof.
- a00J03 (graded narrower, repaired and admitted faithful): `he_symm` was
  derivable, since μ(φA) = μ(φ⁻¹(φA)) = μ(A). I removed it from
  `composition_isometric_isomorphism` and derived it inside the proof
  from Mathlib's `MeasurePreserving.symm e he`. The file compiles
  (`lake env lean`, warnings only). Admitted with `composition_isometry` and
  `composition_isometric_isomorphism` pinned. The old canary copy under
  `ApmCanaries/Frames/A00J03/` is unchanged.
- a01A03 (graded faithful, admit refused, now admitted): the refusal was
  for the bare ⊤ in `convolution_identity_counterexample` (line 229), the
  compiled refutation of the old analytic-test version. The pin-every-theorem
  fallback in `admit-batch.py` had picked it up. The graded theorem
  `convolution_identity_implies_indicator` (98-104) uses `ContDiff ℝ ∞`;
  admitted with that declaration pinned. Restricting the hypothesis from
  C^1 to C_c^∞ weakens it (so the theorem is at least as strong), and it is
  the class where g * f' is defined for g ∈ L¹.
- m99J03 (narrower, already overridden): rechecked. Same `(⊤ : ℕ∞)`
  test class as m99J02.
- Faithful check, a00J02: f(x)/√x → 0 from the right under absolute
  continuity, f(0) = 0 and f' ∈ L² (lines 119-126). Upheld.

`admit-batch.py` now skips ids in the registry's `revoked` list and reports
them as HELD; without that, rerunning batch 08 re-admitted a00J06. Held
count after batch 08: 38 rows, 32 of them narrower, plus a00J06 revoked.

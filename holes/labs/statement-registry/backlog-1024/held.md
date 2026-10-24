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

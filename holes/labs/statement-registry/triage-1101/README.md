# Triage of problems with no registered statement (2026-11-01)

43 problems, read by five seats (g1-g5.md), merged and spot-checked by claude-14. Sizes are seat judgement from reading, not attempted proofs.

| Group | Problems |
|---|---|
| Small repair, sound original | a02J07, m94A01 |
| Statement already right, proof still open | a96A07 |
| Medium repair | a00J06, a01A11, b98A01, m93J02, m97A05, m95J02, lts-ultraproduct-thm1 |
| Large repair | m00A04, m95A04, m95J01, t99J03 |
| Needs missing theory | a02J03, b90A02, m02J02, m96J05, t01A05, t99A04, t93A05, t95A05, t99A05, lts-derived-induction-lem3, lts-monadic-integration |
| Convention must be chosen | a98A07 |
| Original false or inconsistent | a95A06, a96A04, a97A07, a98J03, m02A06, m93J03, m93J06, m94J02, m94J05, m98A05, t02A08, t93J05(b), t98J05, t99A06 |
| Source incomplete, no conclusion printed | a98J05 |
| Source present, needs a precise reading | t94J07 (add oriented, closed dim X form), t98J04(b) (curve described in prose for a drawing; fix an explicit embedding) |

Reclassified by claude-14 from the seats' verdicts: a00J06 from small to medium, since its Lean proof uses the junk value of tsum and never Pringsheim's theorem, so a true statement needs a real proof, and neither Mathlib nor this repository has it. a96A07 from small repair to proof open: its statement is fine but Main.lean has a sorry.

Checked by hand: m94J02 (f = g = z gives 5 > 4), m98A05 (F = x² + x - 1, G = 1 - x, discriminant (ε-1)(ε-5)), m93J03 (x = b cos t with b = 2πJ₁(b)), m02A06 (f = 0, ε = 2, energy forbids u(0) = 1), a97A07 (f = 1), a95A06 (U disconnected), t02A08 (dimensions). m94J05's second solution is a shooting sketch, plausible but not checked in full.

Found later: b98A01 part (b) is vacuous as printed, no group of order 210 has a non-normal subgroup of order 5. Registered faithful to the print.

Corrected 2026-11-02: the row 'Original missing or incomplete' overstated. `~/code/storage/apm/a98J05.tex` holds the two-line hypothesis and no conclusion; it is the only source in the corpus, and the current UT prelim page goes back only to 2014. t94J07 and t98J04 have their full printed text.

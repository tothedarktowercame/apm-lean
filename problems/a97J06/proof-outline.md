# Proof Outline: a97J06

## Problem

Evaluate ∫₀^∞ cos(tx)/(x²+4) dx for all real t.
Answer: π/4 · e^{-2|t|}.

## Strategy

Contour integration:
1. Evenness: ∫₀^∞ = ½ Re ∫₋∞^∞ e^{itx}/(x²+4).
2. Close upper half-plane for t ≥ 0; pole at z=2i.
3. Residue: e^{-2t}/(4i); theorem gives π/2 · e^{-2t}.
4. ML estimate: arc → 0.
5. Combine: π/4 · e^{-2|t|}.

## Proved (exit 0, 1 sorry)

Statement compiles. 1 sorry: contour integral proof body.

## Phase-A hints used
- #1 `e-codexpilot-evaluate-a-rational-circle-integral-by-separating-interior-and-exterior-poles`: cited.
- #2 `e-j07-reuse-two-pole-partial-fraction-contour-pattern`: cited.
- #6 `math-informal/estimate-by-bounding`: cited (ML estimate).

## Mid-solve lookups
None beyond Phase A.

# Informal Solution: a99J07

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  The bound looks asymmetric: it uses only the supremum on the unit disk yet must control the polynomial everywhere. Direct coefficient bounds (triangle inequality) often overshoot. The trick needs a complex-analysis tool: the maximum modulus principle applied to an auxiliary “reciprocal” polynomial. Students who don’t split into |w|≤1 vs |w|≥1 or who forget to invent q(z)=z^N p(1/z) run out of ideas quickly.

*Key insight.*  Inside the unit disk the inequality is exactly the definition of ‖p‖_∞. Outside, consider q(z)=z^N p(1/z); for |z|≤1 this is analytic, and on |z|=1 it equals p evaluated on the unit circle, so its modulus is bounded by ‖p‖_∞. The maximum modulus principle then controls q everywhere inside, and substituting z=1/w converts the bound back to p.

*Complete proof.*  Let N≥1 and ‖p‖_∞=sup{|p(z)|:|z|≤1}.
- If |w|≤1, then |p(w)|≤‖p‖_∞ by definition, and max{1,|w|}^N=1, so the bound holds.
- If |w|>1, define q(z)=z^N p(1/z). This polynomial is analytic on |z|≤1 (including z=0). On the unit circle |z|=1 we have |q(z)|=|p(1/z)|≤‖p‖_∞. By the maximum modulus principle, |q(z)|≤‖p‖_∞ for every |z|≤1. Put z=1/w (since |w|>1 ⇒ |1/w|<1) to get |p(w)|=|w|^N|q(1/w)|≤|w|^N ‖p‖_∞ = ‖p‖_∞ max{1,|w|}^N.
Combining the two cases proves the inequality for all w∈ℂ.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *Unit disk case* → direct consequence of the definition. Lean target: `poly_abs_le_sup_norm_of_norm_le_one`.
2. *Reciprocal polynomial* → define q(z)=z^N p(1/z) and show |q(z)|≤‖p‖_∞ on |z|=1. Lean target: `reciprocal_poly_boundary_bound`.
3. *Maximum modulus principle* → apply to q on |z|≤1 and substitute z=1/w for |w|>1. Lean target: `polynomial_outside_unit_bound`.

**Stage 3 — LEAN FORMALIZATION**

Plan: reuse Mathlib lemmas `Complex.polynomial_maxabs_on_closedBall`. Define `q := Polynomial.reverse p` (the reversal already lives in Mathlib) composed with evaluation at 1/z. Need to prove `Complex.abs (Polynomial.eval₂ _ _ p w) ≤ supNorm * max 1 ‖w‖^N`. Present status: `Main.lean` only imports Mathlib; the actual proof is pending because I still need a lemma relating `Polynomial.reverse` evaluation to `z^N p(1/z)` and a wrapper lemma packaging the maximum modulus principle for polynomials. Once those are written (likely in `Scratch.lean`), the rest should go through. `lake build` deferred until then.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

No additional revision needed; once the reciprocal-polynomial lemma is implemented, the Lean proof will mirror the Stage 1 argument verbatim. EOF

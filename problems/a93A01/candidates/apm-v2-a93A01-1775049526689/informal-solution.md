# Informal Solution: a93A01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** The condition in (b) looks like a statement about derivatives, so it is easy to forget that the function need not be differentiable. Students also mix up which constants depend on what: in (b) the same `N` must work for all pairs once ε is fixed. Finally, the (b) ⇒ (a) direction requires building witness sequences when uniform continuity fails—a standard trick, but easy to overlook.

**Key insight.** For (a) ⇒ (b), extract the usual δ from uniform continuity and take `N = ε/δ`. If the slope exceeds `N`, then the points must be closer than δ, so the uniform-continuity bound already forces `|f(x)-f(y)| < ε`. For (b) ⇒ (a), argue by contrapositive: if `f` is not uniformly continuous there are sequences with `|x_n-y_n| → 0` but `|f(x_n)-f(y_n)| ≥ ε₀`. Their slopes blow up, contradicting the slope condition.

**Proof.**
1. **(a ⇒ b)** Fix ε > 0. By uniform continuity choose δ > 0 so that |x − y| < δ ⇒ |f(x) − f(y)| < ε. Set `N = ε/δ`. Suppose |(f(x) − f(y))/(x − y)| > N. Then |f(x) − f(y)| > N|x − y|, so |x − y| < |f(x) − f(y)|/N ≤ ε/N = δ. The uniform-continuity condition now yields |f(x) − f(y)| < ε.
2. **(b ⇒ a)** Assume the slope condition and suppose uniform continuity fails. Then there exist ε₀ > 0 and sequences (x_n), (y_n) with |x_n − y_n| > 0, |x_n − y_n| → 0, but |f(x_n) − f(y_n)| ≥ ε₀ for all n. Given ε = ε₀/2, let N be the constant from (b). Since |x_n − y_n| → 0, for large n we have |f(x_n) − f(y_n)|/|x_n − y_n| > N, yet |f(x_n) − f(y_n)| ≥ ε₀ ≥ ε, contradicting (b). Hence f must be uniformly continuous.

*Proof sanity pass.* The fragile step is the claim that the slopes of the witness sequences diverge when uniform continuity fails; this uses the fact that the numerator stays ≥ ε₀ while the denominator tends to 0. Both directions are fully proved, so the equivalence stands.

**What connects.** The argument is a standard “ε–δ vs. slope” translation: it shows up whenever you use bounded difference quotients to deduce uniform continuity (e.g., Lipschitz functions), and conversely when you detect a failure of uniform continuity through sequences whose slopes explode.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `uniform_continuity_constants`: supplies δ given ε in part (a).
- `slope_threshold`: defines `N = ε/δ` and translates slope bounds into `|x − y| < δ`.
- `non_uniform_sequences`: if uniform continuity fails, there exist sequences with `|x_n − y_n| → 0` but `|f(x_n) − f(y_n)| ≥ ε₀`.
- `sequence_slopes_blow_up`: for such sequences, the difference quotients exceed any fixed N for large n, contradicting the hypothesis.

**Stage 3 — LEAN FORMALIZATION**

Status: *blocked (missing API/theory).* Mathlib already defines uniform continuity, but there is no ready-made lemma equating it with the slope-threshold property. Proving it formally would require building the contrapositive sequence argument and carefully handling the absolute value of slopes—work that goes beyond the current frame. Consequently `Main.lean` still contains only the default namespace header, and `lake build ApmCanaries.Frames.A93A01.Apm_v2_a93A01_1775049526689.Main` succeeds trivially.

**Stage 4 — FORMAL-TO-INFORMAL REVISION (blocked)**

The Lean gap is exactly the equivalence stated in Stage 1; no part of it has been certified yet. Once a `uniformContinuous_iff_slope_condition` lemma is implemented, the entire Stage 1 proof will be backed by Lean. Until then, the sentence “their slopes blow up, contradicting the slope condition” in Stage 1 is the critical informal step.

# Informal Solution: a99J05

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  Mere decay of ‖f_n‖_1 need not force pointwise control: the norm sees only the “average size,” so a function can be huge on a tiny moving set. Part (a) exploits this loophole; the trap is assuming vanishing L¹ norm already gives almost-everywhere convergence. Part (b) adds a fast geometric decay. The challenge is to translate that analytic hypothesis into a measure-theoretic statement about where the sequence can stay large, and then rule out infinitely many “bad” visits at each point.

*Key insight.*  For (a), cycle through dyadic intervals whose lengths go to zero but which cover every point infinitely often; the indicator functions have ever smaller integrals but never settle down pointwise. For (b), combine Chebyshev/Markov with Borel–Cantelli. The inequality µ{|f_n|>ε} ≤ ε^{-1}‖f_n‖_1 makes the exceptional sets summable, and Borel–Cantelli then shows each point can belong to only finitely many of them, forcing f_n(x)→0.

*Complete proof.*
(a) Enumerate all dyadic subintervals of [0,1]. For each m≥0 and 0≤k<2^m, set
\[
I_{m,k}=[k/2^m,(k+1)/2^m).
\]
Each x∈[0,1) lies in exactly one I_{m,k} for every m. Now list the pairs (m,k) in any sequence (for definiteness, by increasing m and then k), and define
\[
f_n=χ_{I_{m_n,k_n}}.
\]
Then ‖f_n‖_1=|I_{m_n,k_n}|=2^{-m_n}→0 because m_n→∞ along the enumeration. However, every x∈[0,1) belongs to infinitely many of the intervals I_{m,k} (one for each m), hence f_n(x)=1 for infinitely many n and 0 otherwise, so the pointwise limit does not exist anywhere (except possibly at x=1 where all indicators vanish). Thus the sequence fails to converge almost everywhere even though the L¹ norms vanish.

(b) Fix ε>0 and consider the measurable sets E_{n,ε}={x∈[0,1]:|f_n(x)|>ε}. Chebyshev (Markov) gives
\[
μ(E_{n,ε}) ≤ ε^{-1}‖f_n‖_1 ≤ ε^{-1}2^{-n}.
\]
Therefore \(∑_{n} μ(E_{n,ε}) < ∞\). By the Borel–Cantelli lemma (for Lebesgue measure on [0,1]), almost every x belongs to only finitely many of the sets E_{n,ε}. Equivalently, for a.e. x we have |f_n(x)|>ε only finitely often, so |f_n(x)|→0. Since this holds for every rational ε>0, the same conclusion holds for all ε>0, proving f_n(x)→0 almost everywhere.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *Dyadic-interval example* → constructs the sequence χ_{I_{m,k}} with ‖f_n‖_1→0 yet no a.e. convergence. (Lean target: `example_sequence_no_ae_limit`.)
2. *Chebyshev inequality* → µ{|f_n|>ε} ≤ ε^{-1}‖f_n‖_1. (Lean target: `measure_tail_bound`.)
3. *Borel–Cantelli lemma* → summable exceptional measures ⇒ |f_n(x)|>ε only finitely often, hence f_n(x)→0. (Lean target: `tendsto_zero_ae_from_summable`.)

**Stage 3 — LEAN FORMALIZATION**

Status: `Main.lean` currently imports Mathlib and the plan but contains no finished statements yet. Part (a) requires encoding the enumeration of dyadic intervals and showing their indicator functions sit in `L¹`. I have sketched this in `Scratch.lean`, but the bookkeeping lemma that every x lies in infinitely many enumerated intervals still needs to be formalized. Part (b) hinges on Chebyshev plus the Borel–Cantelli lemma. Mathlib has both ingredients (`MeasureTheory.measure_gt_mul_le_add` and `MeasureTheory.borelCantelli_zero`), but they are packaged for general measures. I still need to assemble them into a lemma of the form
```
lemma tendsto_zero_of_l1_geometric
```
that concludes `ae` convergence; wiring this up is the remaining blocker before running `lake build`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal solution mirrors the Lean plan exactly: build the moving-indicator example for (a), then apply Chebyshev plus Borel–Cantelli for (b). Once the dyadic-interval enumeration and the “summable exceptional sets ⇒ ae convergence” lemma are formalized, the Lean code will match the prose line-for-line. EOF

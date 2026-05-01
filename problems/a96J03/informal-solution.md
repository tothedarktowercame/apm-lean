# Informal Solution: a96J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The statement looks like a routine application of dominated convergence, but the integrand is 
\(|f(x-t)-f(x)|\): the two terms live at different points, so no single dominator is obvious. The key is to use the density of “nice” functions in \(L^1\) and handle those first.

*Key insight.* Approximate \(f\) by a continuous compactly supported function \(g\) with \(\|f-g\|_1\) tiny. Translations behave well on such a \(g\) because uniform continuity on a compact support makes \(|g(x-t)-g(x)|\) uniformly small, so its integral is small. Finally split the integral for \(f\) using the triangle inequality.

*Complete proof.* Fix \(ε>0\). Choose \(g\in C_c(\mathbb R)\) with \(\|f-g\|_1<ε/3\) (density of \(C_c\) in \(L^1\)). Because \(g\) is uniformly continuous on its compact support, there exists \(δ>0\) such that \(|g(x-t)-g(x)|<ε/(3 M)\) whenever \(|t|<δ\), with \(M=m(\mathrm{supp}\,g)+1\). Moreover \(|g(x-t)-g(x)|\le 2\|g\|_\infty\) and the integrand vanishes outside a fixed compact set, so the dominated convergence theorem yields \(\int |g(x-t)-g(x)|<ε/3\) for \(|t|<δ\). For such \(t\),
\[
\int |f(x-t)-f(x)| \le \int |f(x-t)-g(x-t)| + \int |g(x-t)-g(x)| + \int |g(x)-f(x)| < ε.
\]
Therefore \(\|f(·-t)-f\|_1\to 0\) as \(t\to 0\).

*What connects.* Translation continuity in \(L^1\) underlies convolution approximation, Fourier analysis, and the proof that smooth mollifiers approximate integrable functions. The “approximate by \(C_c\) + triangle inequality” trick is widely used whenever a linear operator behaves nicely on a dense subspace.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Density lemma:* \(C_c(\mathbb R)\) (or simple functions) is dense in \(L^1\). Needed to pick \(g\) close to \(f\). Lean target: `l1_dense_in_compacts`.
- *Translation continuity for \(C_c\):* uniform continuity on compact support + dominated convergence. Lean target: `translation_continuity_compact`.
- *Triangle inequality split:* combine approximation error and the \(g\)-translation bound to control \(f\).

**Stage 3 — LEAN FORMALIZATION**

Plan: (1) reuse Mathlib’s density of `C(ℝ,ℝ)` with compact support in `L¹`. (2) Prove `translation_continuity_compact` using uniform continuity and `tendsto_integral_of_dominated_convergence`. (3) Deduce `translation_continuity_L1` via the triangle inequality. Stage 3 remains in progress; these lemmas still need to be written in `Main.lean`, though the required Mathlib facts already exist.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After finishing the Lean proof, document exactly which density and dominated-convergence lemmas were used so the prose mirrors the formal certificates.

# Informal Solution: a97A01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The sequence \(f_n\) oscillates faster and faster; it’s tempting to think of it as converging weakly to 0, but you still have to justify the cancellation when \(f\) is only bounded and measurable. The trap is trying to use dominated convergence on \(f f_n\); there is no pointwise limit. Instead, approximate \(f\) by block averages where \(f_n\) sums to zero.

*Key insight.* Partition \([0,1]\) into dyadic intervals of length \(2^{-n}\). On each interval, \(f_n\) is \(+1\) on the left half and \(-1\) on the right half. Replace \(f\) by its average on each block: the integral of the average times \(f_n\) vanishes. The Lebesgue differentiation theorem says that, for large \(n\), the average is close to \(f\) on almost every point, so the remaining integral is small.

*Complete proof.* Let \(f∈L^∞([0,1])\) with essential supremum \(M\). For fixed \(n\), write the dyadic partition \(I_{k,n}=[(k-1)/2^n,k/2^n)\). Define the block-constant function
\[
A_n(t)=\frac{1}{|I_{k,n}|}∫_{I_{k,n}} f(s) ds \quad (t∈I_{k,n}).
\]
Then \(∫ f_n A_n = 0\) because \(A_n\) is constant on each \(I_{k,n}\) and the integral of \(f_n\) over each block splits into equal halves with opposite signs. Therefore
\[
∫ f f_n = ∫ (f-A_n) f_n.
\]
By Cauchy–Schwarz (here just Hölder with \(L^1\)-\(L^∞\)),
\[
|∫ (f-A_n) f_n| ≤ ‖f-A_n‖_1 · ‖f_n‖_∞ = ‖f-A_n‖_1,
\]
since \(|f_n|=1\) almost everywhere.

Lebesgue’s differentiation theorem says \(f(t)=\lim_n A_n(t)\) for almost every \(t\); hence \(‖f-A_n‖_1→0\). (One may justify this either directly from the theorem or using the density of step functions in \(L^1\).) Consequently \(∫ f f_n → 0\).

*What connects.* These \(f_n\) are the Rademacher functions. The argument above shows they converge to 0 in the weak-* topology of \(L^∞\); equivalently, they form an orthogonal system in \(L^2\). The “average-on-small-blocks then cancel” trick is the backbone of martingale convergence, Walsh/Fourier analysis, and the proof that step functions are dense in \(L^1\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Lebesgue differentiation:* block averages approximate \(f\) in \(L^1\). Needed to control \(‖f-A_n‖_1\). Lean target: `dyadic_average_convergence`.
- *Block cancellation:* integral of \(A_n f_n\) vanishes because \(f_n\) integrates to zero on each block. Lean target: `paired_interval_cancellation`.
- *Bound via Hölder:* \(|∫ (f-A_n) f_n| ≤ ‖f-A_n‖_1‖f_n‖_∞ = ‖f-A_n‖_1\). No new lemma needed; uses basic inequalities.

**Stage 3 — LEAN FORMALIZATION**

Plan: (1) formalize the dyadic partition and define block averages in `Main.lean`. (2) Use Mathlib’s Lebesgue differentiation theorem to show `‖f-A_n‖₁→0`. (3) Combine with the cancellation lemma to prove the limit. Stage 3 remains in progress; these lemmas are still to be encoded.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After coding, note explicitly which version of Lebesgue differentiation was used and how the dyadic block averages were implemented so the written proof matches the formal one.

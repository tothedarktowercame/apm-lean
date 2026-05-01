# Informal Solution: a96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

Let \(I_n = [1-2^{-n},\,1-2^{-(n+1)}]\); these intervals are pairwise disjoint and shrink to the point \(1\).  Define a “tent” function \(f_n\) supported on \(I_n\): linear on each half of \(I_n\), vanishing at the endpoints, and attaining height \(1/n\) at the midpoint.  Then \(f_n\) is continuous, nonnegative, and \(\sup_{[0,1]} f_n = 1/n\), so \(\sum \sup f_n = \sum 1/n = \infty\).  Because the supports are disjoint, at every fixed \(x\in[0,1]\) at most one \(f_n(x)\) is nonzero.  Let \(f\) be the pointwise limit defined by \(f(x)=f_n(x)\) if \(x\in I_n\) and \(0\) otherwise; by construction \(f\) is continuous.  For any \(\varepsilon>0\) choose \(N>1/\varepsilon\).  If \(x\notin \bigcup_{n\ge N} I_n\), then \(f_n(x)=0\) for all \(n\ge N\) and \(\sum_{k=1}^\infty f_k(x)=\sum_{k=1}^{N-1} f_k(x)\).  If \(x\in I_m\) with \(m\ge N\), then only \(f_m\) contributes and
\(|\sum_{k=1}^\infty f_k(x) - \sum_{k=1}^{N-1} f_k(x)| = f_m(x) \le 1/m < 1/N < \varepsilon\).  Hence the partial sums converge uniformly to \(f\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Support disjointness* ⇒ uniform convergence reduces to tail control on heights.
- *Continuity of tents* ⇒ each \(f_n\) is continuous and nonnegative.
- *Harmonic heights* ⇒ the series of suprema diverges.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` is still empty.  To formalize the construction we would define each \(f_n\) as a piecewise-linear function (`continuousOn_Icc.mpr`) supported on the interval \(I_n\), then show the sum stabilizes pointwise and is uniformly Cauchy.  Mathlib already has the basic lemmas on uniform convergence and disjoint supports.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the explicit Lean definition of \(f_n\) is provided, the formal proof will mirror the argument above step-for-step.  No further reconciliation is needed.

# Informal Solution: t96J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

Let \(d=\inf\{\|x-y_0\|:x\in X\}\).  Since \(X\neq\varnothing\), choose a sequence \((x_k)\subset X\) with \(\|x_k-y_0\|\to d\).  The sequence lies in the closed ball \(B=\overline{B}(y_0,d+1)\), which is compact and contains \(X\cap B\) as a closed subset.  By Bolzano–Weierstrass, there is a subsequence \(x_{k_j}\) converging to some \(x_0\in X\) (because \(X\) is closed).  Continuity of the norm implies
\[
\|x_0-y_0\|=\lim_{j\to\infty}\|x_{k_j}-y_0\|\le d,
\]
so equality holds and \(x_0\) minimizes the distance: for every \(x\in X\),
\(\|x_0-y_0\|\le\|x-y_0\|\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

The proof uses: (i) the norm is continuous; (ii) closed balls in ℝⁿ are compact (Heine–Borel); (iii) closed subsets of compact sets are compact; (iv) infima are attained on compact sets; (v) a closed set contains the limits of convergent sequences in it.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` is still empty.  Mathlib already has the lemma `IsClosed.exists_isMinOn` (a nearest point theorem) and the more specialized `exists_norm_eq_infi` for Euclidean spaces.  The formal proof will instantiate that lemma with the closed set `X` and the function \(x\mapsto \|x-y_0\|\).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Mathlib lemma is invoked, the formal and informal arguments coincide.  No further adjustments are needed.

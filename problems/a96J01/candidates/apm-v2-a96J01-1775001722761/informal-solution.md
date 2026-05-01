# Informal Solution: a96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Uniform convergence usually suggests applying the Weierstrass $M$-test, so your instinct is that $\sum \|f_n\|_\infty$ must converge. The trap is that the hypothesis only says “partial sums converge uniformly,” not “$\sum \|f_n\|_\infty$ converges.” If you concentrate each $f_n$ on a different subinterval of $[0,1]$, no two bumps are ever active at the same point. The tails are uniformly small even though the sup norms add up like the harmonic series.

***Key insight.***  Use disjoint supports: let $I_n=[1-2^{-n}, 1-2^{-(n+1)}]$ and let $f_n$ be the continuous “tent” over $I_n$ with height $1/n$ at its midpoint and value $0$ at the endpoints. Because the $I_n$ only meet at endpoints (where the tents vanish), at any $x$ at most one $f_n(x)$ is nonzero.

***Complete proof.***  (1) Define $f_n$ as above. Each $f_n$ is nonnegative and continuous on $[0,1]$, satisfies $\|f_n\|_\infty=1/n$, and has support contained in $I_n$. (2) For every $x$ there is at most one index $n$ with $f_n(x)>0$. Hence for every $N$ and every $x$, $\sum_{n\ge N} f_n(x) \le \sup_{n\ge N} \|f_n\|_\infty = 1/N$. This uniform tail bound implies the partial sums converge uniformly to the pointwise sum $f(x)=\sum_n f_n(x)$. (3) Because $\|f_n\|_\infty=1/n$, the series $\sum \|f_n\|_\infty$ diverges. Therefore the desired example exists.

***What connects.***  This is the classical way to show that uniform convergence does not imply absolute convergence of sup norms. The same trick—spreading the mass over disjoint intervals—appears in counterexamples to the Weierstrass $M$-test and in constructive proofs of approximation theorems.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Dyadic geometry.*  The endpoints $1-2^{-n}$ guarantee the supports are pairwise disjoint (except for endpoints where the tents vanish).
- *Tent continuity.*  Writing $f_n(x)=\max(0,1-|x-c_n|/r_n)$ shows each $f_n$ is continuous and nonnegative.
- *Uniform tail bound.*  At any $x$ the tail consists of at most one positive term, so $\sup_x \sum_{n\ge N} f_n(x) \le 1/N$, which yields uniform convergence.

**Stage 3 — LEAN FORMALIZATION**

- *Type signature.*  The target statement `tent_sequence_exists` (see `formal-alignment.edn`) asserts the existence of $f : \mathbb N \to C([0,1],\mathbb R)$ with the three properties above.
- *Status — blocked.*  Mathlib provides the Banach-space structure on `C([0,1], ℝ)` and the divergence of the harmonic series, but it lacks convenient constructors for these piecewise linear tent functions together with the lemmas about their disjoint supports. Implementing them would require a substantial amount of bespoke real-analysis code (continuity proofs for `max`/`abs` combinations on subtypes, dyadic-interval arithmetic, “at most one active index” lemmas). With the current time budget that work is not yet written, so `Main.lean` remains a stub. To finish, one would need to define the tents, prove they form a nonnegative sequence with the harmonic sup norms, and then encode the tail bound in the sup norm.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the tent constructors are available, the Lean proof will follow Stage 1 verbatim: disjoint supports give the uniform tail estimate, and evaluating at the midpoint shows each sup norm equals its prescribed height. Until then, the informal proof above serves as the authoritative argument and `formal-alignment.edn` documents the intended Lean target.

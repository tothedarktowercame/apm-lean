# Informal Solution: a96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

# Stage 1 — reader-facing solution
## Why it’s hard
Uniform convergence usually goes hand-in-hand with the Weierstrass M-test, so people instinctively expect \(\sum \\sup f_n\) to converge. The puzzle asks you to make the M-test fail while uniform convergence still holds; the trap is thinking “positive terms + divergent majorant ⇒ no uniform convergence.” The way around it is to let the bumps live on disjoint pieces, so tails of the series never add more than one bump at a time.

## Key insight
Tile \([0,1]\) by a chain of shrinking intervals \([\frac{n}{n+1}, \frac{n+1}{n+2}]\) creeping toward 1. On each interval, draw a tent function of height \(1/(n+1)\) that vanishes at the endpoints. At any fixed \(x\) only finitely many tents are ever nonzero, and for tails beyond \(N\) you see at most one bump, so the tail error is \(\le 1/(N+1)\). Yet the sum of heights \(\sum 1/(n+1)\) diverges, so the series of sup norms blows up.

## Complete proof
For \(n\ge 0\) let \(I_n=[a_n,b_n]=[\frac{n}{n+1}, \frac{n+1}{n+2}]\). Define the tent function
\[
  f_n(x)= \frac{1}{n+1}\,\max\Bigl(1-\frac{|x-c_n|}{r_n},0\Bigr),
\]
where \(c_n=(a_n+b_n)/2\) and \(r_n=(b_n-a_n)/2=1/(2(n+1)(n+2))\). Each \(f_n\) is continuous, nonnegative, supported in \(I_n\), and attains height \(1/(n+1)\). The supports intersect only at endpoints where the tents vanish.

Let \(S_N(x)=\sum_{n=0}^{N-1} f_n(x)\). For any \(x\) and \(N\), the tail \(\sum_{n\ge N} f_n(x)\) has at most one nonzero term, so
\[
  0 \le \bigl|S(x)-S_N(x)\bigr| \le \sup_{n\ge N} \|f_n\|_{\infty} = \frac{1}{N+1}.
\]
Hence \(S_N\) converges uniformly to the continuous function \(S\) obtained by piecing together the tents. Finally,
\[
  \sum_{n=0}^{\infty} \sup_{[0,1]} f_n = \sum_{n=0}^{\infty} \frac{1}{n+1}=\infty
\]
(divergence of the harmonic series). Thus the required sequence exists.

## What connects / exam kit
The same trick (disjoint supports ⇒ uniform control of tails) appears in counterexamples contrasting the M-test with uniform convergence, in constructing continuous but nowhere differentiable functions, and in building Schauder bases. When you need uniform convergence without absolute convergence, localize the mass.

# Stage 2 — lemma dependency graph
`proof-plan.edn` records the moving parts: (i) partition \([0,1]\) into disjoint shrinking intervals; (ii) manufacture triangular bumps of prescribed height; (iii) use the “one bump per tail” argument to show uniform convergence; (iv) observe that \(\sum \|f_n\|=\sum 1/(n+1)\) diverges. The alignment file states the target theorem in `ContinuousMap` language along with a helper lemma about tails over disjoint supports.

# Stage 3 — Lean formalization
I attempted to encode the explicit tent functions in `C(Icc 0 1, ℝ)` so that the partial sums converge in the sup norm but the supremum norms add up to the harmonic series. This requires a piecewise-linear constructor in `ContinuousMap` (something like a `ContinuousMap.piecewise` or “hat” builder) to define a function that is linear on \([a_n,c_n]` and `[c_n,b_n]` and zero outside. A search for such an API (`rg -n "ContinuousMap.piecewise" .lake/packages/mathlib`) returned no hits, so the missing ingredient is a reusable `ContinuousMap` helper for gluing continuous branches along shared endpoints. Adding that would let us instantiate the above construction verbatim. Without it, the Lean file `ApmCanaries/Frames/A96J01/Apm_v2_a96J01_1774999742972/Main.lean` still contains only the default stub.

# Stage 4 — back-propagation
Once the `ContinuousMap`-piecewise tool is in place, the Lean development will mirror the paper argument: define the hat functions, prove the tail bound \(\|S-S_N\|_{\infty}\le 1/(N+1)\), derive uniform convergence, and calculate the sup norms. The informal proof already reflects these steps.

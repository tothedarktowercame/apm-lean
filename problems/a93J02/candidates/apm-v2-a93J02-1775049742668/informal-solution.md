# Informal Solution: a93J02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it's hard.*  The alternating harmonic series is only conditionally convergent, so the usual algebraic tricks that work for absolutely convergent series (termwise integration, rearrangements, etc.) fail.  The expression \((-1)^n/(n+1)\) does not come from the usual Taylor series evaluated inside its interval of convergence, so we cannot simply quote a power-series identity.  The right way to pin the sum down is to recognise each term as an integral and then exchange the limit of the partial sums with that integral; the trap is that this “integration under the limit'' must be justified with a precise convergence theorem.

*Key insight.*  For each \(n\) we can write
\[
\frac{(-1)^n}{n+1}=\int_0^1 (-x)^n\,dx.
\]
If we set \(S_N(x)=\sum_{k=0}^N (-x)^k\), then the \(N\)-th partial sum of the alternating harmonic series equals \(\int_0^1 S_N(x)\,dx\).  On the interval \([0,1]\) the geometric identity
\(S_N(x)=\frac{1-(-x)^{N+1}}{1+x}\) shows that \(|S_N(x)|\le 2/(1+x)\); that bound is integrable and does not depend on \(N\).  Moreover \(S_N(x)\to \frac{1}{1+x}\) for every \(x\in[0,1)\) (and the single bad point \(x=1\) has measure zero).  The dominated convergence theorem therefore lets us take the limit inside the integral and identify the series with \(\int_0^1\frac{dx}{1+x}=\log 2\).

*Complete proof.*  For each integer \(n\ge 0\) the elementary integral formula \(\int_0^1 x^n\,dx=1/(n+1)\) gives
\[
\frac{(-1)^n}{n+1}=(-1)^n\int_0^1 x^n\,dx=\int_0^1 (-x)^n\,dx.
\]
Let \(S_N(x)=\sum_{k=0}^N (-x)^k\).  Then
\[
\sum_{k=0}^N \frac{(-1)^k}{k+1}=\int_0^1 S_N(x)\,dx.
\]
Because the geometric sum satisfies \(S_N(x)=\frac{1-(-x)^{N+1}}{1+x}\) whenever \(x\ne -1\), we have the bound
\[
|S_N(x)|\le \frac{1+|(-x)^{N+1}|}{1+x}=\frac{1+x^{N+1}}{1+x}\le \frac{2}{1+x}
\]
for every \(x\in[0,1]\).  The function \(g(x)=2/(1+x)\) lies in \(L^1([0,1])\).  For each fixed \(x\in[0,1)\) the factor \((-x)^{N+1}\) tends to zero, so \(S_N(x)\) converges to \(f(x)=1/(1+x)\); the convergence fails at \(x=1\), but that single point does not affect an integral.  Thus the dominated convergence theorem applies on the interval \([0,1]\) with dominating function \(g\) and pointwise limit \(f\).  We obtain
\[
\lim_{N\to\infty} \sum_{k=0}^N \frac{(-1)^k}{k+1}
 =\lim_{N\to\infty} \int_0^1 S_N(x)\,dx
 =\int_0^1 \frac{dx}{1+x}
 =\log(1+x)\big\rvert_{0}^{1}=\log 2.
\]
Therefore the alternating harmonic series converges and its sum equals \(\log 2\).

*What connects.*  Turning a slowly convergent alternating sum into an integral and then using dominated convergence is a standard exam-day manoeuvre; it also appears when evaluating \(\sum (-1)^n/(n+a)\), when proving Abel summation for alternating Dirichlet series, and when analysing Fourier series via Cesàro averages.  The essential pattern is: represent each term as an integral, identify a uniformly integrable dominating function, and then swap limit and integral.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Integral representation.*  Show that \((-1)^n/(n+1)=\int_0^1 (-x)^n dx\); this follows from \(\int_0^1 x^n dx=1/(n+1)\).
- *Geometric sum control.*  Use the closed form \(S_N(x)=(1-(-x)^{N+1})/(1+x)\) to deduce \(|S_N(x)|\le 2/(1+x)\) on \([0,1]\).
- *Dominated convergence.*  The bound above makes \(S_N\) uniformly integrable, while \(S_N(x)\to 1/(1+x)\) for almost every \(x\in[0,1]\).  The DCT therefore yields \(\lim_N\int S_N=\int \lim_N S_N\).
- *Evaluation of the limit integral.*  Compute \(\int_0^1 (1/(1+x)) dx=\log 2\).
- *Series conclusion.*  Combine the steps to identify the alternating harmonic series with \(\log 2\).

**Stage 3 — LEAN FORMALIZATION**

*Status:* blocked.

I started encoding the analytic argument directly in Lean: I defined a `geomPartial` function for the partial sums \(S_N(x)\), sketched a closed-form expression `geomPartial_closed_form`, and set up the plan to use `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`.  Unfortunately this spiralled: getting the absolute-value bound `|S_N(x)| ≤ 2/(1+x)` required a fair amount of inequality plumbing, and wiring that into the dominated-convergence API forced me to juggle several interval-integral lemmas.  I burned too much time wrestling with these auxiliary bounds (and even managed to corrupt the working file during one of the editing attempts), so the Lean file currently only contains the original namespace stub.  The missing pieces are exactly the lemmas outlined in Stage 2 together with the final invocation of `tendsto_integral_filter_of_dominated_convergence`; once those are in place, the final theorem would follow mechanically.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode:* blocked.  The Stage 1 proof still rests on the dominated convergence argument, and that step has not yet been formalised in Lean; until `geomPartial_closed_form`, the domination estimate, and the interval integral computation are implemented, the informal proof remains stronger than the current formal artefact.

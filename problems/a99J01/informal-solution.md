<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J01: A Jensen bound — $\int_E \log|f| \le -\lambda(E)\log\lambda(E)$ for an $L^1$ density

## Why It's Hard

The inequality ties a *logarithmic* integral of $f$ to a purely *geometric* quantity in the measure of $E$ alone — the right-hand side $-\lambda(E)\log\lambda(E)$ does not see $f$ at all. So whatever $f$ does on $E$, only its total $L^1$ mass ($=1$ globally) is allowed to matter. The log integral is delicate: $\log|f|$ is $-\infty$ wherever $f$ vanishes and is positive wherever $|f|>1$, so one must first check the integral even makes sense before bounding it. The right move is to stop thinking of $\lambda$ as the ambient (possibly infinite) measure and instead **renormalize $E$ into a probability space**, turning "$\int_E \log|f|$" into an *average* of $\log|f|$. Once it is an average, concavity of $\log$ (Jensen) converts it into the log of an average, and the global constraint $\|f\|_1=1$ caps that average by $1/\lambda(E)$. The difficulty is seeing that the bizarre-looking $-\lambda(E)\log\lambda(E)$ is just $\lambda(E)\cdot\log(1/\lambda(E))$ — the normalization factor times Jensen.

## The Key Insight

Set $t=\lambda(E)\in(0,\infty)$ and let $\mu = \tfrac{1}{t}\,\lambda|_E$ be the **normalized (probability) measure on $E$**. Two facts combine:

1. **Jensen for the concave logarithm.** Since $\log$ is concave and $\mu$ is a probability measure,
$$\int_E \log|f|\,d\mu \;\le\; \log\!\left(\int_E |f|\,d\mu\right).$$
(Average of $\log$ $\le$ $\log$ of average.)

2. **The global mass constraint.** Because $|f|\ge 0$ and $\|f\|_1=1$,
$$\int_E |f|\,d\mu = \frac{1}{t}\int_E |f|\,d\lambda \;\le\; \frac{1}{t}\int_X |f|\,d\lambda = \frac{1}{t}.$$

Feeding (2) into (1) (with $\log$ increasing) and unwinding $\mu = \lambda|_E/t$ gives $\frac1t\int_E\log|f|\,d\lambda \le \log\frac1t = -\log t$, i.e. $\int_E\log|f|\,d\lambda \le -t\log t$. The whole content is "renormalize, then Jensen, then use $\|f\|_1=1$."

## Complete Proof

Let $t=\lambda(E)$, with $0<t<\infty$, and define the probability measure $\mu=\tfrac1t\,\lambda|_E$ on $E$ (so $\mu(E)=1$, and $\int_E g\,d\mu = \tfrac1t\int_E g\,d\lambda$ for $g\ge0$ or $g\in L^1$).

**Step 0: the integral $\int_E \log|f|\,d\lambda$ is well-defined in $[-\infty,+\infty)$.**
Write $\log|f| = (\log|f|)^+ - (\log|f|)^-$. For $s>0$ one has the elementary bound $\log s \le s$, hence $(\log|f|)^+ = \max(\log|f|,0) \le |f|$ pointwise (this also holds where $f=0$, since there $(\log|f|)^+=0$). Therefore
$$\int_E (\log|f|)^+\,d\lambda \le \int_E |f|\,d\lambda \le \|f\|_1 = 1 < \infty.$$
So the positive part is integrable, and $\int_E\log|f|\,d\lambda$ is a well-defined element of $[-\infty,+\infty)$. If it equals $-\infty$, the desired inequality holds trivially; assume henceforth it is finite (equivalently, $\log|f|\in L^1(E,\lambda)$).

**Step 1: dispose of the degenerate mass case.**
If $\int_E|f|\,d\lambda = 0$, then $f=0$ $\lambda$-a.e. on $E$, so $\log|f|=-\infty$ a.e. on $E$ and $\int_E\log|f|\,d\lambda=-\infty$, and again the inequality holds. So assume $\int_E|f|\,d\lambda>0$; then $a:=\int_E|f|\,d\mu = \tfrac1t\int_E|f|\,d\lambda \in (0,\infty)$ and $\log a$ is finite.

**Step 2: Jensen's inequality.**
The function $\varphi(s)=\log s$ is concave on $(0,\infty)$. Apply Jensen's inequality to the nonnegative measurable $|f|$ against the probability measure $\mu$:
$$\int_E \log|f|\,d\mu \;\le\; \log\!\left(\int_E |f|\,d\mu\right) = \log a.$$
(The hypotheses are met: $\int_E|f|\,d\mu=a<\infty$, and by Step 0 the left integral is well-defined with integrable positive part, so Jensen for concave functions applies, the left side lying in $[-\infty,\log a]$.)

**Step 3: apply the global $L^1$ bound.**
Since $|f|\ge 0$ and $E\subseteq X$,
$$a = \int_E|f|\,d\mu = \frac{1}{t}\int_E|f|\,d\lambda \le \frac{1}{t}\int_X|f|\,d\lambda = \frac{1}{t}\,\|f\|_1 = \frac{1}{t}.$$
Because $\log$ is increasing, $\log a \le \log\frac1t = -\log t$. Combined with Step 2,
$$\int_E \log|f|\,d\mu \;\le\; -\log t.$$

**Step 4: unnormalize.**
Multiply both sides by $t=\lambda(E)>0$ and use $\int_E\log|f|\,d\mu = \tfrac1t\int_E\log|f|\,d\lambda$:
$$\int_E \log|f|\,d\lambda \;\le\; -t\log t \;=\; -\lambda(E)\,\log\lambda(E).$$
This is the claimed inequality, valid for every $E\in\mathcal{A}$ with $0<\lambda(E)<\infty$. $\qquad\blacksquare$

**Sanity check.** Equality is approached when $|f|$ is (essentially) constant on $E$ and carries all the mass there: if $|f|=\tfrac1t \mathbf{1}_E$, then $\int_E|f|\,d\lambda=1$, $a=1/t$, and $\int_E\log|f|\,d\lambda = t\log(1/t) = -t\log t$ — the bound is attained, confirming it is sharp.

## What Connects

**Within analysis / information theory.** This is a clean instance of the **Jensen + normalization** pattern: to bound an integral of a concave (or convex) function over a set, renormalize the set to a probability space so the integral becomes an expectation, then apply Jensen. The appearance of $-\lambda(E)\log\lambda(E)$ is not a coincidence — it is an **entropy** term: writing $p=|f|\,d\lambda$ as a (sub)probability density, $\int_E \log|f|\,d\lambda$ is a log-likelihood and $-t\log t$ is the entropy of the uniform distribution on a set of mass $t$. The same concavity-of-$\log$ mechanism underlies the **Gibbs inequality** / nonnegativity of Kullback–Leibler divergence and the AM–GM inequality (its integral form). The sharpness case ($f$ uniform on $E$) is exactly the "maximum entropy under a support constraint" configuration. The well-definedness care in Step 0 ($\log^+ s\le s$) is the standard device for making log-integrals of $L^1$ densities meaningful, recurring in the definition of differential entropy and of $\int f\log f$ functionals.

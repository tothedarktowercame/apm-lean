<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A03: When does $f(1)-f(0)=\int_0^1 f'$? (Cantor function vs. the MVT)

## Why It's Hard

The question looks like the Fundamental Theorem of Calculus, but it is really a question about *which* hypotheses make FTC true. The setup is deliberately weak: $f$ is only continuous, and $f'$ is only assumed to exist **almost everywhere** with a finite essential supremum. That is just enough rope to hang yourself — bounding the derivative where it exists says nothing about what $f$ does on the (possibly nonempty) measure-zero set where $f'$ fails to exist, and *all* of a function's increase can hide on a set of measure zero. So the first question is a trap inviting a counterexample, while the second question quietly strengthens the hypothesis to everywhere-differentiability on the open interval plus Riemann integrability of $f'$ — exactly the combination that lets a Mean-Value-Theorem argument convert the telescoping sum $\sum [f(x_i)-f(x_{i-1})]$ into a Riemann sum of $f'$. The difficulty is recognizing that the *same* equation is false in part one and true in part two, and seeing precisely which extra assumption flips it.

## The Key Insight

**Part 1 — the equation can fail.** The bound $\esssup f' < \infty$ is not enough, because $f$ need not be *absolutely continuous*. The Cantor function $c$ is the decisive witness: it is continuous, $c(0)=0$, $c(1)=1$, and $c'(x)=0$ for almost every $x$ (so $\esssup c' = 0 < \infty$), yet $\int_0^1 c' = 0 \ne 1 = c(1)-c(0)$. A function can climb from $0$ to $1$ while its derivative is zero almost everywhere — all the climbing happens on the measure-zero Cantor set, where $c'$ does not exist.

**Part 2 — the extra hypotheses force the equation.** Once $f'$ exists at **every** point of $(0,1)$ and is **Riemann integrable**, the Cantor pathology is impossible (the Cantor function is *not* differentiable on the Cantor set, so it is excluded). The engine is the **Mean Value Theorem**: on each piece of a partition, $f(x_i)-f(x_{i-1}) = f'(t_i)\,(x_i-x_{i-1})$ for some interior tag $t_i$. Summing telescopes the left side to $f(1)-f(0)$ and exhibits the right side as a tagged Riemann sum of $f'$; Riemann integrability makes every such sum converge to $\int_0^1 f'$ as the mesh shrinks. (The hint's "intermediate value theorem" is **Darboux's theorem** — the intermediate value property *of derivatives* — which guarantees $f'$ is a well-behaved Darboux function; the MVT is what actually produces the equality.)

## Complete Proof

Throughout, "$\int_0^1 g$" denotes the Riemann integral and $m$ Lebesgue measure.

### Part 1: In general the equation is FALSE.

**Claim.** There is a continuous $f:[0,1]\to\mathbb{R}$ with $f'$ existing a.e. and $\esssup_{[0,1]} f' < \infty$, for which $f(1)-f(0)\ne \int_0^1 f'(t)\,dt$.

**Construction.** Let $f = c$ be the **Cantor function** (the "devil's staircase"), built on the standard middle-thirds Cantor set $C$. Recall its properties:

1. $c$ is continuous and non-decreasing on $[0,1]$, with $c(0)=0$ and $c(1)=1$.
2. $c$ is *locally constant on the complement of $C$*: on each open middle-third interval removed in the construction, $c$ takes a constant value. The removed intervals are open, disjoint, and their lengths sum to $\sum_{k\ge 1} 2^{k-1}\cdot 3^{-k} = 1$, so their union $[0,1]\setminus C$ has measure $1$, i.e. $m(C)=0$.

**The derivative.** At every point $x \in [0,1]\setminus C$, $x$ lies in one of the open intervals on which $c$ is constant, so $c$ is differentiable there with $c'(x)=0$. Since $m([0,1]\setminus C)=1$, we have
$$c'(x) = 0 \quad\text{for almost every } x\in[0,1].$$
In particular $c'$ exists a.e. and $\esssup_{[0,1]} c' = 0 < \infty$, so $c$ satisfies every hypothesis of the problem.

**The equation fails.** Since $c' = 0$ a.e.,
$$\int_0^1 c'(t)\,dt = \int_0^1 0\,dt = 0,$$
whereas
$$c(1)-c(0) = 1 - 0 = 1.$$
Thus $c(1)-c(0) = 1 \ne 0 = \int_0^1 c'(t)\,dt$, so the equation does **not** hold in general. $\qquad\blacksquare$

**Why it fails (the moral).** The Cantor function is *singular*: it is not absolutely continuous, and all of its increase is concentrated on the measure-zero set $C$, precisely where $c'$ does not exist. A bound on $f'$ *where it exists* controls nothing on that exceptional set. The correct general statement (Lebesgue's FTC) requires $f$ to be **absolutely continuous**, which is strictly stronger than "continuous with bounded a.e.-derivative."

### Part 2: With $f'$ existing on all of $(0,1)$ and $f'$ Riemann integrable, the equation is TRUE.

**Theorem.** Let $f$ be continuous on $[0,1]$, differentiable at every $x\in(0,1)$, with $f'$ Riemann integrable on $[0,1]$. Then
$$f(1)-f(0) = \int_0^1 f'(t)\,dt.$$

**Proof.** Let $\varepsilon > 0$. Because $f'$ is Riemann integrable on $[0,1]$, there is a $\delta>0$ such that for **every** tagged partition $\{(x_{i-1},x_i],\,\xi_i\}$ with mesh $\max_i (x_i-x_{i-1}) < \delta$,
$$\left| \sum_{i=1}^n f'(\xi_i)\,(x_i-x_{i-1}) \;-\; \int_0^1 f'(t)\,dt \right| < \varepsilon, \tag{$\ast$}$$
**regardless of how the tags $\xi_i$ are chosen** (this tag-independence is exactly the content of Riemann integrability).

Fix any partition $0 = x_0 < x_1 < \cdots < x_n = 1$ with mesh $< \delta$. On each subinterval $[x_{i-1},x_i] \subseteq [0,1]$, the function $f$ is continuous on $[x_{i-1},x_i]$ and differentiable on the open interval $(x_{i-1},x_i)\subseteq(0,1)$. Hence the **Mean Value Theorem** applies: there exists a tag
$$t_i \in (x_{i-1},x_i) \quad\text{with}\quad f(x_i)-f(x_{i-1}) = f'(t_i)\,(x_i-x_{i-1}).$$

Now sum over $i$. The left side **telescopes**:
$$\sum_{i=1}^n \big(f(x_i)-f(x_{i-1})\big) = f(x_n)-f(x_0) = f(1)-f(0),$$
while the right side is the tagged Riemann sum of $f'$ with the MVT tags $t_i$:
$$f(1)-f(0) = \sum_{i=1}^n f'(t_i)\,(x_i-x_{i-1}).$$

Applying $(\ast)$ to this particular (valid) choice of tags $\xi_i = t_i$:
$$\left| \big(f(1)-f(0)\big) - \int_0^1 f'(t)\,dt \right| < \varepsilon.$$

The left-hand quantity $f(1)-f(0)-\int_0^1 f'$ does not depend on $\varepsilon$, yet it is smaller in absolute value than every $\varepsilon>0$. Therefore it is $0$:
$$f(1)-f(0) = \int_0^1 f'(t)\,dt. \qquad\blacksquare$$

**Remark on the hint (Darboux / the IVT for derivatives).** A derivative need not be continuous, so one might worry $f'$ is too wild to integrate or to control. **Darboux's theorem** — the intermediate value theorem *for derivatives* — guarantees that $f'$, being a derivative, has the intermediate value property: it cannot jump over values, and in particular has no jump discontinuities. This is the sense in which the intermediate value theorem is "relevant": it certifies $f'$ is a Darboux function, well-behaved enough that the only obstruction to integrability would be an oscillation/discontinuity set of positive measure — which is excluded here by the explicit Riemann-integrability hypothesis. The equality itself, however, is delivered by the Mean Value Theorem as above.

### Summary

- **General case:** **No** — the Cantor function gives $f(1)-f(0)=1\ne 0=\int_0^1 f'$ despite $\esssup f' = 0$. Bounded a.e.-derivative ⇏ FTC; absolute continuity is what is missing.
- **Strengthened case:** **Yes** — everywhere-differentiability on $(0,1)$ plus Riemann integrability of $f'$ makes the MVT-to-Riemann-sum argument go through, and the equation holds.

## What Connects

**Within analysis.** This problem is the boundary case between the two Fundamental Theorems of Calculus. The naive (continuous + a.e.-differentiable) hypotheses are governed by **Lebesgue's FTC**, whose correct sufficient condition is **absolute continuity**; the gap between "bounded a.e.-derivative" and "absolutely continuous" is exactly inhabited by **singular functions** like the Cantor staircase (and, more generally, the Lebesgue decomposition of a monotone function into absolutely continuous + singular parts). The second part is the **Riemann-theoretic FTC**: continuity on the closed interval, differentiability on the open interval, and Riemann integrability of the derivative. The proof technique — apply the **MVT** on each cell of a partition to manufacture tags, then exploit tag-independence of Riemann sums — is the canonical way to prove FTC without assuming $f'$ is continuous, and it is where **Darboux's theorem** (IVT for derivatives) explains why dropping continuity of $f'$ is harmless.

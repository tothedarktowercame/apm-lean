<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m00A02: Poincaré asymptotic expansions — definition, the e^{-x} null case, why differentiation can fail, and when it works

## Why It's Hard

The whole problem lives on the gap between *asymptotic* and *convergent*, and each
part probes a different consequence of that gap. Part (a) just wants the **Poincaré
definition**, but stated correctly: it is a statement about *partial sums and
remainders*, not about the series converging (it usually diverges). Part (b) is
the canonical lesson that the scale $\{x^{-n}\}$ is **blind to exponential decay**:
$e^{-x}$ beats every power, so its expansion is identically zero — already showing
expansions are *not unique*. Part (c) exploits exactly that blindness: take a
function that is asymptotically zero but whose *derivative* oscillates with
amplitude $\to1$; differentiation amplifies the invisible $e^{x}$-scale wiggle into
something $O(1)$. The trap in (d) is thinking you need strong smoothness — what you
actually need is the **existence of an expansion for $f'$**; then, because
**integration of asymptotic series is always legal** (unlike differentiation), you
integrate $f'$ back and match coefficients to force it to be the termwise
derivative. (Note: the series displayed in the problem for the differentiated
expansion has a typo; the genuine formal derivative of $\sum a_n x^{-n}$ is
$-\sum_{n\ge1} n a_n x^{-n-1}$.)

## The Key Insight

Write $S_N(x)=\sum_{n=0}^N a_n x^{-n}$. The definition is *remainder control at
every order*:
$$
f\sim\sum_{n\ge0}\frac{a_n}{x^n}\iff
\forall N:\ x^{N}\Bigl(f(x)-S_N(x)\Bigr)\xrightarrow[x\to+\infty]{}0 .
$$
Three consequences drive the rest:
- **(b)** $x^N e^{-x}\to0$ for all $N$, so $e^{-x}\sim\sum 0\cdot x^{-n}$.
- **(c)** $f(x)=e^{-x}\sin(e^{x})$ has $|f|\le e^{-x}$, so $f\sim0$; but
  $f'(x)=\cos(e^{x})-e^{-x}\sin(e^{x})$ does **not** tend to $0$, so $f'\not\sim0$
  — formal differentiation (which gives $0$) is invalid.
- **(d)** If *also* $f'\sim\sum b_n x^{-n}$, then integrating
  ($\int_x^\infty f'=a_0-f$) and using uniqueness of coefficients forces
  $b_0=b_1=0$ and $b_n=-(n-1)a_{n-1}$, i.e. $f'$ **is** the termwise derivative.

The asymmetry "integrate freely, differentiate only with a license" is the whole
story.

## Complete Proof

### Part (a): definition of asymptotic expansion

Let $f$ be real-valued, defined for large $x$. We say $f$ is **asymptotic to the
series** $\sum_{n=0}^\infty a_n x^{-n}$ as $x\to+\infty$, written
$f(x)\sim\sum_{n=0}^\infty a_n x^{-n}$, if for **every** nonnegative integer $N$,
$$
f(x)-\sum_{n=0}^{N}\frac{a_n}{x^n}=o\!\left(\frac1{x^{N}}\right)\quad(x\to+\infty),
\qquad\text{equivalently}\qquad
\lim_{x\to+\infty}x^{N}\Bigl(f(x)-\sum_{n=0}^{N}\frac{a_n}{x^n}\Bigr)=0 .
$$
Crucially, the series is **not** required to converge; the condition concerns only
the partial sums $S_N$ and the decay of each remainder $f-S_N$. (Equivalently, one
may demand $f-S_N=O(x^{-(N+1)})$ for every $N$.)

The coefficients are then **uniquely determined** by $f$, recursively:
$$
a_0=\lim_{x\to\infty}f(x),\qquad
a_N=\lim_{x\to\infty}x^{N}\Bigl(f(x)-\sum_{n=0}^{N-1}\frac{a_n}{x^n}\Bigr).
\tag{$\ast$}
$$

### Part (b): $e^{-x}$ is asymptotic to the null expansion

Take $a_n=0$ for all $n$, so $S_N\equiv0$ for every $N$. We must check
$x^{N}\bigl(e^{-x}-0\bigr)\to0$ for each $N$. Indeed, for fixed $N$,
$$
x^{N}e^{-x}\xrightarrow[x\to+\infty]{}0,
$$
since the exponential dominates every power (e.g. $x^N e^{-x}=x^N/e^{x}$ and
$e^{x}\ge x^{N+1}/(N+1)!$ gives $x^N e^{-x}\le (N+1)!/x\to0$). Hence for every $N$,
$e^{-x}-S_N(x)=e^{-x}=o(x^{-N})$, so
$$
e^{-x}\sim\sum_{n=0}^\infty\frac{0}{x^n}=0 .
$$
$\checkmark$ (This already shows asymptotic expansions are not unique: $e^{-x}$ and
$0$ share the same expansion.)

### Part (c): formal differentiation can fail

Let
$$
f(x)=e^{-x}\sin\!\bigl(e^{x}\bigr).
$$
This is $C^\infty$ on $\mathbb{R}$.

**$f$ is asymptotic to the null expansion.** Since $|\sin|\le1$,
$$
|f(x)|=\bigl|e^{-x}\sin(e^x)\bigr|\le e^{-x},
$$
so $x^{N}|f(x)|\le x^{N}e^{-x}\to0$ for every $N$ (part (b)). Thus $f\sim\sum
0\cdot x^{-n}$, the null expansion ($a_n=0$ for all $n$). Its formal derivative is
the null series as well (every term $-n a_n x^{-n-1}=0$).

**But $f'$ is not asymptotic to the null series.** Differentiating,
$$
f'(x)=-e^{-x}\sin(e^{x})+e^{-x}\cos(e^{x})\cdot e^{x}
=\cos(e^{x})-e^{-x}\sin(e^{x}).
$$
As $x\to+\infty$ the second term $e^{-x}\sin(e^x)\to0$, while
$\cos(e^{x})$ **oscillates** through all of $[-1,1]$ and has no limit. Hence
$f'(x)\not\to0$; in particular the $N=0$ requirement fails:
$x^{0}\bigl(f'(x)-0\bigr)=f'(x)$ does not tend to $0$. So $f'\not\sim0$.

Therefore $f\sim\sum 0\cdot x^{-n}$ does **not** imply $f'\sim$ (formal derivative
$=0$): term-by-term differentiation of an asymptotic expansion can be invalid even
for $C^\infty$ functions. $\quad\checkmark$

### Part (d): a hypothesis making differentiation valid

**Hypothesis.** Suppose $f$ is $C^1$ for large $x$, $f(x)\sim\sum_{n\ge0}a_n
x^{-n}$, **and in addition $f'$ itself possesses an asymptotic power-series
expansion** $f'(x)\sim\sum_{n\ge0}b_n x^{-n}$ as $x\to+\infty$.

**Claim.** Then that expansion is forced to be the term-by-term derivative:
$$
f'(x)\sim\sum_{n\ge1}(-n)\,a_n\,x^{-n-1}
=-\frac{a_1}{x^2}-\frac{2a_2}{x^3}-\cdots,
$$
i.e. $b_0=b_1=0$ and $b_n=-(n-1)a_{n-1}$ for $n\ge2$.

We use two standard facts and prove the only non-routine one.

**Fact 1 (uniqueness).** Coefficients of an asymptotic expansion are determined by
the function, via $(\ast)$.

**Fact 2 (integration is always valid).** *If $g(x)\sim\sum_{n\ge2}c_n x^{-n}$,
then $\int_x^\infty g(t)\,dt\sim\sum_{n\ge2}\dfrac{c_n}{n-1}\,x^{-(n-1)}$.* Proof:
for each $N\ge2$, $g(t)-\sum_{n=2}^N c_n t^{-n}=o(t^{-N})$; since $N\ge2$ all terms
are integrable on $[x,\infty)$, and integrating,
$$
\int_x^\infty g(t)\,dt-\sum_{n=2}^N\frac{c_n}{n-1}x^{-(n-1)}
=\int_x^\infty\Bigl(g(t)-\sum_{n=2}^N c_n t^{-n}\Bigr)dt .
$$
Given $\varepsilon>0$, eventually the integrand is $\le\varepsilon t^{-N}$ in
absolute value, so the right side is $\le\varepsilon\int_x^\infty t^{-N}dt
=\frac{\varepsilon}{N-1}x^{-(N-1)}=o(x^{-(N-1)})$. This is exactly the assertion.

**Step 1: $b_0=b_1=0$.** Since $f\sim\sum a_n x^{-n}$, $f(x)\to a_0$ (finite).
- If $b_0\neq0$, then $f'(x)\to b_0\neq0$, so $f'$ keeps one sign for large $x$ and
  $f(x)\to\pm\infty$ — contradicting $f\to a_0$. Hence $b_0=0$, i.e. $f'(x)\to0$.
- Now $f'(x)\sim b_1 x^{-1}+\cdots$, so $x f'(x)\to b_1$. If $b_1\neq0$, then
  $f'(t)=b_1/t+o(1/t)$, and $f(X)-f(x_0)=\int_{x_0}^X f'=b_1\ln(X/x_0)+\int_{x_0}^X
  o(1/t)\,dt$. Choosing the error rate $\varepsilon<|b_1|$ eventually, the right
  side $\to\pm\infty$, again contradicting $f\to a_0$. Hence $b_1=0$.

So $f'(x)\sim\sum_{n\ge2}b_n x^{-n}$.

**Step 2: match coefficients by integrating $f'$.** Because $f'(x)=O(x^{-2})$ it is
integrable near $\infty$, and by the Fundamental Theorem of Calculus together with
$f(X)\to a_0$,
$$
\int_x^\infty f'(t)\,dt=\lim_{X\to\infty}f(X)-f(x)=a_0-f(x).
$$
Apply Fact 2 with $g=f'$ ($c_n=b_n$, $n\ge2$):
$$
a_0-f(x)=\int_x^\infty f'(t)\,dt\ \sim\ \sum_{n\ge2}\frac{b_n}{n-1}\,x^{-(n-1)}
=\sum_{m\ge1}\frac{b_{m+1}}{m}\,x^{-m}.
$$
Hence $f(x)\sim a_0-\sum_{m\ge1}\frac{b_{m+1}}{m}x^{-m}$. Comparing with the given
$f(x)\sim a_0+\sum_{m\ge1}a_m x^{-m}$ and invoking uniqueness (Fact 1),
$$
a_m=-\frac{b_{m+1}}{m}\quad(m\ge1)\ \Longrightarrow\ b_{n}=-(n-1)\,a_{n-1}\quad(n\ge2).
$$

**Conclusion.** Therefore
$$
f'(x)\sim\sum_{n\ge2}b_n x^{-n}=\sum_{n\ge2}\bigl(-(n-1)a_{n-1}\bigr)x^{-n}
=\sum_{m\ge1}(-m\,a_m)\,x^{-m-1},
$$
which is precisely $\dfrac{d}{dx}\sum_{m\ge0}a_m x^{-m}$ (since
$\frac{d}{dx}a_m x^{-m}=-m a_m x^{-m-1}$). So under the hypothesis that **$f'$ has
an asymptotic expansion**, formal term-by-term differentiation is valid.
$\quad\blacksquare$

### Remark

The clean dividing line is: *integrate asymptotic series with impunity, but
differentiate only when you already know $f'$ has an expansion.* Part (c)'s
$e^{-x}\sin(e^x)$ violates the license — its derivative has no expansion at all
(it oscillates) — which is exactly why differentiation fails. A common alternative
sufficient hypothesis is **analyticity in a sector**: if $f$ is holomorphic and
$f\sim\sum a_n z^{-n}$ uniformly in a sector $|\arg z|\le\theta$, then Cauchy's
estimates let you differentiate the expansion term by term (the derivative
expansion is automatic, so the result of (d) applies). The recurring moral from
(b)–(c) is that the power scale $\{x^{-n}\}$ cannot see — and differentiation can
resurrect — exponentially small oscillation.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02J06: Mollification and Kolmogorov–Riesz compactness in $L^{1}$

## Why It's Hard

This is a compactness problem in an *infinite-dimensional* space, so Heine–Borel
is useless: closed and bounded does not imply compact in $L^{1}(\mathbb{R})$. You need a
genuine compactness criterion — the Kolmogorov–Riesz–Fréchet theorem — whose
hypotheses are (i) uniform boundedness, (ii) uniform $L^{1}$-equicontinuity of
translation, and (iii) uniform decay at infinity.

The subtlety is that the smoothness you are *handed* is the wrong **kind**. The
defining bound on $K$ is an *averaged* ($L^{1}$) modulus of continuity,
$\int|f(x+h)-f(x)|dx \leq h^{1/2}$. The functions in $K$ need not be continuous at all,
so Arzelà–Ascoli — the tool you instinctively want — cannot touch $K$ directly.

The whole problem is a single engineered maneuver: **mollify**. Convolving with
$\varphi_\epsilon$ turns each rough $f$ into an honestly continuous $f \ast \varphi_\epsilon$. Part (a) says
the mollified copy is uniformly close to the original; part (b) says the
mollified family is genuinely (pointwise) equicontinuous, with the $L^{1}$ Hölder-$1/2$
bound reincarnated as a *pointwise* Hölder-$1/2$ bound. Then Arzelà–Ascoli applies to
the smooth family, and the uniform approximation of (a) transfers total
boundedness back down to $K$. Parts (a) and (b) are not side-quests; they are the
scaffolding of part (c).

## The Key Insight

The mollifier is a **bridge between two notions of smoothness**: the weak,
averaged $L^{1}$ modulus of continuity that $K$ actually possesses, and the strong,
pointwise equicontinuity that Arzelà–Ascoli demands.

Both convolution estimates collapse onto the *same* one-line input — the single
translation bound $\|\tau_t f - f\|_{1} \leq |t|^{1/2}$ — which is exactly the defining
property of $K$. In (a) you integrate that bound against $\varphi_\epsilon$ (supported in
$|t| \leq \epsilon$), so the error inherits $\epsilon^{1/2}$. In (b) you pull the difference of
translates out under the integral and integrate against $|\varphi_\epsilon| \leq M/\epsilon$, so the
modulus inherits $(M/\epsilon)|x-y|^{1/2}$. The Hölder exponent $1/2$ survives untouched in
both directions because each estimate reduces to that one translation bound. Once
the smooth family $K_\epsilon$ is uniformly bounded, uniformly compactly supported, and
Hölder-$1/2$ equicontinuous, Arzelà–Ascoli finishes it, and $\epsilon^{1/2} \to 0$ does the
rest.

## Complete Proof

Throughout, $\|\cdot\|$ denotes the $L^{1}(\mathbb{R})$ norm and $\tau_t f(x) := f(x - t)$. We assume
the standard *nonnegative* mollifier: $\varphi \in C_0^\infty(\mathbb{R})$, $\varphi \geq 0$, $\int \varphi = 1$,
$\varphi(x) = 0$ for $|x| \geq 1$, and $\max|\varphi| = M$. Then
$\varphi_\epsilon(x) = \epsilon^{-1} \varphi(x/\epsilon)$ satisfies $\varphi_\epsilon \geq 0$, $\int \varphi_\epsilon = 1$,
$\max|\varphi_\epsilon| = M/\epsilon$, and $\varphi_\epsilon(t) = 0$ for $|t| \geq \epsilon$.

**The one translation bound we use repeatedly.** The defining property of $K$,
$\int|f(x+h) - f(x)|dx \leq h^{1/2}$ for $h > 0$, extends to all real $t$ by
translation invariance of Lebesgue measure: for $t < 0$, writing $t = -s$ with
$s > 0$ and substituting $y \mapsto y + s$,
$\int|f(y+t) - f(y)|dy = \int|f(y) - f(y+s)|dy \leq s^{1/2} = |t|^{1/2}$. Hence

$$\|\tau_t f - f\| = \int |f(x-t) - f(x)|\,dx \le |t|^{1/2}\quad\text{for all }t\in\mathbb{R}. \tag{$\ast$}$$

---

### (a)  $\|f - f \ast \varphi_\epsilon\| \leq \epsilon^{1/2}$

Since $\int \varphi_\epsilon = 1$, we may write $f(x) = \int f(x)\,\varphi_\epsilon(t)\,dt$, so

$$f(x) - (f \ast \varphi_\epsilon)(x) = \int \big[f(x) - f(x-t)\big]\,\varphi_\epsilon(t)\,dt.$$

Taking absolute values, using $\varphi_\epsilon \geq 0$, and integrating in $x$, Tonelli's
theorem lets us swap the order of integration:

$$\|f - f\ast\varphi_\epsilon\|
= \int_x \left| \int_t [f(x)-f(x-t)]\varphi_\epsilon(t)\,dt \right| dx
\le \int_t \varphi_\epsilon(t) \left( \int_x |f(x)-f(x-t)|\,dx \right) dt.$$

The inner integral is $\|f - \tau_t f\| \leq |t|^{1/2}$ by $(\ast)$. Since $\varphi_\epsilon$ is
supported in $|t| \leq \epsilon$, we have $|t|^{1/2} \leq \epsilon^{1/2}$ on that support, so

$$\|f - f\ast\varphi_\epsilon\| \le \int_t \varphi_\epsilon(t)\,|t|^{1/2}\,dt
\le \epsilon^{1/2} \int \varphi_\epsilon(t)\,dt = \epsilon^{1/2}\cdot 1 = \epsilon^{1/2}.$$

This bound is **uniform over** $f \in K$, since $(\ast)$ holds for every $f \in K$. ∎

---

### (b)  $K_\epsilon$ is equicontinuous:  $|f \ast \varphi_\epsilon(x) - f \ast \varphi_\epsilon(y)| \leq (M/\epsilon)|x-y|^{1/2}$

Write the convolution as $(f \ast \varphi_\epsilon)(x) = \int f(x-t)\,\varphi_\epsilon(t)\,dt$. Then

$$(f\ast\varphi_\epsilon)(x) - (f\ast\varphi_\epsilon)(y)
= \int \big[f(x-t) - f(y-t)\big]\,\varphi_\epsilon(t)\,dt,$$

so, bounding $|\varphi_\epsilon| \leq \max|\varphi_\epsilon| = M/\epsilon$,

$$\big|(f\ast\varphi_\epsilon)(x) - (f\ast\varphi_\epsilon)(y)\big|
\le \frac{M}{\epsilon} \int |f(x-t) - f(y-t)|\,dt.$$

Substitute $u = y - t$ (Lebesgue measure is translation invariant), so
$x - t = u + (x-y)$:

$$\int |f(x-t) - f(y-t)|\,dt = \int |f(u + (x-y)) - f(u)|\,du = \|\tau_{-(x-y)} f - f\| \le |x-y|^{1/2}$$

by $(\ast)$ with $t = -(x-y)$. Therefore

$$\big|(f\ast\varphi_\epsilon)(x) - (f\ast\varphi_\epsilon)(y)\big|
\le \frac{M}{\epsilon}\,|x-y|^{1/2},$$

with the same $M$, and the bound is identical for every $f \in K$ — i.e. $K_\epsilon$ is
(uniformly) equicontinuous, indeed uniformly Hölder-$1/2$. ∎

---

### (c)  $K$ is compact in $L^{1}(\mathbb{R})$

We read the third defining condition of $K$ as the **uniform compact-support
(tightness)** requirement that there is a fixed bounded set outside of which
every $f \in K$ vanishes; concretely, take $f(x) = 0$ for $|x| \geq 1$ for all
$f \in K$. (This is the condition Kolmogorov–Riesz needs to control mass escaping
to infinity; the source statement is garbled at this point.) We show $K$ is
**totally bounded** and **closed** in the complete space $L^{1}(\mathbb{R})$, hence compact.

**Step 1 — Reduce to $K_\epsilon$.** Fix $\eta > 0$ and choose $\epsilon \in (0,1]$ with
$\epsilon^{1/2} < \eta/2$. By part (a), every $f \in K$ lies within $\eta/2$ (in $L^{1}$) of
$f \ast \varphi_\epsilon \in K_\epsilon$. Hence any finite $(\eta/2)$-net for $K_\epsilon$ in $L^{1}$ becomes a finite
$\eta$-net for $K$ (enlarge each ball's radius from $\eta/2$ to $\eta$). So it suffices to
show $K_\epsilon$ is totally bounded in $L^{1}$.

**Step 2 — $K_\epsilon$ is a nice family on a fixed compact set.** Let $g = f \ast \varphi_\epsilon$
with $f \in K$.

- *Fixed compact support.* $f$ is supported in $[-1,1]$ and $\varphi_\epsilon$ in $[-\epsilon,\epsilon]$, so
  $g$ is supported in $[-1-\epsilon, 1+\epsilon] \subseteq [-2,2]$ (as $\epsilon \leq 1$).
- *Uniform sup bound.* For each $x$,
  $|g(x)| = |\int f(x-t)\varphi_\epsilon(t)\,dt| \leq \max|\varphi_\epsilon|\cdot\|f\| \leq (M/\epsilon)\cdot 1 = M/\epsilon$,
  using $\|f\| \leq 1$. So $\|g\|_\infty \leq M/\epsilon$ uniformly over $K_\epsilon$.
- *Equicontinuity.* By part (b), $|g(x) - g(y)| \leq (M/\epsilon)|x-y|^{1/2}$ — a single
  modulus of continuity for the whole family.

**Step 3 — Arzelà–Ascoli, then back to $L^{1}$.** On the fixed compact interval
$[-2,2]$, $K_\epsilon$ is a uniformly bounded, equicontinuous family of continuous
functions, so by the **Arzelà–Ascoli theorem** it is totally bounded in
$C([-2,2])$ under the sup norm. Because every $g \in K_\epsilon$ is supported in $[-2,2]$
(length $4$), sup-norm proximity controls $L^{1}$ proximity:

$$\|g - g'\| = \int_{-2}^{2} |g - g'|\,dx \le 4\,\|g - g'\|_\infty.$$

Thus a finite $(\delta/4)$-net of $K_\epsilon$ in $C([-2,2])$ is a finite $\delta$-net in $L^{1}$, and
$K_\epsilon$ is **totally bounded in $L^{1}$**. By Step 1, so is $K$.

**Step 4 — $K$ is closed.** Each defining condition is preserved under $L^{1}$
limits. Suppose $f_n \in K$ and $f_n \to f$ in $L^{1}$.

- $\|f\| = \lim \|f_n\| \leq 1$ (norm is continuous).
- For each fixed $h$, $\tau_h f_n - f_n \to \tau_h f - f$ in $L^{1}$ (translation is an $L^{1}$
  isometry), so $\int|f(x+h)-f(x)|dx = \lim \int|f_n(x+h)-f_n(x)|dx \leq h^{1/2}$.
- Some subsequence converges a.e., so $f = 0$ a.e. on $|x| \geq 1$ as well.

Hence $f \in K$, and $K$ is closed.

**Conclusion.** $K$ is a closed, totally bounded subset of the complete metric
space $L^{1}(\mathbb{R})$. A closed totally bounded subset of a complete space is compact.
Therefore $K$ is compact. ∎

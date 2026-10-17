<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99J01: Global existence/uniqueness for $u' + u = \cos u$, and convergence to the unique fixed point of cosine

## Why It's Hard

The equation $u'(t) = \cos(u(t)) - u(t)$ is autonomous and the right-hand side $F(u) = \cos u - u$ is as
nice as one could want — but each part needs the *right* general theorem invoked with its hypotheses
actually checked.

- **Part (a)** is not just "Picard–Lindelöf gives a solution": Picard gives a *local* solution. Promoting
  it to existence for **all** $t > 0$ requires ruling out finite-time blow-up, which needs a growth/Lipschitz
  bound on $F$ over *all* of $\mathbb{R}$ (not just near $u_0$) plus a continuation/Grönwall argument. The pleasant
  fact that $F'(u) = -\sin u - 1$ is bounded ($|F'| \le 2$) is exactly what supplies a *global* Lipschitz
  constant and hence both global uniqueness and global existence.
- **Part (b)** asks for a limit at $t = \infty$. The naïve Lyapunov computation $\tfrac{d}{dt}\tfrac12(u-\xi)^2 =
  -(1+\sin c)(u-\xi)^2 \le 0$ only gives *non-increase*, not convergence — the coefficient $1+\sin c$ can
  vanish, so you cannot conclude $u \to \xi$ from monotone energy decay alone. The clean route is **qualitative,
  not quantitative**: the equation has a *unique* equilibrium (the fixed point of cosine), solutions cannot
  cross it (uniqueness), so every solution is eventually *monotone and bounded*, hence convergent, and a
  convergent solution of an autonomous ODE must limit to an equilibrium. The subtlety is proving the
  equilibrium is unique and that the limit is forced to be it.

## The Key Insight

Read the equation as $u' = F(u)$ with $F(u) = \cos u - u$. Two facts drive everything:

- **$F$ is globally Lipschitz:** $F'(u) = -\sin u - 1 \in [-2,0]$, so $|F(u)-F(v)| \le 2|u-v|$ for all
  $u,v$. Picard–Lindelöf + this global bound $\Rightarrow$ a **unique solution existing for all $t \geq 0$** (part a).
- **$F$ is strictly decreasing with a single zero $\xi$:** $\cos \xi = \xi$ has exactly one real root $\xi$ (the
  "Dottie number," $\xi \approx 0.739$), and $F > 0$ left of $\xi$, $F < 0$ right of $\xi$. The constant $u \equiv \xi$ is
  the unique equilibrium; by uniqueness no solution can cross it, so each solution is trapped on one side,
  is therefore **monotone and bounded**, hence converges — and a convergent autonomous trajectory must
  limit to an equilibrium, which can only be $\xi$. So $\lim_{t\to\infty} u(t) = \xi$ (part b), the *same* $\xi$
  for every $u_0$.

## Complete Proof

Write the equation in autonomous form $u'(t) = F(u(t))$, $u(0)=u_0$, where
$$F(u) := \cos u - u, \qquad F'(u) = -\sin u - 1.$$

### (a) Exactly one solution for all $t > 0$

**$F$ is globally Lipschitz.** $F$ is $C^1$ and $F'(u) = -\sin u - 1$ satisfies $-2 \le F'(u) \le 0$, so
$|F'(u)| \le 2$ for all $u$. By the mean value theorem, for any $u, v$,
$$|F(u) - F(v)| = |F'(\eta)|\,|u-v| \le 2\,|u-v|,$$
i.e. $F$ is Lipschitz on all of $\mathbb{R}$ with constant $L = 2$.

**Local existence and uniqueness (Picard–Lindelöf).** Since $F$ is continuous and (locally, indeed
globally) Lipschitz in $u$, the **Picard–Lindelöf theorem (Cauchy–Lipschitz)** gives a unique solution
$u$ of $u' = F(u)$, $u(0)=u_0$, on some interval $[0, T)$, $T > 0$.

**Global existence (no blow-up).** Let $[0, T)$ be the *maximal* interval of existence. $F$ has linear
growth: $|F(u)| \le |\cos u| + |u| \le 1 + |u|$. Hence along the solution
$$\frac{d}{dt}|u(t)| \le |u'(t)| = |F(u(t))| \le 1 + |u(t)|,$$
and Grönwall's inequality gives $|u(t)| \le (|u_0| + 1)e^{t} - 1$ for $t \in [0,T)$. If $T < \infty$, this
bound keeps $u$ bounded on $[0,T)$, so by the continuation theorem the solution extends past $T$ —
contradicting maximality. Therefore $T = \infty$: the solution exists on all of $[0,\infty)$. Uniqueness
on the whole half-line follows from the global Lipschitz bound (two solutions agreeing at $t=0$ satisfy
$|u_1-u_2|' \le 2|u_1-u_2|$, $|u_1-u_2|(0)=0$, so by Grönwall they coincide).

Thus there is **exactly one** solution $u : [0,\infty) \to \mathbb{R}$. *(General theorems used: Picard–Lindelöf for
local existence/uniqueness; Grönwall's inequality and the continuation theorem for global existence.)* ∎

### (b) The limit $\xi = \lim_{t\to\infty} u(t)$ exists and is unique

**Step 1: a unique equilibrium.** Equilibria solve $F(\xi) = 0$, i.e. $\cos \xi = \xi$. The function
$g(\xi) = \cos \xi - \xi$ has $g'(\xi) = -\sin \xi - 1 \le 0$, vanishing only at the isolated points
$\xi = \tfrac\pi2 + 2\pi k$; hence $g$ is **strictly decreasing** on $\mathbb{R}$. Since $g(0) = 1 > 0$ and
$g(\tfrac\pi2) = -\tfrac\pi2 < 0$, the intermediate value theorem and strict monotonicity give a **unique**
root $\xi \in (0, \tfrac\pi2)$. Moreover, because $F = g$ is strictly decreasing with $F(\xi)=0$,
$$F(u) > 0 \ \text{ for } u < ξ, \qquad F(u) < 0 \ \text{ for } u > ξ. \tag{$\dagger$}$$
The constant function $u \equiv \xi$ solves the ODE (since $F(\xi)=0$); it is the unique equilibrium.

**Step 2: solutions cannot cross $\xi$.** Suppose $u_0 \ne \xi$ but $u(t_1) = \xi$ for some $t_1 \ge 0$. Then
$u$ and the constant solution $\xi$ agree at $t_1$; by the uniqueness in part (a), $u \equiv \xi$, forcing
$u_0 = \xi$ — a contradiction. Hence if $u_0 \ne \xi$, then $u(t) \ne \xi$ for all $t$, and by continuity
$u(t) - \xi$ keeps a constant sign. (If $u_0 = \xi$, then $u \equiv \xi$ and trivially $u(t) \to \xi$.)

**Step 3: monotone + bounded $\Rightarrow$ convergent.** Assume $u_0 < \xi$ (the case $u_0 > \xi$ is symmetric). By Step
2, $u(t) < \xi$ for all $t$, so by $(\dagger)$ $u'(t) = F(u(t)) > 0$: $u$ is **strictly increasing** and
**bounded above** by $\xi$. A bounded monotone function converges: $\ell := \lim_{t\to\infty} u(t)$ exists
and $\ell \le \xi$.

**Step 4: the limit is the equilibrium.** Since $F$ is continuous and $u(t) \to \ell$, we have
$u'(t) = F(u(t)) \to F(\ell)$. A $C^1$ function that converges to a finite limit and whose derivative
converges must have derivative limit $0$: if $F(\ell) =: m \ne 0$, then for large $t$, $u'(t)$ has the
fixed sign of $m$ and is bounded away from $0$, so $u(t) = u(t_0) + \int_{t_0}^t u' \to \pm\infty$,
contradicting $u(t) \to \ell$. Hence $F(\ell) = 0$, so $\ell$ is an equilibrium, and by Step 1 the only
equilibrium is $\xi$. Therefore $\ell = \xi$.

In every case $\lim_{t\to\infty} u(t) = \xi$, the unique solution of $\cos \xi = \xi$. So the limit exists and
is **exactly one number** $\xi$ (the same value for every initial datum $u_0$). ∎

**Remark.** The two parts use the two faces of $F(u) = \cos u - u$: *boundedness of $F'$* (global Lipschitz
constant $2$) gives global existence and uniqueness, while *strict monotonicity of $F$* (with its single
zero) gives global asymptotic stability of the unique equilibrium. The qualitative trapping argument
(no crossing $\Rightarrow$ eventual monotonicity $\Rightarrow$ convergence to an equilibrium) sidesteps the failure of the naïve
energy estimate to show decay; the equilibrium $\xi$ is the Dottie number, the unique fixed point of cosine.

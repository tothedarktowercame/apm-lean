<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J02: Local versus global Hölder seminorms — a degenerate seminorm and an incomplete norm on the Hölder space

Throughout, fix a Hölder exponent $0<\alpha<1$ (the genuinely Hölder regime; the
Lipschitz case $\alpha=1$ is remarked on at the end), and assume $\Omega$ is a
compact connected set in $\mathbb R^n$ with more than one point. Recall the two
quantities:
$$\|f\|_{C^\alpha}=\sup_{\substack{x,y\in\Omega\\ x\neq y}}\frac{|f(x)-f(y)|}{|x-y|^\alpha}
\qquad\text{(global Hölder seminorm),}$$
$$\|f\|_{\alpha}=\sup_{x\in\Omega}\ \limsup_{\epsilon\to 0}\
\sup_{(y,z)\in X_{x,\epsilon}}\frac{|f(z)-f(y)|}{|z-y|^\alpha},
\qquad X_{x,\epsilon}=\{(y,z)\in\Omega^2:|y-x|\le\epsilon,\,|z-x|\le\epsilon,\,z\neq y\}$$
(the **local** Hölder seminorm: the worst infinitesimal Hölder quotient,
maximized over base points $x$).

## Why It's Hard

The two seminorms look almost identical, but $\|f\|_\alpha$ is an *infinitesimal*
quantity (a $\limsup$ as $\epsilon\to0$) while $\|f\|_{C^\alpha}$ is a *global*
supremum over all pairs. Three traps:

- **The easy direction hides the hard one.** $\|f\|_\alpha\le\|f\|_{C^\alpha}$ is
  a one-liner (so (b), (c) are nearly free with $K=1$), which tempts you to
  expect symmetry. But the reverse — controlling the global seminorm by the
  local one — is where all the content lives, and it splits: the *qualitative*
  reverse (a) is **true**, the *quantitative* reverse (d) is **false**.
- **(a) is true for a non-obvious reason.** One is tempted to chain along a path
  (using connectedness), but chaining *loses* for $\alpha<1$: $N$ steps of size
  $h/N$ give $\sum(h/N)^\alpha = h^\alpha N^{1-\alpha}\to\infty$. The correct
  proof discards chaining entirely and uses **compactness**: a global Hölder
  blow-up of a *bounded* function can only happen across *short* distances, and
  short-distance blow-ups are exactly what the local seminorm detects, via a
  cluster point.
- **The local seminorm is degenerate.** For $\alpha<1$ it *vanishes on every
  Lipschitz function*, even non-constant ones — because a Lipschitz quotient is
  $\le\Lambda|z-y|^{1-\alpha}\to0$. This single fact sinks (d), makes (e)'s norm
  inequivalent to (f)'s, and ultimately makes (e)'s space **incomplete** while
  (f)'s is the classical Banach Hölder space.

## The Key Insight

**A Hölder blow-up of a bounded function is always a short-distance event.** If
$|f|\le \|f\|_\infty<\infty$, then for pairs at distance $\ge\delta$ the quotient
is $\le 2\|f\|_\infty/\delta^\alpha$ — bounded. So $\|f\|_{C^\alpha}=\infty$ forces
supremizing pairs with $|y_n-z_n|\to0$; compactness sends them to a common
cluster point $x^*$, and there the *local* seminorm already sees the blow-up.
That is why local finiteness controls global finiteness **(a)** — using only
compactness, not connectedness. Conversely the local seminorm, being
infinitesimal, is *blind to macroscopic slope*: it is zero on Lipschitz
functions, so it cannot dominate the global seminorm **(d)**, and the gap between
the two is genuine — large enough that the norm $|\cdot|_\alpha$ it generates is
**not complete** on the very space where the Hölder norm $|\cdot|_{C^\alpha}$ is.

## Complete Proof

### Part (b) — TRUE: $\|f\|_\alpha\le\|f\|_{C^\alpha}$ (and hence (c) with $K=1$)

For any base point $x$ and any $(y,z)\in X_{x,\epsilon}$, the pair $y\neq z$ lies
in $\Omega\times\Omega$, so by definition of the global seminorm
$$\frac{|f(z)-f(y)|}{|z-y|^\alpha}\le\|f\|_{C^\alpha}.$$
Taking $\sup$ over $X_{x,\epsilon}$, then $\limsup_{\epsilon\to0}$, then $\sup_x$
preserves the bound:
$$\boxed{\ \|f\|_\alpha\le\|f\|_{C^\alpha}.\ }$$
In particular $\|f\|_{C^\alpha}<\infty\Rightarrow\|f\|_\alpha<\infty$, proving
**(b)**, and the inequality is exactly **(c)** with $K=1$ (a constant trivially
depending only on $\Omega$). $\blacksquare$

### Part (a) — TRUE: $\|f\|_\alpha<\infty\Rightarrow\|f\|_{C^\alpha}<\infty$

Suppose $\|f\|_\alpha=L<\infty$.

**Step 1 — $f$ is continuous.** Fix $x\in\Omega$. Since
$\limsup_{\epsilon\to0}\sup_{X_{x,\epsilon}}(\cdots)\le L$, there is
$\epsilon_x>0$ with
$$|f(z)-f(y)|\le (L+1)\,|z-y|^\alpha\qquad\text{for all }y,z\in B(x,\epsilon_x)\cap\Omega.$$
Letting $z\to x$ shows $f$ is continuous at $x$ (indeed locally $\alpha$-Hölder).

**Step 2 — $f$ is bounded.** A continuous function on the compact set $\Omega$ is
bounded: $\|f\|_\infty<\infty$.

**Step 3 — global finiteness, by contradiction.** Suppose
$\|f\|_{C^\alpha}=\infty$. Then there are pairs $y_n\neq z_n$ in $\Omega$ with
$$R_n:=\frac{|f(y_n)-f(z_n)|}{|y_n-z_n|^\alpha}\longrightarrow\infty.$$
Because $|f(y_n)-f(z_n)|\le 2\|f\|_\infty$, we get
$|y_n-z_n|^\alpha\le 2\|f\|_\infty/R_n\to0$, hence $|y_n-z_n|\to0$. By
compactness, pass to a subsequence with $y_n\to x^*\in\Omega$; since
$|y_n-z_n|\to0$, also $z_n\to x^*$. Now fix any $\epsilon>0$: for all large $n$,
both $y_n,z_n\in B(x^*,\epsilon)$ with $y_n\neq z_n$, so $(y_n,z_n)\in
X_{x^*,\epsilon}$ and therefore
$$\sup_{X_{x^*,\epsilon}}\frac{|f(z)-f(y)|}{|z-y|^\alpha}\ge R_n\xrightarrow{n}\infty,
\quad\text{i.e.}\quad \sup_{X_{x^*,\epsilon}}(\cdots)=\infty\ \text{ for every }\epsilon>0.$$
Hence $\limsup_{\epsilon\to0}\sup_{X_{x^*,\epsilon}}(\cdots)=\infty$ and
$\|f\|_\alpha\ge\infty$, contradicting $\|f\|_\alpha=L<\infty$. Therefore
$\|f\|_{C^\alpha}<\infty$. $\blacksquare$

*Remark.* The proof uses only **compactness** of $\Omega$ (for the cluster
point); connectedness is not needed for (a)–(d). Note also the asymmetry with the
naive chaining approach, which fails precisely because $\alpha<1$.

### Part (d) — FALSE: no $K$ with $\|f\|_{C^\alpha}\le K\|f\|_\alpha$

The local seminorm is **degenerate**: it vanishes on Lipschitz functions. Indeed
if $f$ is Lipschitz with constant $\Lambda$, then for $y,z\in X_{x,\epsilon}$,
$$\frac{|f(z)-f(y)|}{|z-y|^\alpha}\le \Lambda\,|z-y|^{1-\alpha}\le\Lambda(2\epsilon)^{1-\alpha}
\xrightarrow{\epsilon\to0}0,$$
so $\|f\|_\alpha=0$.

Now take any **non-constant** Lipschitz $f$ on $\Omega$ — e.g.
$f(p)=|p-p_0|$ for a fixed $p_0\in\Omega$, or a non-constant coordinate function;
one exists because $\Omega$ has at least two points. Then $\|f\|_\alpha=0$, while
$f$ is non-constant so $\|f\|_{C^\alpha}>0$. The inequality
$\|f\|_{C^\alpha}\le K\|f\|_\alpha=K\cdot0=0$ is then impossible for any finite
$K$. Hence **(d) is false** — and with it, the quantitative reverse control
fails, even though (a) gives the qualitative reverse. $\blacksquare$

(Consistency check with the hint: (d)$\Rightarrow$(a), so falsity of (d) is
*compatible* with truth of (a); it does not contradict it.)

### Part (e) — TRUE: $|f|_\alpha:=\|f\|_\alpha+\|f\|_\infty$ is a norm

Work on the space $\mathcal E=\{f:\Omega\to\mathbb R\,:\,|f|_\alpha<\infty\}$. The
three norm axioms:

- **Definiteness.** $|f|_\alpha=0\Rightarrow\|f\|_\infty=0\Rightarrow f\equiv0$.
  (The $\|\cdot\|_\infty$ term supplies definiteness even though $\|\cdot\|_\alpha$
  alone is degenerate.)
- **Homogeneity.** Each difference quotient scales by $|c|$, so
  $\|cf\|_\alpha=|c|\,\|f\|_\alpha$; likewise $\|cf\|_\infty=|c|\,\|f\|_\infty$;
  hence $|cf|_\alpha=|c|\,|f|_\alpha$.
- **Triangle inequality.** From
  $\tfrac{|(f+g)(z)-(f+g)(y)|}{|z-y|^\alpha}\le\tfrac{|f(z)-f(y)|}{|z-y|^\alpha}+\tfrac{|g(z)-g(y)|}{|z-y|^\alpha}$,
  and subadditivity of $\sup$, $\limsup$, $\sup_x$, we get
  $\|f+g\|_\alpha\le\|f\|_\alpha+\|g\|_\alpha$; with the sup-norm triangle
  inequality, $|f+g|_\alpha\le|f|_\alpha+|g|_\alpha$.

So $|\cdot|_\alpha$ is a genuine norm on $\mathcal E$. **(e) is true.**
$\blacksquare$

### Part (f) — TRUE: $|f|_{C^\alpha}:=\|f\|_{C^\alpha}+\|f\|_\infty$ is a norm

Identical verification: definiteness from $\|\cdot\|_\infty$; homogeneity; and the
global Hölder seminorm is subadditive
($\|f+g\|_{C^\alpha}\le\|f\|_{C^\alpha}+\|g\|_{C^\alpha}$ by the same quotient
inequality). This is the **classical Hölder norm** on
$C^\alpha(\Omega)=\{f:|f|_{C^\alpha}<\infty\}$. **(f) is true.** $\blacksquare$

### Completeness: the same space, two inequivalent norms

We answered "yes" to both (e) and (f), so we discuss completeness; this is where
the earlier parts interlock (the hint's "truth of some implies something for
others").

**The two norms live on the same space.** By (c) ($K=1$),
$\{|f|_{C^\alpha}<\infty\}\subseteq\{|f|_\alpha<\infty\}$; by (a), the reverse
inclusion holds (local-finite $\Rightarrow$ global-finite, and bounded). Hence
$$\mathcal E=\{|f|_\alpha<\infty\}=\{|f|_{C^\alpha}<\infty\}=C^\alpha(\Omega),$$
the **same underlying set**, carrying the two norms $|\cdot|_\alpha\le|\cdot|_{C^\alpha}$.

**The norms are inequivalent.** On $\Omega\supseteq[0,1]$ (a segment), let
$f_\eta(x)=\sin(x/\eta)$. It is smooth, hence Lipschitz, so $\|f_\eta\|_\alpha=0$
and $\|f_\eta\|_\infty=1$, giving $|f_\eta|_\alpha=1$. But choosing $y,z$ with
$f_\eta(y)=1,\ f_\eta(z)=-1$ at distance $\sim\pi\eta$,
$$\|f_\eta\|_{C^\alpha}\gtrsim\frac{2}{(\pi\eta)^\alpha}\xrightarrow{\eta\to0}\infty,
\qquad\text{so}\qquad \frac{|f_\eta|_{C^\alpha}}{|f_\eta|_\alpha}\to\infty.$$
No constant relates them: $|\cdot|_\alpha$ is **strictly weaker**. (This is the
quantitative shadow of (d): the local seminorm cannot see macroscopic
oscillation.)

**$(C^\alpha,|\cdot|_{C^\alpha})$ is complete.** This is the standard fact that
the Hölder space is Banach. If $(f_k)$ is $|\cdot|_{C^\alpha}$-Cauchy, it is
sup-Cauchy, so $f_k\to f$ uniformly with $f$ continuous; and the quotients
$\tfrac{(f_k-f_m)(z)-\cdots}{|z-y|^\alpha}$ are uniformly small, so passing
$m\to\infty$ gives $\|f_k-f\|_{C^\alpha}\to0$ and $f\in C^\alpha$. Complete.

**$(C^\alpha,|\cdot|_\alpha)$ is NOT complete.** Because $\|\cdot\|_\alpha$
vanishes on Lipschitz functions, *any* uniformly-Cauchy sequence of Lipschitz
functions is $|\cdot|_\alpha$-Cauchy: if $f_k,f_m$ are Lipschitz then $f_k-f_m$ is
Lipschitz, so $\|f_k-f_m\|_\alpha=0$ and $|f_k-f_m|_\alpha=\|f_k-f_m\|_\infty$.
Take $\beta$ with $0<\beta<\alpha$ and the Lipschitz truncations of $x^\beta$ on
$[0,1]$,
$$f_k(x)=\min\{k\,x,\ x^\beta\}\quad\Big(=k x\text{ for }x\le k^{-1/(1-\beta)},\ =x^\beta\text{ after}\Big),$$
each Lipschitz, with $\|f_k-x^\beta\|_\infty\le k^{-\beta/(1-\beta)}\to0$. Thus
$(f_k)$ is $|\cdot|_\alpha$-Cauchy. Its only possible limit (uniform limits are
unique) is $x^\beta$, but
$$\|x^\beta\|_\alpha=\infty\quad\Big(\text{at }x=0:\ \tfrac{t^\beta-0}{t^\alpha}=t^{\beta-\alpha}\to\infty\text{ as }t\to0\Big),$$
so $x^\beta\notin C^\alpha=\mathcal E$. The Cauchy sequence has no limit in the
space: $(C^\alpha,|\cdot|_\alpha)$ is **incomplete**.

**Summary.**

| statement | verdict | reason |
|---|---|---|
| (a) $\|f\|_\alpha<\infty\Rightarrow\|f\|_{C^\alpha}<\infty$ | **TRUE** | compactness: blow-ups are short-range, caught at a cluster point |
| (b) $\|f\|_{C^\alpha}<\infty\Rightarrow\|f\|_\alpha<\infty$ | **TRUE** | $\|f\|_\alpha\le\|f\|_{C^\alpha}$ |
| (c) $\|f\|_\alpha\le K\|f\|_{C^\alpha}$ | **TRUE** | same inequality, $K=1$ |
| (d) $\|f\|_{C^\alpha}\le K\|f\|_\alpha$ | **FALSE** | $\|\cdot\|_\alpha\equiv0$ on Lipschitz; non-constant Lipschitz breaks it |
| (e) $|f|_\alpha$ a norm | **TRUE**, but space **incomplete** | definiteness from $\|\cdot\|_\infty$; weaker norm |
| (f) $|f|_{C^\alpha}$ a norm | **TRUE**, space **complete** | classical Banach Hölder space |

*The $\alpha=1$ caveat.* For the Lipschitz exponent $\alpha=1$ the degeneracy of
(d) disappears: $\|f\|_1$ (local) equals the supremal local Lipschitz constant,
which on a quasiconvex $\Omega$ (e.g. a segment or convex body) coincides with the
global Lipschitz constant, so (d) can hold and the two norms agree. The
phenomena above are specific to the strict Hölder range $0<\alpha<1$.

## What Connects

**To the local-vs-global Hölder dichotomy.** That local Hölder control upgrades
to global control *qualitatively* but not *quantitatively* (and only on suitable
domains in the quantitative case) is a recurring theme: on quasiconvex / John
domains the intrinsic and Euclidean metrics are comparable and the seminorms are
equivalent, while on cusped or slit domains they diverge. Here compactness alone
rescues the qualitative statement (a).

**To equivalent-norm pathologies.** The pair (e)/(f) is a clean textbook example
of *two norms on one vector space that are not equivalent, one complete and one
not*. The incompleteness of $|\cdot|_\alpha$ comes from a seminorm that is too
weak to be closed under uniform limits — the same mechanism by which $C^0$ with
the $L^1$ norm is incomplete.

**To Hölder spaces and their "little" subspaces.** The degeneracy $\|f\|_\alpha=0$
on smooth functions is reminiscent of the *little Hölder space*
$c^\alpha=\overline{C^\infty}^{\,\|\cdot\|_{C^\alpha}}$, the closure of smooth
functions, which is a proper closed subspace of $C^\alpha$. The local seminorm
$\|\cdot\|_\alpha$ measures a "defect of smoothness at infinitesimal scale" and
annihilates exactly the regular part, paralleling how $c^\alpha$ isolates
functions with vanishing fine-scale Hölder oscillation.

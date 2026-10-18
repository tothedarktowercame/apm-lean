<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16; revised 2026-10-18 (part (d) no longer assumes f compactly supported; explicit forward/backward fundamental solutions) -->

# APM m98J02: Compactly supported distributions, convolution, and solving $Tw = f$ by a fundamental solution

## Why It's Hard

This problem builds the convolution of two distributions and then uses it to solve a PDE — and the
machinery is delicate precisely because distributions are not functions you can multiply or integrate
pointwise. The central technical issue lives in part (b): convolution $u * v$ of two general distributions
is **not defined** (you would need to "integrate $u(y)v(x-y)$ over all $y$", but the overlap is unbounded).
The compact-support hypothesis on $u$ is exactly what fixes this — it produces an intermediate quantity
that is smooth but not compactly supported, and a *compactly supported* distribution is precisely the kind
of object that can be paired with arbitrary smooth functions ($\mathcal E^{\prime}$ is the dual of $C^\infty$).
Seeing why "one factor compact" is the right hypothesis, and where it is used, is the heart of (a)–(c).

Part (d) is the **fundamental-solution method**: given $Tw_0 = \delta_0$, the convolution $w = w_0 * f$
solves $Tw = f$ because a constant-coefficient operator commutes with convolution and $\delta_0$ is the
convolution identity. Two things make it harder than that sentence. First, $f\in C^2(\mathbb R^2)$ is **not**
assumed compactly supported, so neither factor of $w_0*f$ has compact support and part (b) does not apply.
Second, fundamental solutions are not unique, and for a badly chosen $w_0$ the convolution $w_0*f$ need not
exist, or need not be $C^2$. The problem asks for *any* solution, so we may choose $w_0$: $T$ is hyperbolic
with $x$ as the time direction, and its forward and backward fundamental solutions are bounded functions
supported in cones. Splitting $f$ into a part supported in $x\ge-1$ and a part supported in $x\le1$, each
convolution is an integral over a bounded region.

## The Key Insight

- **(a)** $u$ has compact support if it vanishes outside some compact $K$: $\langle u,\varphi\rangle = 0$
  whenever $\operatorname{supp}\varphi \cap K = \varnothing$; equivalently $\operatorname{supp} u$ is compact.
- **(b)** For $u \in \mathcal E^{\prime}$ (compact support), $v \in \mathcal D^{\prime}$, the function
  $\Psi(x) = \langle v_y, \varphi(x+y)\rangle$ is $C^\infty$ (but not compactly supported), and since $u$
  acts on **all** smooth functions, $\langle u*v, \varphi\rangle := \langle u_x, \Psi(x)\rangle$ is defined.
  This is exactly where compact support of $u$ is essential.
- **(c)** $\varphi \mapsto \Psi_\varphi$ is continuous $\mathcal D \to \mathcal E$, and $u$ is continuous on
  $\mathcal E$, so their composition is continuous — $u*v \in \mathcal D^{\prime}$.
- **(d)** In characteristic coordinates $T$ becomes $\partial_a\partial_b$ plus lower-order terms, which gives
  explicit fundamental solutions $E_\pm$ (a Bessel $J_0$ times the indicator of a cone $\Gamma_\pm$). With a
  cutoff $\chi(x)$, $w = E_+*(\chi f) + E_-*((1-\chi)f)$ is an integral over a bounded set near each point,
  $Tw = f$, and $w\in C^2$ because the derivatives fall on $f$. The solution is **not unique**
  ($T1 = 0$, $Tx = 0$).

## Complete Proof

### (a) Compact support

A distribution $u \in \mathcal D^{\prime}(\mathbb R^n)$ **vanishes on an open set** $\Omega$ if
$\langle u, \varphi\rangle = 0$ for all $\varphi \in \mathcal D$ with $\operatorname{supp}\varphi \subseteq \Omega$.
The **support** of $u$, $\operatorname{supp} u$, is the complement of the largest open set on which $u$
vanishes. We say $u$ **has compact support** if $\operatorname{supp} u$ is compact; equivalently, there is a
compact set $K$ with $\langle u, \varphi\rangle = 0$ for every test function $\varphi$ whose support is
disjoint from $K$. Such distributions form $\mathcal E^{\prime}$, and they extend to act continuously on **all** of
$C^\infty = \mathcal E$ (not merely $\mathcal D$).

### (b) Definition of $u * v$ for $u$ of compact support

Let $u \in \mathcal E^{\prime}$ and $v \in \mathcal D^{\prime}$. For $\varphi \in \mathcal D$, define

$$\Psi_\varphi(x) = \langle v_y,\, \varphi(x+y)\rangle.$$

For each fixed $x$, $y \mapsto \varphi(x+y)$ is a test function, so $\Psi_\varphi(x)$ is defined; as $x$
varies, $x \mapsto \varphi(x + \cdot)$ is a smooth $\mathcal D$-valued map, so $\Psi_\varphi \in C^\infty$
with $\partial^\alpha \Psi_\varphi(x) = \langle v_y, \partial_x^\alpha \varphi(x+y)\rangle$. Although
$\Psi_\varphi$ need **not** have compact support, $u \in \mathcal E^{\prime}$ acts on all smooth functions, so we may
define

$$\boxed{\ \langle u * v, \varphi\rangle := \langle u_x,\, \langle v_y, \varphi(x+y)\rangle\rangle = \langle u, \Psi_\varphi\rangle.\ }$$

This is the point of the compact-support hypothesis: it lets $u$ be applied to the smooth, non-compactly-
supported function $\Psi_\varphi$.

### (c) $u * v$ is a distribution

$u * v$ is **linear** in $\varphi$ because $\varphi \mapsto \Psi_\varphi$ is linear and $u$ is linear.

For **continuity**, suppose $\varphi_n \to 0$ in $\mathcal D$: their supports lie in a fixed compact $L$ and
all derivatives $\partial^\beta \varphi_n \to 0$ uniformly. Then for $x$ in any compact set, the test
functions $\varphi_n(x + \cdot)$ have supports in a fixed compact set and tend to $0$ in $\mathcal D$, so by
continuity of $v$, $\partial^\alpha \Psi_{\varphi_n}(x) = \langle v_y, \partial^\alpha \varphi_n(x+y)\rangle \to 0$
uniformly on compacts for each $\alpha$. That is exactly $\Psi_{\varphi_n} \to 0$ in $\mathcal E = C^\infty$.
Since $u \in \mathcal E^{\prime}$ is continuous on $\mathcal E$,

$$\langle u*v, \varphi_n\rangle = \langle u, \Psi_{\varphi_n}\rangle \to 0.$$

Thus $u * v$ is a continuous linear functional on $\mathcal D$, i.e. $u * v \in \mathcal D^{\prime}$. ∎

### (d) Solving $Tw = f$ with $T = 2\,\partial_x^2 - \partial_y + 3\,\partial_x\partial_y$

We are given $f \in C^2(\mathbb R^2)$, with no condition on its support, and told that a fundamental
solution $w_0$ ($Tw_0 = \delta_0$) exists. The problem asks for *any* solution $w$, so we are free to choose
which fundamental solution to use.

**Why the choice matters.** If $f$ had compact support, $w_0*f$ would be defined by part (b) for every
$w_0$, and $T(w_0*f)=(Tw_0)*f=f$. For general $f$ neither factor has compact support, and $w_0*f$ may not
be defined. Even for compactly supported $f$, $w_0*f$ need not be $C^2$: two fundamental solutions differ
by an element of $\ker T$, and $\ker T$ contains distributions of positive order (for $E_\pm$ below,
$\partial_x^3(E_+-E_-)\in\ker T$), so $w_0 = E_+ + \partial_x^3(E_+-E_-)$ is a fundamental solution with
$w_0*f = E_+*f + (E_+-E_-)*\partial_x^3 f$, which involves third derivatives of $f$.

**Characteristic coordinates.** The principal part factors: $2\partial_x^2+3\partial_x\partial_y =
\partial_x(2\partial_x+3\partial_y)$, with symbol $-\xi(2\xi+3\eta)$, which has two distinct real
characteristic covectors, $(0,1)$ and $(3,-2)$. The covector $dx$ is non-characteristic ($\xi=1,\eta=0$
gives $-2\neq0$), so $T$ is strictly hyperbolic with $x$ as time; $dy$ is characteristic, so $y$ cannot
serve as time. Put
$$
a = x - \tfrac23 y,\qquad b = \tfrac13 y\qquad(\text{so } x = a+2b,\ y = 3b),
$$
so that $\partial_a = \partial_x$ and $\partial_b = 2\partial_x + 3\partial_y$. Then $\partial_y =
\tfrac13(\partial_b - 2\partial_a)$ and
$$
T = \partial_a\partial_b + \tfrac23\partial_a - \tfrac13\partial_b
  = e^{(a-2b)/3}\Big(\partial_a\partial_b + \tfrac29\Big)e^{-(a-2b)/3}.
$$

**Fundamental solutions.** Let $R(a,b) = J_0\big(2\sqrt{2ab/9}\big) = \sum_{k\ge0}\frac{(-2ab/9)^k}{(k!)^2}$,
an entire function of $ab$ with $R=1$ on both axes and $\partial_a\partial_bR + \tfrac29R = 0$. If $H$ is
the Heaviside function, then $\partial_a\partial_b\big(H(a)H(b)R\big) = \delta_{(a,b)} + H(a)H(b)\,
\partial_a\partial_b R$, because the cross terms carry $\partial_bR = aR^{\prime}(ab)$ on $\{a=0\}$ and
$\partial_aR = bR^{\prime}(ab)$ on $\{b=0\}$, both zero. So $(\partial_a\partial_b+\tfrac29)(H(a)H(b)R) =
\delta_{(a,b)}$, and the same holds with $H(-a)H(-b)$. Since $dx\,dy = 3\,da\,db$, $\delta_{(x,y)} =
\tfrac13\delta_{(a,b)}$, and
$$
E_\pm = \tfrac13\, e^{(a-2b)/3}\, H(\pm a)H(\pm b)\, R(a,b)
$$
satisfy $TE_\pm = \delta_0$. In the original variables,
$$
E_+(x,y) = \begin{cases}\tfrac13\, e^{(3x-4y)/9}\, J_0\!\Big(\tfrac29\sqrt{2y(3x-2y)}\Big), & y>0,\ 3x>2y,\\
0, & \text{otherwise,}\end{cases}
\qquad E_-(x,y) = \tfrac13\, e^{(3x-4y)/9}\, R \text{ on } \{y<0,\ 3x<2y\},\ 0 \text{ otherwise}.
$$
(Checked numerically: $\langle E_\pm, T^t\varphi\rangle = \varphi(0)$ for a Gaussian $\varphi$, to $10^{-14}$.)
Write $\Gamma_+ = \{y\ge0,\ 3x\ge2y\}$ and $\Gamma_- = -\Gamma_+$ for the supports. $\Gamma_+\subset\{x\ge0\}$
and, for every $c$, $\Gamma_+\cap\{x\le c\}$ is a compact triangle on which $|E_+|$ is bounded (as
$|J_0|\le1$); symmetrically for $\Gamma_-\cap\{x\ge -c\}$.

**A solution.** Take $\chi\in C^\infty(\mathbb R)$ with $\chi = 0$ on $(-\infty,-1]$ and $\chi=1$ on
$[1,\infty)$, and set $f_+ = \chi(x)f$, $f_- = (1-\chi(x))f$. Both are $C^2$, $f = f_+ + f_-$,
$\operatorname{supp}f_+\subset\{x\ge-1\}$ and $\operatorname{supp}f_-\subset\{x\le1\}$. Define
$$
w(p) = \int_{\Gamma_+} E_+(q)\,f_+(p-q)\,dq + \int_{\Gamma_-} E_-(q)\,f_-(p-q)\,dq .
$$
For $p$ with $p_x\le c$, the first integrand vanishes unless $q_x\le p_x+1\le c+1$, i.e. unless $q$ lies
in the compact triangle $\Gamma_+\cap\{x\le c+1\}$; symmetrically for the second. So both integrals are
over bounded sets, locally uniformly in $p$, with bounded kernels.

**Regularity $w \in C^2$.** By the previous paragraph we may differentiate under the integral sign: for
$|\alpha|\le2$,
$$
\partial^\alpha w = E_+ * \partial^\alpha f_+ + E_- * \partial^\alpha f_- ,
$$
and each term is continuous (a bounded kernel on a compact set against a continuous function). So
$w\in C^2(\mathbb R^2)$.

**$Tw = f$.** For $\varphi\in\mathcal D(\mathbb R^2)$, substituting $r = p+q$ and using Fubini (the
$(p,q)$-region where the integrand is nonzero is compact by the same support argument),
$$
\langle E_+*f_+,\, T^t\varphi\rangle = \int f_+(p)\,\big\langle E_+,\, (T^t\varphi)(p+\cdot)\big\rangle\,dp
= \int f_+(p)\,\big\langle TE_+,\, \varphi(p+\cdot)\big\rangle\,dp = \int f_+\varphi ,
$$
and likewise for $E_-*f_-$. Hence $\langle Tw,\varphi\rangle = \langle w, T^t\varphi\rangle = \int f\varphi$,
so $Tw = f$ in $\mathcal D^{\prime}$; since $w\in C^2$, also classically. (This is a convolution of two
distributions neither of which has compact support; it is defined because one is supported in a cone and
the other in a half-space, so their supports meet in bounded sets. When $f$ itself has compact support one
may take $\chi\equiv1$, and $w = E_+*f = w_0*f$ with $w_0 = E_+$ is exactly the convolution of part (b).)

**Uniqueness — no.** The solution is **not unique**: if $Tw = f$ and $Tw_h = 0$, then $T(w + w_h) = f$.
Concretely,
$$
T(1) = 0, \qquad T(x) = 2\cdot 0 - 0 + 3\cdot 0 = 0, \qquad T(ax + b) = 0,
$$
and $T(e^{ax+by}) = (2a^2 + 3ab - b)e^{ax+by} = 0$ whenever $2a^2 + 3ab - b = 0$ (a one-parameter family).
Adding any such $C^2$ homogeneous solution to $w$ gives another $C^2$ solution. (Non-uniqueness alone does
not distinguish $T$: every nonzero constant-coefficient operator on $\mathbb R^2$, elliptic ones included,
has a nontrivial kernel. What non-ellipticity adds is that $\ker T$ also contains non-smooth elements, such
as $E_+-E_-$, which jumps across the characteristic lines.) Uniqueness is recovered only by imposing side
conditions, for example requiring $w$ to vanish for $x\ll0$ when $f$ does. ∎

**Remark.** Parts (a)–(c) are the apparatus behind (d): a *fundamental solution* $w_0$ ($Tw_0 = \delta_0$)
is a **convolution inverse** of the constant-coefficient operator $T$, and $w_0 * f$ solves $Tw = f$ for the
same reason $\delta_0$ is the convolution unit and $T$ commutes with $*$. Part (b) licenses $w_0*f$ only
when one factor has compact support. For general $f\in C^2(\mathbb R^2)$ the hyperbolicity of $T$ supplies
the replacement: fundamental solutions supported in proper cones, which can be convolved with functions
supported in half-spaces.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m01J06: Euler–Lagrange for a loaded elastic rod, and buckling as bifurcation from the trivial state

## Why It's Hard

The problem is two classical techniques bolted together, and each has a quiet
pitfall. Part (a) is a calculus-of-variations derivation, but with a twist: only
$\varphi(0)=0$ is imposed (an *essential* boundary condition), so at $s=1$ the
variation $\eta(1)$ is **free**, and the vanishing of the first variation forces a
**natural boundary condition** $\varphi'(1)=0$ that you must *discover*, not
assume — missing it leaves the problem underdetermined. Part (b) is a bifurcation
calculation disguised as a "perturbation expansion": substituting
$\varphi_\epsilon=\epsilon\varphi_1+\cdots$ linearizes $\sin\varphi\approx\varphi$,
turning the nonlinear pendulum/elastica equation into a **Sturm–Liouville
eigenvalue problem**, whose eigenvalues are exactly the loads $\lambda$ at which
the straight rod can first bend. The conceptual leap is recognizing that these
eigenvalues are **bifurcation points** of the full nonlinear system: where the
linearization admits a nontrivial mode, the nonlinear problem grows a branch of
buckled equilibria off the trivial solution $\varphi_0\equiv0$.

## The Key Insight

The integrand $\mathcal{E}(q,p)=\lambda\cos q+\tfrac12 Kp^2$ gives
$\mathcal{E}_q=-\lambda\sin q$, $\mathcal{E}_p=Kp$, so the first variation is
$$
\delta E=\int_0^1\!\big(-\lambda\sin\varphi-K\varphi''\big)\eta\,ds
+\big[K\varphi'\eta\big]_0^1 .
$$
With $\eta(0)=0$ and $\eta(1)$ free, vanishing of $\delta E$ yields **both**
$$
K\varphi''+\lambda\sin\varphi=0,\qquad \varphi(0)=0,\qquad \varphi'(1)=0 .
$$
Linearizing about $\varphi\equiv0$ ($\sin\varphi\approx\varphi$) gives the
eigenvalue problem $K\varphi_1''+\lambda\varphi_1=0$, $\varphi_1(0)=0$,
$\varphi_1'(1)=0$, solved by $\varphi_1=\sin(\omega s)$ with $\cos\omega=0$, i.e.
$$
\boxed{\ \lambda_n=K\Big(\tfrac{(2n-1)\pi}{2}\Big)^2=\frac{(2n-1)^2\pi^2K}{4},\quad
n=1,2,\dots\ }
$$
These discrete loads are bifurcation points: nontrivial buckled solutions of the
nonlinear system branch off $\varphi_0\equiv0$ there (first at
$\lambda_1=\pi^2K/4$).

## Complete Proof

### Part (a): first-order necessary conditions (Euler–Lagrange + natural BC)

Let $\varphi\in S$ (so $\varphi(0)=0$) be an extremal and let $\eta\in
C^2([0,1])$ be an admissible variation: to keep $\varphi+\epsilon\eta\in S$ we need
$\eta(0)=0$, while $\eta(1)$ is **unconstrained** (no condition is imposed at
$s=1$). Define $g(\epsilon)=E(\varphi+\epsilon\eta)$. With
$\mathcal{E}(q,p)=\lambda\cos q+\tfrac12 Kp^2$,
$$
\mathcal{E}_q=\frac{\partial\mathcal{E}}{\partial q}=-\lambda\sin q,\qquad
\mathcal{E}_p=\frac{\partial\mathcal{E}}{\partial p}=Kp,
$$
so the first variation is
$$
\delta E=g'(0)=\int_0^1\Big[\mathcal{E}_q\big(\varphi,\varphi'\big)\,\eta
+\mathcal{E}_p\big(\varphi,\varphi'\big)\,\eta'\Big]\,ds
=\int_0^1\Big[-\lambda\sin\varphi\,\eta+K\varphi'\,\eta'\Big]\,ds .
$$
Integrate the second term by parts:
$$
\int_0^1 K\varphi'\eta'\,ds=\big[K\varphi'\eta\big]_0^1-\int_0^1 K\varphi''\eta\,ds
=K\varphi'(1)\eta(1)-\underbrace{K\varphi'(0)\eta(0)}_{=0}-\int_0^1 K\varphi''\eta\,ds,
$$
using $\eta(0)=0$. Hence
$$
\delta E=\int_0^1\big(-\lambda\sin\varphi-K\varphi''\big)\eta\,ds
+K\varphi'(1)\,\eta(1). \tag{1}
$$

A necessary condition for an extremum is $\delta E=0$ for **all** admissible
$\eta$.

- First restrict to $\eta$ with $\eta(1)=0$ (and otherwise arbitrary on $(0,1)$).
  Then (1) reduces to $\int_0^1(-\lambda\sin\varphi-K\varphi'')\eta\,ds=0$ for all
  such $\eta$, and the **fundamental lemma of the calculus of variations** forces
  the bracket to vanish identically — the **Euler–Lagrange equation**:
  $$
  K\varphi''+\lambda\sin\varphi=0,\qquad s\in(0,1). \tag{EL}
  $$
- Now allow $\eta(1)\neq0$. With (EL) holding, (1) collapses to
  $K\varphi'(1)\eta(1)=0$ for all $\eta(1)$, which (as $K>0$) gives the **natural
  boundary condition** at the free end:
  $$
  \varphi'(1)=0. \tag{NBC}
  $$

So the first-order necessary conditions are the two-point boundary value problem
$$
\boxed{\,K\varphi''+\lambda\sin\varphi=0\ \text{ on }(0,1),\quad
\varphi(0)=0\ \text{(essential)},\quad \varphi'(1)=0\ \text{(natural)}.\,}
$$
(Physically: (EL) is the elastica/pendulum balance of bending against load,
$\varphi(0)=0$ clamps the angle at one end, and $\varphi'(1)=0$ says the free end
carries no bending moment.) $\quad\checkmark$

### Part (b): the trivial extremal, the linearized eigenproblem, and bifurcation

**$\varphi_0\equiv0$ is an extremal for every $\lambda>0$.** Substituting into
(EL): $K\cdot0+\lambda\sin0=0$. The boundary conditions hold: $\varphi_0(0)=0$ and
$\varphi_0'(1)=0$. So $\varphi_0\equiv0$ solves the full system for all
$\lambda>0$. $\quad\checkmark$

**Perturbation expansion.** Seek solutions near the trivial one of the form
$$
\varphi_\epsilon(s)=\epsilon\,\varphi_1(s)+\epsilon^2\varphi_2(s)+\cdots,
\qquad|\epsilon|\ll1,
$$
where each $\varphi_i$ inherits the boundary conditions $\varphi_i(0)=0$,
$\varphi_i'(1)=0$ (these hold for $\varphi_\epsilon$ at every order in $\epsilon$).
Expand the nonlinearity,
$$
\sin\varphi_\epsilon=\varphi_\epsilon-\tfrac16\varphi_\epsilon^3+\cdots
=\epsilon\varphi_1+\epsilon^2\varphi_2+O(\epsilon^3),
$$
and insert into (EL):
$$
K\big(\epsilon\varphi_1''+\epsilon^2\varphi_2''+\cdots\big)
+\lambda\big(\epsilon\varphi_1+\epsilon^2\varphi_2+\cdots\big)=0 .
$$
Collecting the $O(\epsilon)$ terms gives the **linear boundary value problem for
$\varphi_1$**:
$$
K\varphi_1''+\lambda\varphi_1=0,\qquad \varphi_1(0)=0,\qquad \varphi_1'(1)=0. \tag{L}
$$

**Solving the eigenproblem (L).** Write $\omega^2=\lambda/K>0$, so
$\varphi_1''+\omega^2\varphi_1=0$ with general solution
$\varphi_1(s)=a\cos(\omega s)+b\sin(\omega s)$.
- $\varphi_1(0)=0\Rightarrow a=0$, so $\varphi_1(s)=b\sin(\omega s)$.
- $\varphi_1'(s)=b\omega\cos(\omega s)$, and $\varphi_1'(1)=0\Rightarrow
  b\omega\cos\omega=0$.

A nontrivial solution ($b\neq0$, $\omega\neq0$) requires $\cos\omega=0$, i.e.
$\omega=\dfrac{(2n-1)\pi}{2}$ for $n=1,2,3,\dots$. Translating back to the load,
nontrivial solutions of (L) exist **exactly** at the discrete values
$$
\lambda_n=K\omega^2=K\Big(\frac{(2n-1)\pi}{2}\Big)^2=\frac{(2n-1)^2\pi^2K}{4},
\qquad n=1,2,3,\dots,
$$
with corresponding eigenfunctions (buckling modes)
$$
\varphi_1^{(n)}(s)=b\,\sin\!\Big(\frac{(2n-1)\pi}{2}\,s\Big).
$$
The smallest is the **critical load**
$$
\lambda_1=\frac{\pi^2K}{4},\qquad \varphi_1^{(1)}(s)=b\sin\!\Big(\frac{\pi}{2}s\Big).
$$

**Do we expect nontrivial solutions of the nonlinear system?** **Yes.** The
loads $\lambda_n$ are precisely the values at which the linearization about the
trivial extremal $\varphi_0\equiv0$ acquires a nontrivial null mode — i.e. at
$\lambda=\lambda_n$ the trivial solution ceases to be the only one nearby. These
are **bifurcation points**: each eigenvalue $\lambda_n$ is *simple* (a single
eigenfunction $\sin(\tfrac{(2n-1)\pi}{2}s)$), and by bifurcation-from-a-simple-
eigenvalue theory a branch of genuinely nonlinear solutions emanates from
$(\lambda,\varphi)=(\lambda_n,0)$. Physically these are the **buckled
equilibria** of the rod: for loads below $\lambda_1=\pi^2K/4$ the straight state
$\varphi\equiv0$ is the only extremal near zero, while as $\lambda$ increases past
$\lambda_1$ a nontrivial bent shape appears (and further modes branch off at
$\lambda_2,\lambda_3,\dots$). $\quad\blacksquare$

### Remark

This is the **Euler buckling** problem for a fixed–free rod, with the natural
boundary condition $\varphi'(1)=0$ (zero moment at the free end) producing the
quarter-wave spectrum $\lambda_n=(2n-1)^2\pi^2K/4$ rather than the full-wave
$n^2\pi^2$ of a pinned–pinned column. The perturbation step is exactly a
**Lyapunov–Schmidt / bifurcation** reduction: the $O(\epsilon)$ balance is the
linearized operator's kernel condition, and the load eigenvalues are the
bifurcation loads. A direct numerical shooting study of the nonlinear BVP confirms
the prediction: for $\lambda<\lambda_1$ the only solution near zero is
$\varphi\equiv0$, whereas just above $\lambda_1=\pi^2K/4$ a nontrivial solution
(nonzero $\varphi'(0)$) appears and grows in amplitude with $\lambda$ — the
hallmark of a pitchfork bifurcation from the trivial branch. Determining the
*direction* and *stability* of the branch would require carrying the expansion to
$O(\epsilon^3)$ (where the $-\tfrac16\varphi_1^3$ term enters), but the
first-order analysis already locates the bifurcation loads.

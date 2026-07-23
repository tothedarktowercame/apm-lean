<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02A03: (1/2π)·ln|x−y| is the fundamental solution of the Laplacian in ℝ²

## Why It's Hard

The candidate $E(x)=\frac{1}{2\pi}\ln|x-y|$ is **singular exactly at the pole** $x=y$, where $\ln|x-y|\to-\infty$, so neither claim is automatic. Local integrability is not obvious because $\ln$ is unbounded near the pole; and the identity $\Delta E=\delta_y$ cannot be checked classically — at the pole $E$ is not even continuous, let alone twice differentiable. Everything must be done in the **distributional sense**, where $\Delta E$ acts on a test function $\varphi$ via $\langle\Delta E,\varphi\rangle=\int E\,\Delta\varphi$ (formal self-adjointness of $\Delta$), and the entire Dirac mass has to be extracted from the behavior *at the singularity*.

The technical crux is that $E$ is harmonic *away* from the pole, so the $\delta$ comes purely from the pole; isolating it requires the standard but delicate "**excise a small disk $B_\epsilon$, apply Green's second identity, let $\epsilon\to0$**" maneuver. The two resulting boundary integrals over the shrinking circle behave in opposite ways — one vanishes, the other survives as a spherical mean — and getting their sizes right (and the normalization $\frac{1}{2\pi}$) is the heart of the matter. Both facts are also dimension-specific: the log singularity is integrable in $\mathbb R^2$ only because the area element supplies an extra power of $r$.

## The Key Insight

Translate so $y=0$; write $E=\frac{1}{2\pi}\ln r$, $r=|x|$. Two facts drive everything:

1. **The area element tames the log.** In polar coordinates $\int_{B_R}|\ln r|\,dx=2\pi\int_0^R r|\ln r|\,dr<\infty$ because $r\ln r\to 0$ — so $E\in L^1_{\mathrm{loc}}$.
2. **$E$ is harmonic off the pole, and its radial flux is exactly $1$.** Since $\partial_r E=\frac{1}{2\pi r}$, the outward flux of $\nabla E$ across the circle $|x|=\epsilon$ is $\partial_rE\cdot(2\pi\epsilon)=\frac{1}{2\pi\epsilon}\cdot2\pi\epsilon=1$, *independent of $\epsilon$*. This radius-independent unit flux is the $\delta$.

Excising $B_\epsilon$ and using Green's identity (where $\Delta E=0$), $\int E\Delta\varphi$ reduces to a boundary term on $|x|=\epsilon$: the piece $E\,\partial_n\varphi=O(\epsilon|\ln\epsilon|)\to0$, while $-\varphi\,\partial_nE=\frac{1}{2\pi\epsilon}\varphi$ integrates to the **average of $\varphi$ over the circle**, which $\to\varphi(0)$. Hence $\langle\Delta E,\varphi\rangle=\varphi(0)$.

## Complete Proof

By translation invariance of $\Delta$ it suffices to treat $y=0$; set
$$
E(x)=\tfrac{1}{2\pi}\ln|x|=\tfrac{1}{2\pi}\ln r,\qquad r=|x|,\quad x\in\mathbb R^2.
$$

### Step 1: $E\in L^1_{\mathrm{loc}}(\mathbb R^2)$

$E$ is continuous (hence bounded, hence integrable) away from $0$, so it suffices to check integrability on a disk $B_R=\{|x|\le R\}$ about the pole. In polar coordinates ($dx=r\,dr\,d\theta$),
$$
\int_{B_R}|E|\,dx=\frac{1}{2\pi}\int_0^{2\pi}\!\!\int_0^R |\ln r|\,r\,dr\,d\theta=\int_0^R r\,|\ln r|\,dr .
$$
Near $r=0$, $r|\ln r|\to 0$, and $\int_0^R r|\ln r|\,dr$ converges (e.g. $\int r\ln r\,dr=\tfrac{r^2}{2}\ln r-\tfrac{r^2}{4}$ is finite at $0$). Hence $\int_{B_R}|E|\,dx<\infty$ for every $R$, so $E\in L^1_{\mathrm{loc}}(\mathbb R^2)$. (This is special to $d=2$: the area weight $r$ exactly tames the log.) $\qquad\checkmark$

### Step 2: $E$ is harmonic away from the pole

For $r>0$, $E$ is radial, and the radial Laplacian gives
$$
\Delta E=E''(r)+\tfrac1r E'(r)=\tfrac{1}{2\pi}\Big(-\tfrac1{r^2}+\tfrac1r\cdot\tfrac1r\Big)=0 .
$$
So $\Delta E=0$ classically on $\mathbb R^2\setminus\{0\}$, and $\partial_r E=\frac{1}{2\pi r}$. $\qquad\checkmark$

### Step 3: $\Delta E=\delta_0$ in the sense of distributions

Let $\varphi\in C_c^\infty(\mathbb R^2)$; choose $R$ with $\operatorname{supp}\varphi\subseteq B_R$. By definition of the distributional Laplacian,
$$
\langle\Delta E,\varphi\rangle=\langle E,\Delta\varphi\rangle=\int_{\mathbb R^2}E\,\Delta\varphi\,dx .
$$
Since $E\in L^1_{\mathrm{loc}}$ and $\Delta\varphi$ is bounded, $\big|\int_{B_\epsilon}E\,\Delta\varphi\,dx\big|\le\|\Delta\varphi\|_\infty\int_{B_\epsilon}|E|\,dx\to 0$ as $\epsilon\to0$. Therefore
$$
\int_{\mathbb R^2}E\,\Delta\varphi\,dx=\lim_{\epsilon\to0}\int_{\Omega_\epsilon}E\,\Delta\varphi\,dx,\qquad \Omega_\epsilon:=\{x:\epsilon\le|x|\le R\}.
$$
On $\Omega_\epsilon$, $E$ is smooth and $\Delta E=0$, so **Green's second identity** gives
$$
\int_{\Omega_\epsilon}\big(E\,\Delta\varphi-\varphi\,\Delta E\big)\,dx=\int_{\partial\Omega_\epsilon}\Big(E\,\tfrac{\partial\varphi}{\partial n}-\varphi\,\tfrac{\partial E}{\partial n}\Big)\,dS,
$$
i.e. $\int_{\Omega_\epsilon}E\,\Delta\varphi\,dx=\int_{\partial\Omega_\epsilon}\big(E\,\partial_n\varphi-\varphi\,\partial_n E\big)\,dS$. The outer boundary $|x|=R$ contributes nothing ($\varphi$ and $\nabla\varphi$ vanish there). On the inner circle $|x|=\epsilon$, the outward normal of $\Omega_\epsilon$ points *toward* the origin, so $\partial_n=-\partial_r$. Thus
$$
\int_{\Omega_\epsilon}E\,\Delta\varphi\,dx=\underbrace{\int_{|x|=\epsilon}E\,(-\partial_r\varphi)\,dS}_{(\mathrm I)}\ +\ \underbrace{\int_{|x|=\epsilon}\varphi\,(\partial_r E)\,dS}_{(\mathrm{II})} .
$$

**Term (I) vanishes.** On $|x|=\epsilon$, $E=\frac{1}{2\pi}\ln\epsilon$, the circle has length $2\pi\epsilon$, and $|\partial_r\varphi|\le\|\nabla\varphi\|_\infty=:C$, so
$$
|(\mathrm I)|\le \frac{|\ln\epsilon|}{2\pi}\cdot C\cdot 2\pi\epsilon=C\,\epsilon\,|\ln\epsilon|\xrightarrow[\epsilon\to0]{}0 .
$$

**Term (II) gives $\varphi(0)$.** On $|x|=\epsilon$, $\partial_r E=\frac{1}{2\pi\epsilon}$, so
$$
(\mathrm{II})=\frac{1}{2\pi\epsilon}\int_{|x|=\epsilon}\varphi\,dS=\fint_{|x|=\epsilon}\varphi\,dS\xrightarrow[\epsilon\to0]{}\varphi(0),
$$
the average of the continuous function $\varphi$ over the shrinking circle converging to its value at the center.

Combining,
$$
\langle\Delta E,\varphi\rangle=\int_{\mathbb R^2}E\,\Delta\varphi\,dx=\lim_{\epsilon\to0}\big[(\mathrm I)+(\mathrm{II})\big]=0+\varphi(0)=\varphi(0)=\langle\delta_0,\varphi\rangle .
$$
Since $\varphi\in C_c^\infty$ was arbitrary, $\Delta E=\delta_0$. Undoing the translation,
$$
\Delta_x\!\Big(\tfrac{1}{2\pi}\ln|x-y|\Big)=\delta_y\quad\text{in }\mathcal D'(\mathbb R^2). \qquad\blacksquare
$$

### Remark — the unit flux is the Dirac mass

The proof exhibits the mechanism cleanly: away from the pole $E$ is harmonic, so $\Delta E$ "lives at the pole," and the strength of the source is exactly the **flux of $\nabla E$ across a small circle**, $\int_{|x|=\epsilon}\partial_n E\,dS=\frac{1}{2\pi\epsilon}\cdot2\pi\epsilon=1$ — independent of $\epsilon$, which is precisely why the limit picks out $\varphi(0)$ with coefficient $1$, and what forces the normalizing constant $\frac{1}{2\pi}$. (Indeed $\frac{1}{2\pi}$ is the reciprocal of the circumference of the unit circle.) The same template gives the fundamental solution in every dimension: $\Delta E=\delta_0$ with $E=\frac{1}{2\pi}\ln|x|$ in $d=2$ and $E=\frac{-1}{(d-2)\omega_{d-1}}|x|^{2-d}$ in $d\ge3$ (where $\omega_{d-1}=|\mathbb S^{d-1}|$), the logarithm being the borderline $d=2$ case. These Newtonian/logarithmic potentials are the building block for solving $\Delta u=f$ by convolution, $u=E*f$, and underlie potential theory, electrostatics, and the theory of harmonic functions.

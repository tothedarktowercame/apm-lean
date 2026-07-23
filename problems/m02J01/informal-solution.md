<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m02J01: Every distribution on ℝ has a primitive, unique up to a constant

## Why It's Hard

The result "antiderivatives exist and are unique up to a constant" is familiar for
functions, but for **distributions** you cannot integrate pointwise — everything
must be phrased through the duality $v'(\varphi)=-v(\varphi')$, so the whole proof
runs *on the test-function side*. The linchpin is part (a): the range of
$\dfrac{d}{dx}$ acting on $D(\mathbb{R})$ is **exactly** the kernel of the
integration functional $\varphi\mapsto\int\varphi$. The forward direction is the
fundamental theorem of calculus; the subtle direction is that $\psi(x)=\int_{-
\infty}^x\varphi$ is again **compactly supported** — and that holds *only because*
$\int\varphi=0$ (otherwise $\psi$ tends to a nonzero constant at $+\infty$). Part
(b) then must *define* a distribution $v$ by prescribing $v(\varphi')=-u(\varphi)$;
the danger is that not every test function is a derivative, so you need a fixed
reference bump $\rho$ with $\int\rho=1$ to split off the "non-derivative part," and
you must check the resulting $v$ is genuinely continuous on $D$. Part (c) is the
same kernel fact run backwards: $w'=0$ means $w$ annihilates every derivative,
hence every mean-zero test function, hence is a constant.

## The Key Insight

Let $D_0=\{\varphi\in D(\mathbb{R}):\int_\mathbb{R}\varphi=0\}$. Part (a) says
$$
\{\psi':\psi\in D(\mathbb{R})\}=D_0,
$$
because $\psi(x)=\int_{-\infty}^x\varphi$ is a compactly supported smooth function
**iff** $\int\varphi=0$. Fix once and for all a bump $\rho\in D(\mathbb{R})$ with
$\int\rho=1$. Then **every** $\chi\in D$ decomposes uniquely as
$$
\chi=\Big(\!\int\chi\Big)\rho+\chi_0,\qquad \chi_0\in D_0,\quad
\chi_0=\Theta'\ \text{with}\ \Theta(x)=\int_{-\infty}^x\chi_0\in D .
$$
Defining $v(\chi):=-u(\Theta)$ gives a distribution with $v'=u$ (since for
$\chi=\varphi'$ one has $\Theta=\varphi$, so $v(\varphi')=-u(\varphi)$). And if
$w'=0$, then $w$ kills all of $D_0$, so $w(\chi)=(\int\chi)\,w(\rho)$ — i.e. $w$ is
the constant $w(\rho)$ — which forces any two primitives to differ by a constant.

## Complete Proof

Throughout, $D(\mathbb{R})=C_c^\infty(\mathbb{R})$ with its usual convergence
($\varphi_n\to0$ means all $\varphi_n$ are supported in one fixed compact set and
$\varphi_n^{(k)}\to0$ uniformly for every $k$), and a distribution $u\in
D'(\mathbb{R})$ is a linear functional on $D$ that is continuous for this
convergence. The distributional derivative is defined by $v'(\varphi)=-v(\varphi')$.

### Part (a): $\int\varphi=0\iff\varphi=\psi'$ for some $\psi\in D(\mathbb{R})$

**($\Leftarrow$)** If $\varphi=\psi'$ with $\psi\in D(\mathbb{R})$, then $\psi$ has
compact support, so $\psi(x)\to0$ as $x\to\pm\infty$, and by the fundamental
theorem of calculus
$$
\int_\mathbb{R}\varphi=\int_{-\infty}^{\infty}\psi'(x)\,dx
=\lim_{x\to\infty}\psi(x)-\lim_{x\to-\infty}\psi(x)=0 .
$$

**($\Rightarrow$)** Suppose $\int_\mathbb{R}\varphi=0$. Define
$$
\psi(x)=\int_{-\infty}^{x}\varphi(t)\,dt .
$$
Then $\psi$ is $C^\infty$ with $\psi'=\varphi$ (FTC; $\varphi$ is smooth). It
remains to show $\psi$ has compact support. Choose $R$ with
$\operatorname{supp}\varphi\subseteq[-R,R]$.
- For $x<-R$: the interval $(-\infty,x]$ misses $\operatorname{supp}\varphi$, so
  $\psi(x)=0$.
- For $x>R$: $\psi(x)=\int_{-\infty}^{x}\varphi=\int_{-\infty}^{\infty}\varphi=0$,
  using $\int\varphi=0$ and that $\varphi$ vanishes beyond $R$.

Hence $\psi\equiv0$ outside $[-R,R]$, so $\psi\in D(\mathbb{R})$ and
$\varphi=\psi'$. $\quad\checkmark$

(The compact support to the *right* is exactly where the hypothesis $\int\varphi=0$
is used. We record for later that this antiderivative $\psi$ is the **unique** one
in $D(\mathbb{R})$: two would differ by a constant, and a compactly supported
constant is $0$.)

### Part (b): every $u\in D'(\mathbb{R})$ has a primitive

Fix a reference bump $\rho\in D(\mathbb{R})$ with $\int_\mathbb{R}\rho=1$ (e.g. a
normalized standard mollifier). For any $\chi\in D(\mathbb{R})$ set
$$
\chi_0:=\chi-\Big(\!\int_\mathbb{R}\chi\Big)\rho .
$$
Then $\int\chi_0=\int\chi-(\int\chi)\!\int\rho=0$, so $\chi_0\in D_0$; by part (a)
it has a unique antiderivative in $D(\mathbb{R})$, namely
$$
\Theta_\chi(x)=\int_{-\infty}^{x}\chi_0(t)\,dt\in D(\mathbb{R}),\qquad
\Theta_\chi'=\chi_0 .
$$
Define
$$
v(\chi):=-\,u(\Theta_\chi).
$$

**$v$ is linear.** Each of $\chi\mapsto\int\chi$, $\chi\mapsto\chi_0$,
$\chi_0\mapsto\Theta_\chi$ (integration), and $u$ is linear, so $v$ is linear.

**$v$ is continuous (hence $v\in D'$).** Suppose $\chi_n\to0$ in $D(\mathbb{R})$,
with all $\operatorname{supp}\chi_n\subseteq K$ for a fixed compact $K$. Then
$\int\chi_n\to0$ and $\chi_{0,n}=\chi_n-(\int\chi_n)\rho\to0$ in $D$, with supports
in the fixed compact $K':=K\cup\operatorname{supp}\rho\subseteq[-R,R]$. For the
antiderivatives $\Theta_n=\Theta_{\chi_n}$:
- $\operatorname{supp}\Theta_n\subseteq[-R,R]$ (as in (a), since
  $\operatorname{supp}\chi_{0,n}\subseteq[-R,R]$ and $\int\chi_{0,n}=0$);
- $\|\Theta_n\|_\infty\le\int|\chi_{0,n}|\le 2R\,\|\chi_{0,n}\|_\infty\to0$;
- $\Theta_n'=\chi_{0,n}\to0$ uniformly, and likewise $\Theta_n^{(k)}=
  \chi_{0,n}^{(k-1)}\to0$ for all $k\ge1$.

Thus $\Theta_n\to0$ in $D(\mathbb{R})$, so $v(\chi_n)=-u(\Theta_n)\to0$ by the
continuity of $u$. Hence $v\in D'(\mathbb{R})$.

**$v'=u$.** Let $\varphi\in D(\mathbb{R})$ and apply the definition to
$\chi=\varphi'$. Since $\int\varphi'=0$ (part (a)), we have $\chi_0=\varphi'$, and
its antiderivative in $D$ is $\Theta_{\varphi'}(x)=\int_{-\infty}^x\varphi'=\varphi$
(because $\varphi(-\infty)=0$). Therefore
$$
v(\varphi')=-u(\Theta_{\varphi'})=-u(\varphi),
$$
and so
$$
v'(\varphi)=-v(\varphi')=u(\varphi)\qquad\text{for all }\varphi\in D(\mathbb{R}).
$$
That is, $v'=u$: $v$ is a primitive of $u$. $\quad\checkmark$

### Part (c): two primitives differ by a constant

Let $v_1,v_2\in D'(\mathbb{R})$ both satisfy $v_i'=u$, and put $w=v_1-v_2$. Then
$w'=u-u=0$. We show $w$ is a constant distribution.

$w'=0$ means $w'(\varphi)=-w(\varphi')=0$ for all $\varphi\in D$, i.e.
$$
w(\varphi')=0\quad\text{for all }\varphi\in D(\mathbb{R}).
$$
By part (a), $\{\varphi':\varphi\in D\}=D_0$, so $w$ **vanishes on all of $D_0$**:
$w(\psi)=0$ whenever $\int\psi=0$.

Now use the same reference bump $\rho$ ($\int\rho=1$). For an arbitrary
$\chi\in D(\mathbb{R})$, the function $\chi-(\int\chi)\rho$ lies in $D_0$, so
$$
0=w\Big(\chi-\Big(\!\int\chi\Big)\rho\Big)=w(\chi)-\Big(\!\int\chi\Big)w(\rho).
$$
Writing $C:=w(\rho)$ (a fixed scalar), we get
$$
w(\chi)=C\int_\mathbb{R}\chi\qquad\text{for all }\chi\in D(\mathbb{R}),
$$
which is precisely the distribution induced by the **constant function** $C$ (the
regular distribution $\chi\mapsto\int C\chi$). Hence $w=C$ is a constant, i.e.
$$
v_1-v_2=C .
$$
$\blacksquare$

### Remark

The entire argument pivots on part (a)'s identification
$$
\operatorname{range}\Big(\tfrac{d}{dx}:D\to D\Big)=\ker\Big(\varphi\mapsto
\textstyle\int\varphi\Big)=D_0,
$$
a single codimension-one fact. Existence (b) is "invert $d/dx$ against this
range," made into an honest distribution by splitting off the one missing
direction $\rho$; uniqueness (c) is the dual statement that the only distributions
killing $D_0$ are the constants. Equivalently, $\tfrac{d}{dx}:D'(\mathbb{R})\to
D'(\mathbb{R})$ is **surjective with kernel the constants** — so on the line,
"integration of distributions" works exactly as it does for functions, with the
usual $+C$. (The choice of $\rho$ only fixes *which* primitive $v$ you name; a
different bump changes $v$ by a constant, consistent with (c).)

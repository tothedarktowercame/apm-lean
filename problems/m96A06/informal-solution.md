<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96A06: A quadratic functional on $H^1([0,1])$ — its Fréchet derivative, the Neumann Sturm–Liouville equation, and Lax–Milgram uniqueness

## Why It's Hard

The three parts trace the entire arc of the **direct method in the calculus of variations** for a model energy
$$
F(u)=\int_0^1\big(|u'|^2+a(t)u^2-2b(t)u\big)\,dt,\qquad u\in H=H^1([0,1]),
$$
and each part hides a standard pitfall:

- **(a)** "Compute the Fréchet derivative" is easy to do *formally* but the grader wants the **rigorous** statement: a bounded linear functional $F'(u)\in H^*$ together with the proof that the remainder is $o(\|h\|_H)$. The quadratic structure makes the remainder *exactly* the second-order term $\int(|h'|^2+ah^2)$, which one must bound by $\|h\|_H^2$ using $a\in L^\infty$.
- **(b)** Passing from "$F'(u)=0$" to a **Sturm–Liouville problem** is the subtle one: the weak/variational equation $\int(u'h'+auh-bh)=0$ holds for *all* $h\in H$, and one must extract **two different pieces of information** from it — the ODE (by testing against compactly supported $h$, i.e. distribution theory) **and** the **natural boundary conditions** $u'(0)=u'(1)=0$ (by testing against $h$ with nonzero boundary values and integrating by parts). Forgetting the natural BCs — or imposing Dirichlet BCs that aren't there — is the classic error.
- **(c)** Uniqueness needs **coercivity**, and the trap is that with Neumann conditions the constants lie in $H$, so the Poincaré inequality fails and the $|u'|^2$ term alone is **not** coercive. The hypothesis $a(t)\ge\epsilon>0$ is precisely what rescues coercivity by controlling the $\int u^2$ part directly. Lax–Milgram (or strict convexity) then delivers existence *and* uniqueness in one stroke.

## The Key Insight

Split $F(u+h)-F(u)$ into its linear and quadratic parts in $h$:
$$
F(u+h)-F(u)=\underbrace{2\!\int_0^1(u'h'+auh-bh)\,dt}_{\text{linear }=F'(u)h}
+\underbrace{\int_0^1(|h'|^2+ah^2)\,dt}_{=\,O(\|h\|_H^2)} .
$$
So $F'(u)h=2\int_0^1(u'h'+auh-bh)\,dt$, and everything else is the symmetric bilinear form
$$
B(u,h)=\int_0^1(u'h'+auh)\,dt,\qquad \ell(h)=\int_0^1 bh\,dt,\qquad F'(u)h=2\big(B(u,h)-\ell(h)\big).
$$
Then:

- **$F'(u)=0\iff B(u,h)=\ell(h)\ \forall h\in H$** — the *weak form* of $-u''+au=b$. Testing against $C_c^\infty$ gives the ODE distributionally; integrating by parts with general $h$ reveals the **natural (Neumann) boundary conditions** $u'(0)=u'(1)=0$.
- **$B$ is coercive** because $a\ge\epsilon>0$: $B(u,u)=\int(|u'|^2+au^2)\ge\min(1,\epsilon)\,\|u\|_H^2$. With $B$ bounded and symmetric and $\ell\in H^*$, **Lax–Milgram** gives a unique $u$. (Equivalently, $F$ is strictly convex and coercive, so it has a unique minimizer = unique critical point.)

The hypothesis $a\ge\epsilon>0$ is doing the coercivity work that Poincaré cannot do under Neumann conditions — that is the crux of part (c).

## Complete Proof

Throughout, $H=H^1([0,1])$ is a Hilbert space with inner product $\langle u,v\rangle_H=\int_0^1(uv+u'v')\,dt$ and norm $\|u\|_H^2=\int_0^1(|u|^2+|u'|^2)\,dt$. Recall the embedding $H\hookrightarrow C([0,1])$, so point values $u(0),u(1)$ are well defined.

### Part (a): the Fréchet derivative

Fix $u,h\in H$. Expanding the integrand of $F(u+h)$,
$$
|u'+h'|^2=|u'|^2+2u'h'+|h'|^2,\quad a(u+h)^2=au^2+2auh+ah^2,\quad -2b(u+h)=-2bu-2bh,
$$
so
$$
F(u+h)-F(u)=\int_0^1\!\big(2u'h'+2auh-2bh\big)dt+\int_0^1\!\big(|h'|^2+ah^2\big)dt .
$$
Define
$$
\boxed{\,F'(u)h=2\int_0^1\big(u'(t)h'(t)+a(t)u(t)h(t)-b(t)h(t)\big)\,dt\,}.
$$

**$F'(u)$ is a bounded linear functional on $H$.** Linearity in $h$ is clear. By Cauchy–Schwarz and $a\in L^\infty$,
$$
|F'(u)h|\le 2\big(\|u'\|_2\|h'\|_2+\|a\|_\infty\|u\|_2\|h\|_2+\|b\|_2\|h\|_2\big)
\le 2\big(\|u'\|_2+\|a\|_\infty\|u\|_2+\|b\|_2\big)\,\|h\|_H,
$$
using $\|h\|_2,\|h'\|_2\le\|h\|_H$. So $F'(u)\in H^*$.

**The remainder is $o(\|h\|_H)$.** The leftover quadratic term obeys
$$
\Big|\int_0^1(|h'|^2+ah^2)\,dt\Big|\le \int_0^1|h'|^2+\|a\|_\infty\int_0^1 h^2\le (1+\|a\|_\infty)\,\|h\|_H^2 .
$$
Hence
$$
\frac{\big|F(u+h)-F(u)-F'(u)h\big|}{\|h\|_H}\le (1+\|a\|_\infty)\,\|h\|_H\xrightarrow[\|h\|_H\to0]{}0 .
$$
Therefore $F$ is Fréchet differentiable at every $u\in H$ with derivative $F'(u)$ as boxed. (Since $u\mapsto F'(u)$ is affine and continuous into $H^*$, $F$ is in fact $C^\infty$, with $F''(u)[h,k]=2\int(h'k'+ahk)$ independent of $u$.) $\qquad\checkmark$

### Part (b): $F'(u)=0$ is a Sturm–Liouville problem

By part (a), $F'(u)=0$ means the **weak equation**
$$
\int_0^1\big(u'h'+auh-bh\big)\,dt=0\qquad\text{for all }h\in H. \tag{W}
$$

**The differential equation (test against $C_c^\infty$).** Take $h\in C_c^\infty((0,1))\subset H$. Then (W) reads
$$
\int_0^1 u'h'\,dt=\int_0^1(b-au)h\,dt .
$$
By the definition of the distributional derivative, the left side is $-\int_0^1 (u')'\,h\,dt$. Since this holds for all test functions $h$,
$$
-(u')'=b-au\quad\Longrightarrow\quad -u''+a u=b\ \text{ in }\mathcal D'(0,1).
$$
Because $a\in L^\infty$, $u\in L^2$, $b\in L^2$, the right side $b-au\in L^2$, so $u''=au-b\in L^2$; thus $u\in H^2([0,1])$, the ODE holds **a.e.**, and $u'\in H^1\hookrightarrow C([0,1])$ has genuine boundary values $u'(0),u'(1)$.

**The natural boundary conditions (test against general $h$).** Now let $h\in H$ be arbitrary. Since $u\in H^2$, integrate the first term of (W) by parts:
$$
\int_0^1 u'h'\,dt=\big[u'h\big]_0^1-\int_0^1 u''h\,dt=u'(1)h(1)-u'(0)h(0)-\int_0^1 u''h\,dt .
$$
Substituting into (W),
$$
u'(1)h(1)-u'(0)h(0)+\int_0^1\big(-u''+au-b\big)h\,dt=0 .
$$
The integral vanishes by the ODE just established, leaving
$$
u'(1)h(1)-u'(0)h(0)=0\qquad\text{for all }h\in H .
$$
Choosing $h$ with $(h(0),h(1))=(1,0)$ and then $(0,1)$ (e.g. affine functions, which lie in $H$) forces
$$
u'(0)=0,\qquad u'(1)=0 .
$$

Thus $F'(u)=0$ is **equivalent** to the regular **Sturm–Liouville boundary value problem with Neumann conditions**
$$
\boxed{\,-u''(t)+a(t)\,u(t)=b(t)\ \text{ a.e. on }(0,1),\qquad u'(0)=u'(1)=0\,}
$$
(in self-adjoint form $-(pu')'+qu=b$ with $p\equiv1$, $q=a$). The converse direction is immediate: if $u\in H^2$ solves this BVP, then for any $h\in H$, integrating by parts and using $u'(0)=u'(1)=0$ recovers (W), i.e. $F'(u)=0$. $\qquad\checkmark$

### Part (c): existence and uniqueness of the critical point

Write $F'(u)=0$ in the form $B(u,h)=\ell(h)$ for all $h\in H$, where
$$
B(u,h)=\int_0^1(u'h'+auh)\,dt,\qquad \ell(h)=\int_0^1 bh\,dt
$$
(so that $F'(u)h=2(B(u,h)-\ell(h))$). We verify the hypotheses of the **Lax–Milgram theorem**.

**$B$ is a bounded bilinear form.** Bilinearity is clear (and $B$ is symmetric). By Cauchy–Schwarz,
$$
|B(u,h)|\le\|u'\|_2\|h'\|_2+\|a\|_\infty\|u\|_2\|h\|_2\le\max(1,\|a\|_\infty)\,\|u\|_H\,\|h\|_H .
$$

**$B$ is coercive.** Using $a(t)\ge\epsilon>0$ a.e.,
$$
B(u,u)=\int_0^1\big(|u'|^2+a\,u^2\big)\,dt\ge\int_0^1\big(|u'|^2+\epsilon\,u^2\big)\,dt\ge\min(1,\epsilon)\int_0^1\big(|u'|^2+u^2\big)\,dt=\min(1,\epsilon)\,\|u\|_H^2 .
$$
The coercivity constant $\min(1,\epsilon)>0$.

**$\ell$ is a bounded linear functional.** $|\ell(h)|\le\|b\|_2\|h\|_2\le\|b\|_2\|h\|_H$, so $\ell\in H^*$.

By **Lax–Milgram**, there exists a **unique** $u\in H$ such that $B(u,h)=\ell(h)$ for all $h\in H$ — equivalently, a unique $u\in H$ with $F'(u)=0$. $\qquad\blacksquare$

### Remark — why $a\ge\epsilon>0$, and the variational reading

**Role of the hypotheses.** Coercivity is the heart of (c), and the condition $a\ge\epsilon>0$ is exactly what supplies it. Under the **Neumann** conditions found in (b), the constant functions belong to $H$ and have $\int|u'|^2=0$, so the Dirichlet term alone is *not* coercive and the Poincaré inequality is unavailable (it needs a vanishing boundary or mean-zero constraint). The lower bound $a\ge\epsilon$ controls $\int u^2$ directly, restoring full $H^1$-coercivity. (Had the problem instead imposed Dirichlet conditions $u(0)=u(1)=0$, Poincaré would let one weaken $a\ge\epsilon$ to merely $a\ge0$, or even allow slightly negative $a$.)

**Variational equivalence.** Because $B$ is symmetric, bounded, and coercive, $F$ is **strictly convex** ($F''(u)[h,h]=2B(h,h)\ge 2\min(1,\epsilon)\|h\|_H^2>0$ for $h\ne0$) and **coercive** ($F(u)\ge\min(1,\epsilon)\|u\|_H^2-2\|b\|_2\|u\|_H\to+\infty$). The direct method then gives a unique global minimizer, which — $F$ being differentiable — is the unique critical point. So "unique solution of $F'(u)=0$," "unique minimizer of the energy $F$," and "unique weak solution of the Neumann Sturm–Liouville problem $-u''+au=b$" are three names for the same object. This is the prototype for elliptic existence theory: energy minimization $\Leftrightarrow$ weak Euler–Lagrange equation $\Leftrightarrow$ Lax–Milgram, with the natural boundary conditions emerging from the variational structure rather than being imposed.

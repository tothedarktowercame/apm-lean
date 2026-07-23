<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b94A02: A balanced map computing bR ⊗ R/I, and tensoring breaks exactness

## Why It's Hard

The first two parts ask you to build a tensor-product isomorphism *by hand* — define a
balanced map, check it is well defined, and invert it — and the only delicate point is
**well-definedness**, which is where the hypothesis $\operatorname{Ann}(b)\subseteq I$
silently does all the work (different representatives $br=br'$ differ by an element of
$\operatorname{Ann}(b)\subseteq I$, which the quotient swallows). Part (c) is the
conceptual payoff: tensoring is only *right*-exact, and you must exhibit a concrete
nonzero element that gets killed — the simple tensor $b\otimes(1+I)$, nonzero by part
(b) but annihilated because $b\in I$. Seeing that single element is the whole game.

## The Key Insight

Define $\varphi(br,\,s+I)=rs+I$. It is well defined precisely because $br=br'\Rightarrow
r-r'\in\operatorname{Ann}(b)\subseteq I\Rightarrow (r-r')s\in I$. This balanced map
gives $bR\otimes_R R/I\cong R/I$, with the generator $b\otimes(1+I)\leftrightarrow
1+I\neq 0$. Now tensor $0\to bR\hookrightarrow R$ with $R/I$: under $R\otimes_R R/I\cong
R/I$ the map sends
$$
b\otimes(1+I)\ \longmapsto\ b\cdot1+I=b+I .
$$
By part (b) the source element is **nonzero**, but $b\in I$ makes the image $b+I=0$. So
$\iota\otimes 1$ is not injective — exactness fails.

## Complete Proof

Let $R$ be commutative with $1$, $I\subsetneq R$ an ideal, $b\in R$,
$\operatorname{Ann}(b)=\{c: bc=0\}$, and assume $\operatorname{Ann}(b)\subseteq I$.
Here $bR=\{br:r\in R\}$ is the principal ideal, an $R$-submodule of $R$.

### (a) The balanced map $\varphi: bR\times R/I\to R/I$

Define
$$
\varphi(br,\ s+I) := rs+I .
$$

**Well defined.** An element of $bR$ may be written $br$ for several $r$, and a coset
$s+I$ for several $s$; we check $\varphi$ does not depend on the choices.
- In the first argument: if $br=br'$ then $b(r-r')=0$, i.e.
  $r-r'\in\operatorname{Ann}(b)\subseteq I$. Hence $(r-r')s\in I$ (as $I$ is an ideal),
  so $rs+I=r's+I$. *(This is the one and only place the hypothesis
  $\operatorname{Ann}(b)\subseteq I$ is used.)*
- In the second argument: if $s+I=s'+I$ then $s-s'\in I$, so $r(s-s')\in I$, giving
  $rs+I=rs'+I$.

So $\varphi$ is a well-defined function $bR\times R/I\to R/I$.

**Onto.** For any $s+I$, taking $b=b\cdot 1\in bR$ gives $\varphi(b,\,s+I)=1\cdot s+I=
s+I$. So $\varphi$ is surjective.

**Balanced** (additive in each slot and middle-linear over $R$):
- $\varphi(br_1+br_2,\,s+I)=\varphi(b(r_1+r_2),\,s+I)=(r_1+r_2)s+I=
  \varphi(br_1,s+I)+\varphi(br_2,s+I)$.
- $\varphi(br,\,(s+s')+I)=r(s+s')+I=\varphi(br,s+I)+\varphi(br,s'+I)$.
- Middle-linearity: for $t\in R$, $\varphi\big((br)t,\,s+I\big)=\varphi(b(rt),\,s+I)=
  (rt)s+I=r(ts)+I=\varphi\big(br,\,t(s+I)\big)$.

Thus $\varphi$ is an onto balanced map. $\quad\checkmark$

### (b) $bR\otimes_R R/I\cong R/I$

By the universal property of the tensor product, the balanced map $\varphi$ induces a
unique $R$-linear map
$$
\Phi: bR\otimes_R R/I\to R/I,\qquad \Phi\big(br\otimes(s+I)\big)=rs+I,
$$
which is surjective because $\varphi$ is. Define $\psi:R/I\to bR\otimes_R R/I$ by
$$
\psi(s+I)=b\otimes(s+I).
$$
This is well defined: if $s+I=s'+I$ then $(s-s')\in I$ so $(s-s')+I=0$ in $R/I$, whence
$b\otimes(s+I)-b\otimes(s'+I)=b\otimes\big((s-s')+I\big)=b\otimes 0=0$; and it is clearly
$R$-linear.

Now check $\Phi$ and $\psi$ are mutually inverse.
- $\Phi\big(\psi(s+I)\big)=\Phi\big(b\otimes(s+I)\big)=\Phi\big(b\cdot1\otimes(s+I)\big)=
  1\cdot s+I=s+I$. So $\Phi\circ\psi=\mathrm{id}_{R/I}$.
- On a generator $br\otimes(s+I)$, use middle-linearity in the tensor (move the scalar
  $r$): $br\otimes(s+I)=b\otimes\big(r(s+I)\big)=b\otimes(rs+I)$. Hence
  $$
  \psi\big(\Phi(br\otimes(s+I))\big)=\psi(rs+I)=b\otimes(rs+I)=br\otimes(s+I).
  $$
  So $\psi\circ\Phi=\mathrm{id}$ on generators, hence on all of $bR\otimes_R R/I$.

Therefore $\Phi$ is an isomorphism: $bR\otimes_R R/I\cong R/I$. $\quad\checkmark$

*(Conceptually: $bR\cong R/\operatorname{Ann}(b)$ via $br\mapsto r+\operatorname{Ann}(b)$,
so $bR\otimes R/I\cong R/(\operatorname{Ann}(b)+I)=R/I$ since
$\operatorname{Ann}(b)\subseteq I$.)*

### (c) Tensoring $0\to bR\hookrightarrow R$ with $R/I$ is not exact

Assume now also $b\in I$. Let $\iota: bR\hookrightarrow R$ be the inclusion. Applying
$-\otimes_R R/I$ yields the map
$$
\iota\otimes\mathrm{id}:\ bR\otimes_R R/I\ \longrightarrow\ R\otimes_R R/I .
$$
For the sequence $0\to bR\otimes R/I\xrightarrow{\ \iota\otimes\mathrm{id}\ } R\otimes
R/I$ to be exact (at the left term), $\iota\otimes\mathrm{id}$ would have to be
**injective**. We show it is not.

Use the canonical isomorphism $R\otimes_R R/I\cong R/I$, $r\otimes(s+I)\mapsto rs+I$.
Under it, $\iota\otimes\mathrm{id}$ becomes
$$
bR\otimes_R R/I\ \xrightarrow{\ \cong\ }\ R/I,\qquad br\otimes(s+I)\mapsto brs+I,
$$
since $\iota(br)=br$ inside $R$.

Consider the element $b\otimes(1+I)\in bR\otimes_R R/I$.
- It is **nonzero**: by part (b), $\Phi\big(b\otimes(1+I)\big)=\Phi\big(b\cdot1\otimes
  (1+I)\big)=1\cdot1+I=1+I$, which is nonzero in $R/I$ because $I\neq R$. As $\Phi$ is
  injective, $b\otimes(1+I)\neq 0$.
- Its image under $\iota\otimes\mathrm{id}$ is $b\cdot1+I=b+I$. But $b\in I$, so
  $b+I=0$.

Thus $b\otimes(1+I)$ is a nonzero element of $bR\otimes_R R/I$ lying in
$\ker(\iota\otimes\mathrm{id})$. Hence $\iota\otimes\mathrm{id}$ is not injective, and
the tensored sequence
$$
0\ \to\ bR\otimes_R R/I\ \xrightarrow{\ \iota\otimes\mathrm{id}\ }\ R\otimes_R R/I
$$
is **not exact**. $\quad\blacksquare$

### Remark

This is the standard demonstration that tensoring is only right-exact: the injection
$bR\hookrightarrow R$ is destroyed by $-\otimes R/I$. The two hypotheses do precisely
opposite jobs on the witness $b\otimes(1+I)$: $\operatorname{Ann}(b)\subseteq I$ keeps it
*alive* in $bR\otimes R/I$ (part b), while $b\in I$ *kills* its image in $R\otimes R/I$.
The obstruction is measured by $\operatorname{Tor}_1^R(R/bR,\,R/I)\neq 0$; concretely it
says the ideal $bR$ (equivalently $R/\operatorname{Ann}(b)$) fails to be flat for this
$I$. A clean instance: $R=\mathbb{Z}$, $b=2$, $I=(2)$ (so $\operatorname{Ann}(2)=0
\subseteq I$ and $2\in I$): $2\mathbb{Z}\otimes\mathbb{Z}/2\cong\mathbb{Z}/2$, but the
map to $\mathbb{Z}\otimes\mathbb{Z}/2\cong\mathbb{Z}/2$ sends the generator $2\otimes1$
to $2\equiv0$.

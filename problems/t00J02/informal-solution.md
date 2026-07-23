<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J02: A degree-zero criterion from preimages bounding disks — Poincaré duality and transverse pullback

## Why It's Hard

The statement connects two things that live at opposite ends of topology: the **degree** of $f:\Sigma\to\Sigma$ is a single global integer ($f_*[\Sigma]=\deg(f)\,[\Sigma]$), while the hypothesis is *local-looking* — every circle of the preimage $f^{-1}(C)$ bounds a disk. The work is building the bridge:

- **Translate "bounds a disk" into homology.** A curve bounding an embedded disk is null-homotopic, hence **null-homologous**. So the real hypothesis is $[f^{-1}(C)]=0$ in $H_1(\Sigma;\mathbb Z)$ — and one must see that this is the usable form.
- **Connect a preimage to a pullback.** The bridge from $f^{-1}(C)$ to $f$ acting on cohomology is the fact that, for a **transverse** map, the Poincaré dual of the preimage is the pullback of the Poincaré dual: $\mathrm{PD}[f^{-1}(C)]=f^*\mathrm{PD}[C]$. This is the crux, and it is exactly why transversality is hypothesized.
- **Extract the degree.** Degree is the factor by which $f^*$ scales the cup-product (intersection) pairing on $H^1(\Sigma)$. To *see* the degree one needs a class to pair $\mathrm{PD}[C]$ against — and here the hypothesis "**$C$ wraps a handle**" is essential: it guarantees $[C]\ne0$ and supplies a **dual curve** $C'$ with $[C]\cdot[C']=1$. (Were $C$ separating/null-homologous, the conclusion would be false.)

The difficulty is orchestrating Poincaré duality, transversality, and naturality of cup product so that a vanishing preimage class forces the global degree to vanish.

## The Key Insight

Let $\omega=\mathrm{PD}[C]\in H^1(\Sigma;\mathbb Z)$. Two facts collide:

1. **Transversality** gives $f^*\omega=\mathrm{PD}\big[f^{-1}(C)\big]$, and the hypothesis (every component bounds a disk $\Rightarrow$ null-homologous) gives $[f^{-1}(C)]=0$. Hence
$$
f^*\omega=0 .
$$
2. **Degree scales the pairing:** for $\alpha,\beta\in H^1(\Sigma)$, naturality of cup product and $f_*[\Sigma]=\deg(f)[\Sigma]$ give
$$
\big\langle f^*\alpha\cup f^*\beta,[\Sigma]\big\rangle=\deg(f)\,\big\langle\alpha\cup\beta,[\Sigma]\big\rangle .
$$

Because $C$ wraps a handle, pick a dual curve $C'$ with $[C]\cdot[C']=1$ and set $\omega'=\mathrm{PD}[C']$, so $\langle\omega\cup\omega',[\Sigma]\rangle=[C]\cdot[C']=1$. Then
$$
\deg(f)=\deg(f)\cdot\langle\omega\cup\omega',[\Sigma]\rangle=\big\langle f^*\omega\cup f^*\omega',[\Sigma]\big\rangle=\big\langle 0\cup f^*\omega',[\Sigma]\big\rangle=0 .
$$
The vanishing of one pullback class $f^*\omega$ annihilates the whole pairing, and that pairing *is* the degree.

## Complete Proof

$\Sigma$ is a closed oriented genus-$2$ surface; $H_1(\Sigma;\mathbb Z)\cong\mathbb Z^4$ carries the (unimodular, skew-symmetric) algebraic intersection form $\cdot$, with Poincaré duality $\mathrm{PD}:H_1(\Sigma)\xrightarrow{\ \cong\ }H^1(\Sigma)$ intertwining the intersection form with the cup-product pairing:
$$
\big\langle \mathrm{PD}[A]\cup\mathrm{PD}[B],\,[\Sigma]\big\rangle=[A]\cdot[B]. \tag{1}
$$

### Step 1: $C$ is nonseparating and has a dual curve

$C$ wraps around one of the two handles, so in a standard symplectic basis $\{a_1,b_1,a_2,b_2\}$ of $H_1(\Sigma)$ (with $a_i\cdot b_i=1$ and all other basis intersections $0$) we may take $[C]=a_1$. In particular $[C]\ne0$, and the curve $C'$ representing $b_1$ — the companion loop of the same handle — satisfies
$$
[C]\cdot[C']=a_1\cdot b_1=1 . \tag{2}
$$

### Step 2: the preimage is a closed $1$-manifold dual to $f^*\mathrm{PD}[C]$

Since $f$ is transverse to the codimension-$1$ submanifold $C\subset\Sigma$, the preimage $f^{-1}(C)$ is a smooth closed $1$-submanifold of $\Sigma$ — a disjoint union of embedded circles — carrying the pulled-back co-orientation. The defining property of the Poincaré dual (Thom class) is natural under transverse pullback: writing $\omega=\mathrm{PD}[C]\in H^1(\Sigma)$,
$$
\mathrm{PD}\big[f^{-1}(C)\big]=f^*\omega . \tag{3}
$$
(Concretely, $\omega$ is represented by a Thom form supported near $C$; transversality makes $f^*$ of that form a Thom form supported near $f^{-1}(C)$, which represents $\mathrm{PD}[f^{-1}(C)]$.)

### Step 3: the hypothesis forces $f^*\omega=0$

Each connected component of $f^{-1}(C)$ is a simple closed curve that, by hypothesis, **bounds an embedded disk** in $\Sigma$. A loop bounding a disk is null-homotopic, hence null-homologous, so each component represents $0\in H_1(\Sigma;\mathbb Z)$. The class of the whole preimage is the (oriented) sum of its components' classes,
$$
\big[f^{-1}(C)\big]=\sum_{\text{components}}0=0\in H_1(\Sigma;\mathbb Z).
$$
Applying $\mathrm{PD}$ and (3),
$$
f^*\omega=\mathrm{PD}\big[f^{-1}(C)\big]=\mathrm{PD}(0)=0 . \tag{4}
$$

### Step 4: degree scales the cup-product pairing

For any $\alpha,\beta\in H^1(\Sigma)$, naturality of cup product ($f^*(\alpha\cup\beta)=f^*\alpha\cup f^*\beta$) and the definition of degree ($f_*[\Sigma]=\deg(f)\,[\Sigma]$) give
$$
\big\langle f^*\alpha\cup f^*\beta,[\Sigma]\big\rangle
=\big\langle f^*(\alpha\cup\beta),[\Sigma]\big\rangle
=\big\langle \alpha\cup\beta,\,f_*[\Sigma]\big\rangle
=\deg(f)\,\big\langle\alpha\cup\beta,[\Sigma]\big\rangle . \tag{5}
$$

### Step 5: conclusion

Let $\omega'=\mathrm{PD}[C']$. By (1) and (2), $\langle\omega\cup\omega',[\Sigma]\rangle=[C]\cdot[C']=1$. Now apply (5) with $\alpha=\omega,\ \beta=\omega'$, and then (4):
$$
\deg(f)=\deg(f)\cdot\underbrace{\big\langle\omega\cup\omega',[\Sigma]\big\rangle}_{=1}
\overset{(5)}{=}\big\langle f^*\omega\cup f^*\omega',[\Sigma]\big\rangle
\overset{(4)}{=}\big\langle 0\cup f^*\omega',[\Sigma]\big\rangle=0 .
$$
Therefore $\deg(f)=0$. $\qquad\blacksquare$

### Remark — where each hypothesis is used, and an equivalent homological argument

- **Transversality** is exactly what makes $f^{-1}(C)$ a manifold with $\mathrm{PD}[f^{-1}(C)]=f^*\mathrm{PD}[C]$ (Step 2); without it the preimage need not even be a submanifold.
- **"$C$ wraps a handle"** ($[C]\ne0$ with a dual $C'$) is indispensable: it provides the class $\omega'$ that exposes the degree. If $C$ were null-homologous (e.g. separating), then $\mathrm{PD}[C]$ pairs trivially with everything and the argument — correctly — says nothing; indeed a degree-$d$ branched cover can have all preimages of a separating curve bounding disks.
- **"Components bound disks"** is used only through the weaker fact that they are **null-homologous** (Step 3). So the same proof works under the weaker hypothesis "$[f^{-1}(C)]=0$."

*Equivalent homological version.* Dualizing, transversality yields the geometric identity $[f^{-1}(C)]\cdot x=[C]\cdot f_*x$ for all $x\in H_1(\Sigma)$ (each intersection of $x$ with $f^{-1}(C)$ maps to an intersection of $f(x)$ with $C$, signs matching by transversality). With $[f^{-1}(C)]=0$ this gives $[C]\cdot f_*x=0$ for all $x$, so $\operatorname{im}(f_*)\subseteq [C]^{\perp}$, a rank-$3$ subgroup of $\mathbb Z^4$. Hence $\det(f_*)=0$; but $f_*$ preserves the intersection form up to the factor $\deg(f)$ (i.e. $M^{\mathsf T}JM=\deg(f)\,J$, giving $\det(f_*)=\pm\deg(f)^2$), so $\deg(f)^2=0$ and $\deg(f)=0$. This is the same fact viewed through $H_1$ rather than $H^1$.

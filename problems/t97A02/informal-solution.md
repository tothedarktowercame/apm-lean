<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97A02: If H₁(X) is finite, every map X → T² is nullhomotopic

## Why It's Hard

Maps into the torus could be wild, but the torus is special: it is **aspherical** — a `K(\mathbb Z^2,1)`,
with contractible universal cover `\mathbb R^2`. For such targets, the homotopy class of a map is controlled
**entirely by its effect on `\pi_1`**, and since `\pi_1(T^2)=\mathbb Z^2` is abelian, that effect factors
through `H_1`. The crux is a clash of algebraic features:

- `\pi_1(T^2)=\mathbb Z^2` is **torsion-free**, while `H_1(X)` is **finite** (all torsion). A homomorphism
  from a finite group to a torsion-free group must be **zero** (it kills every element, since each has finite
  order). So the induced map on `\pi_1` is forced trivial.
- A map inducing the trivial map on `\pi_1` into a `K(\pi,1)` **lifts to the contractible universal cover**,
  hence is nullhomotopic. Recognizing that "trivial on `\pi_1` ⇒ nullhomotopic" *uses asphericity* (it is
  false for non-aspherical targets like `S^2`) is the key.

Two technical snags: the target's abelianness is what lets `\pi_1(X)` be replaced by `H_1(X)`; and `X` may be
**disconnected**, so one must homotope each component to a constant and then merge the (possibly different)
constant values into one, using path-connectedness of `T^2`.

## The Key Insight

`T^2=\mathbb R^2/\mathbb Z^2` with contractible universal cover `p:\mathbb R^2\to T^2`. For a map `f:X\to
T^2` on a connected `X`, the induced `f_*:\pi_1(X)\to\mathbb Z^2` factors through `H_1(X)` (target abelian);
as `H_1(X)` is finite and `\mathbb Z^2` torsion-free, `f_*=0`. By the lifting criterion, `f` lifts to
`\tilde f:X\to\mathbb R^2`; since `\mathbb R^2` is contractible, `\tilde f` is nullhomotopic, hence so is
`f=p\circ\tilde f`. For disconnected `X`, apply this to each component and merge the resulting constants by
paths in the connected `T^2`.

## Complete Proof

Let `X` be a finite simplicial complex with `H_1(X)` finite, and `f:X\to T^2` continuous. Recall `T^2=S^1\times
S^1=\mathbb R^2/\mathbb Z^2`, with `\pi_1(T^2)=\mathbb Z^2` and universal covering `p:\mathbb R^2\to T^2`
(where `\mathbb R^2` is contractible).

### Algebraic lemma

> A homomorphism `\varphi:G\to A` from a finite group `G` to a torsion-free abelian group `A` is trivial.

*Proof.* For `g\in G`, `g` has finite order `n`, so (writing `A` additively) `n\cdot\varphi(g)=\varphi(g^n)=
\varphi(e)=0`. Since `A` is torsion-free, `\varphi(g)=0`. Hence `\varphi\equiv0`. ∎

### Step 1: each component maps trivially on `\pi_1`

`X` is a finite complex, so it has finitely many connected components `X_1,\dots,X_m`, each a connected
finite complex; and `H_1(X)=\bigoplus_j H_1(X_j)` is finite, so each `H_1(X_j)` is finite. Fix a component
`X_j` with basepoint, and consider
$$
f_{j*}:\pi_1(X_j)\to\pi_1(T^2)=\mathbb Z^2 .
$$
Because `\mathbb Z^2` is **abelian**, `f_{j*}` kills commutators and so factors through the abelianization
`H_1(X_j)=\pi_1(X_j)^{\mathrm{ab}}`:
$$
\pi_1(X_j)\twoheadrightarrow H_1(X_j)\xrightarrow{\ \overline{f_{j*}}\ }\mathbb Z^2 .
$$
Here `H_1(X_j)` is finite and `\mathbb Z^2` is torsion-free, so by the Lemma `\overline{f_{j*}}=0`, hence
`f_{j*}=0`: the map `f_j:=f|_{X_j}` is trivial on `\pi_1`.

### Step 2: each component is nullhomotopic

`X_j` is a connected simplicial complex, hence path-connected, locally path-connected, and semilocally simply
connected. Since
$$
f_{j*}\big(\pi_1(X_j)\big)=0=p_*\big(\pi_1(\mathbb R^2)\big),
$$
the **lifting criterion** for the covering `p:\mathbb R^2\to T^2` gives a continuous lift `\tilde
f_j:X_j\to\mathbb R^2` with `p\circ\tilde f_j=f_j`. Because `\mathbb R^2` is **contractible**, `\tilde f_j`
is homotopic to a constant map `\tilde c_j` (a straight-line homotopy `H(x,t)=(1-t)\tilde f_j(x)+t\,\tilde
c_j` works). Composing with `p`,
$$
f_j = p\circ\tilde f_j \ \simeq\ p\circ\tilde c_j = \text{const}_{c_j}, \qquad c_j:=p(\tilde c_j)\in T^2 .
$$
So each `f_j` is homotopic to a constant map `X_j\to\{c_j\}`.

### Step 3: assemble and merge the constants

The homotopies of Step 2 on the individual components fit together into a homotopy of `f` (the components
`X_j` are open-and-closed in `X`, so a map defined component-wise is continuous, and likewise the homotopy):
$$
f\ \simeq\ g, \qquad g|_{X_j}\equiv c_j \ \ (\text{a locally constant map}).
$$
Finally collapse the constants to one point. Fix `c_0\in T^2`; since `T^2` is path-connected, choose paths
`\gamma_j:[0,1]\to T^2` with `\gamma_j(0)=c_j`, `\gamma_j(1)=c_0`. Define
$$
G:X\times[0,1]\to T^2, \qquad G(x,t)=\gamma_j(t)\ \text{ for } x\in X_j .
$$
`G` is continuous (each `X_j` is open-and-closed, and `G` is continuous on each `X_j\times[0,1]`), with
`G(\cdot,0)=g` and `G(\cdot,1)\equiv c_0`. Hence `g\simeq\text{const}_{c_0}`, and therefore
$$
f\ \simeq\ g\ \simeq\ \text{const}_{c_0} .
$$

So every map `f:X\to T^2` is homotopic to a constant map. ∎

**Remark.** The engine is the **asphericity** of the torus: `T^2=K(\mathbb Z^2,1)`, so `[X,T^2]` is governed
by `\pi_1`, and (target abelian) by `H_1`. Concretely, free homotopy classes of maps `X\to T^2` correspond to
`\operatorname{Hom}(H_1(X),\mathbb Z^2)`, which is `0` exactly when `H_1(X)` is finite (or more generally pure
torsion). The two ingredients are the algebraic incompatibility *finite vs. torsion-free* (no nonzero
homomorphism) and the geometric fact that trivial-on-`\pi_1` maps into a `K(\pi,1)` lift to the contractible
universal cover and die. This *fails* for non-aspherical targets: a map `X\to S^2` can be trivial on `\pi_1`
yet essential (detected by `\pi_2` or `H_2`), so "finite `H_1` ⇒ nullhomotopic" is special to aspherical
targets like the torus. Equivalently, since `H^1(X;\mathbb Z)=\operatorname{Hom}(H_1(X),\mathbb Z)=0` for
finite `H_1(X)`, and `[X,T^2]\cong H^1(X;\mathbb Z)^2`, there is a single homotopy class — the constant.

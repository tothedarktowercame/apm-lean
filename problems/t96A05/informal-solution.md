<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96A05: A nullhomotopic map on a closed set extends — the homotopy extension property via Tietze, the tube lemma, and Urysohn

## Why It's Hard

This is the homotopy extension property proved *by hand* in a normal space (no CW or cofibration hypothesis),
and the cleverness is geometric: the homotopy `f\simeq\text{const}` is repackaged as a map `h` on the
**L-shaped** subspace `Y=(A\times I)\cup(X\times\{1\})` of the cylinder, and the extension of `f` is read off
by threading a *section* `x\mapsto(x,\varphi(x))` of the cylinder through a neighborhood of `Y`. Three
separate tools must be orchestrated, each with a snag:

- **(a)** Extending `h` uses that `\mathbb R^2\setminus\{0\}` is an *open* subset of `\mathbb R^2`:
  Tietze-extend the `\mathbb R^2`-valued `h` to the whole cylinder, then take the preimage of `\mathbb
  R^2\setminus\{0\}` to get an *open* neighborhood `U` on which the extension still avoids `0`. (You cannot
  Tietze-extend directly into `\mathbb R^2\setminus\{0\}`, which isn't convex — the detour through `\mathbb
  R^2` is essential.)
- **(b)** Getting a *uniform tube* `W\times I\subseteq U` around `A\times I` is the **tube lemma**, valid
  because the fiber `I=[0,1]` is **compact**.
- **(c)** Building the section needs a function `\varphi:X\to[0,1]` that is `0` on `A` (to recover `f`) and
  `1` off the tube (to escape into the safe top `X\times\{1\}`); **Urysohn's lemma** provides it. The graph
  of `\varphi` must be shown to stay inside `U` — in the tube where `\varphi\in[0,1)`, and on the top where
  `\varphi=1`.

The subtlety is that no single step does the job; the extension emerges only from the relay
*Tietze `\to` tube `\to` Urysohn*.

## The Key Insight

Encode the homotopy `H:A\times I\to\mathbb R^2\setminus\{0\}` (with `H(\cdot,0)=f`, `H(\cdot,1)=` const) as
`h:Y\to\mathbb R^2\setminus\{0\}` on `Y=(A\times I)\cup(X\times\{1\})`. Then:

1. **(Tietze)** extend `h` to `\widetilde h:X\times I\to\mathbb R^2`; `U:=\widetilde h^{-1}(\mathbb
   R^2\setminus\{0\})` is open, contains `Y`, and `\widetilde h|_U` maps into `\mathbb R^2\setminus\{0\}`.
2. **(Tube lemma)** there is open `W\supseteq A` with `W\times I\subseteq U`.
3. **(Urysohn)** pick `\varphi:X\to[0,1]` with `\varphi|_A=0`, `\varphi|_{X\setminus W}=1`; then the section
   `s(x)=(x,\varphi(x))` lands in `U` (in `W\times I` when `x\in W`, in `X\times\{1\}` when `x\notin W`), and
   $$
   \bar f := \widetilde h\circ s : X\to\mathbb R^2\setminus\{0\}, \qquad \bar f(x)=\widetilde h(x,\varphi(x)),
   $$
   satisfies `\bar f|_A=f` (since `\varphi|_A=0` and `\widetilde h(a,0)=h(a,0)=f(a)`).

## Complete Proof

`X` and `X\times I` (`I=[0,1]`) are normal, `A\subseteq X` is closed, and `f:A\to\mathbb R^2\setminus\{0\}`
is continuous and homotopic to a constant. Fix such a homotopy `H:A\times I\to\mathbb R^2\setminus\{0\}` with
`H(a,0)=f(a)` and `H(a,1)=c` (a constant point of `\mathbb R^2\setminus\{0\}`). Define `h` on
$$
Y=(A\times I)\cup(X\times\{1\})
$$
by `h|_{A\times I}=H` and `h|_{X\times\{1\}}\equiv c`. The two definitions agree on the overlap `A\times\{1\}`
(both equal `c`), and `A\times I`, `X\times\{1\}` are closed in `X\times I`, so by the pasting lemma `h:Y\to
\mathbb R^2\setminus\{0\}` is continuous; `Y` is closed in `X\times I`.

### (a) Extend `h` to an open neighborhood `U` of `Y`

Compose with the inclusion `\mathbb R^2\setminus\{0\}\hookrightarrow\mathbb R^2` and write `h=(h_1,h_2)` in
coordinates. Each `h_j:Y\to\mathbb R` is continuous on the closed subset `Y` of the **normal** space
`X\times I`, so by the **Tietze extension theorem** it extends to a continuous `\widetilde h_j:X\times I\to
\mathbb R`. Set `\widetilde h=(\widetilde h_1,\widetilde h_2):X\times I\to\mathbb R^2`, a continuous extension
of `h` (now `\mathbb R^2`-valued). Define
$$
U := \widetilde h^{-1}\big(\mathbb R^2\setminus\{0\}\big).
$$
`U` is open (preimage of the open set `\mathbb R^2\setminus\{0\}` under continuous `\widetilde h`), and `U\supseteq
Y` because `\widetilde h|_Y=h` already maps into `\mathbb R^2\setminus\{0\}`. Then `\widetilde h|_U:U\to\mathbb
R^2\setminus\{0\}` is a continuous extension of `h` to the open neighborhood `U` of `Y`. ∎

### (b) True: there is open `W\supseteq A` with `W\times I\subseteq U`

This is **true**, by the **tube lemma**. Fix `a\in A`. The slice `\{a\}\times I` is contained in `A\times
I\subseteq Y\subseteq U`, and `I` is **compact**, so the tube lemma gives an open `W_a\ni a` in `X` with
`W_a\times I\subseteq U`. Let
$$
W := \bigcup_{a\in A} W_a,
$$
an open set containing `A`. Then `W\times I=\bigcup_{a\in A}(W_a\times I)\subseteq U`. (Compactness of the
fiber `I` is exactly what makes a *single* tube `W_a\times I` fit inside `U`; without it the statement can
fail.)

### (c) Construct `\bar f:X\to\mathbb R^2\setminus\{0\}` with `\bar f|_A=f`

**A section of the cylinder.** `A` and `X\setminus W` are disjoint closed subsets of the **normal** space
`X` (`A\subseteq W`, so `A\cap(X\setminus W)=\varnothing`). By **Urysohn's lemma** there is a continuous
$$
\varphi:X\to[0,1], \qquad \varphi|_A\equiv0, \qquad \varphi|_{X\setminus W}\equiv1 .
$$
Define the (continuous) section
$$
s:X\to X\times I, \qquad s(x)=(x,\varphi(x)).
$$

**The section lands in `U`.** For any `x\in X`:

- if `x\in W`, then `s(x)=(x,\varphi(x))\in W\times I\subseteq U` (part b);
- if `x\notin W`, then `\varphi(x)=1`, so `s(x)=(x,1)\in X\times\{1\}\subseteq Y\subseteq U`.

Either way `s(x)\in U`, so `s` maps `X` into `U`.

**The extension.** Define
$$
\bar f := \widetilde h\circ s : X\to\mathbb R^2\setminus\{0\}, \qquad \bar f(x)=\widetilde h\big(x,\varphi(x)\big),
$$
continuous as a composition of continuous maps (`s` into `U`, then `\widetilde h|_U` into `\mathbb
R^2\setminus\{0\}`).

**It restricts to `f`.** For `a\in A`, `\varphi(a)=0`, so
$$
\bar f(a)=\widetilde h(a,0)=h(a,0)=H(a,0)=f(a),
$$
using `(a,0)\in A\times I\subseteq Y` where `\widetilde h=h`. Hence `\bar f|_A=f`.

Therefore `f` extends to the continuous map `\bar f:X\to\mathbb R^2\setminus\{0\}`. ∎

**Remark.** This is the **homotopy extension theorem** for the target `\mathbb R^2\setminus\{0\}\simeq S^1`:
a map on a closed subset extends to the whole (normal) space *provided it is nullhomotopic*, and the proof is
a clean three-step relay. Tietze turns the difficulty of the *non-convex* target into an open neighborhood
`U` of the L-shaped `Y` (the homotopy plus the constant cap); the tube lemma upgrades the neighborhood to a
full cylinder `W\times I` over a neighborhood of `A`; and Urysohn slides the base `X\times\{0\}` up through
this cylinder — staying at height `0` on `A` (to recover `f`) and rising to the safe top `X\times\{1\}`
elsewhere (where `h` is the constant). The nullhomotopy hypothesis is essential: it is what lets the constant
cap `X\times\{1\}` exist, giving the section somewhere to escape; a non-nullhomotopic `f` (e.g. the identity
`S^1\to\mathbb R^2\setminus\{0\}` on `A=S^1\subseteq X=D^2`) cannot extend, which is the obstruction-theoretic
content of `H^1`.

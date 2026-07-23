<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J10: The product of two regular spaces is regular

## Why It's Hard

Regularity is stated as "separate a *point* from a *closed set* by disjoint opens," but in a product `X\times
Y` the closed sets are genuinely complicated — they are *not* just products `C\times D` of closed sets, but
arbitrary closed subsets. Trying to separate `(x,y)` from a general closed `C\subseteq X\times Y` directly,
factor by factor, is awkward and error-prone, because `C` need not respect the product structure at all.

The way through is to **reformulate regularity locally**: a space is regular iff every point has a
neighborhood base of *closed* sets, i.e.
$$
z\in W\ \text{open}\ \Longrightarrow\ \exists\ \text{open } U\ \text{with}\ z\in U\subseteq\overline U\subseteq W .
$$
This version refers only to a point and an *open* neighborhood — and open neighborhoods in a product *do*
have a friendly base (the boxes `A\times B`). So the proof becomes: shrink a basic box around `(x,y)` to a
smaller box whose **closure** still sits inside, using regularity in each factor, and assemble via the
identity `\overline{U_1\times U_2}=\overline{U_1}\times\overline{U_2}`. The subtleties are proving the
reformulation and the closure-of-a-product identity.

## The Key Insight

Use the closed-neighborhood form of regularity. Given `(x,y)` in an open `W\subseteq X\times Y`, pick a basic
box `A\times B\subseteq W` with `x\in A`, `y\in B`. Regularity of `X` and `Y` gives open `U_1,U_2` with
$$
x\in U_1\subseteq\overline{U_1}\subseteq A, \qquad y\in U_2\subseteq\overline{U_2}\subseteq B .
$$
Then `U=U_1\times U_2` is open, `(x,y)\in U`, and since `\overline{U_1\times U_2}=\overline{U_1}\times
\overline{U_2}`,
$$
(x,y)\in U\subseteq\overline U=\overline{U_1}\times\overline{U_2}\subseteq A\times B\subseteq W ,
$$
which is exactly the closed-neighborhood condition. So `X\times Y` is regular.

## Complete Proof

Throughout, "regular" means: for every point `z` and closed set `C` with `z\notin C`, there are disjoint open
sets `U\ni z` and `V\supseteq C`. Let `X` and `Y` be regular and give `X\times Y` the product topology (basic
open sets are `A\times B` with `A\subseteq X`, `B\subseteq Y` open).

### Lemma 1 (closed neighborhoods characterize regularity)

> A space `Z` is regular **iff** for every `z\in Z` and every open `W` with `z\in W`, there is an open `U`
> with `z\in U\subseteq\overline U\subseteq W`.

*Proof.* (`\Rightarrow`) Let `z\in W` open. Then `C:=Z\setminus W` is closed and `z\notin C`. By regularity
there are disjoint opens `U\ni z` and `V\supseteq C`. Since `U\subseteq Z\setminus V` and `Z\setminus V` is
closed, `\overline U\subseteq Z\setminus V\subseteq Z\setminus C=W`. So `z\in U\subseteq\overline U\subseteq
W`.

(`\Leftarrow`) Let `z\notin C` with `C` closed; then `z\in W:=Z\setminus C` open. Get open `U` with `z\in
U\subseteq\overline U\subseteq W`. Put `V:=Z\setminus\overline U`, open. Then `C=Z\setminus W\subseteq
Z\setminus\overline U=V`, and `U\cap V=U\cap(Z\setminus\overline U)\subseteq\overline U\cap(Z\setminus\overline
U)=\varnothing`. So `U\ni z` and `V\supseteq C` are disjoint opens. ∎

### Lemma 2 (closure of a product is the product of closures)

> In `X\times Y`, for any `S\subseteq X` and `T\subseteq Y`, `\overline{S\times T}=\overline S\times\overline
> T`.

*Proof.* (`\subseteq`) `\overline S\times\overline T` is closed: it equals `\pi_X^{-1}(\overline
S)\cap\pi_Y^{-1}(\overline T)`, an intersection of preimages of closed sets under the continuous projections,
hence closed. Since `S\times T\subseteq\overline S\times\overline T`, also `\overline{S\times
T}\subseteq\overline S\times\overline T`.

(`\supseteq`) Let `(a,b)\in\overline S\times\overline T`, so `a\in\overline S`, `b\in\overline T`. Any basic
open neighborhood `N_1\times N_2` of `(a,b)` has `N_1\ni a` meeting `S` (as `a\in\overline S`) and `N_2\ni b`
meeting `T`; choosing `s\in N_1\cap S` and `t\in N_2\cap T` gives `(s,t)\in(N_1\times N_2)\cap(S\times T)\ne
\varnothing`. So every neighborhood of `(a,b)` meets `S\times T`, i.e. `(a,b)\in\overline{S\times T}`. ∎

### The product is regular

By Lemma 1, it suffices to verify the closed-neighborhood condition in `X\times Y`. Let `(x,y)\in X\times Y`
and let `W` be an open set with `(x,y)\in W`.

**Find a box.** By definition of the product topology, there is a basic open box `A\times B\subseteq W` with
`x\in A` (open in `X`) and `y\in B` (open in `Y`).

**Shrink in each factor.** Since `X` is regular, Lemma 1 (applied in `X` to `x\in A`) gives an open `U_1`
with
$$
x\in U_1\subseteq\overline{U_1}\subseteq A .
$$
Since `Y` is regular, likewise there is an open `U_2` with
$$
y\in U_2\subseteq\overline{U_2}\subseteq B .
$$

**Assemble.** Set `U:=U_1\times U_2`, an open neighborhood of `(x,y)` in `X\times Y`. By Lemma 2,
$$
\overline U=\overline{U_1\times U_2}=\overline{U_1}\times\overline{U_2}\subseteq A\times B\subseteq W .
$$
Thus
$$
(x,y)\in U\subseteq\overline U\subseteq W .
$$
By Lemma 1, `X\times Y` is **regular**. ∎

**Remark.** The proof turns on the *local* reformulation (Lemma 1): regularity says open neighborhoods can be
shrunk to ones with closure still inside, and this "shrinking" passes effortlessly to products because
(i) product opens have a base of boxes and (ii) closure distributes over products (Lemma 2). The same
argument shows an *arbitrary* product of regular spaces is regular (shrink in the finitely many factors a
basic open set constrains, leave the rest whole) — regularity, unlike normality, is productive. If one's
definition of "regular" also demands `T_1`, note products of `T_1` spaces are `T_1` (a singleton
`\{(x,y)\}=\{x\}\times\{y\}` is a product of closed points, hence closed), so the product is `T_3` as well.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J01: Separating closed sets by a function on the quotient — push down, then Urysohn

## Why It's Hard

The desired function `g` lives **downstairs on `Y`**, but the data `A,B` separating it lives **upstairs in
`X`**. So one cannot apply a separation theorem to `A,B` directly; one must first transport the problem to
`Y`, where it becomes Urysohn's lemma — *provided* `Y` is normal and the images `f(A),f(B)` are disjoint
closed sets. Verifying that requires assembling three point-set facts, each using a different hypothesis:

- **`f(A),f(B)` are closed in `Y`:** `A,B` are closed in the **compact** `X`, hence compact; their continuous
  images are compact; and compact subsets of the **Hausdorff** `Y` are closed. (They are disjoint by
  hypothesis.) Both "X compact" and "Y Hausdorff" are needed here.
- **`Y` is normal:** `Y=f(X)` is compact (continuous image of compact) and Hausdorff, and *compact Hausdorff
  spaces are normal*.
- **Urysohn's lemma** then produces `g:Y\to[0,1]` with `g|_{f(A)}=0`, `g|_{f(B)}=1`, and pulling back along
  `f` gives `g\circ f=0` on `A` and `=1` on `B`.

The trap is trying to build `g` directly from `A,B`; the whole point is that the separation must happen *after*
projecting to the normal space `Y`.

## The Key Insight

Project the closed sets down: `f(A)` and `f(B)` are disjoint **closed** subsets of `Y`, because `A,B` are
compact (closed in compact `X`), their images are compact, and compact sets are closed in the Hausdorff `Y`.
Since `Y=f(X)` is **compact Hausdorff**, it is **normal**, so **Urysohn's lemma** gives a continuous
`g:Y\to[0,1]` with
$$
g\equiv0 \text{ on } f(A), \qquad g\equiv1 \text{ on } f(B).
$$
Then `g\circ f(x)=0` for `x\in A` (as `f(x)\in f(A)`) and `=1` for `x\in B`.

## Complete Proof

Let `f:X\to Y` be a continuous surjection, `X` compact, `Y` Hausdorff, and `A,B\subseteq X` closed with
`f(A)\cap f(B)=\varnothing`.

### Lemma 1: continuous images of compact sets are compact

If `K\subseteq X` is compact and `\{V_\alpha\}` is an open cover of `f(K)`, then `\{f^{-1}(V_\alpha)\}` is an
open cover of `K` (continuity); a finite subcover `f^{-1}(V_{\alpha_1}),\dots,f^{-1}(V_{\alpha_n})` of `K`
gives `V_{\alpha_1},\dots,V_{\alpha_n}` covering `f(K)`. So `f(K)` is compact. In particular `Y=f(X)` is
compact, and (since `A,B` are closed in the compact `X`, hence compact) `f(A)` and `f(B)` are compact.

### Lemma 2: compact subsets of a Hausdorff space are closed

Let `K\subseteq Y` be compact, `Y` Hausdorff; we show `Y\setminus K` open. Fix `y\notin K`. For each `k\in K`
choose disjoint opens `U_k\ni y`, `W_k\ni k` (Hausdorff). The `\{W_k\}` cover compact `K`, so finitely many
`W_{k_1},\dots,W_{k_m}` do; then `U:=\bigcap_i U_{k_i}\ni y` is open and disjoint from `\bigcup_i
W_{k_i}\supseteq K`, so `U\subseteq Y\setminus K`. Hence `K` is closed. Thus `f(A)` and `f(B)` are **closed**
in `Y` (and disjoint, by hypothesis).

### Lemma 3: a compact Hausdorff space is normal

Let `C,D` be disjoint closed subsets of the compact Hausdorff `Y`; they are compact (closed in compact). We
separate them by disjoint opens. *First* separate a point from a compact set: for `c\in C` and each `d\in D`,
Hausdorffness gives disjoint opens `P_d\ni c`, `Q_d\ni d`; finitely many `Q_{d_1},\dots,Q_{d_k}` cover the
compact `D`, and `U_c:=\bigcap_j P_{d_j}\ni c` is disjoint from `W_c:=\bigcup_j Q_{d_j}\supseteq D`. *Then*
the `\{U_c\}_{c\in C}` cover the compact `C`, so finitely many `U_{c_1},\dots,U_{c_l}` do; set `U:=\bigcup_i
U_{c_i}\supseteq C` and `W:=\bigcap_i W_{c_i}\supseteq D`. These are disjoint open sets. So `Y` is **normal**.

### Urysohn's lemma

> **(Urysohn.)** In a normal space `Y`, for disjoint closed sets `C,D` there is a continuous `g:Y\to[0,1]`
> with `g|_C\equiv0` and `g|_D\equiv1`.

*(Idea of proof: using normality repeatedly, build open sets `\{U_q\}` indexed by dyadic rationals `q\in[0,1]`
with `C\subseteq U_0`, `D\subseteq Y\setminus U_1`, and `\overline{U_q}\subseteq U_{q'}` whenever `q<q'`;
then `g(y)=\inf\{q:y\in U_q\}` (with `g=1` off all `U_q`) is continuous and has the required values.)*

### Assembling the proof

By Lemmas 1–2, `f(A)` and `f(B)` are disjoint **closed** subsets of `Y`. By Lemma 1, `Y=f(X)` is **compact**,
and `Y` is Hausdorff by hypothesis, so by Lemma 3 `Y` is **normal**. Apply **Urysohn's lemma** to the
disjoint closed sets `f(A),f(B)\subseteq Y`: there is a continuous
$$
g:Y\to[0,1], \qquad g\equiv0 \text{ on } f(A), \qquad g\equiv1 \text{ on } f(B).
$$

Finally, for the composition `g\circ f:X\to[0,1]` (continuous as a composition):

- if `x\in A`, then `f(x)\in f(A)`, so `g\circ f(x)=g(f(x))=0`;
- if `x\in B`, then `f(x)\in f(B)`, so `g\circ f(x)=g(f(x))=1`.

Thus `g:Y\to[0,1]` is continuous with `g\circ f=0` on `A` and `g\circ f=1` on `B`, as required. ∎

**Remark.** The proof is "separate downstairs, pull back." The function necessarily lives on `Y` because the
constraint is on `g\circ f`, and the cleanest way to control `g\circ f` on `A` and `B` is to control `g` on
the images `f(A),f(B)` and compose. Every hypothesis pulls its weight: *`X` compact* makes the closed `A,B`
compact and `Y=f(X)` compact; *`Y` Hausdorff* turns those compact images into *closed* sets and (with
compactness) makes `Y` normal; *`f(A)\cap f(B)=\varnothing`* is what lets Urysohn apply. Note the disjointness
hypothesis is on the **images** `f(A),f(B)`, not on `A,B` — `A` and `B` may even overlap upstairs, as long as
they project to disjoint sets; the function `g\circ f` is constant on fibers of `f`, so it can only separate
`A` from `B` when their images are already disjoint.

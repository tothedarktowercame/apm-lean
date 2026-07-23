<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97A03: Connected double covers of a sphere with a circle attached at the poles

## Why It's Hard

The space `X` (a `2`-sphere `\Sigma` with a circle attached at its two poles, the circle split into two arcs)
hides a clean homotopy type, and the double covers must be found *and drawn*, then have their homology and
`\pi_1` computed. Several things must line up:

- **Identify `X` up to homotopy.** Attaching the circle at the two poles `N,S` and reading off a CW structure
  shows `X\simeq S^2\vee S^1\vee S^1`, so `\pi_1(X)=F_2` (the sphere is simply connected and contributes only
  to `H_2`). The non-obvious point is that the sphere's `2`-cell attaches along a *null-homotopic* loop, so it
  is invisible to `\pi_1`.
- **Classify the covers.** Connected double covers ↔ index-`2` subgroups of `F_2` ↔ surjections `F_2\to\mathbb
  Z/2`, of which there are `2^2-1=3`. The key geometric fact is that the sphere is **simply connected**, so it
  *always* lifts to two disjoint spheres; the only variation is how the **circle** lifts — into one circle or
  two — which is what makes the pictures differ.
- **The surprise:** all three covers have the **same** homology and `\pi_1` (they are all homotopy equivalent
  to `S^2\vee S^2\vee S^1\vee S^1\vee S^1`), so (b) and (c) give a single answer even though the *spaces* in
  (a) look different. Seeing that the homotopy invariants can't separate homeomorphism types is the lesson.

## The Key Insight

`X\simeq S^2\vee S^1\vee S^1`, so `\pi_1(X)=F_2`. The `2`-sphere `\Sigma` (simply connected) lifts to **two
disjoint spheres** `\Sigma_1,\Sigma_2` in every double cover; only the circle's lift varies, governed by the
monodromy `(\varepsilon_\alpha,\varepsilon_\beta)\in\{(1,0),(0,1),(1,1)\}` on the two arcs:

- `(1,0),(0,1)`: the circle lifts to **one** connected circle (double-covering the original), threading
  through all four poles — homeomorphic spaces (swap the two arcs);
- `(1,1)`: the circle lifts to **two** circles, each joining one pole of `\Sigma_1` to one pole of `\Sigma_2`.

Either way `Y\simeq S^2\vee S^2\vee S^1\vee S^1\vee S^1`, so
$$
H_0=\mathbb Z,\quad H_1=\mathbb Z^3,\quad H_2=\mathbb Z^2,\quad H_{\ge3}=0, \qquad \pi_1(Y)=F_3 .
$$

## Complete Proof

### Setting up `X`

Give `X` a CW structure: vertices `N=A` and `S=B`; edges `m` (a meridian of `\Sigma` from `N` to `S`), and
`\alpha,\beta` (the two arcs of the circle, each from `A=N` to `B=S`); one `2`-cell `f` filling `\Sigma`,
attached along `m\,m^{-1}`. The `1`-skeleton is a graph with `2` vertices and `3` edges (`\simeq` figure-eight,
`F_2`), and `f` is attached along the *null-homotopic* loop `m\,m^{-1}`, so
$$
\pi_1(X)=F_2, \qquad X\simeq S^2\vee S^1\vee S^1 .
$$
(Indeed `H_0(X)=\mathbb Z`, `H_1(X)=\mathbb Z^2`, `H_2(X)=\mathbb Z`.)

### (a) The possible covers `Y`

Connected double covers of `X` correspond to surjections `\varphi:\pi_1(X)=F_2\to\mathbb Z/2`; there are
`2^2-1=3` of them. Build the cover explicitly. The sphere `\Sigma` is **simply connected**, so its preimage is
the trivial cover `\Sigma_1\sqcup\Sigma_2` (two disjoint `2`-spheres). Label their poles `N_1,S_1\in\Sigma_1`
and `N_2,S_2\in\Sigma_2` (the meridian `m` lifts to `m_i:N_i\to S_i` inside `\Sigma_i`). Over the circle, each
arc `\alpha,\beta` lifts to two arcs; writing `\varepsilon_\alpha,\varepsilon_\beta\in\{0,1\}` for whether
lifting the arc swaps sheets,
$$
\alpha_i : N_i\to S_{i+\varepsilon_\alpha}, \qquad \beta_i : N_i\to S_{i+\varepsilon_\beta}
$$
(indices mod `2`), and `(\varphi(\alpha m^{-1}),\varphi(\beta m^{-1}))=(\varepsilon_\alpha,\varepsilon_\beta)`.
The three nontrivial cases:

**Space `Y_1` (`(\varepsilon_\alpha,\varepsilon_\beta)=(1,0)` or `(0,1)` — homeomorphic by swapping arcs).**
The circle's monodromy is `\varepsilon_\alpha+\varepsilon_\beta=1\ne0`, so the circle lifts to **one connected
circle** double-covering the original, visiting `N_1\to S_2\to N_2\to S_1\to N_1`. So `Y_1` is **two spheres
joined by a single circle** that passes through all four poles (hitting `\Sigma_1` at `N_1,S_1` and `\Sigma_2`
at `N_2,S_2`):
```
        ___                       ___
      /     \   N1            S2 /     \
     |  Σ1   |--o----.   .----o-|  Σ2   |     one circle through N1,S2,N2,S1
     |       |   \    \ /    /  |       |     (drawn as the loop weaving
      \ ___ /  S1 o----X----o N2 \ ___ /       between the two spheres)
```

**Space `Y_2` (`(\varepsilon_\alpha,\varepsilon_\beta)=(1,1)`).** The circle's monodromy is `1+1=0`, so the
circle lifts to **two circles**: `C_1` through `N_1\in\Sigma_1` and `S_2\in\Sigma_2`, and `C_2` through
`N_2\in\Sigma_2` and `S_1\in\Sigma_1`. So `Y_2` is **two spheres joined by two separate circles**, each circle
touching one pole on each sphere:
```
        ___      C1 (loop)     ___
      /     \   N1__________S2 /     \
     |  Σ1   |--o            o-|  Σ2   |
     |       |                |       |
      \ ___ /   o____________o \ ___ /
              S1     C2 (loop)  N2
```

So up to homeomorphism there are **two** possible spaces, `Y_1` and `Y_2` (three covers in all, with the
`(1,0)` and `(0,1)` covers homeomorphic).

### (b) Homology (same for every connected double cover)

Lift the CW structure: `Y` has `4` vertices `N_1,N_2,S_1,S_2`, `6` edges `m_1,m_2,\alpha_1,\alpha_2,\beta_1,
\beta_2`, and `2` faces `f_1,f_2` (one per sphere sheet, each attached along `m_i m_i^{-1}`). The cellular
boundaries are
$$
\partial_2 f_i = m_i - m_i = 0, \qquad \partial_1 m_i = S_i-N_i,\quad \partial_1\alpha_i=S_{i+\varepsilon_\alpha}-N_i,\quad \partial_1\beta_i=S_{i+\varepsilon_\beta}-N_i .
$$
Then:

- **`H_2(Y)=\ker\partial_2=\mathbb Z^2`** (both `f_1,f_2` are cycles, since `\partial_2=0`) — the two spheres.
- **`H_0(Y)=\mathbb Z`** (`Y` connected).
- **`H_1(Y)=\ker\partial_1/\operatorname{im}\partial_2=\ker\partial_1`.** Since `Y` is connected,
  `\operatorname{rank}(\operatorname{im}\partial_1)=4-1=3`, so `\ker\partial_1\subseteq\mathbb Z^6` has rank
  `6-3=3`; being a subgroup of a free group it is free: **`H_1(Y)=\mathbb Z^3`**.
- `H_n(Y)=0` for `n\ge3` (no higher cells).

This computation used only that `Y` is connected and `\partial_2=0`, so it is identical for all three covers:
$$
\boxed{\ H_0(Y)=\mathbb Z,\quad H_1(Y)=\mathbb Z^3,\quad H_2(Y)=\mathbb Z^2,\quad H_n(Y)=0\ (n\ge3).\ }
$$
(Check: `\chi(Y)=1-3+2=0=2\cdot\chi(X)`.)

### (c) Fundamental group (same for every connected double cover)

`\pi_1(Y)` is an index-`2` subgroup of `\pi_1(X)=F_2`. By the **Nielsen–Schreier index formula**, an index-`n`
subgroup of a free group of rank `r` is free of rank `1+n(r-1)`; here `n=2`, `r=2`, giving rank `1+2(2-1)=3`.
Therefore
$$
\boxed{\ \pi_1(Y)=F_3 \ \text{(free group on 3 generators)}\ }
$$
for every connected double cover. (Consistently, `Y\simeq S^2\vee S^2\vee S^1\vee S^1\vee S^1`: the
`1`-skeleton graph of `Y` has `b_1=6-4+1=3`, and the two `2`-cells attach along null-homotopic loops
`m_im_i^{-1}`, creating two spheres without changing `\pi_1`; this reads off `\pi_1=F_3`, `H_2=\mathbb Z^2`,
`H_1=\mathbb Z^3` directly.)

**Remark.** The structural reason the answers coincide: the sphere is simply connected, so it splits off two
spheres in *any* cover, contributing a fixed `H_2=\mathbb Z^2` and nothing to `\pi_1`; meanwhile every index-`2`
subgroup of `F_2` is `F_3` and every connected double cover of a finite graph multiplies `\chi` by `2` while
adding the same Betti numbers. Thus all three covers are *homotopy equivalent* (`\simeq S^2\vee S^2\vee
S^1\vee S^1\vee S^1`), and homology/`\pi_1` cannot tell them apart — the genuine difference between `Y_1` and
`Y_2` is **how the circle reassembles** (one double-covering loop vs. two single loops), a homeomorphism-type
distinction visible only in the pictures of part (a), not in the algebraic invariants.

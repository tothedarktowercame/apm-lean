<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A06: Perturbing a map transverse to the z-axis — translation in the normal plane + parametric transversality

## Why It's Hard

The task is to make an *arbitrary* smooth `f:X\to\mathbb R^3` transverse to the `z`-axis `Y` by an
explicit, low-dimensional family of perturbations — and to *prove* that almost every member of the family
works. Two design choices must be exactly right:

- **Which perturbations?** Transversality to `Y` is a condition only on the directions *normal* to `Y`. Since
  `Y` is the `z`-axis, its normal directions span the `xy`-plane, so the perturbations should be
  **translations in the `xy`-plane**: `F_{\alpha,\beta} = f + (\alpha,\beta,0)`. Crucially this is a
  **2-parameter** family (matching `\operatorname{codim} Y = 2`), and translating in the `z`-direction would
  be useless (it slides along `Y`, never helping transversality).
- **Why does almost every member work?** This is *not* obvious for `f_s` individually — it is the content of
  the **parametric transversality theorem**, whose engine is **Sard's theorem**. The move is to bundle the
  whole family into one "big map" `G(x,\alpha,\beta)=f(x)+(\alpha,\beta,0)`, show **`G` itself is transverse
  to `Y`** (free, because the parameter derivatives already sweep out the entire normal plane), and then use
  that the bad parameters are the critical values of a projection — a measure-zero set by Sard.

The subtlety is the reduction "`f_s` transverse `\iff` `s` is a regular value of a projection," which
converts a transversality statement about uncountably many maps into a single Sard application.

## The Key Insight

Translate `f` in the plane normal to the `z`-axis:
$$
F_{\alpha,\beta}(x) = f(x) + (\alpha,\beta,0), \qquad (\alpha,\beta)\in S=\mathbb R^2 .
$$
Then `F_{0,0}=f` (so `f` is in the family), and the **big map** `G(x,\alpha,\beta)=f(x)+(\alpha,\beta,0)` is
transverse to `Y` because its `\alpha`- and `\beta`-derivatives are `(1,0,0)` and `(0,1,0)`, which together
with `T Y=\langle(0,0,1)\rangle` already span `\mathbb R^3`. By the parametric transversality theorem —
`W=G^{-1}(Y)` is a manifold, and `s` is a regular value of the projection `\pi:W\to S` iff `F_s\pitchfork Y`,
while by **Sard** almost every `s` is a regular value — we get `F_s\pitchfork Y` for almost every `s`.

## Complete Proof

`Y=\{(0,0,z):z\in\mathbb R\}\subset\mathbb R^3` is the `z`-axis, a `1`-dimensional submanifold with
`T_qY=\langle(0,0,1)\rangle` for every `q\in Y`, so `\operatorname{codim} Y=2`. Recall a smooth map
`h:X\to\mathbb R^3` is **transverse to `Y`** (written `h\pitchfork Y`) if at every `x` with `h(x)\in Y`,
$$
dh_x\big(T_xX\big) + T_{h(x)}Y = \mathbb R^3 .
$$

### The family

For `(\alpha,\beta)\in S := \mathbb R^2` (an open subset of `\mathbb R^2`), define
$$
\boxed{\ F_{\alpha,\beta}(x) = f(x) + (\alpha,\beta,0).\ }
$$
Each `F_{\alpha,\beta}` is smooth, and the assignment is smooth in all variables.

**(a) `f` is in the family.** Taking `(\alpha,\beta)=(0,0)\in S` gives `F_{0,0}=f`.

### The big map is transverse to `Y`

Define `G:X\times S\to\mathbb R^3` by
$$
G(x,\alpha,\beta) = f(x) + (\alpha,\beta,0).
$$
We claim `G\pitchfork Y`. Let `(x,\alpha,\beta)` be a point with `q:=G(x,\alpha,\beta)\in Y`. The
differential `dG_{(x,\alpha,\beta)} : T_xX\oplus T_{(\alpha,\beta)}S \to \mathbb R^3` includes the partial
derivatives in the parameter directions,
$$
\frac{\partial G}{\partial\alpha} = (1,0,0), \qquad \frac{\partial G}{\partial\beta} = (0,1,0),
$$
so its image contains the entire `xy`-plane `\langle(1,0,0),(0,1,0)\rangle`. Together with `T_qY=\langle
(0,0,1)\rangle`,
$$
\operatorname{Im}\big(dG_{(x,\alpha,\beta)}\big) + T_qY \supseteq \langle(1,0,0),(0,1,0)\rangle + \langle(0,0,1)\rangle = \mathbb R^3 .
$$
Hence `G\pitchfork Y` (indeed `G` is a submersion). The point is that the parameters were chosen to translate
in *exactly* the directions normal to `Y`, so the parameter derivatives alone fill out `\mathbb R^3/T Y`.

### (b) Almost every `F_s` is transverse to `Y` (parametric transversality via Sard)

Since `G\pitchfork Y`, the **preimage theorem** makes
$$
W := G^{-1}(Y) \subseteq X\times S
$$
a smooth submanifold, of codimension `\operatorname{codim} Y = 2` in `X\times S`. Let `\pi: W\to S` be the
restriction to `W` of the projection `(x,s)\mapsto s` (here `s=(\alpha,\beta)`).

**Reduction lemma.** *For `s\in S`, the map `F_s` is transverse to `Y` if and only if `s` is a regular value
of `\pi`.* (This is the heart of the parametric transversality theorem.) Sketch: fix `(x,s)\in W`, so
`q:=G(x,s)\in Y`. Because `G\pitchfork Y`, the linear map `\overline{dG}:T_xX\oplus T_sS \to \mathbb
R^3/T_qY` (the composite of `dG` with the quotient by `T_qY`) is **surjective**, and `T_{(x,s)}W=\ker
\overline{dG}`. One checks by linear algebra that the restriction `\overline{dG}|_{T_xX}` (i.e.
`d(F_s)_x` projected to `\mathbb R^3/T_qY`) is surjective — which is exactly `F_s\pitchfork Y` at `x` — **iff**
`d\pi_{(x,s)} : T_{(x,s)}W\to T_sS` is surjective at every such `(x,s)`, i.e. iff `s` is a regular value of
`\pi`.

**Apply Sard.** `\pi:W\to S` is a smooth map between manifolds. By **Sard's theorem**, the set of *critical*
values of `\pi` has measure zero in `S`; equivalently, **almost every `s\in S` is a regular value of `\pi`**.
By the Reduction Lemma, for every such regular value `s`, `F_s\pitchfork Y`. Therefore
$$
F_s = F_{\alpha,\beta}\ \pitchfork\ Y \qquad\text{for almost every } s=(\alpha,\beta)\in S .
$$

This establishes (a) and (b): the `2`-parameter family `F_{\alpha,\beta}=f+(\alpha,\beta,0)` over
`S=\mathbb R^2` contains `f` and is transverse to the `z`-axis for almost every parameter. ∎

**Remark.** The construction is the standard proof of the **Transversality Homotopy Theorem**: any map can be
perturbed, by an arbitrarily small translation, to be transverse to a given submanifold. The two
ingredients are (1) translating in the **normal directions** to `Y` — here the `xy`-plane, which is why a
`2`-parameter family (and not `1` or `3`) is the natural choice, since `\operatorname{codim} Y=2` — so that
the big map `G` is automatically transverse, and (2) **Sard's theorem**, which turns "the big map is
transverse" into "almost every slice is transverse" by identifying the bad parameters with critical values
of a projection. Restricting `S` to a small ball around `(0,0)` shows the perturbation can be taken
arbitrarily small, recovering the density of transverse maps.

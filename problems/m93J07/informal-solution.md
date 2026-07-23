<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J07: A zoo of Banach-space examples — separability, reflexivity, dense-range operators, and L^p membership

## Why It's Hard

This is twelve quick questions, but two of them are traps: they ask for an example that
**cannot exist**, and the whole difficulty is recognizing this rather than hunting forever.

- **(f)** "A nonseparable Banach space whose dual is separable" — impossible, because
  *separability of the dual forces separability of the space* (`X^*` separable `\Rightarrow`
  `X` separable). You must know and prove this theorem, not search.
- **(l)** "A function in `L^4([0,1])` but not `L^2([0,1])`" — impossible, because on a
  *finite* measure space the `L^p` spaces nest the "wrong" way: `L^4([0,1]) \subset L^2([0,1])`.

Everything else is a matter of having the standard menagerie at hand — `\ell^1`, `\ell^2`,
`\ell^\infty`, `c_0`, and their separability/reflexivity status — and of understanding *why*
`L^p` membership can fail: from a **local singularity** (kills high exponents) or from a
**heavy tail at infinity** (kills low exponents). Which failure is available depends entirely
on whether the measure space is finite (`[0,1]`) or infinite (`\mathbb{R}`).

## The Key Insight

Three organizing principles handle all twelve parts.

1. **The sequence-space table.** `\ell^1` is separable but not reflexive (`(\ell^1)^*=\ell^\infty`);
   `\ell^p` (`1<p<\infty`) is separable and reflexive; `\ell^\infty` and `L^\infty` are
   nonseparable and nonreflexive; for an *uncountable* index set, `\ell^p(I)` keeps the
   reflexivity of `\ell^p` but becomes nonseparable. One table answers (a)–(e).

2. **`X^*` separable `\Rightarrow X` separable.** This single theorem makes (f) impossible and
   is the deepest content in the problem.

3. **`L^p` membership = singularity vs. tail, gated by the measure.** On finite measure,
   `p<q \Rightarrow L^q \subseteq L^p` (Hölder), so only a singularity can break membership and
   only in the *high*-exponent direction — making (k) possible and (l) impossible. On
   `\mathbb{R}`, neither inclusion holds: a singularity `|x|^{-1/3}` near `0` lives in `L^2\setminus L^4`,
   a tail `|x|^{-1/3}` near `\infty` lives in `L^4\setminus L^2`. The *same* exponent `-1/3`
   does both jobs, just relocated.

A dense-but-proper range (g,h) is delivered by any bounded injective operator with non-closed
range, e.g. multiplication by `x`.

## Complete Proof

Throughout, `\{e_n\}` denotes a standard basis (of a sequence space, or an orthonormal basis
of `L^2`), and measures are Lebesgue.

### (a) A nonseparable Banach space — **YES: `\ell^\infty`.**
`\ell^\infty` (bounded sequences, sup norm) is complete. For each subset `A\subseteq\mathbb{N}`
let `\chi_A` be its indicator sequence; these are uncountably many points with
`\|\chi_A-\chi_B\|_\infty = 1` for `A\ne B`. The balls of radius `\tfrac12` about them are
disjoint and uncountable, so no countable set is dense. Nonseparable. (`L^\infty([0,1])` works
identically, using indicators of intervals.)

### (b) A separable nonreflexive Banach space — **YES: `\ell^1`.**
`\ell^1` is separable (finitely-supported rational sequences are dense). It is not reflexive:
`(\ell^1)^* = \ell^\infty` and `(\ell^\infty)^* \supsetneq \ell^1`, so the canonical embedding
`\ell^1 \hookrightarrow (\ell^1)^{**} = (\ell^\infty)^*` is not onto. (Equivalently, `c_0` is
separable with `c_0^{**}=\ell^\infty \ne c_0`.)

### (c) A nonseparable reflexive Banach space — **YES: `\ell^2(I)`, `I` uncountable.**
`\ell^2(I)` (functions `I\to\mathbb{C}` with countable support and `\sum|x_i|^2<\infty`) is a
Hilbert space, hence reflexive. It is nonseparable: the basis vectors `\{e_i\}_{i\in I}` are
uncountable and pairwise at distance `\sqrt 2`. (Any nonseparable Hilbert space, or `\ell^p(I)`
with `1<p<\infty` uncountable `I`, serves.)

### (d) A nonseparable nonreflexive Banach space — **YES: `\ell^\infty`.**
Nonseparable by (a). Nonreflexive because `\ell^\infty=(\ell^1)^*`: if `\ell^\infty` were
reflexive then its predual `\ell^1` would be reflexive (the dual of a reflexive space is
reflexive, and reflexivity passes between a space and its dual), contradicting (b). (Also
`\ell^1(I)` or `L^\infty([0,1])` work.)

### (e) A separable Banach space with nonseparable dual — **YES: `\ell^1`.**
`\ell^1` is separable (b), and `(\ell^1)^* = \ell^\infty` is nonseparable (a). (Likewise
`L^1([0,1])` is separable with dual `L^\infty([0,1])` nonseparable.)

### (f) A nonseparable Banach space with separable dual — **NO such space exists.**
**Theorem.** If `X^*` is separable, then `X` is separable.

*Proof.* Let `\{f_n\}` be dense in the unit sphere of `X^*`. For each `n` pick `x_n\in X`,
`\|x_n\|=1`, with `|f_n(x_n)| > \tfrac12`. Let `Y = \overline{\operatorname{span}}\{x_n\}`, a
separable closed subspace. If `Y \ne X`, then by Hahn–Banach there is `f\in X^*` with
`\|f\|=1` and `f|_Y = 0`. For every `n`,
`\|f - f_n\| \ge |(f-f_n)(x_n)| = |f_n(x_n)| > \tfrac12` (using `f(x_n)=0`), contradicting the
density of `\{f_n\}` in the unit sphere. Hence `Y=X` and `X` is separable. ∎

Contrapositive: a nonseparable `X` has nonseparable dual, so no example exists.

### (g) A linear map `\Phi:L^2([0,1])\to L^2([0,1])` with dense, proper image — **YES: `(\Phi f)(x)=x\,f(x)`.**
This multiplication operator is linear (indeed bounded, `\|\Phi\|\le 1`), so it a fortiori
satisfies (g). Its image is dense: if `g\perp \operatorname{ran}\Phi`, then
`\int_0^1 x f(x)\,g(x)\,dx = 0` for all `f\in L^2`, forcing `x\,g(x)=0` a.e., i.e. `g=0`. But it
is not all of `L^2`: the constant function `1` is not in the range, since `1 = x f(x)` would
require `f(x)=1/x \notin L^2([0,1])`. (Verification of properness/boundedness completed in (h).)

### (h) A *bounded* linear map with dense, proper image — **YES: the same `\Phi`, `(\Phi f)(x)=x f(x)`.**
Boundedness: `\|\Phi f\|_2^2 = \int_0^1 x^2|f|^2 \le \int_0^1 |f|^2 = \|f\|_2^2`, so `\|\Phi\|\le1`.
Density and properness are shown in (g). Thus `\Phi` is bounded, has dense range, but is not
surjective. (Equivalently, the diagonal operator `\Phi e_n = \tfrac1n e_n` on an orthonormal
basis: bounded, injective, dense range, yet `\sum \tfrac1n e_n \in L^2` is not in the range.)

### (i) `f\in L^2(\mathbb{R})`, `f\notin L^4(\mathbb{R})` — **YES: `f(x)=|x|^{-1/3}\mathbf 1_{(0,1)}(x)`.**
`\int_0^1 |x|^{-2/3}\,dx < \infty` (exponent `2/3<1`), so `f\in L^2`. But
`\int_0^1 |x|^{-4/3}\,dx = \infty` (exponent `4/3>1`), so `f\notin L^4`. A local singularity at
`0` defeats the higher exponent.

### (j) `f\in L^4(\mathbb{R})`, `f\notin L^2(\mathbb{R})` — **YES: `f(x)=|x|^{-1/3}\mathbf 1_{\{|x|\ge 1\}}(x)`.**
`\int_{|x|\ge1} |x|^{-4/3}\,dx < \infty` (exponent `4/3>1`), so `f\in L^4`. But
`\int_{|x|\ge1} |x|^{-2/3}\,dx = \infty` (exponent `2/3<1`), so `f\notin L^2`. The *same*
function `|x|^{-1/3}`, now placed in the tail, defeats the lower exponent.

### (k) `f\in L^2([0,1])`, `f\notin L^4([0,1])` — **YES: `f(x)=x^{-1/3}`.**
`\int_0^1 x^{-2/3}\,dx < \infty` so `f\in L^2`; `\int_0^1 x^{-4/3}\,dx = \infty` so `f\notin L^4`.
(On finite measure only the singularity route is available, and it works only in this
high-exponent direction — see (l).)

### (l) `f\in L^4([0,1])`, `f\notin L^2([0,1])` — **NO such function exists.**
On a finite measure space with `\mu([0,1])=1`, Hölder's inequality (with exponents `2` and `2`
applied to `|f|^2\cdot 1`) gives

$$\|f\|_2^2 = \int_0^1 |f|^2\cdot 1 \le \Big(\int_0^1 |f|^4\Big)^{1/2}\Big(\int_0^1 1\Big)^{1/2}
= \|f\|_4^2,$$

so `\|f\|_2 \le \|f\|_4`. Hence `L^4([0,1]) \subseteq L^2([0,1])`: every `L^4` function on `[0,1]`
is automatically `L^2`. No example exists. ∎

---

**Summary.** Ten constructions and two impossibilities. The impossibilities — (f) `X^*`
separable `\Rightarrow X` separable, and (l) `L^4([0,1]) \subseteq L^2([0,1])` — are the heart
of the problem: recognizing that the requested object is forbidden by a theorem, not merely
hard to find. The two `L^p`-on-`\mathbb{R}` examples (i),(j) are the same singular profile
`|x|^{-1/3}` relocated from the origin to the tail, dramatizing that on infinite measure the
two inclusion failures are symmetric, whereas on finite measure (k),(l) only one direction is
possible.

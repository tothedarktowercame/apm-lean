<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t98A01: A regular 5-fold self-cover (only the torus), and the canonical form of K#T#T#P#K#T

## Why It's Hard

Both parts test the classification of surfaces, but the traps are different:

- **(a)** Euler characteristic multiplies under a `5`-fold cover, `\chi(\Sigma)=5\chi(\Sigma')`, so if
  `\Sigma\cong\Sigma'` then `\chi=5\chi` forces `\chi=0` — *only the torus* can self-cover `5`-foldly. But
  ruling-in is not enough: one must **exhibit** a genuine regular `5`-sheeted cover `T^2\to T^2`. The
  enabling fact is that `\pi_1(T^2)=\mathbb Z^2` is **abelian**, so *every* connected cover is regular.
- **(b)** The connected sum mixes **orientable** (`T`) and **non-orientable** (`P,K`) pieces, so one cannot
  naively add genera. The decisive tool is **Dyck's theorem** `T\#P\cong P\#P\#P`: *in the presence of a
  crosscap, a handle becomes two crosscaps.* Forgetting this and treating the tori as handles gives the
  wrong canonical form. Once everything is converted to crosscaps, the count and `\chi` follow.

## The Key Insight

- **(a)** `\chi(\Sigma)=5\chi(\Sigma')` and `\Sigma\cong\Sigma'\Rightarrow\chi(\Sigma')=5\chi(\Sigma')
  \Rightarrow\chi(\Sigma')=0`, i.e. both are the **torus**. And the torus *does* self-cover `5`-foldly:
  `(z,w)\mapsto(z^5,w)` is a `5`-sheeted covering `T^2\to T^2`, regular because `\pi_1(T^2)=\mathbb Z^2` is
  abelian (every subgroup normal). **Yes, possible** — exactly when `\Sigma=\Sigma'=T^2`.
- **(b)** The surface is non-orientable (it contains `P`), so its canonical form is `\#^k\mathbb{RP}^2`.
  Convert to crosscaps via `K=P\#P` and `T\#P\cong3P`: `2K\!=\!4`, `1P\!=\!1`, `3T\!=\!6` crosscaps, total
  `k=11`. So the canonical form is `\#^{11}\mathbb{RP}^2`, with `\chi=2-11=-9` (check:
  `\chi=\sum\chi-2(6-1)=1-10=-9`).

## Complete Proof

### (a) A regular 5-sheeted self-cover exists only for the torus — and there it does

Let `\pi:\Sigma\to\Sigma'` be a regular `5`-sheeted covering of closed orientable surfaces.

**Necessity (only the torus).** Euler characteristic multiplies under a finite cover:
`\chi(\Sigma)=5\,\chi(\Sigma')`. If `\Sigma\cong\Sigma'`, then `\chi(\Sigma)=\chi(\Sigma')`, so
$$
\chi(\Sigma') = 5\,\chi(\Sigma') \implies 4\,\chi(\Sigma')=0 \implies \chi(\Sigma')=0 .
$$
A closed orientable surface of genus `g` has `\chi=2-2g`, so `\chi=0` means `g=1`: both `\Sigma` and
`\Sigma'` must be the **torus** `T^2`.

**Sufficiency (the torus works).** It remains to produce a regular `5`-sheeted cover `T^2\to T^2`. Write
`T^2=S^1\times S^1` and define
$$
\pi:T^2\to T^2, \qquad \pi(z,w)=(z^5,\,w).
$$
Since `z\mapsto z^5` is a `5`-to-`1` covering of `S^1` and `w\mapsto w` is a homeomorphism, `\pi` is a
`5`-sheeted covering. It is **regular**: the deck transformations `(z,w)\mapsto(\zeta z,w)` for `\zeta^5=1`
(the `5`th roots of unity) form a group `\cong\mathbb Z/5` acting transitively on each fiber, so the cover is
Galois. (More structurally, `\pi` corresponds to the index-`5` subgroup `5\mathbb Z\times\mathbb Z\le\mathbb
Z^2=\pi_1(T^2)`, which is normal because `\mathbb Z^2` is abelian — so *every* connected cover of `T^2` is
regular.)

**Conclusion.** It **is** possible for `\Sigma\cong\Sigma'`, and this happens exactly when both are the torus;
`(z,w)\mapsto(z^5,w)` is an explicit regular `5`-sheeted cover `T^2\to T^2`. ∎

### (b) Canonical form and Euler characteristic of `K\#T\#T\#P\#K\#T`

Recall the building blocks and their Euler characteristics:
$$
\chi(T)=0,\qquad \chi(P)=\chi(\mathbb{RP}^2)=1,\qquad \chi(K)=0\ \ (K=P\#P).
$$

**Compute `\chi` first (a clean cross-check).** For a connected sum of `m` closed surfaces,
`\chi(S_1\#\cdots\#S_m)=\sum_i\chi(S_i)-2(m-1)`. Here `m=6` and the summands are `K,T,T,P,K,T`:
$$
\chi = \big[\chi(K)+\chi(T)+\chi(T)+\chi(P)+\chi(K)+\chi(T)\big] - 2(6-1) = \big[0+0+0+1+0+0\big] - 10 = -9 .
$$

**Identify the canonical form.** The surface contains the non-orientable summand `P`, hence is
**non-orientable**; every closed non-orientable surface is `N_k=\#^k\mathbb{RP}^2` (a connected sum of `k`
crosscaps), with `\chi(N_k)=2-k`. Convert each summand to crosscaps:

- each `K=P\#P` contributes `2` crosscaps; the two `K`'s give `4`;
- the lone `P` contributes `1`;
- each `T` contributes `2` crosscaps **because the surface is already non-orientable** — by **Dyck's
  theorem** `T\#\mathbb{RP}^2\cong\mathbb{RP}^2\#\mathbb{RP}^2\#\mathbb{RP}^2`, a handle in the presence of a
  crosscap equals two crosscaps; the three `T`'s give `6`.

Total crosscaps `k=4+1+6=11`. Hence
$$
\boxed{\ K\#T\#T\#P\#K\#T \ \cong\ N_{11}=\underbrace{\mathbb{RP}^2\#\cdots\#\mathbb{RP}^2}_{11}\ }
$$
the non-orientable surface of (non-orientable) genus `11`, with
$$
\chi(N_{11}) = 2 - 11 = -9,
$$
matching the direct computation. ∎

**Remark.** Part (a) is the `\chi`-multiplicativity rigidity: a surface that self-covers nontrivially must
have `\chi=0`, and abelian `\pi_1` is what guarantees the cover can be made *regular* (for higher-genus
surfaces, `\chi<0` already forbids any self-cover of degree `>1`). Part (b) hinges on the one
counterintuitive relation of surface arithmetic: handles and crosscaps are *not* independent once a crosscap
is present — `T\#P=3P`, equivalently "orientability, once lost, turns every handle into two crosscaps." That
is why the answer is a connected sum of `11` projective planes rather than something built from `3` tori and
some crosscaps; the orientable summands are absorbed. The `\chi`-additivity `\sum\chi-2(m-1)` is the reliable
shortcut, and the canonical form `N_k` is then pinned down by `k=2-\chi=11`.

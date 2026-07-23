<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A05: A k-sheeted cover multiplies integrals and intersection numbers by k

## Why It's Hard

The unifying theme is that an orientation-preserving `k`-sheeted covering "counts everything `k` times,"
but each part requires turning that slogan into a rigorous local-to-global argument:

- **(a)** is a construction: produce, for *every* `k`, a genuine `k`-sheeted orientation-preserving cover of
  compact oriented surfaces. The trap is overcomplicating it — the degree-`k` self-map of a circle factor
  of the torus does it in one line, and one must remember to check *orientation-preserving* (the power map
  `z\mapsto z^k` wraps the same way, so it is).
- **(b)** is the integration identity. The subtlety is that `\pi^*\omega` lives upstairs and there is no
  global diffeomorphism to change variables by; the proof must **localize** to evenly-covered charts with a
  partition of unity, on each of which `\pi` restricts to `k` separate orientation-preserving
  diffeomorphisms, each contributing `\int_X\omega`. The orientation hypothesis is exactly what makes each
  of the `k` local change-of-variables come with a `+` sign rather than cancelling.
- **(c)** is the intersection-number identity, and the difficulty is threefold: (i) check `\pi^{-1}(Z_i)` is
  again a *compact oriented submanifold* (uses that `\pi` is a local diffeomorphism and proper); (ii) see
  that transversality and local intersection *signs* are preserved upstairs (again orientation-preserving
  local diffeo); (iii) count: each transverse intersection point downstairs has exactly `k` preimages, each
  carrying the **same** sign. Mishandling the signs — the one place the orientation hypotheses bite — is the
  classic error.

## The Key Insight

Locally an orientation-preserving covering is just `k` disjoint orientation-preserving diffeomorphic copies.
So everything that is "counted by integration or by signed point-counting" is reproduced `k` times:

- **(a)** `\pi : T^2 \to T^2`, `(z,w)\mapsto (z^k, w)`, is `k`-sheeted and orientation-preserving.
- **(b)** Over an evenly-covered `U`, `\pi^{-1}(U)=\bigsqcup_{j=1}^k V_j` with each `\pi|_{V_j}:V_j\to U` an
  orientation-preserving diffeomorphism, so `\int_{\pi^{-1}(U)}\pi^*\omega = \sum_{j=1}^k\int_U\omega =
  k\int_U\omega`; a partition of unity globalizes this to `\int_{\tilde X}\pi^*\omega = k\int_X\omega`.
- **(c)** Each transverse point `p\in Z_1\cap Z_2` has exactly `k` preimages `\tilde p_1,\dots,\tilde p_k`,
  and because `\pi` is an orientation-preserving local diffeomorphism the local sign is preserved,
  `\mathrm{sign}(\tilde p_j)=\mathrm{sign}(p)`. Summing, `I_{\tilde X}(\tilde Z_1,\tilde Z_2) = k\,
  I_X(Z_1,Z_2)`.

## Complete Proof

### (a) A `k`-sheeted orientation-preserving cover of surfaces, for every `k`

Let `X = \tilde X = T^2 = S^1 \times S^1` (compact, oriented by the product orientation), and define
$$
\pi : T^2 \to T^2, \qquad \pi(z, w) = (z^k, w),
$$
viewing `S^1 \subset \mathbb C`. The map `z \mapsto z^k` is a `k`-sheeted covering of `S^1` (each point has
the `k` distinct `k`-th roots as preimages) and is a local diffeomorphism preserving the orientation of
`S^1` (its derivative `kz^{k-1}` rotates without reversing, i.e. it has positive degree `k`). Hence
`\pi = (z\mapsto z^k) \times \mathrm{id}_{S^1}` is a `k`-sheeted covering of `T^2` and, as a product of two
orientation-preserving local diffeomorphisms, is **orientation-preserving**. This is the desired example for
every `k \ge 1`. ∎

### (b) `\int_{\tilde X}\pi^*\omega = k\int_X\omega`

Let `\omega \in \Omega^n(X)`. The integral of an `n`-form over an oriented `n`-manifold is invariant under
orientation-preserving diffeomorphisms: if `\phi : V \to U` is an orientation-preserving diffeomorphism then
`\int_V \phi^*\omega = \int_U \omega` (the change-of-variables formula, with `+` sign because `\phi`
preserves orientation).

**Localize.** Each point of `X` has an evenly-covered open neighborhood. Since `X` is compact, choose a
finite cover `\{U_\alpha\}` by evenly-covered open sets, and a subordinate partition of unity `\{\rho_\alpha\}`,
`\sum_\alpha \rho_\alpha \equiv 1`, with `\mathrm{supp}\,\rho_\alpha \subset U_\alpha`. Then
`\omega = \sum_\alpha \rho_\alpha\omega` with each `\rho_\alpha\omega` supported in the evenly-covered
`U_\alpha`. By linearity of both integrals and of `\pi^*`, it suffices to prove the identity for a form `\eta`
supported in a single evenly-covered set `U`.

**Compute over one evenly-covered set.** Write `\pi^{-1}(U) = \bigsqcup_{j=1}^k V_j`, where each
`\pi|_{V_j} : V_j \to U` is a diffeomorphism — and *orientation-preserving*, since `\pi` is
orientation-preserving and `V_j, U` carry the restricted orientations. As `\pi^*\eta` is supported in
`\pi^{-1}(U)`,
$$
\int_{\tilde X}\pi^*\eta = \int_{\pi^{-1}(U)}\pi^*\eta = \sum_{j=1}^k \int_{V_j}\big(\pi|_{V_j}\big)^*\eta = \sum_{j=1}^k \int_U \eta = k\int_U \eta = k\int_X \eta,
$$
using the orientation-preserving change of variables on each `V_j`.

**Globalize.** Apply this to `\eta = \rho_\alpha\omega` and sum over `\alpha`:
$$
\int_{\tilde X}\pi^*\omega = \sum_\alpha \int_{\tilde X}\pi^*(\rho_\alpha\omega) = \sum_\alpha k\int_X \rho_\alpha\omega = k\int_X \Big(\sum_\alpha \rho_\alpha\Big)\omega = k\int_X \omega . \qquad \blacksquare
$$

### (c) `\tilde Z_i` are compact oriented submanifolds, and `I_{\tilde X}(\tilde Z_1,\tilde Z_2) = k\,I_X(Z_1,Z_2)`

**The preimages are compact oriented submanifolds.** A covering map `\pi` is a local diffeomorphism. Around
any `\tilde x \in \tilde X`, `\pi` restricts to a diffeomorphism of a neighborhood `\tilde W` onto a
neighborhood `W = \pi(\tilde W)`, carrying `\pi^{-1}(Z_i)\cap \tilde W` onto `Z_i \cap W`. Hence
`\tilde Z_i := \pi^{-1}(Z_i)` is locally diffeomorphic to `Z_i`, so it is an **embedded submanifold** of
`\tilde X` of the same dimension as `Z_i`. It is **closed** (preimage of the closed set `Z_i` under the
continuous `\pi`) in the compact `\tilde X`, hence **compact**. Finally, the restriction
`\pi|_{\tilde Z_i} : \tilde Z_i \to Z_i` is itself a `k`-sheeted covering and a local diffeomorphism; orient
`\tilde Z_i` by **pulling back the orientation of `Z_i`** through this local diffeomorphism. This is
consistent (local diffeos transport orientations) and makes `\pi|_{\tilde Z_i}` orientation-preserving. So
each `\tilde Z_i` is a compact oriented submanifold.

**Reduce to the transverse case.** The intersection number depends only on the homology/cobordism classes of
`Z_1, Z_2`, so by perturbing `Z_2` within its homotopy class we may assume `Z_1 \pitchfork Z_2`
(transverse). Because `\dim Z_1 + \dim Z_2 = n` and both are compact, `Z_1\cap Z_2` is then a finite set of
points, and
$$
I_X(Z_1,Z_2) = \sum_{p \in Z_1\cap Z_2} \mathrm{sign}(p), \qquad \mathrm{sign}(p) = \pm 1,
$$
where `\mathrm{sign}(p) = +1` iff the orientation `(T_pZ_1)\oplus(T_pZ_2)` agrees with `T_pX` (here
`T_pZ_1 \oplus T_pZ_2 = T_pX` by transversality and complementary dimension).

**Transversality and signs lift.** Since `\pi` is a local diffeomorphism, `\tilde Z_1 \pitchfork \tilde Z_2`
as well, and
$$
\tilde Z_1 \cap \tilde Z_2 = \pi^{-1}(Z_1)\cap \pi^{-1}(Z_2) = \pi^{-1}(Z_1\cap Z_2).
$$
Each `p \in Z_1\cap Z_2` has exactly `k` preimages `\tilde p_1, \dots, \tilde p_k` (the cover is
`k`-sheeted). Fix one, `\tilde p_j`. The differential `d\pi_{\tilde p_j} : T_{\tilde p_j}\tilde X \to T_p X`
is an orientation-preserving isomorphism (since `\pi` is orientation-preserving), and it restricts to
orientation-preserving isomorphisms `T_{\tilde p_j}\tilde Z_i \xrightarrow{\sim} T_p Z_i` (by our choice of
orientation on `\tilde Z_i`). Therefore `d\pi_{\tilde p_j}` carries the oriented splitting
`(T_{\tilde p_j}\tilde Z_1)\oplus(T_{\tilde p_j}\tilde Z_2)` to `(T_pZ_1)\oplus(T_pZ_2)` *and* the ambient
orientation `T_{\tilde p_j}\tilde X` to `T_pX`, all orientation-preservingly. Comparing, the local sign is
unchanged:
$$
\mathrm{sign}(\tilde p_j) = \mathrm{sign}(p) \qquad \text{for each } j = 1, \dots, k.
$$

**Count.** Summing over all upstairs intersection points, grouped by their image `p`:
$$
I_{\tilde X}(\tilde Z_1, \tilde Z_2) = \sum_{p \in Z_1\cap Z_2}\ \sum_{j=1}^k \mathrm{sign}(\tilde p_j) = \sum_{p \in Z_1\cap Z_2} k\,\mathrm{sign}(p) = k\sum_{p} \mathrm{sign}(p) = k\,I_X(Z_1, Z_2). \qquad \blacksquare
$$

**Remark.** All three parts are the same phenomenon at different levels: a `k`-sheeted orientation-preserving
cover is *locally `k` disjoint orientation-preserving diffeomorphic copies*, so any quantity computed by
"integrate a top form" (part b) or "count signed points" (part c) is reproduced exactly `k` times. The
orientation-preserving hypothesis is indispensable in both: without it the `k` local copies could contribute
with mixed signs and partially cancel (e.g. the integral identity would fail, and the intersection identity
would read `\sum_j \pm\,\mathrm{sign}(p)` instead of `k\,\mathrm{sign}(p)`). Part (b) for the special
`n`-form case and part (c) are both incarnations of the statement `\pi_*[\tilde X] = k\,[X]`, that a
`k`-fold cover has degree `k`.

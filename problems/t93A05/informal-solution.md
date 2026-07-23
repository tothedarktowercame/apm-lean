<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93A05: Maps into RP³, and the mod-2 vs. integral intersection dichotomy

## Why It's Hard

`\mathbb{RP}^3` is deceptively simple — it is an orientable closed `3`-manifold with universal cover `S^3` —
but the three parts probe quite different invariants and the punchline is a contrast between **mod-`2`** and
**integral** intersection theory that is easy to get backwards. Part (a) requires lifting to the universal
cover and knowing the higher homotopy of spheres. Parts (b) and (c) ask the *same* geometric question — does
a circle and a surface in `\mathbb{RP}^3` intersect essentially — but with mod-`2` versus oriented counts, and
the answers are opposite: **yes** mod `2`, **no** over `\mathbb Z`. The subtlety is that the class detecting
the intersection lives in `2`-torsion: it is visible in `H_2(\mathbb{RP}^3; \mathbb Z/2) = \mathbb Z/2` but
*invisible* in `H_2(\mathbb{RP}^3; \mathbb Z) = 0`. Tracking which coefficient ring "sees" the obstruction is
the heart of the problem.

## The Key Insight

`\mathbb{RP}^3` has universal cover `S^3` and integral homology `H_*(\mathbb{RP}^3;\mathbb Z) = (\mathbb Z,\ \mathbb Z/2,\ 0,\ \mathbb Z)`,
while `H_*(\mathbb{RP}^3;\mathbb Z/2) = (\mathbb Z/2,\mathbb Z/2,\mathbb Z/2,\mathbb Z/2)`.

- **(a)** A map `f : S^2 \to \mathbb{RP}^3` lifts to `\tilde f : S^2 \to S^3` (`S^2` is simply connected); and
  `S^3` is `2`-connected (`\pi_2(S^3) = 0`), so `\tilde f` — hence `f` — is null-homotopic. (Equivalently
  `\pi_2(\mathbb{RP}^3) = \pi_2(S^3) = 0`.)
- **(b)** Mod `2`, the intersection pairing `H_1(\cdot;\mathbb Z/2) \times H_2(\cdot;\mathbb Z/2) \to \mathbb Z/2`
  is nondegenerate (Poincaré duality), and both groups are `\mathbb Z/2`. It is realized by a projective line
  `\mathbb{RP}^1` and a projective plane `\mathbb{RP}^2`, which meet in one point: `\mathbb{RP}^1 \cdot \mathbb{RP}^2 = 1`.
- **(c)** Over `\mathbb Z`, `H_2(\mathbb{RP}^3;\mathbb Z) = 0`, so every closed oriented surface in `\mathbb{RP}^3`
  is null-homologous, forcing oriented intersection number `0` with any closed oriented curve. None exist.

## Complete Proof

### (a) Every `f : S^2 \to \mathbb{RP}^3` is null-homotopic

Let `p : S^3 \to \mathbb{RP}^3` be the universal (double) covering. Since `S^2` is simply connected,
`f_*\pi_1(S^2) = 1 \subseteq p_*\pi_1(S^3) = 1`, so by the lifting criterion `f` lifts to a smooth map
`\tilde f : S^2 \to S^3` with `p \circ \tilde f = f`.

Now `S^3` is `2`-connected: `\pi_2(S^3) = 0` (the homotopy groups `\pi_k(S^n)` vanish for `k < n`). Hence
`\tilde f : S^2 \to S^3` is homotopic to a constant map `c`. Composing with `p`,

$$f = p \circ \tilde f \simeq p \circ c = \text{constant}.$$

So every smooth `f : S^2 \to \mathbb{RP}^3` is homotopic to a constant map. ∎

### (b) A mod-2 essential intersection: `\mathbb{RP}^1` and `\mathbb{RP}^2`

Take `C = \mathbb{RP}^1 \subset \mathbb{RP}^3` (a projective line — a circle, compact `1`-manifold) and
`F = \mathbb{RP}^2 \subset \mathbb{RP}^3` (a projective plane — a compact surface). In `\mathbb{RP}^3` a line
not contained in a plane meets that plane in exactly **one** point (the projective version of "a line meets a
hyperplane in a point"); put them in general position so the single intersection is transverse. Hence the
**mod-2 intersection number** is

$$C \cdot F \equiv 1 \pmod 2 \ \ne 0.$$

Invariantly: `[C]` generates `H_1(\mathbb{RP}^3;\mathbb Z/2) = \mathbb Z/2` and `[F]` generates
`H_2(\mathbb{RP}^3;\mathbb Z/2) = \mathbb Z/2`, and the mod-`2` Poincaré duality pairing
`H_1 \times H_2 \to \mathbb Z/2` is nondegenerate, so the two generators pair to `1`. Such `C, F` exist. ∎

### (c) No oriented essential intersection

Suppose `C` is a closed oriented `1`-manifold and `F` a closed oriented surface in `\mathbb{RP}^3`. The
**oriented intersection number** `C \cdot F \in \mathbb Z` depends only on the homology classes
`[C] \in H_1(\mathbb{RP}^3;\mathbb Z)` and `[F] \in H_2(\mathbb{RP}^3;\mathbb Z)`, via the integral
intersection pairing. But by Poincaré duality (`\mathbb{RP}^3` is orientable) and the universal coefficient
theorem,

$$H_2(\mathbb{RP}^3;\mathbb Z) \cong H^1(\mathbb{RP}^3;\mathbb Z) \cong \operatorname{Hom}(H_1, \mathbb Z) \oplus \operatorname{Ext}(H_0, \mathbb Z) = \operatorname{Hom}(\mathbb Z/2, \mathbb Z) = 0.$$

So `[F] = 0` for **every** closed oriented surface `F` in `\mathbb{RP}^3` (it is null-homologous over
`\mathbb Z`). Therefore

$$C \cdot F = \langle [C], [F]\rangle = \langle [C], 0\rangle = 0$$

for any such `C, F`. No oriented submanifolds with nonzero oriented intersection number exist. ∎

**Remark.** Parts (b) and (c) are the same geometric configuration seen through two coefficient rings, and the
difference is `2`-torsion. The surface realizing the mod-`2` intersection is `\mathbb{RP}^2`, which is **not
orientable** — so it cannot even be used in (c) — and integrally it is null-homologous (`H_2(\mathbb{RP}^3;\mathbb Z) = 0`),
the class living only in `H_2(\cdot;\mathbb Z/2) = \mathbb Z/2`, the mod-`2` reduction of the torsion in `H_1`.
This is the general lesson: `\mathbb Z/2` intersection theory detects obstructions carried by torsion
(including by non-orientable submanifolds), which oriented/integral intersection theory, blind to torsion in
the relevant degree, registers as zero. Part (a) is independent and reflects that `\mathbb{RP}^3` has the same
`\pi_2` as its cover `S^3`, namely `0`.

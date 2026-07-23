<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91J05: Finite covers of the genus-3 surface are exactly the odd-genus surfaces ≥ 3

## Why It's Hard

The connected sum of three tori is the closed orientable surface `\Sigma_3` of genus `3`, and the question
"which spaces finitely cover it?" is open-ended — one must both *constrain* the possibilities (rule out
everything that cannot occur) and *realize* the survivors (show each really does occur as a cover). The
constraining direction needs two structural facts about covers of surfaces working together: a finite cover
of a closed surface is again a closed surface, it inherits **orientability**, and its **Euler
characteristic** is multiplied by the number of sheets. The realizing direction needs to know that surfaces
are "flexible" enough to admit a connected cover of *every* degree. The subtlety is that the Euler-
characteristic constraint forces the covering genus into a specific arithmetic progression (odd numbers),
and one must verify there are no further obstructions.

## The Key Insight

`\chi(\Sigma_3) = 2 - 2\cdot 3 = -4`. A connected `n`-sheeted cover `\widetilde\Sigma \to \Sigma_3` is:

- a **closed orientable** surface (covers of orientable manifolds are orientable), hence `\Sigma_g` for some `g`;
- with `\chi(\widetilde\Sigma) = n\,\chi(\Sigma_3) = -4n`.

Solving `2 - 2g = -4n` gives `g = 2n + 1`. So the only candidates are the **odd-genus** surfaces
`g = 3, 5, 7, \dots`. And each occurs: `\Sigma_3` admits a connected `n`-fold cover for every `n \ge 1` (e.g.
a cyclic cover from `H_1(\Sigma_3) \twoheadrightarrow \mathbb Z \twoheadrightarrow \mathbb Z/n`), realizing
genus `2n+1`. Hence the finite connected covers of `\Sigma_3` are *exactly* the closed orientable surfaces of
odd genus `\ge 3`.

## Complete Proof

The connected sum of three tori is `\Sigma_3`, the closed orientable surface of genus `3`, with
`\chi(\Sigma_3) = 2 - 2\cdot 3 = -4` and `\pi_1(\Sigma_3) = \langle a_1,b_1,a_2,b_2,a_3,b_3 \mid \prod_i [a_i,b_i]\rangle`,
`H_1(\Sigma_3) = \mathbb Z^6`.

### Necessity: a finite connected cover must be `\Sigma_{2n+1}`

Let `p : Y \to \Sigma_3` be a connected finite covering, with `n` sheets (`n \ge 1`, finite since `\Sigma_3` is
compact and `Y` connected).

1. **`Y` is a closed surface.** A covering space of a `2`-manifold is a `2`-manifold (covers are local
   homeomorphisms), and a finite cover of a compact space is compact; `Y` is also without boundary. So `Y`
   is a closed surface.
2. **`Y` is orientable.** `\Sigma_3` is orientable, and an orientation pulls back through the local
   homeomorphism `p` to an orientation of `Y`. Hence `Y = \Sigma_g` for some genus `g \ge 0`.
3. **Euler characteristic multiplies.** Lifting a CW (or triangulation) structure of `\Sigma_3` gives `Y` a CW
   structure with `n` times as many cells in each dimension, so `\chi(Y) = n\,\chi(\Sigma_3) = -4n`.

Combining `\chi(\Sigma_g) = 2 - 2g` with `\chi(Y) = -4n`:

$$2 - 2g = -4n \ \Longrightarrow\ g = 2n + 1.$$

So `g` is odd and `g \ge 3` (as `n \ge 1`). The only possible connected covers are `\Sigma_{2n+1}`,
`n = 1, 2, 3, \dots` — the orientable surfaces of odd genus `\ge 3`.

### Sufficiency: every `\Sigma_{2n+1}` is realized

Fix `n \ge 1`. The abelianization gives a surjection `\pi_1(\Sigma_3) \twoheadrightarrow H_1(\Sigma_3) = \mathbb Z^6 \twoheadrightarrow \mathbb Z`
(project to a coordinate), and `\mathbb Z \twoheadrightarrow \mathbb Z/n`. Composing yields a surjection
`\varphi : \pi_1(\Sigma_3) \to \mathbb Z/n`; its kernel is an index-`n` subgroup, corresponding to a **connected
`n`-fold covering** `Y_n \to \Sigma_3`. By the necessity computation, `Y_n` is the closed orientable surface of
genus `g = 2n + 1`. Thus every odd genus `\ge 3` is attained (taking `n = (g-1)/2`).

### Conclusion

$$\boxed{\ \text{The finite connected covers of } \#^3 T^2 = \Sigma_3 \text{ are exactly the closed orientable surfaces of odd genus } g \ge 3,\ \text{i.e. } \Sigma_{2n+1}\ (n \ge 1).\ }$$

(Allowing disconnected covers, a finite cover is a disjoint union of such connected covers — including copies
of `\Sigma_3` itself — so any finite disjoint union of odd-genus orientable surfaces of genus `\ge 3`; the
total Euler characteristic is always a negative multiple of `4`.) $\qquad\blacksquare$

**Remark.** Two invariants do all the constraining: **orientability is inherited** by covers (ruling out all
non-orientable surfaces) and **Euler characteristic multiplies by the degree** (forcing `\chi = -4n`, hence
odd genus). What is *not* an obstruction is realizability — closed surfaces of genus `\ge 1` have connected
covers of every degree, so the arithmetic candidates `g = 2n+1` are all genuinely achieved. Even genus,
genus `< 3`, and non-orientable surfaces never appear: e.g. `\Sigma_4` would need `\chi = -6 = -4n`, forcing
`n = 3/2 \notin \mathbb Z`. The answer is the clean statement that covering `\#^3 T^2` is possible exactly for
the orientable surfaces whose Euler characteristic is a negative multiple of `4` (equivalently odd genus
`\ge 3`).

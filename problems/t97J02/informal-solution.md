<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J02: 5-fold and 6-fold covers of the genus-4 non-orientable surface

## Why It's Hard

`X = \mathbb{RP}^2 \# \mathbb{RP}^2 \# \mathbb{RP}^2 \# \mathbb{RP}^2 = N_4` is the non-orientable surface of
genus `4`, with `\chi(X) = 2 - 4 = -2`. The problem has the "note" baked in: a list is not enough — one must
both **pin the candidate list** and then, for each candidate, either **construct a genuine cover** or **prove
it cannot occur**. Two facts do all the work, and the difficulty is in using them together. First, Euler
characteristic is multiplicative under coverings, `\chi(M) = n\,\chi(X) = -2n`, which together with the
classification of surfaces leaves *exactly one orientable and one non-orientable candidate per degree*. Second
— the subtle one — an **orientable** surface can only cover a **non-orientable** one in **even** degree,
because the cover must factor through the orientation double cover. This parity obstruction is exactly what
distinguishes the odd case `n=5` (where the orientable candidate is *killed*) from the even case `n=6` (where
it survives). Getting "no other covers exist" right means invoking this obstruction, not just Euler
characteristics.

## The Key Insight

Two principles pin everything down.

1. **Euler characteristic multiplies:** an `n`-fold cover `M \to X` has `\chi(M) = n\,\chi(X) = -2n`. By the
   classification of compact surfaces, the homeomorphism type of `M` is determined by `(\text{orientability},
   \chi)`, so for each `n` there is **at most one** orientable type (`\Sigma_g`, `2 - 2g = -2n \Rightarrow g = n+1`)
   and **at most one** non-orientable type (`N_k`, `2 - k = -2n \Rightarrow k = 2n+2`).

2. **Parity obstruction:** if `M` is orientable and connected and covers the non-orientable `X`, the covering
   factors through the orientation double cover `\widetilde X \to X`, so its degree is **even**.

For `n = 5` (odd): the orientable candidate `\Sigma_6` is **excluded** by (2); only the non-orientable
`N_{12}` can occur — and it does. For `n = 6` (even): both `\Sigma_7` and `N_{14}` survive, and both are
realized. Concretely, a single cyclic-cover construction yields the non-orientable covers `N_{12}` and `N_{14}`,
and a tower `\Sigma_7 \to \Sigma_3 \to N_4` yields the orientable `6`-fold cover.

$$\boxed{\ \text{5-fold covers of } X:\ \text{only } N_{12}. \qquad \text{6-fold covers of } X:\ \Sigma_7 \text{ and } N_{14}.\ }$$

## Complete Proof

`X = N_4`, closed connected non-orientable, `\chi(X) = -2`. Let `p : M \to X` be a connected `n`-fold covering.
A finite cover of a closed surface is a closed surface (compact, since a finite cover of a compact space is
compact; boundaryless, since `p` is a local homeomorphism). So `M` is one of the surfaces in the classification
list, determined by orientability and `\chi`.

### Step 0 — The candidate list (`\chi` is multiplicative)

A degree-`n` covering satisfies `\chi(M) = n\,\chi(X) = -2n`. By the classification of closed surfaces, `M` is
either orientable `\Sigma_g` with `\chi = 2 - 2g`, or non-orientable `N_k` with `\chi = 2 - k`. Solving:

| degree `n` | `\chi(M) = -2n` | orientable candidate | non-orientable candidate |
|---|---|---|---|
| `5` | `-10` | `\Sigma_6` `\;(g = 6)` | `N_{12}` `\;(k = 12)` |
| `6` | `-12` | `\Sigma_7` `\;(g = 7)` | `N_{14}` `\;(k = 14)` |

These are the **only** possible homeomorphism types; everything below decides which occur.

### Step 1 — The parity obstruction (orientable `\Rightarrow` even degree)

**Lemma.** If `M` is connected and orientable and `p : M \to X` is a covering of the non-orientable `X`, then
`\deg p` is even.

*Proof.* `X` non-orientable means its first Stiefel–Whitney / orientation character `w_1 : \pi_1(X) \to \mathbb Z/2`
is a **surjection**; its kernel `K = \ker w_1` has index `2` and corresponds to the connected **orientation
double cover** `q : \widetilde X \to X`. A connected cover `M \to X` corresponds to the subgroup
`H = p_\#\pi_1(M) \le \pi_1(X)`, and `M` is orientable **iff** the orientation character pulls back trivially
to `M`, i.e. iff `H \subseteq K`. When `H \subseteq K`,

$$\deg p = [\pi_1(X) : H] = [\pi_1(X) : K]\,[K : H] = 2\,[K : H],$$

which is even. `\square`

Since `5` is odd, **no orientable surface is a `5`-fold cover of `X`.** In particular `\Sigma_6` does **not**
occur. (This is the crux the "note" is testing.)

### Step 2 — Construction of the non-orientable covers `N_{12}` and `N_{14}`

`\pi_1(X) = \langle a_1, a_2, a_3, a_4 \mid a_1^2 a_2^2 a_3^2 a_4^2 \rangle`. Define a homomorphism to the
integers by

$$\varphi : \pi_1(X) \to \mathbb Z, \qquad a_1 \mapsto 1,\ a_2 \mapsto -1,\ a_3, a_4 \mapsto 0,$$

which respects the relation (`2(1 - 1 + 0 + 0) = 0`) and is **surjective**. For `n \in \{5, 6\}` compose with
reduction `\mathbb Z \twoheadrightarrow \mathbb Z/n` to get a surjection `\varphi_n : \pi_1(X) \to \mathbb Z/n`.
Surjectivity makes the associated cyclic cover `M_n \to X` **connected** of degree `n`, so `\chi(M_n) = -2n`.

`M_n` is **non-orientable**: the orientation character sends every crosscap generator to the nontrivial
element, `w_1(a_i) = 1` for all `i` (a loop through a crosscap reverses orientation; check on the relation:
`w_1(a_1^2a_2^2a_3^2a_4^2) = 8 \equiv 0`). The subgroup of `M_n` is `H = \ker \varphi_n`, and `a_3 \in H`
(since `\varphi_n(a_3) = 0`) while `w_1(a_3) = 1 \ne 0`. So `w_1|_H \ne 0`, i.e. `H \not\subseteq \ker w_1`,
so by the criterion in Step 1, `M_n` is non-orientable. Therefore:

- `n = 5`: `M_5` is a connected **non-orientable** `5`-fold cover with `\chi = -10`, hence `M_5 \cong N_{12}`.
- `n = 6`: `M_6` is a connected **non-orientable** `6`-fold cover with `\chi = -12`, hence `M_6 \cong N_{14}`.

So `N_{12}` occurs (degree `5`) and `N_{14}` occurs (degree `6`).

### Step 3 — Construction of the orientable `6`-fold cover `\Sigma_7`

The orientation double cover of `X = N_4` is the orientable surface `\widetilde X` with
`\chi(\widetilde X) = 2\,\chi(X) = -4`, i.e. `\widetilde X \cong \Sigma_3`, giving a degree-`2` cover
`\Sigma_3 \to N_4`. Now `\Sigma_3` (genus `\ge 1`) has `\pi_1(\Sigma_3)` surjecting onto `\mathbb Z` (abelianize
and project to one `\mathbb Z`-factor), and composing with `\mathbb Z \twoheadrightarrow \mathbb Z/3` gives a
connected `3`-fold cyclic cover `\Sigma' \to \Sigma_3` with `\chi(\Sigma') = 3 \cdot (-4) = -12`. A connected
cover of an orientable surface is orientable, so `\Sigma' \cong \Sigma_7`. Composing,

$$\Sigma_7 \xrightarrow{\ 3\ } \Sigma_3 \xrightarrow{\ 2\ } N_4$$

is a degree-`6` **orientable** cover. So `\Sigma_7` occurs (degree `6`). (As Step 1 demands, the degree `6` is
even — consistent.)

### Conclusion

Combining Steps 0–3:

- **`5`-fold covers of `X`.** Candidates `\Sigma_6, N_{12}`. `\Sigma_6` is excluded by the parity obstruction
  (Step 1); `N_{12}` is realized (Step 2). **The only `5`-fold cover is `N_{12}`.**
- **`6`-fold covers of `X`.** Candidates `\Sigma_7, N_{14}`. `\Sigma_7` is realized by the tower (Step 3);
  `N_{14}` is realized by the cyclic cover (Step 2). **The `6`-fold covers are exactly `\Sigma_7` and `N_{14}`.**

`\blacksquare`

**Remark.** The whole problem is the interplay of one equality and one parity. `\chi(M) = n\,\chi(X)` together
with the surface classification reduces the answer to *at most* two homeomorphism types per degree (one
orientable, one non-orientable). The orientation-character obstruction — orientable covers of a non-orientable
base have even degree — is what makes the odd degree `5` lose its orientable candidate while the even degree `6`
keeps it. Existence in the surviving cases is never in doubt for `\chi < 0`: surface groups are rich enough
(they surject onto `\mathbb Z`) that connected cyclic covers of every degree exist, and one only has to read
off orientability from where the chosen subgroup sits relative to `\ker w_1`.

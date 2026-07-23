<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t98A04: The Hopf fibration — submersion, circle fibers, and no section

## Why It's Hard

This is the **Hopf fibration** `\pi : S^3 \to S^2 = \mathbb{CP}^1`, `(z_1, z_2) \mapsto [z_1 : z_2]`, dressed as
three short questions whose difficulty is in *not* hand-waving. (a) "Submersion" is a statement about the
*differential* of a map between spheres of different dimension (`3 \to 2`); the clean argument is that `\pi` is
the restriction to `S^3` of the linear projection `\mathbb C^2 \setminus \{0\} \to \mathbb{CP}^1`, and one must
check that restricting to the sphere keeps `d\pi` surjective — the kernel must *shrink* from the `2`-real-
dimensional complex line (the fiber direction upstairs) down to a `1`-dimensional "vertical" circle direction.
(b) The fibers are circles, but seeing that they are exactly the orbits of the `U(1)`-action takes the
observation `\pi(z) = \pi(w) \iff w = e^{i\theta}z`. (c) The punchline — and where the problem has a **typo** —
asks whether `\pi` has a continuous section. As printed it says `\iota : S^2 \to S^2`, but `\pi \circ \iota = \mathrm{id}_{S^2}`
forces `\iota : S^2 \to S^3` (the domain of `\pi`). The answer is **no**, for a purely topological reason: a
section would make the identity of `H_2(S^2) = \mathbb Z` factor through `H_2(S^3) = 0`, which is impossible.

## The Key Insight

`\pi` extends to the holomorphic submersion `\Pi : \mathbb C^2 \setminus \{0\} \to \mathbb{CP}^1`, whose fibers
are the complex lines `\mathbb C \cdot p`. Restricting to `S^3`:

- **(a)** at `p \in S^3`, `\ker d\Pi_p = \mathbb C\cdot p`, and intersecting with `T_pS^3 = \{v : \operatorname{Re}\langle v, p\rangle = 0\}`
  leaves only `i\mathbb R \cdot p` — a single real dimension. So `\operatorname{rank} d\pi_p = 3 - 1 = 2 = \dim S^2`:
  a submersion.
- **(b)** `\pi(z) = \pi(w) \iff w = e^{i\theta} z`, so the fibers are exactly the orbits of the free `U(1)`-action
  `e^{i\theta}\cdot(z_1, z_2) = (e^{i\theta}z_1, e^{i\theta}z_2)`. Each is a great **circle** `S^1`; e.g.
  `\pi^{-1}([1,0]) = \{(e^{i\theta}, 0)\} \cong S^1`. This is the bundle `S^1 \hookrightarrow S^3 \to S^2`.
- **(c)** No continuous `\iota : S^2 \to S^3` with `\pi\circ\iota = \mathrm{id}` exists: applying `H_2`,
  `\mathrm{id} = \pi_*\iota_*` would factor `\mathrm{id}_{\mathbb Z}` through `H_2(S^3) = 0`.

## Complete Proof

Use the Hermitian inner product `\langle v, p\rangle = v_1\bar p_1 + v_2 \bar p_2` on `\mathbb C^2`; then
`S^3 = \{p : |p| = 1\}` and `T_pS^3 = \{v \in \mathbb C^2 : \operatorname{Re}\langle v, p\rangle = 0\}` (real
codimension `1`).

### (a) `\pi` is a submersion

Cover `\mathbb{CP}^1` by the two affine charts. On `U_0 = \{[z_1 : z_2] : z_1 \ne 0\}`, the coordinate is
`w = z_2/z_1`, so on `S^3 \cap \{z_1 \ne 0\}` the map `\pi` is `F(z_1, z_2) = z_2/z_1 \in \mathbb C \cong \mathbb R^2`.
As a map on the open set `\{z_1 \ne 0\} \subseteq \mathbb C^2`, `F` is holomorphic with differential

$$dF_p = \frac{z_1\,dz_2 - z_2\,dz_1}{z_1^2},$$

a nonzero `\mathbb C`-linear functional, hence surjective onto `\mathbb C` with `\ker dF_p = \mathbb C\cdot p`
(the complex line on which `F` is constant: `F(\lambda z_1, \lambda z_2) = F(z_1, z_2)`).

Now restrict to `T_pS^3`. The kernel of `d\pi_p = dF_p\big|_{T_pS^3}` is `T_pS^3 \cap \mathbb C\cdot p`. A vector
`\lambda p \in \mathbb C\cdot p` lies in `T_pS^3` iff `\operatorname{Re}\langle \lambda p, p\rangle = \operatorname{Re}(\lambda |p|^2) = \operatorname{Re}\lambda = 0`,
i.e. `\lambda \in i\mathbb R`. Hence

$$\ker d\pi_p = i\mathbb R \cdot p \quad (\dim_{\mathbb R} = 1),$$

the **vertical/Hopf direction**. Therefore `\operatorname{rank} d\pi_p = \dim T_pS^3 - 1 = 3 - 1 = 2 = \dim S^2`,
so `d\pi_p` is surjective. Every `p \in S^3` has `z_1 \ne 0` or `z_2 \ne 0`; the chart `U_1` (`w' = z_1/z_2`)
handles the latter identically. So `\pi` is a submersion everywhere. `\square`

### (b) The fibers

For `p = (z_1, z_2), q = (w_1, w_2) \in S^3`: `\pi(p) = \pi(q)` means `[w_1 : w_2] = [z_1 : z_2]`, i.e.
`(w_1, w_2) = \lambda(z_1, z_2)` for some `\lambda \in \mathbb C^*`; the norm constraint `|q| = |p| = 1` forces
`|\lambda| = 1`, so `\lambda = e^{i\theta}`. Thus

$$\pi(p) = \pi(q) \iff q = e^{i\theta} p \ \text{ for some } \theta,$$

and the fibers are precisely the orbits of the free `U(1) = S^1` action `e^{i\theta}\cdot(z_1, z_2) = (e^{i\theta}z_1, e^{i\theta}z_2)`.
In particular

$$\boxed{\ \pi^{-1}([1,0]) = \{(z_1, z_2) \in S^3 : z_2 = 0\} = \{(e^{i\theta}, 0)\} \cong S^1.\ }$$

For general `p = [a : b]`, choose the unit representative `(a, b)/\sqrt{|a|^2 + |b|^2}`; then

$$\pi^{-1}(p) = \{ e^{i\theta}(a, b)/\sqrt{|a|^2 + |b|^2} : \theta \in [0, 2\pi)\} \cong S^1,$$

a great circle of `S^3`. **Every fiber is a circle**, and `\pi` is the Hopf fibration `S^1 \hookrightarrow S^3 \xrightarrow{\pi} S^2`
(distinct fibers are pairwise *linked* — the Hopf link — though that is not needed here).

### (c) No continuous section exists

*(The problem statement's `\iota : S^2 \to S^2` is a typo: since `\pi : S^3 \to S^2`, the equation
`\pi\circ\iota = \mathrm{id}_{S^2}` requires `\iota : S^2 \to S^3`. We answer that.)*

Suppose a continuous `\iota : S^2 \to S^3` satisfied `\pi\circ\iota = \mathrm{id}_{S^2}`. Apply the (covariant,
functorial) singular homology functor `H_2(-; \mathbb Z)`:

$$\mathrm{id}_{H_2(S^2)} = (\pi\circ\iota)_* = \pi_* \circ \iota_* : H_2(S^2) \to H_2(S^3) \to H_2(S^2).$$

But `H_2(S^2) = \mathbb Z` while `H_2(S^3) = 0`. The composite thus factors as
`\mathbb Z \xrightarrow{\iota_*} 0 \xrightarrow{\pi_*} \mathbb Z`, so it is the **zero** homomorphism — yet it is
supposed to be the **identity** of `\mathbb Z`. Since `\mathrm{id}_{\mathbb Z} \ne 0`, this is a contradiction.

$$\boxed{\ \text{No continuous } \iota : S^2 \to S^3 \text{ with } \pi\circ\iota = \mathrm{id}_{S^2} \text{ exists.}\ } \qquad \blacksquare$$

**Remark.** Continuity is all that is used — the obstruction is topological, not differential. Equivalently, on
`\pi_2`: a section would split `\pi_* : \pi_2(S^3) = 0 \to \pi_2(S^2) = \mathbb Z`, impossible for the same
reason; indeed the Hopf map *generates* `\pi_3(S^2) = \mathbb Z` and is the prototype of a nontrivial bundle. A
section would force the principal `S^1`-bundle to be trivial, `S^3 \cong S^2 \times S^1` — false already on
homology (`H_1(S^3) = 0 \ne \mathbb Z = H_1(S^2\times S^1)`). So `\pi` is a submersion with circle fibers that
nonetheless admits no continuous right inverse: local product structure (it *is* a fiber bundle) does not imply
a global section.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93J03: The Klein bottle group, and why a subspace mapping into ⟨a⟩ is planar

## Why It's Hard

Part (a) is a standard but sign-sensitive `\pi_1` computation: the Klein bottle's defining polygon word
`abab^{-1}` must be massaged into the conjugation relation `b^{-1}ab = a^{-1}`, and one slip in the rewriting
flips the group. Part (b) is the conceptually rich half. The Klein bottle is **not** planar (it does not embed
in `\mathbb R^2`), yet the claim is that a subspace `X` whose loops all map into the cyclic subgroup
`A = \langle a\rangle` *does* embed in the plane. The leap is to recognize that "`\operatorname{im} i_* \subseteq A`"
is precisely the **lifting criterion** for the covering space corresponding to `A`, so `X` lifts into that
cover — and the cover happens to be a *cylinder*, which is planar. The difficulty is identifying which cover
`A` names (an infinite cyclic cover unwinding the base circle) and seeing that it is `S^1 \times \mathbb R \cong \mathbb R^2 \setminus \{0\}`,
hence sits in `\mathbb R^2`. The hypotheses (path-connected, locally path-connected) are exactly what the
lifting theorem requires.

## The Key Insight

`\pi_1(K) = \langle a, b \mid abab^{-1}\rangle`, and `abab^{-1} = 1` rearranges to `b^{-1}ab = a^{-1}` — "`b`
conjugates `a` to its inverse."

For (b): `A = \langle a\rangle` is normal (`b^{-1}ab = a^{-1} \in A`) with `\pi_1(K)/A = \langle b\rangle \cong \mathbb Z`,
so `A` corresponds to an **infinite cyclic covering** `p : K_A \to K` with `p_*\pi_1(K_A) = A`. Geometrically
`K` is the mapping torus of the reflection of `S^1`, and the `A`-cover unwinds the mapping-torus (base)
direction, giving

$$K_A \cong S^1 \times \mathbb R,$$

an open cylinder. Since `\operatorname{im} i_* \subseteq A = p_*\pi_1(K_A)`, the inclusion `i : X \hookrightarrow K`
**lifts** to an embedding `\tilde i : X \hookrightarrow K_A = S^1 \times \mathbb R`. And `S^1 \times \mathbb R \cong \mathbb R^2 \setminus \{0\} \subset \mathbb R^2`,
so `X` embeds in the plane.

## Complete Proof

### (a) `\pi_1(K) \cong \langle a, b \mid b^{-1}ab = a^{-1}\rangle`

Give `K` its standard CW structure: one `0`-cell `v`, two `1`-cells `a, b`, and one `2`-cell attached to the
`1`-skeleton along the boundary word `abab^{-1}` (the Klein-bottle polygon: a square with horizontal edges
identified directly — `a` — and vertical edges identified with a flip — `b`). The `1`-skeleton is a wedge of
two circles, with `\pi_1 = F(a, b)` free of rank `2`. By **van Kampen** (attaching a `2`-cell adds the relation
spelled by its attaching word),

$$\pi_1(K) = \langle a, b \mid abab^{-1} = 1\rangle.$$

Rewrite the relator: `abab^{-1} = 1 \Rightarrow aba = b \Rightarrow ba = a^{-1}b` (multiply by `a^{-1}` on the
left) `\Rightarrow a = b^{-1}a^{-1}b` (multiply by `b^{-1}` on the left) `\Rightarrow b^{-1}ab = a^{-1}` (invert).
Hence

$$\boxed{\ \pi_1(K) \cong \langle a, b \mid b^{-1}ab = a^{-1}\rangle.\ }$$

### (b) `X` embeds in `\mathbb R^2`

Let `A = \langle a\rangle = \{a^n : n \in \mathbb Z\} \le \pi_1(K)`; `a` has infinite order, so `A \cong \mathbb Z`.

**Step 1 — `A` names a covering space.** `A` is normal in `\pi_1(K)` (`b^{-1}ab = a^{-1} \in A`, and `A` is
closed under conjugation), with quotient `\pi_1(K)/A = \langle b \rangle \cong \mathbb Z`. By covering-space
theory (`K` is a nice space) there is a connected covering `p : K_A \to K` with `p_*\pi_1(K_A) = A`, of infinite
index `[\pi_1(K) : A] = \infty`.

**Step 2 — Identify the cover as a cylinder.** Realize `K` as the mapping torus of the reflection
`\varphi : S^1 \to S^1`, `\varphi(z) = \bar z`:

$$K = (S^1 \times \mathbb R)/\big((z, t) \sim (\bar z, t+1)\big),$$

where the fiber circle `S^1 \times \{t\}` represents `a` and the `\mathbb R`-direction (mod the identification)
represents `b`. The quotient map

$$p : S^1 \times \mathbb R \to K$$

is a covering with deck group `\mathbb Z = \langle b\rangle` and `p_*\pi_1(S^1 \times \mathbb R) = \pi_1(S^1) = \langle a\rangle = A`.
By uniqueness of the cover associated to a subgroup, `K_A \cong S^1 \times \mathbb R`, an open cylinder.

**Step 3 — Lift the inclusion.** The inclusion `i : X \hookrightarrow K` satisfies, by hypothesis,
`\operatorname{im} i_* = i_*\pi_1(X) \subseteq A = p_*\pi_1(K_A)`. Since `X` is path-connected and locally
path-connected, the **lifting criterion** gives a continuous lift `\tilde i : X \to K_A` with `p \circ \tilde i = i`.

`\tilde i` is an **embedding**: it is injective (if `\tilde i(x) = \tilde i(x')` then `i(x) = p\tilde i(x) = p\tilde i(x') = i(x')`,
and `i` is injective, so `x = x'`); and since `i = p \circ \tilde i` is an embedding with `p` continuous,
`\tilde i^{-1} = (p \circ \tilde i)^{-1} \circ p|_{\tilde i(X)}` is continuous, so `\tilde i` is a homeomorphism
onto its image. Thus `X` embeds in `K_A = S^1 \times \mathbb R`.

**Step 4 — The cylinder is planar.** The open cylinder embeds in the plane:

$$S^1 \times \mathbb R \xrightarrow{\ \cong\ } \mathbb R^2 \setminus \{0\}, \qquad (e^{i\theta}, t) \mapsto e^{t}(\cos\theta, \sin\theta),$$

a homeomorphism onto the punctured plane. Composing, `X \hookrightarrow K_A \cong \mathbb R^2 \setminus \{0\} \subset \mathbb R^2`.

$$\boxed{\ X \text{ embeds in } \mathbb R^2.\ }\qquad\blacksquare$$

**Remark.** The Klein bottle is itself non-planar, so the result is genuinely about the *subspace condition*.
The hypothesis `\operatorname{im} i_* \subseteq A` is exactly the lifting criterion for the `A`-cover, and the
whole proof is "lift, then observe the cover is a cylinder." The cylinder appears because `A = \langle a\rangle`
is the **fiber** subgroup of the `S^1`-mapping-torus structure: passing to the `A`-cover unwinds the base
direction (`b`) completely, untwisting the Klein bottle into the orientable product `S^1 \times \mathbb R`,
which is planar. Any `X` that only "sees" the fiber loop `a` therefore lives on a planar cover and is itself
planar.

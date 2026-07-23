<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A09: Nowhere-zero and single-zero vector fields, decided by Euler characteristic

## Why It's Hard

All three parts are governed by one theorem — **Poincaré–Hopf**: on a closed manifold `M`, the signed sum
of the indices of the zeros of any vector field with isolated zeros equals the Euler characteristic `\chi(M)`.
The difficulty is that this single principle gives *opposite* answers depending on the manifold, and the
problem is deliberately set up to test whether one knows the difference. Parts (a) and (b) ask the *same*
question ("no zeros") for `S^2` and `S^3` — the repetition flagged as "not a typo" — and the answers differ
because `\chi(S^2) = 2` while `\chi(S^3) = 0`: even and odd spheres behave oppositely. Part (c) is subtler:
`\chi(T^2) = 0` *permits* a vector field with zeros summing to index `0`, so one zero is allowed **only if it
is degenerate of index `0`**, and one must actually build such a field — a single zero that "doesn't wind."

## The Key Insight

`\sum_{\text{zeros}} \operatorname{ind} = \chi(M)`.

- **(a)** `\chi(S^2) = 2 \ne 0`, so a nowhere-zero field (empty index sum `= 0`) is impossible. **None exists**
  (the hairy ball theorem).
- **(b)** `\chi(S^3) = 0` (odd-dimensional sphere), so there is no index obstruction; and `S^3` is
  *parallelizable* (unit quaternions / `S^3 \subset \mathbb C^2` with `v(z) = iz`), giving an explicit
  nowhere-zero field. **Exists.**
- **(c)** `\chi(T^2) = 0`, so a single zero is allowed provided its index is `0`. A field of *constant
  direction* whose magnitude vanishes at exactly one point has one zero, of index `0`. **Exists.**

## Complete Proof

We use the **Poincaré–Hopf index theorem**: for a smooth vector field with isolated zeros on a closed
manifold `M`, `\sum_p \operatorname{ind}_p(v) = \chi(M)`. In particular a nowhere-zero field (no zeros) forces
`\chi(M) = 0`.

### (a) `S^2`: no nowhere-zero field — does **not** exist

`\chi(S^2) = 2 \ne 0`. If `v` were a smooth vector field on `S^2` with no zeros, the index sum would be the
empty sum `0`, contradicting `\sum \operatorname{ind} = \chi(S^2) = 2`. Hence every smooth vector field on
`S^2` has a zero; a nowhere-zero one **does not exist**. (This is the hairy ball theorem.)

### (b) `S^3`: a nowhere-zero field **exists**

`\chi(S^3) = 0`, so there is no Poincaré–Hopf obstruction. Construct one explicitly. View
`S^3 = \{z = (z_1, z_2) \in \mathbb C^2 : |z_1|^2 + |z_2|^2 = 1\}` and define

$$v(z_1, z_2) = (i z_1,\ i z_2).$$

This is tangent to `S^3`: with the real inner product, `\langle v(z), z\rangle = \operatorname{Re}\langle iz, z\rangle = 0`,
so `v(z) \perp z` (perpendicular to the radial direction). And `|v(z)| = |z| = 1 \ne 0`, so `v` is **nowhere
zero**. (In real coordinates `x = (x_1,x_2,x_3,x_4) \in S^3 \subset \mathbb R^4`, this is
`v(x) = (-x_2, x_1, -x_4, x_3)`, manifestly smooth, unit length, and orthogonal to `x`.) So a smooth
nowhere-zero vector field on `S^3` **exists** — indeed `S^3` is parallelizable.

### (c) `T^2`: a field with exactly one zero **exists**

`\chi(T^2) = 0`, so Poincaré–Hopf requires the indices to sum to `0`; a single zero must therefore have index
`0`. Build such a field on the flat torus `T^2 = \mathbb R^2/\mathbb Z^2`. Let

$$g(x,y) = 2 - \cos(2\pi x) - \cos(2\pi y) \ge 0, \qquad v(x,y) = \big(g(x,y),\ 0\big).$$

This is a smooth, doubly-periodic (hence well-defined on `T^2`) vector field.

- **Exactly one zero.** `v = 0 \iff g = 0 \iff \cos(2\pi x) = \cos(2\pi y) = 1 \iff (x,y) \in \mathbb Z^2`,
  which on `T^2` is the single point `p_0 = (0,0)`. (Near `p_0`, `g \approx 2\pi^2(x^2 + y^2)`, vanishing to
  second order.)

- **Index `0`.** Where `v \ne 0`, `v = (g, 0)` with `g > 0`, so `v` points in the constant direction `(1,0)`.
  On a small circle around `p_0` the normalized field `v/|v| \equiv (1,0)` is **constant**, so its degree
  (the index) is `0`.

Thus `v` has **exactly one zero**, of index `0`, consistent with `\sum \operatorname{ind} = 0 = \chi(T^2)`.
Such a field **exists**. ∎

**Remark.** The "apparent typo" — asking for no zeros on both `S^2` and `S^3` — is the point of the problem:
even-dimensional spheres have `\chi = 2` (so the hairy ball theorem forbids nowhere-zero fields), while
odd-dimensional spheres have `\chi = 0` (and `S^1, S^3, S^7` are even parallelizable). For (c), the constraint
`\chi(T^2) = 0` cannot prevent a *single* zero — it only forces its index to be `0`, and an index-`0` isolated
zero is exactly a "non-winding" zero, realized by a field of constant direction that merely *dips to zero* in
magnitude at one spot (the merge of a `+1` and a `-1` zero). All three answers are read off `\chi`: `2` blocks
(a), `0` permits (b) and (c).

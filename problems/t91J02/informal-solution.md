<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91J02: The torus is not the sphere — a fundamental group obstruction

## Why It's Hard

Proving two spaces are *not* homeomorphic cannot be done by inspecting all possible maps; one must exhibit a
**topological invariant** — a quantity preserved by homeomorphisms — that the two spaces fail to share. Both
`S^1 \times S^1` (the torus) and `S^2` are compact connected `2`-manifolds, so crude invariants like
dimension, compactness, and connectedness do *not* distinguish them. The difficulty is choosing an invariant
sensitive enough to tell them apart, and the cleanest is an *algebraic-topological* one: the fundamental
group, which detects that the torus has loops that cannot be contracted while the sphere does not.

## The Key Insight

The fundamental group is a homeomorphism (indeed homotopy) invariant, and the two spaces have different ones:

$$\pi_1(S^1 \times S^1) = \pi_1(S^1) \times \pi_1(S^1) = \mathbb Z \times \mathbb Z = \mathbb Z^2 \ne 1,
\qquad \pi_1(S^2) = 1.$$

A homeomorphism would force an isomorphism `\mathbb Z^2 \cong 1`, which is false (the torus has a
non-contractible loop, the sphere has none). Hence `S^1 \times S^1 \not\cong S^2`.

## Complete Proof

**The invariant.** A homeomorphism `h : X \to Y` induces an isomorphism `h_* : \pi_1(X, x_0) \to \pi_1(Y, h(x_0))`
of fundamental groups (it has a continuous inverse, and `h_* \circ (h^{-1})_* = \mathrm{id}`,
`(h^{-1})_* \circ h_* = \mathrm{id}`). So if `X \cong Y` then `\pi_1(X) \cong \pi_1(Y)`. We compute both groups
and show they are not isomorphic.

**`\pi_1(S^1 \times S^1) = \mathbb Z^2`.** The fundamental group of a product is the product of the
fundamental groups, `\pi_1(A \times B) \cong \pi_1(A) \times \pi_1(B)`. Since `\pi_1(S^1) \cong \mathbb Z`,

$$\pi_1(S^1 \times S^1) \cong \mathbb Z \times \mathbb Z = \mathbb Z^2,$$

a nontrivial group (e.g. the meridian loop `S^1 \times \{pt\}` represents the generator `(1,0) \ne 0`, so it
is not null-homotopic).

**`\pi_1(S^2) = 1`.** The `2`-sphere is simply connected. Concretely, any loop `\gamma` in `S^2` based at a
point may be homotoped (by smooth/simplicial approximation) to miss some point `q \in S^2`; then `\gamma`
lies in `S^2 \setminus \{q\} \cong \mathbb R^2`, which is contractible, so `\gamma` is null-homotopic. Hence
every loop contracts and `\pi_1(S^2) = 1`.

**Conclusion.** If `S^1 \times S^1` were homeomorphic to `S^2`, their fundamental groups would be isomorphic.
But `\mathbb Z^2 \not\cong 1` (the trivial group has one element; `\mathbb Z^2` has infinitely many).
Therefore

$$\boxed{\ S^1 \times S^1 \text{ is not homeomorphic to } S^2.\ }\qquad\blacksquare$$

**Remark.** Any homeomorphism invariant that differs would do. Two further quick certificates: the **Euler
characteristic**, `\chi(S^1\times S^1) = 0 \ne 2 = \chi(S^2)`; and the **first homology**,
`H_1(S^1\times S^1) = \mathbb Z^2 \ne 0 = H_1(S^2)`. Each reflects the same geometric fact — the torus has a
"hole" (a non-bounding, non-contractible loop) that the sphere lacks. The fundamental group is the most
elementary to invoke here because the product formula computes it instantly and the sphere is visibly simply
connected.

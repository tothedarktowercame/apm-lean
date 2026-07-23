<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93A03: A connected sum of two S¹×S² is not simply connected

## Why It's Hard

To prove a space is *not* simply connected one must produce a nontrivial element of `\pi_1` — but `\pi_1` of a
connected sum is not something one reads off by staring at the space. The work is twofold: compute the
fundamental group of each summand `S^1 \times S^2` (where the temptation is to think the `S^2` factor
contributes loops — it does not, being simply connected), and then know how `\pi_1` behaves under connected
sum. The latter is the key structural fact: for manifolds of dimension `\ge 3`, connected sum corresponds to
the **free product** of fundamental groups, because the sphere along which the pieces are glued is simply
connected and removing a ball changes nothing in `\pi_1`. Assembling these gives a free group, which is
visibly nontrivial.

## The Key Insight

`\pi_1(S^1 \times S^2) = \pi_1(S^1) \times \pi_1(S^2) = \mathbb Z \times 1 = \mathbb Z` (the `S^2` factor is
simply connected). For a connected sum of `3`-manifolds, van Kampen gives a **free product**: removing a ball
(codimension `3`) does not change `\pi_1`, and the gluing `2`-sphere `S^2` is simply connected, so there are
no amalgamating relations. Hence

$$\pi_1\big((S^1\times S^2) \# (S^1\times S^2)\big) = \mathbb Z * \mathbb Z = F_2,$$

the free group on two generators — which is nontrivial. So the space is not simply connected.

## Complete Proof

Let `M = (S^1 \times S^2) \# (S^1 \times S^2)`, a closed `3`-manifold.

**Step 1 — `\pi_1` of a summand.** By the product formula, `\pi_1(S^1 \times S^2) \cong \pi_1(S^1) \times \pi_1(S^2)`.
Since `\pi_1(S^1) = \mathbb Z` and `\pi_1(S^2) = 1` (the `2`-sphere is simply connected),

$$\pi_1(S^1 \times S^2) = \mathbb Z.$$

**Step 2 — van Kampen for the connected sum.** Form `M` by removing an open `3`-ball from each copy
`A = B = S^1 \times S^2` and gluing the resulting boundary spheres: `M = A' \cup B'` with
`A' = A \setminus (\text{open ball})`, `B' = B \setminus (\text{open ball})`, and `A' \cap B'` a neighborhood
of the gluing sphere, homotopy equivalent to `S^2`.

- Removing an open ball (equivalently, a point — codimension `3`) from a `3`-manifold does not change the
  fundamental group: loops (`1`-dimensional) and null-homotopies (`2`-dimensional) can be pushed off the
  removed point by general position. So `\pi_1(A') = \pi_1(A) = \mathbb Z` and likewise `\pi_1(B') = \mathbb Z`.
- The overlap `A' \cap B' \simeq S^2` is simply connected: `\pi_1(S^2) = 1`.

By the **van Kampen theorem** (the overlap is path-connected with trivial `\pi_1`), the amalgamation is over
the trivial group, giving the free product:

$$\pi_1(M) = \pi_1(A') * \pi_1(B') = \mathbb Z * \mathbb Z = F_2.$$

**Step 3 — Conclusion.** The free group `F_2 = \mathbb Z * \mathbb Z` on two generators is nontrivial (it is
infinite and nonabelian; e.g. the generator coming from the `S^1` of the first summand is a nontrivial loop).
Since `\pi_1(M) \ne 1`,

$$\boxed{\ (S^1\times S^2) \# (S^1\times S^2) \text{ is not simply connected.}\ }\qquad\blacksquare$$

**Remark.** Two facts carry the proof, and each disposes of a tempting error. First, `S^1 \times S^2` has
`\pi_1 = \mathbb Z`, *not* trivial — the `S^1` survives even though the `S^2` factor contributes nothing.
Second, connected sum of `\ge 3`-manifolds gives the *free product* of fundamental groups (the gluing sphere
`S^{n-1}` is simply connected for `n \ge 3`, so van Kampen adds no relations) — in contrast to dimension `2`,
where the gluing circle `S^1` is *not* simply connected and connected sum behaves quite differently. Here the
net effect is that each summand donates a free `\mathbb Z`, so even one copy of `S^1 \times S^2` already
forces `\pi_1 \ne 1`; the connected sum merely makes it the larger group `F_2`.

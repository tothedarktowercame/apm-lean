<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00A01: π₁ and homology of a connect sum of homology 3-spheres

## Why It's Hard

A connect sum `M_1 \# M_2` is assembled by surgery — cut an open `3`-ball out of each manifold and glue the
two pieces along the resulting boundary `2`-spheres. Computing its invariants means correctly decomposing
`X` into the two punctured pieces and their overlap, and applying the right gluing theorems: **van Kampen**
for `\pi_1` and **Mayer–Vietoris** for homology. The subtleties are (i) understanding what removing a ball
does to each piece — it changes the manifold but not its low-dimensional homotopy, and turns a homology
sphere into a *homology ball*; and (ii) tracking the overlap `S^2`, whose simple-connectivity is what makes
`\pi_1` a clean free product, and whose top homology `H_2(S^2) = \mathbb Z` is what regenerates the
fundamental class of `X`.

The conceptual payoff — easy to miss — is that `\pi_1` and homology behave *oppositely*. The fundamental
group genuinely combines (free product, often huge and nonabelian), while homology trivializes: the connect
sum of homology spheres is **again a homology sphere**, even when its fundamental group is enormous.

## The Key Insight

Write `X = A \cup B` with `A = M_1 \setminus (\text{open ball})`, `B = M_2 \setminus (\text{open ball})`,
overlapping in a collar `A \cap B \simeq S^2` (the gluing sphere).

- **`\pi_1`:** Removing a ball (codimension `3`) from a `3`-manifold doesn't change `\pi_1`, so
  `\pi_1(A) = \pi_1(M_1)`, `\pi_1(B) = \pi_1(M_2)`. The overlap `S^2` is **simply connected**, so van Kampen
  has no relations to amalgamate: `\pi_1(X) = \pi_1(M_1) * \pi_1(M_2)` (free product).
- **Homology:** Removing a ball from a homology `3`-sphere leaves a **homology ball** —
  `H_*(A) = H_*(B) = H_*(\text{pt})`. Mayer–Vietoris glues two homology balls along `S^2`, and the only
  surviving connecting map `H_3(X) \xrightarrow{\sim} H_2(S^2) = \mathbb Z` produces `H_3(X) = \mathbb Z`,
  reproducing `H_*(S^3)`. So `X` is again an integral homology `3`-sphere.

## Complete Proof

Throughout, `M_1, M_2` are integral homology `3`-spheres, so
`H_k(M_i) = H_k(S^3) = \begin{cases}\mathbb Z & k = 0, 3 \\ 0 & \text{otherwise}\end{cases}` (in particular
`H_1(M_i) = H_2(M_i) = 0`). Set `A = M_1 \setminus \varphi_1(\mathring D^3)`,
`B = M_2 \setminus \varphi_2(\mathring D^3)`; then `X = A \cup B` with `A \cap B` a neighborhood of the glued
sphere, homotopy equivalent to `S^2`. Both `A` and `B` deformation retract onto `M_i` minus a point.

### (a) The fundamental group

Removing an open ball from a `3`-manifold does not change `\pi_1`: a point (or ball) has codimension `3`, so
loops (`1`-dimensional) and null-homotopies (`2`-dimensional) can be pushed off it by general position. Hence

$$\pi_1(A) = \pi_1(M_1 \setminus \text{pt}) = \pi_1(M_1), \qquad \pi_1(B) = \pi_1(M_2).$$

The overlap is `A \cap B \simeq S^2`, which is **simply connected**: `\pi_1(S^2) = 1`. By the **van Kampen
theorem** (`A, B` open, path-connected, with path-connected intersection),

$$\pi_1(X) \cong \pi_1(A) *_{\pi_1(A\cap B)} \pi_1(B) = \pi_1(M_1) * \pi_1(M_2),$$

the **free product**, since the amalgamating group `\pi_1(S^2)` is trivial. ∎

$$\boxed{\ \pi_1(M_1 \# M_2) \cong \pi_1(M_1) * \pi_1(M_2).\ }$$

### (b) The homology groups

**Step 1 — each punctured piece is a homology ball.** Compute `H_*(A) = H_*(M_1 \setminus \text{pt})` from the
long exact sequence of the pair `(M_1, M_1 \setminus \text{pt})`, using the local homology
`H_k(M_1, M_1\setminus\text{pt}) \cong H_k(\mathbb R^3, \mathbb R^3 \setminus 0) = \begin{cases}\mathbb Z & k=3\\0&\text{else}\end{cases}`:

$$\cdots \to H_k(M_1\setminus\text{pt}) \to H_k(M_1) \to H_k(M_1, M_1\setminus\text{pt}) \to H_{k-1}(M_1\setminus\text{pt}) \to \cdots$$

The map `H_3(M_1) = \mathbb Z \to H_3(M_1, M_1\setminus\text{pt}) = \mathbb Z` is an isomorphism (it sends the
fundamental class to the local orientation generator). Threading the sequence gives
`H_3(M_1\setminus\text{pt}) = 0`, `H_2(M_1\setminus\text{pt}) = 0`, and `H_k(M_1\setminus\text{pt}) = H_k(M_1)`
for `k = 0, 1`. Therefore

$$H_*(A) = H_*(B) = H_*(\text{pt}): \quad H_0 = \mathbb Z,\ H_1 = H_2 = H_3 = 0.$$

(`A` is a *homology `3`-ball* with boundary `S^2`; for `M_i = S^3` it is literally `D^3`.)

**Step 2 — Mayer–Vietoris for `X = A \cup B`, `A \cap B \simeq S^2`.** With
`H_k(S^2) = \begin{cases}\mathbb Z & k = 0, 2\\0 & \text{else}\end{cases}` and `H_k(A)\oplus H_k(B) = \begin{cases}\mathbb Z^2 & k=0\\0&k\ge1\end{cases}`:

- **`k = 3`:** `0 = H_3(A)\oplus H_3(B) \to H_3(X) \xrightarrow{\partial} H_2(S^2) = \mathbb Z \to H_2(A)\oplus H_2(B) = 0`, so `\partial` is an isomorphism and `H_3(X) \cong \mathbb Z`.
- **`k = 2`:** `H_2(S^2) = \mathbb Z \to H_2(A)\oplus H_2(B) = 0 \to H_2(X) \to H_1(S^2) = 0`, so `H_2(X) = 0`.
- **`k = 1`:** `H_1(A)\oplus H_1(B) = 0 \to H_1(X) \to H_0(S^2) = \mathbb Z \xrightarrow{(1,-1)} H_0(A)\oplus H_0(B) = \mathbb Z^2`. The last map is injective (`X` is connected), so `H_1(X) \to \mathbb Z` is the zero map, forcing `H_1(X) = 0`.
- **`k = 0`:** `H_0(X) = \mathbb Z` (`X` is connected); `H_k(X) = 0` for `k \ge 4`.

Collecting:

$$\boxed{\ H_k(M_1 \# M_2) \cong H_k(S^3) = \begin{cases}\mathbb Z & k = 0, 3 \\ 0 & \text{otherwise.}\end{cases}\ }$$

So `X = M_1 \# M_2` is **again an integral homology `3`-sphere**. ∎

**Remark.** The two computations land in opposite places, which is the moral of the problem. Homology *adds
and trivializes*: the connecting map of Mayer–Vietoris reproduces `H_*(S^3)` because each summand
contributes a homology ball and only the gluing `S^2` carries the top class. (Consistently,
`H_1(X) = 0 = H_1(M_1) \oplus H_1(M_2)`, the abelianization of the free product of the *perfect* groups
`\pi_1(M_i)`.) The fundamental group, by contrast, *genuinely combines* into a free product that can be
infinite and nonabelian — e.g. for two Poincaré homology spheres, `\pi_1(X)` is the free product of two
binary icosahedral groups, yet `X` is still a homology sphere. Connect-summing preserves the homology of
`S^3` while building ever more complicated fundamental groups.

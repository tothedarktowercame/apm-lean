<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t03J02: Two tori glued along null-homotopic curves — π₁ = ℤ²∗ℤ² and the homology

## Why It's Hard

The space `X` is two tori joined along a circle, and the whole computation turns on the *one* hypothesis
that the gluing curves `J_1, J_2` are **homotopically trivial**. That single fact controls both functors,
and missing its consequences is the trap:

- For **van Kampen**, the amalgamating maps `\pi_1(J) \to \pi_1(T_i)` are determined by the class `[J_i]`.
  Because `J_i` is null-homotopic, `[J_i] = 1`, so *both* maps are trivial — and the amalgamated product
  over a trivially-included subgroup collapses to a **free product**. Had `J_i` been an essential `(p,q)`
  curve instead, there would be genuine amalgamation relations and a completely different group.
- For **Mayer–Vietoris**, the connecting maps depend on `i_* : H_1(J) \to H_1(T_i)`, which sends `[J]` to
  the homology class `[J_i] = 0` (null-homotopic ⇒ null-homologous). So the relevant map `H_1(A\cap B) \to
  H_1(A)\oplus H_1(B)` is the **zero** map, which is exactly what frees up an extra `H_2` class.
- The geometric subtlety is *where the extra `H_2` generator comes from*: each `J_i` bounds a disk `D_i` in
  `T_i`, and after gluing, `D_1\cup_J D_2` is a **2-sphere** — a brand-new 2-cycle, joining the two
  fundamental classes `[T_1], [T_2]`. Recognizing this sphere is what makes `H_2 = \mathbb Z^3` (not
  `\mathbb Z^2`) believable.

## The Key Insight

Cover `X` by `A \simeq T_1` and `B \simeq T_2` overlapping in `A\cap B \simeq J = S^1`. Since `J_i` is
**null-homotopic** in `T_i`:

- The inclusions induce the **trivial** map on `\pi_1` (`[J]\mapsto [J_i] = 1`), so van Kampen gives an
  **unamalgamated** free product:
  $$\pi_1(X) = \pi_1(T_1) * \pi_1(T_2) = \mathbb Z^2 * \mathbb Z^2.$$
- They induce the **zero** map on `H_1` (`[J]\mapsto[J_i]=0`), so the Mayer–Vietoris sequence splits into
  short pieces, yielding
  $$H_0 = \mathbb Z,\quad H_1 = \mathbb Z^4,\quad H_2 = \mathbb Z^3,\quad H_{n\ge 3} = 0.$$
  The extra `H_2` generator is the sphere `D_1\cup_J D_2` formed by the two disks the curves bound.

## Complete Proof

Each `J_i` is a homotopically trivial simple closed curve on the torus `T_i`; such a curve bounds a disk
`D_i\subset T_i`, and in particular `[J_i] = 1` in `\pi_1(T_i)` and `[J_i] = 0` in `H_1(T_i)`. Form
`X = (T_1\sqcup T_2)/(J_1\sim J_2)`, and write `J\subset X` for the common image circle.

**The open cover.** Thicken slightly: let
$$
A = T_1 \cup (\text{open collar of } J \text{ in } T_2), \qquad B = T_2 \cup (\text{open collar of } J \text{ in } T_1).
$$
Then `A, B` are open, `A\cup B = X`, `A` deformation-retracts onto `T_1`, `B` onto `T_2`, and `A\cap B` is an
open neighborhood of `J` that deformation-retracts onto `J\cong S^1`. All three are path-connected; pick the
basepoint on `J`.

### (a) `\pi_1(X)` via van Kampen

The relevant fundamental groups are
$$
\pi_1(A) = \pi_1(T_1) = \mathbb Z^2 = \langle a_1, b_1 \mid [a_1,b_1]\rangle, \quad
\pi_1(B) = \pi_1(T_2) = \mathbb Z^2 = \langle a_2, b_2 \mid [a_2,b_2]\rangle,
$$
$$
\pi_1(A\cap B) = \pi_1(S^1) = \mathbb Z = \langle c\rangle, \quad c = [J].
$$
**Van Kampen's theorem** (valid since `A, B, A\cap B` are open and path-connected) gives the amalgamated free
product
$$
\pi_1(X) = \pi_1(A) *_{\pi_1(A\cap B)} \pi_1(B) = \big(\pi_1(T_1) * \pi_1(T_2)\big)\big/ \big\langle\!\big\langle\, i_*(c)\, j_*(c)^{-1} \,\big\rangle\!\big\rangle,
$$
where `i_* : \pi_1(A\cap B)\to\pi_1(A)` and `j_* : \pi_1(A\cap B)\to\pi_1(B)` are induced by inclusion. Now
the generator `c = [J]` maps to
$$
i_*(c) = [J_1] = 1 \in \pi_1(T_1), \qquad j_*(c) = [J_2] = 1 \in \pi_1(T_2),
$$
**because `J_1, J_2` are homotopically trivial.** Hence the amalgamating relation `i_*(c)\,j_*(c)^{-1} = 1`
is vacuous, and the amalgamated product is just the **free product**:
$$
\boxed{\ \pi_1(X) = \pi_1(T_1) * \pi_1(T_2) = \mathbb Z^2 * \mathbb Z^2 = \langle a_1, b_1, a_2, b_2 \mid [a_1,b_1]=1,\ [a_2,b_2]=1\rangle.\ }
$$
(This is `(\mathbb Z\oplus\mathbb Z) * (\mathbb Z\oplus\mathbb Z)`: the two pairs commute internally but
have no relations across the wedge.)

### (b) `H_*(X)` via Mayer–Vietoris

Use reduced homology with the same cover; recall
$$
\tilde H_*(T_i): \ \tilde H_1 = \mathbb Z^2,\ \tilde H_2 = \mathbb Z, \ \text{else } 0; \qquad
\tilde H_*(S^1): \ \tilde H_1 = \mathbb Z, \ \text{else } 0.
$$
The reduced **Mayer–Vietoris** sequence reads
$$
\cdots \to \tilde H_n(A\cap B) \to \tilde H_n(A)\oplus \tilde H_n(B) \to \tilde H_n(X) \xrightarrow{\partial} \tilde H_{n-1}(A\cap B) \to \cdots
$$

**Degrees `\ge 3`.** Here `\tilde H_n(A)\oplus\tilde H_n(B) = 0` and `\tilde H_{n-1}(A\cap B) = 0` for `n\ge
3` (since `\tilde H_2(S^1)=0`), so `\tilde H_n(X) = 0` for all `n\ge 3`.

**The crucial map in degree 1.** The relevant portion is
$$
\underbrace{\tilde H_2(A\cap B)}_{0} \to \underbrace{\tilde H_2(A)\oplus \tilde H_2(B)}_{\mathbb Z\oplus\mathbb Z=\mathbb Z^2} \xrightarrow{\ \alpha\ } \tilde H_2(X) \xrightarrow{\ \partial\ } \underbrace{\tilde H_1(A\cap B)}_{\mathbb Z} \xrightarrow{\ \varphi\ } \underbrace{\tilde H_1(A)\oplus \tilde H_1(B)}_{\mathbb Z^2\oplus\mathbb Z^2 = \mathbb Z^4} \xrightarrow{\ \beta\ } \tilde H_1(X) \to \underbrace{\tilde H_0(A\cap B)}_{0}.
$$
The map `\varphi = (i_*, -j_*) : H_1(S^1)\to H_1(T_1)\oplus H_1(T_2)` sends `[J]\mapsto ([J_1], -[J_2]) =
(0,0)`, **because `J_i` is null-homologous** (being null-homotopic). So `\varphi = 0`.

**Solve for `\tilde H_2`.** Since `\varphi = 0`, `\partial` is onto `\ker\varphi = \mathbb Z`, and `\alpha` is
injective (preceded by `0`), giving the short exact sequence
$$
0 \to \mathbb Z^2 \xrightarrow{\alpha} \tilde H_2(X) \xrightarrow{\partial} \mathbb Z \to 0 .
$$
As `\mathbb Z` is free, this splits:
$$
\tilde H_2(X) = \mathbb Z^2 \oplus \mathbb Z = \mathbb Z^3 .
$$

**Solve for `\tilde H_1`.** Since `\varphi = 0`, the tail `\mathbb Z \xrightarrow{0} \mathbb Z^4
\xrightarrow{\beta} \tilde H_1(X)\to 0` makes `\beta` injective (kernel `= \operatorname{im}\varphi = 0`) and
surjective, hence an isomorphism:
$$
\tilde H_1(X) = \mathbb Z^4 .
$$

**Collecting** (and passing to unreduced homology, `X` connected so `H_0 = \mathbb Z`):
$$
\boxed{\ H_0(X) = \mathbb Z,\quad H_1(X) = \mathbb Z^4,\quad H_2(X) = \mathbb Z^3,\quad H_n(X) = 0 \ (n\ge 3).\ }
$$

**Checks.** *Abelianization:* `H_1(X)` should be the abelianization of `\pi_1(X) = \mathbb Z^2 * \mathbb
Z^2`, which is `\mathbb Z^2 \oplus \mathbb Z^2 = \mathbb Z^4` ✓. *Euler characteristic:* by
inclusion–exclusion `\chi(X) = \chi(T_1) + \chi(T_2) - \chi(S^1) = 0 + 0 - 0 = 0`, matching `1 - 4 + 3 - 0 =
0` ✓.

**Geometry of `H_2 = \mathbb Z^3`.** The three generators are the two torus fundamental classes `[T_1],
[T_2]` (the image of `\alpha`, i.e. `\ker\partial`) and the **2-sphere** `\Sigma = D_1 \cup_J D_2` obtained
by gluing the two disks that `J_1` and `J_2` bound. The class `[\Sigma]` is the one with `\partial[\Sigma] =
[J]` (cutting the sphere along `J` returns the two bounding disks), the generator that the surjection
`\partial : H_2(X)\to H_1(A\cap B)=\mathbb Z` detects. ∎

**Remark.** The triviality of `J_i` is the hinge for both computations: it kills the van Kampen amalgamation
(free product instead of a one-relator quotient) and kills the Mayer–Vietoris connecting map
(`\varphi = 0`), which both *splits off* an extra `H_2 = \mathbb Z^3` and leaves `H_1 = \mathbb Z^4`
unconstrained. Up to homotopy `X` is the wedge-like space `T_1 \vee_{S^2} T_2` — more precisely
`X\simeq T_1 \vee T_2 \vee S^2`, since collapsing the contractible bounding disks shows the gluing circle
caps off into a sphere; one reads off `\pi_1 = \mathbb Z^2*\mathbb Z^2`, `H_2 = \mathbb Z\oplus\mathbb
Z\oplus\mathbb Z` (two tori plus the sphere) and `H_1 = \mathbb Z^4` directly from that wedge.

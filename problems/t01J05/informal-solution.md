<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01J05: A nowhere-zero 1-form forces Euler characteristic zero

## Why It's Hard

The two parts look unrelated — a definition, then a theorem about the Euler characteristic — but they are
secretly linked, and seeing the link is the whole point. A nowhere-zero `1`-form is a section of the
*cotangent* bundle `T^*X`, while the Euler characteristic is governed by the *tangent* bundle `TX` (via
vector fields and Poincaré–Hopf). To pass between them one needs a **Riemannian metric**, which identifies
`TX \cong T^*X` — and a Riemannian metric is built precisely by **patching local metrics with a partition of
unity**. So part (a) is the tool that makes part (b) work.

The conceptual hurdle is recognizing that "nowhere-zero `1`-form" is equivalent to "nowhere-zero vector
field," and that the existence of a nowhere-zero vector field is exactly the obstruction the Euler
characteristic measures: **Poincaré–Hopf** says `\chi(X)` is the signed count of zeros of any vector field,
so a vector field with *no* zeros forces `\chi(X) = 0`. The temptation to attack `\chi` directly (cell
counts, Betti numbers) leads nowhere; the right move is to convert the differential-form hypothesis into a
vector-field statement.

## The Key Insight

Choose a Riemannian metric `g` on `X` (it exists by a partition of unity — part (a)). The metric gives the
musical isomorphism `\sharp : T^*X \xrightarrow{\sim} TX`, fiberwise a linear isomorphism, so the vector
field `V = \omega^\sharp` (defined by `g(V, \cdot) = \omega`) is **nowhere zero** because `\omega` is. By the
**Poincaré–Hopf theorem**,

$$\chi(X) = \sum_{p : V(p) = 0} \operatorname{ind}_p(V) = \sum_{\varnothing} = 0,$$

since a nowhere-zero `V` has no zeros. (Equivalently: a rank-`(\dim X)` bundle with a nowhere-zero section
has Euler class `0`; `\omega` is such a section of `T^*X \cong TX`, so `\langle e(TX), [X]\rangle = \chi(X) = 0`.)

## Complete Proof

### (a) Partition of unity subordinate to `\{U_\alpha\}`

Let `\{U_\alpha\}` be an open cover of `X`. A **smooth partition of unity subordinate to `\{U_\alpha\}`** is a
collection of smooth functions `\{\rho_\alpha : X \to [0,1]\}` such that:

1. **(subordinate)** `\operatorname{supp}\rho_\alpha \subseteq U_\alpha` for every `\alpha`;
2. **(locally finite)** the family of supports `\{\operatorname{supp}\rho_\alpha\}` is locally finite — every
   point of `X` has a neighborhood meeting only finitely many of them;
3. **(nonnegative, bounded)** `0 \le \rho_\alpha \le 1`;
4. **(sums to one)** `\sum_\alpha \rho_\alpha(x) = 1` for all `x \in X` (the sum is finite at each point by
   local finiteness).

On a compact manifold one may take the index set finite. Such partitions of unity exist for any open cover of
a smooth manifold.

### (b) A nowhere-zero `1`-form implies `\chi(X) = 0`

Let `\omega` be a nowhere-zero `1`-form on the compact oriented manifold `X` without boundary.

**Step 1 — Build a Riemannian metric (using part (a)).** Cover `X` by coordinate charts `\{U_\alpha\}`, and on
each `U_\alpha` let `g_\alpha` be the metric pulled back from the Euclidean metric on `\mathbb R^n` via the
chart (a smooth, positive-definite symmetric `2`-tensor on `U_\alpha`). Take a smooth partition of unity
`\{\rho_\alpha\}` subordinate to `\{U_\alpha\}` and define

$$g = \sum_\alpha \rho_\alpha\, g_\alpha.$$

Each term `\rho_\alpha g_\alpha` extends smoothly by zero outside `\operatorname{supp}\rho_\alpha`, and the sum
is locally finite, so `g` is a smooth symmetric `2`-tensor. At each point `x`, `g_x = \sum_\alpha \rho_\alpha(x)\,(g_\alpha)_x`
is a convex combination (with `\sum \rho_\alpha = 1`, not all zero) of positive-definite forms, hence
positive-definite. So `g` is a **Riemannian metric** on `X`.

**Step 2 — Convert `\omega` into a nowhere-zero vector field.** The metric `g` induces, at each point, a linear
isomorphism `T_x^*X \xrightarrow{\sim} T_x X` (the inverse of `v \mapsto g_x(v, \cdot)`). Let `V = \omega^\sharp`
be the corresponding vector field, defined by

$$g_x(V_x, \cdot) = \omega_x \qquad (x \in X).$$

Since `\omega_x \ne 0` for all `x` and the isomorphism is fiberwise linear and injective, `V_x \ne 0` for all
`x`: `V` is a **nowhere-zero** smooth vector field on `X`.

**Step 3 — Apply Poincaré–Hopf.** `X` is a compact oriented manifold without boundary, so the **Poincaré–Hopf
index theorem** applies: any smooth vector field with isolated zeros satisfies

$$\sum_{p : V(p) = 0} \operatorname{ind}_p(V) = \chi(X).$$

Our `V` has **no zeros**, so the left-hand sum is empty, equal to `0`. Therefore

$$\boxed{\ \chi(X) = 0.\ }\qquad\blacksquare$$

**Remark.** The argument is the obstruction-theoretic statement that the Euler characteristic is the *only*
obstruction to a nowhere-zero vector field on a closed manifold: `\chi(X) = \langle e(TX), [X]\rangle`, and a
nowhere-zero section of `TX` (equivalently, via the metric, of `T^*X`) forces the Euler class `e(TX) = 0`. The
`1`-form versus vector field distinction is immaterial once a metric is present — and the metric is exactly
where part (a) does its work. The classic instance is the torus (`\chi = 0`, has nowhere-zero forms/fields)
versus the sphere `S^2` (`\chi = 2 \ne 0`, the "hairy ball theorem" — no nowhere-zero vector field, hence no
nowhere-zero `1`-form).

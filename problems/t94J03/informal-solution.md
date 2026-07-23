<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J03: Tietze extension into Rⁿ, and a neighborhood extension into Sⁿ

## Why It's Hard

Part (a) is the Tietze extension theorem packaged for vector targets: the genuine content is the *scalar*
Tietze theorem (real-valued maps on a closed subset of a normal space extend), and one must see that the
`\mathbb R^n` case reduces to it coordinatewise. Part (b) is conceptually richer and contains a real warning:
a sphere-valued map on `A` **cannot** in general be extended over *all* of `X` — there are genuine homotopy
obstructions (e.g. a degree-`d` map on the boundary sphere of a disk extends over the disk only if `d = 0`).
The claim is the weaker but always-true statement that it extends over some **open neighborhood** of `A`.
The difficulty is to convert the obstructed sphere-valued problem into an unobstructed one: extend into the
ambient `\mathbb R^{n+1}` (where Tietze gives an extension freely), and then *radially project* back to the
sphere — but only where the projection is defined, i.e. where the extension is nonzero, which is exactly an
open neighborhood of `A`.

## The Key Insight

- **(a)** Write `f = (f_1, \dots, f_n)`. Each `f_i : A \to \mathbb R` extends to `F_i : X \to \mathbb R` by the
  **scalar Tietze theorem** (valid since `X` is normal and `A` is closed), and `F = (F_1, \dots, F_n)` extends `f`.
- **(b)** View `S^n \subset \mathbb R^{n+1}`. By (a), extend `f : A \to S^n \subset \mathbb R^{n+1}` to a
  continuous `G : X \to \mathbb R^{n+1}`. Then `U = \{x : G(x) \ne 0\}` is open and contains `A` (on `A`,
  `|G| = |f| = 1 \ne 0`), and the **radial projection**

$$F(x) = \frac{G(x)}{|G(x)|} : U \to S^n$$

  is continuous, lands in `S^n`, and restricts to `f` on `A`.

## Complete Proof

Throughout, `X` is normal and `A \subseteq X` is closed. We use the **scalar Tietze extension theorem**:
*every continuous `g : A \to \mathbb R` extends to a continuous `G : X \to \mathbb R`* (a standard consequence
of Urysohn's lemma for normal spaces; one may also take values in a bounded interval).

### (a) Extension into `\mathbb R^n`

Let `f : A \to \mathbb R^n` be continuous, with components `f = (f_1, \dots, f_n)`, where each
`f_i = \pi_i \circ f : A \to \mathbb R` (`\pi_i` the `i`-th coordinate projection) is continuous. By the scalar
Tietze theorem, each `f_i` extends to a continuous `F_i : X \to \mathbb R` with `F_i|_A = f_i`. Define

$$F = (F_1, \dots, F_n) : X \to \mathbb R^n.$$

`F` is continuous (each coordinate `F_i` is continuous, so `F` is continuous into the product `\mathbb R^n`),
and for `a \in A`, `F(a) = (F_1(a), \dots, F_n(a)) = (f_1(a), \dots, f_n(a)) = f(a)`. So `F|_A = f`: `f` extends
to `\mathbb R^n`. ∎

### (b) Extension into `S^n` over a neighborhood

Let `f : A \to S^n` be continuous, and regard `S^n = \{y \in \mathbb R^{n+1} : |y| = 1\}` as a subspace of
`\mathbb R^{n+1}`. Composing with this inclusion, `f : A \to \mathbb R^{n+1}` is continuous.

**Step 1 — Extend into the ambient Euclidean space.** By part (a) (with `n+1` in place of `n`), there is a
continuous extension

$$G : X \to \mathbb R^{n+1}, \qquad G|_A = f.$$

**Step 2 — The nonvanishing set is a neighborhood of `A`.** Let

$$U = \{x \in X : G(x) \ne 0\} = G^{-1}\big(\mathbb R^{n+1} \setminus \{0\}\big).$$

Since `G` is continuous and `\mathbb R^{n+1} \setminus \{0\}` is open, `U` is **open**. For `a \in A`,
`G(a) = f(a) \in S^n`, so `|G(a)| = 1 \ne 0`, giving `a \in U`. Thus `A \subseteq U`, and `U` is an open
neighborhood of `A`.

**Step 3 — Radially project to the sphere.** On `U`, `|G(x)| > 0`, so define

$$F : U \to S^n, \qquad F(x) = \frac{G(x)}{|G(x)|}.$$

`F` is continuous (`G` is continuous and `x \mapsto |G(x)|` is continuous and nonzero on `U`), and `|F(x)| = 1`,
so `F` indeed maps into `S^n`. Finally, for `a \in A`,

$$F(a) = \frac{G(a)}{|G(a)|} = \frac{f(a)}{|f(a)|} = \frac{f(a)}{1} = f(a),$$

so `F|_A = f`. Hence `f` extends to a continuous `F : U \to S^n` on the open neighborhood `U \supseteq A`.

$$\boxed{\ f : A \to S^n \text{ extends to } F : U \to S^n \text{ for some open } U \supseteq A.\ }\qquad\blacksquare$$

**Remark.** Part (a) is Tietze "vectorized" by coordinates. Part (b) is the standard upgrade for sphere-valued
maps: the target `S^n` is a **neighborhood retract** in `\mathbb R^{n+1}` (radial projection retracts the
punctured space `\mathbb R^{n+1} \setminus \{0\}` onto `S^n`), and combining a free Euclidean extension with
this retraction yields a *local* extension. The restriction to a neighborhood is essential and not a defect of
the method: extending `f` over all of `X` can be genuinely obstructed (the homotopy class of `f` may not be
trivial), whereas extension into the contractible-in-the-relevant-sense Euclidean space is never obstructed.
The construction is the prototype of "ANR (absolute neighborhood retract) targets admit neighborhood
extensions."

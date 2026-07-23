<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J04: Extending a covector to a global 1-form — and making it closed

## Why It's Hard

Part (a) is a "globalize local data" problem: a covector `\omega_p \in T_p^*X` lives at a single point, but a
`1`-form is a global smooth section of the cotangent bundle. The standard difficulty is that a coordinate
expression `\sum a_i\,dx^i` only makes sense on a chart `U`, and naively it has no meaning outside `U`; one
must splice it to the rest of `X` without breaking smoothness. The tool is a **bump function**, and the care
is in checking that `\chi\cdot\eta` extends smoothly by zero.

Part (b) looks like it should run into the **de Rham obstruction** — closed-but-not-exact forms, cohomology
`H^1_{\mathrm{dR}}(X)` — and a hasty answer might be "no, because closedness is a global constraint." The
key realization is that we are only fixing `\omega` at *one* point and are completely free everywhere else,
so there is no cohomological obstruction at all: we can simply take `\omega = df` for a cleverly chosen
function `f`. An exact form is automatically closed, and a single covector is always the differential of some
function at that point. Seeing that "closed" can be achieved *for free* via exactness — rather than wrestling
with cohomology — is the insight.

## The Key Insight

Pick a chart `(U; x^1, \dots, x^n)` at `p` and write `\omega_p = \sum_i a_i\,dx^i|_p`. Let `\chi \in C^\infty(X)`
be a bump function with `\chi \equiv 1` near `p` and `\operatorname{supp}\chi \subset U`.

- **(a)** `\omega = \chi \sum_i a_i\,dx^i` (extended by `0`) is a global smooth `1`-form with `\omega_p = \omega_p`.
- **(b)** **Yes, always** — and we can even make it *exact*. Let `\ell = \sum_i a_i\big(x^i - x^i(p)\big)`, a
  linear coordinate function with `d\ell_p = \omega_p` and `\ell(p) = 0`. Set `f = \chi\,\ell \in C^\infty(X)`
  and `\omega = df`. Then `\omega` is exact (hence **closed**), and at `p`,
  `df_p = (d\chi)_p\,\ell(p) + \chi(p)\,d\ell_p = 0 + d\ell_p = \omega_p`.

Prescribing the value at a single point places no constraint on global cohomology, so taking `\omega = df`
(the differential of a "linearizing" function) realizes any covector by a closed — indeed exact — form.

## Complete Proof

Let `\dim X = n \ge 1` and `\omega_p \in T_p^*X` be nonzero. Fix a coordinate chart `(U; x^1, \dots, x^n)`
about `p`; since `\{dx^i|_p\}` is a basis of `T_p^*X`, write

$$\omega_p = \sum_{i=1}^n a_i\, dx^i\big|_p, \qquad a_i \in \mathbb R.$$

Choose (by smooth Urysohn / bump-function construction) `\chi \in C^\infty(X)` with `0 \le \chi \le 1`,
`\chi \equiv 1` on a neighborhood `V \ni p` with `\overline V \subset U`, and `\operatorname{supp}\chi \subset U`.

### (a) A smooth `1`-form with the prescribed value

On `U`, the form `\eta = \sum_i a_i\,dx^i` is smooth (constant coefficients). Define

$$\omega = \begin{cases} \chi\,\eta & \text{on } U, \\ 0 & \text{on } X \setminus \operatorname{supp}\chi. \end{cases}$$

These two definitions agree on the overlap `U \setminus \operatorname{supp}\chi` (both `0`), and each is smooth
on its open set, so `\omega` is a well-defined smooth `1`-form on `X`. Since `\chi \equiv 1` near `p`,

$$\omega_p = \chi(p)\,\eta_p = 1\cdot \sum_i a_i\,dx^i\big|_p = \omega_p. \qquad\checkmark$$

### (b) It can always be taken closed — in fact exact

**Yes.** Define the smooth function on `U`

$$\ell = \sum_{i=1}^n a_i\big(x^i - x^i(p)\big), \qquad \text{so } \ell(p) = 0 \text{ and } d\ell\big|_p = \sum_i a_i\,dx^i\big|_p = \omega_p.$$

Set `f = \chi\,\ell`, extended by `0` outside `\operatorname{supp}\chi`; as in (a), `f \in C^\infty(X)`. Define

$$\omega = df,$$

which is **exact**, hence **closed** (`d\omega = d(df) = 0`). Its value at `p` is, by the Leibniz rule,

$$\omega_p = df\big|_p = (d\chi)_p\,\ell(p) + \chi(p)\,(d\ell)_p = (d\chi)_p\cdot 0 + 1\cdot \omega_p = \omega_p,$$

using `\ell(p) = 0` and `\chi(p) = 1`. So `\omega = df` is a global smooth, closed (exact) `1`-form with
`\omega_p = \omega_p`. Therefore we can **always** arrange `\omega` to be closed. $\qquad\blacksquare$

**Remark.** The point of (b) is that fixing a `1`-form at a *single* point is far too weak to feel any de Rham
cohomology: there is enormous freedom in the rest of `X`, and exact forms (which are automatically closed)
already realize every covector at every point. Concretely, every `\omega_p \in T_p^*X` is `df|_p` for the
linear function `f = \sum a_i x^i` (bumped to be global), so `\omega = df` works. An obstruction would appear
only if one prescribed the form on a *positive-dimensional* set, or demanded a specific cohomology class — e.g.
requiring a *nowhere-zero* closed form, or a closed form in a fixed nontrivial class, can be impossible. For a
single nonzero covector, no such obstruction exists.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J07: Baire category of non-differentiable functions, and an injective-multiplier continuity test

## Why It's Hard

Both parts are about the *automatic* machinery of Banach spaces, and each rewards finding the right
abstract lever rather than computing.

Part (a) asks you to show a set is "large" (second category), but you cannot exhibit non-differentiable
functions one by one — there are too many, and largeness is a topological statement. The trick is to flip
it: show the *complement* (functions differentiable at `0`) is **small** (first category) by writing it
inside a countable union of closed sets, then proving each such set has empty interior. The empty-interior
step is the crux and the place intuition can mislead: a function with a bounded difference quotient at `0`
can be nudged, by an arbitrarily small but arbitrarily *steep* perturbation, into one with an enormous
difference quotient — so no such set can contain a ball.

Part (b) is a "prove or disprove" trap. The natural instinct is to build a counterexample with a diagonal
operator `Te_n = n e_n` and `Ae_n = e_n/n`, so that `AT = I` is continuous while `T` is unbounded. But
that `T` is **not defined on all of `X`** — and the hypothesis "linear map of `X` into `X`" means
*everywhere* defined. Everywhere-definedness is precisely what the **closed graph theorem** needs, and once
you spot that `A` injective plus `AT, A` continuous forces the graph of `T` closed, the statement is true.

## The Key Insight

**(a)** If `f'(0)` exists, the difference quotient is bounded near `0`, so `f` lies in some

$$A_n = \{f \in C[-1,1] : |f(t) - f(0)| \le n|t| \text{ for all } t\}.$$

Each `A_n` is **closed** (the inequality survives uniform limits) and has **empty interior** (add a tiny
steep zig-zag to escape it), hence is nowhere dense. So `\{f : f'(0)\text{ exists}\} \subseteq \bigcup_n A_n`
is first category; since `C[-1,1]` is a complete (Baire) space, the complement — functions **not**
differentiable at `0` — is second category.

**(b)** The statement is **true**. To show `T` continuous, prove its graph is closed: if `x_n \to 0` and
`Tx_n \to y`, then `A(Tx_n) \to Ay` (`A` continuous) while `(AT)x_n \to 0` (`AT` continuous, `x_n \to 0`),
so `Ay = 0`, and **`A` injective forces `y = 0`**. Closed graph theorem (`X` Banach) then gives `T`
continuous.

## Complete Proof

### (a) Non-differentiable-at-`0` functions are second category

Work in the Banach space `C[-1,1]` with `\|f\| = \sup_{|t|\le1}|f(t)|`; being complete, it is a **Baire
space** (second category in itself). Let `D_0 = \{f \in C[-1,1] : f'(0) \text{ exists}\}`. We show `D_0` is
first category.

**Covering `D_0` by the `A_n`.** Suppose `f'(0)` exists. Then `\frac{f(t)-f(0)}{t} \to f'(0)`, so there are
`\delta > 0`, `C` with `|f(t) - f(0)| \le C|t|` for `|t| \le \delta`. For `|t| > \delta`,
`|f(t)-f(0)| \le 2\|f\| \le \tfrac{2\|f\|}{\delta}|t|`. Hence `|f(t)-f(0)| \le n|t|` for all `t` with
`n = \lceil \max(C, 2\|f\|/\delta)\rceil`, i.e. `f \in A_n`. So `D_0 \subseteq \bigcup_{n\ge1} A_n`, where
`A_n = \{f : |f(t)-f(0)| \le n|t|\ \forall t\}`.

**Each `A_n` is closed.** If `f_k \in A_n` and `f_k \to f` uniformly, then for each fixed `t`,
`|f(t)-f(0)| = \lim_k |f_k(t)-f_k(0)| \le n|t|`. So `f \in A_n`.

**Each `A_n` has empty interior.** Fix `f \in A_n` and `\varepsilon > 0`; we find `g \in B(f,\varepsilon)`
with `g \notin A_n`. Let `\varphi(t) = \tfrac{\varepsilon}{2}\sin(t/h)` for small `h > 0`: then
`\|\varphi\| \le \tfrac{\varepsilon}{2}`, `\varphi(0) = 0`, but `\varphi` is very steep near `0`. Put
`g = f + \varphi`, so `\|g - f\| \le \tfrac{\varepsilon}{2} < \varepsilon`. At `t_h = \tfrac{\pi h}{2}`
(small for small `h`), `\varphi(t_h) = \tfrac{\varepsilon}{2}`, so

$$|g(t_h) - g(0)| \ge |\varphi(t_h)| - |f(t_h) - f(0)| \ge \frac{\varepsilon}{2} - |f(t_h)-f(0)|.$$

Since `f` is continuous, `|f(t_h)-f(0)| < \tfrac{\varepsilon}{4}` for `h` small, giving
`|g(t_h)-g(0)| \ge \tfrac{\varepsilon}{4}`; meanwhile `n|t_h| = n\tfrac{\pi h}{2} < \tfrac{\varepsilon}{4}`
for `h` small. Thus `|g(t_h)-g(0)| > n|t_h|`, so `g \notin A_n`. Hence `B(f,\varepsilon) \not\subseteq A_n`,
and `A_n` has empty interior.

**Conclusion.** Each `A_n` is closed with empty interior, hence nowhere dense, so `\bigcup_n A_n` — and
therefore `D_0 \subseteq \bigcup_n A_n` — is **first category**. If the complement `C[-1,1]\setminus D_0`
were also first category, then `C[-1,1] = D_0 \cup (C[-1,1]\setminus D_0)` would be first category,
contradicting the Baire property. Therefore

$$\boxed{\ \{f \in C[-1,1] : f \text{ is not differentiable at } 0\} = C[-1,1]\setminus D_0 \text{ is of second category.}\ }\quad\blacksquare$$

### (b) `T` must be continuous (statement true)

**Claim.** If `X` is Banach, `T : X \to X` is linear (everywhere defined), `A : X \to X` is continuous,
linear, and injective, and `AT` is continuous, then `T` is continuous.

**Proof via the closed graph theorem.** Since `X` is a Banach space and `T : X \to X` is linear, it
suffices to show the graph of `T` is closed: i.e. whenever `x_n \to x` and `Tx_n \to y`, then `y = Tx`. By
linearity it is enough to treat `x = 0`: suppose `x_n \to 0` and `Tx_n \to y`; we show `y = 0`.

- `A` is continuous and `Tx_n \to y`, so `A(Tx_n) \to Ay`.
- `AT` is continuous and `x_n \to 0`, so `(AT)x_n \to (AT)(0) = 0`.

But `A(Tx_n) = (AT)x_n`, so the two limits coincide: `Ay = 0`. Since `A` is **injective**, `y = 0`.

Thus the graph of `T` is closed, and by the **closed graph theorem** (both domain and codomain are the
Banach space `X`), `T` is continuous. ∎

**Remark (why the diagonal "counterexample" fails).** One is tempted to take `X = \ell^2`,
`A e_n = \tfrac1n e_n` (bounded, injective), and `T e_n = n e_n`, so `AT = I` is continuous while `T` is
unbounded. But `T(\sum c_n e_n) = \sum n c_n e_n` is defined only when `\sum n^2|c_n|^2 < \infty` — *not*
on all of `\ell^2`. So this `T` is not a map `X \to X`, violating the hypothesis. Every hypothesis pulls
its weight: `X` Banach (closed graph theorem), `A` continuous (to push `Tx_n \to y` through `A`), `AT`
continuous (to get `(AT)x_n \to 0`), and `A` injective (to deduce `y = 0` from `Ay = 0`). Drop injectivity
and the conclusion genuinely fails.

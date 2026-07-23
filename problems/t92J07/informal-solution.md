<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t92J07: A common regular value for countably many maps (Sard)

## Why It's Hard

For a *single* smooth map `f_i : M_i \to \mathbb R^m`, the regular value theorem already tells us that
`f_i^{-1}(x)` is a smooth submanifold whenever `x` is a regular value, and Sard's theorem guarantees regular
values are abundant. The difficulty here is the quantifier: we need **one** point `x \in \mathbb R^m` that is
*simultaneously* a regular value for **all** the maps `f_1, f_2, \dots` at once. Each map forbids its own set
of "bad" points (its critical values), and one must show these forbidden sets do not exhaust `\mathbb R^m`.
The crucial structural fact is that the index set is **countable**: a countable union of measure-zero sets is
still measure zero, so the union of all critical-value sets cannot be everything, and a common regular value
survives. (For an *uncountable* family this can fail.)

## The Key Insight

By **Sard's theorem**, the set `C_i` of critical values of `f_i` has Lebesgue measure zero in `\mathbb R^m`.
The "bad" points — those that are a critical value of *some* `f_i` — form

$$C = \bigcup_{i=1}^\infty C_i,$$

a **countable** union of measure-zero sets, hence measure zero. Therefore `\mathbb R^m \setminus C` has full
measure and is nonempty; pick any `x` in it. Then `x` is a regular value of every `f_i`, so by the regular
value theorem `f_i^{-1}(x)` is a smooth submanifold of `M_i` for all `i`.

## Complete Proof

For each `i`, let `f_i : M_i \to \mathbb R^m` be a smooth map of the smooth manifold `M_i`. A point
`p \in M_i` is a *critical point* of `f_i` if `df_{i,p}` is not surjective, and `x \in \mathbb R^m` is a
*critical value* if it is the image of some critical point; otherwise `x` is a *regular value* (in particular
every `x \notin f_i(M_i)` is vacuously regular).

**Step 1 — Each critical-value set is null (Sard).** By **Sard's theorem**, for the smooth map
`f_i : M_i \to \mathbb R^m` the set of critical values

$$C_i = \{\,f_i(p) : p \text{ a critical point of } f_i\,\} \subseteq \mathbb R^m$$

has Lebesgue measure zero. (Smooth manifolds are second countable, so Sard applies.)

**Step 2 — The total bad set is null (countability).** Let `C = \bigcup_{i=1}^\infty C_i`. As a **countable**
union of measure-zero sets, `C` has measure zero:

$$\mathrm{meas}(C) \le \sum_{i=1}^\infty \mathrm{meas}(C_i) = 0.$$

Hence `\mathbb R^m \setminus C` has full measure; in particular it is nonempty (its complement `C` cannot be
all of `\mathbb R^m`, which has positive — indeed infinite — measure). Choose any

$$x \in \mathbb R^m \setminus C.$$

**Step 3 — `x` works for every `i`.** Since `x \notin C \supseteq C_i`, the point `x` is **not** a critical
value of `f_i`, i.e. `x` is a regular value of `f_i`, for every `i`. By the **regular value theorem**
(preimage theorem), for a regular value `x` the preimage `f_i^{-1}(x)` is a smooth embedded submanifold of
`M_i` (of dimension `\dim M_i - m`, and empty — a submanifold — if `x \notin f_i(M_i)`). Therefore

$$\boxed{\ \text{for all } i,\ f_i^{-1}(x) \text{ is a smooth submanifold of } M_i.\ }\qquad\blacksquare$$

**Remark.** The argument is "Sard plus countable additivity of measure-zero sets." The countability of the
index set is essential: it is exactly what keeps the union of forbidden values measure zero (an uncountable
union of null sets can fill `\mathbb R^m`, e.g. `\mathbb R^m = \bigcup_{x} \{x\}`). Sard supplies the
per-map null set, and the regular value theorem converts "regular value" into "submanifold preimage." The
same scheme proves any countable list of generic-position requirements, each holding off a measure-zero set,
can be met simultaneously by a single generic point.

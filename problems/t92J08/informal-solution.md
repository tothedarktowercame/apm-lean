<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t92J08: Compactness makes a vector field complete; non-compactness allows blow-up

## Why It's Hard

"Every integral curve is contained in a complete one" means the vector field `X` is **complete**: every
maximal integral curve is defined for all `t \in \mathbb R`. The subtlety is that completeness can fail for
*two different geometric reasons*, and a correct hypothesis must rule out both. An integral curve can either
**run off the edge** of a non-compact manifold (reach a missing boundary in finite time), or **escape to
infinity** in finite time even on a manifold with no edge (finite-time blow-up driven by the field growing
without bound). The challenge in (a) is to name a single clean hypothesis that forbids both escapes, and in
(b) to exhibit an honest blow-up showing the hypothesis cannot be dropped.

The bridge is the **escape lemma**: a maximal integral curve whose domain has a finite endpoint must
eventually leave *every* compact set. Compactness of `M` makes this impossible (the curve has nowhere to
escape to), forcing the domain to be all of `\mathbb R`.

## The Key Insight

- **(a)** If `M` is **compact** (closed, i.e. without boundary), then `X` is complete. By local existence and
  uniqueness, each point lies on a unique *maximal* integral curve with open domain `(\alpha, \beta)`. The
  escape lemma says: if `\beta < \infty`, the curve must leave every compact set as `t \to \beta^-`. But the
  curve lives in the compact `M` and cannot escape — contradiction — so `\beta = +\infty`, and likewise
  `\alpha = -\infty`. Every maximal curve is defined on all of `\mathbb R`. (Compact support of `X`, or any
  uniform bound forcing finite escape time below, works just as well — these also cover non-compact `M`.)

- **(b)** On the non-compact `M = \mathbb R`, the field `X = x^2 \,\partial/\partial x` has the integral curve
  `\gamma(t) = \frac{1}{1 - t}` (from `\gamma(0) = 1`), which **blows up** as `t \to 1^-`. Its maximal domain
  is `(-\infty, 1) \ne \mathbb R`, so it is not contained in any complete integral curve. Hypotheses are
  genuinely needed.

## Complete Proof

Throughout, "integral curve" means a solution `\gamma : J \to M`, `J \subseteq \mathbb R` an interval, of
`\gamma'(t) = X(\gamma(t))`. By the existence–uniqueness theorem for ODEs (in local coordinates, Picard–
Lindelöf), through each point passes a unique **maximal** integral curve, defined on an open interval
`(\alpha, \beta)` (`-\infty \le \alpha < \beta \le +\infty`); every integral curve is a restriction of a
maximal one. "Contained in a complete integral curve" thus means the maximal curve has domain `\mathbb R`.

### (a) A sufficient hypothesis: `M` compact without boundary

**Claim.** If `M` is a compact smooth manifold without boundary, then every maximal integral curve of `X` is
defined on all of `\mathbb R`; hence every integral curve is contained in a complete one.

**Proof.** Let `\gamma : (\alpha, \beta) \to M` be a maximal integral curve, and suppose for contradiction
`\beta < \infty`. We use the **escape lemma**: *if the maximal domain has a finite right endpoint `\beta`,
then for every compact `K \subseteq M` there is `t < \beta` with `\gamma(t) \notin K`.* (Sketch: by
compactness one gets a uniform `\varepsilon > 0` such that integral curves starting in `K` exist for time at
least `\varepsilon`; if `\gamma` stayed in `K` up to `\beta`, a limit point `\gamma(t_n) \to q` with
`t_n \to \beta` would let one extend `\gamma` past `\beta` by length-`\varepsilon` flow from near `q`,
contradicting maximality.)

Take `K = M`, which is compact. Then `\gamma(t) \in M = K` for all `t`, so `\gamma` never leaves `K` —
contradicting the escape lemma. Hence `\beta = +\infty`. The same argument as `t \to \alpha^+` gives
`\alpha = -\infty`. Therefore `(\alpha, \beta) = \mathbb R`: `\gamma` is complete. ∎

(Variants that also suffice, including for non-compact `M`: `X` has **compact support** — outside a compact
set `X = 0`, so curves are either constant or trapped in the compact set, both complete; or any condition
guaranteeing a uniform positive lower bound on escape times, e.g. `\|X\|` bounded with respect to a complete
metric.)

### (b) An example showing hypotheses are needed

Let `M = \mathbb R` (non-compact, no boundary) and `X = x^2 \dfrac{\partial}{\partial x}`, a smooth vector
field. The integral curve through `x_0 = 1` solves

$$\gamma'(t) = \gamma(t)^2, \qquad \gamma(0) = 1.$$

Separating variables, `-\frac{1}{\gamma} = t - 1`, so

$$\gamma(t) = \frac{1}{1 - t},$$

which satisfies the ODE and initial condition, and `\gamma(t) \to +\infty` as `t \to 1^-`. The maximal
interval of existence is `(-\infty, 1)`, **not** all of `\mathbb R`: the curve blows up in finite forward
time and cannot be extended past `t = 1`. Hence this integral curve is *not* contained in any complete
integral curve. (Consistent with (a): here `M` is non-compact and `X` is unbounded, so neither hypothesis
holds.)

$$\boxed{\ \text{(a) } M \text{ compact (or } X \text{ compactly supported) } \Rightarrow X \text{ complete}; \quad \text{(b) } x^2\partial_x \text{ on } \mathbb R \text{ is incomplete.}\ }\qquad\blacksquare$$

**Remark.** Completeness fails exactly when an integral curve escapes to "infinity" in finite time — either
because the manifold has an edge to fall off (e.g. `\partial_x` on `(0,1)` reaches the boundary in finite
time) or because the field's growth drives a blow-up (the example `x^2\partial_x`). Compactness of `M`
forecloses both at once via the escape lemma; compact support of `X` is the natural extension allowing
non-compact `M`. The phenomenon is genuinely about the *speed* of the field versus the *room* in the
manifold: a slowly-growing field on a non-compact manifold (like `\partial_x` on `\mathbb R`) is complete,
while a fast-growing one (`x^2\partial_x`) is not.

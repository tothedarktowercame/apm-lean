<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97A06: A volume form always extends off a submanifold, but the extension can't be closed if the submanifold is null-homotopic

## Why It's Hard

The two parts pull in opposite directions and meet at the integral `\int_X\eta=\operatorname{vol}(X)>0`:

- **(a)** is an *existence/extension* problem: extend the volume form `\eta` from `X` to a form `\omega` on
  the larger `Y`. Restriction `i^*:\Omega^k(Y)\to\Omega^k(X)` is surjective, but proving it requires real
  geometric input — a **tubular neighborhood** of `X` in `Y` (so one can pull `\eta` back along the normal
  projection) plus a **bump function** to cut the result off to a global form. The naïve "just extend
  pointwise" doesn't produce a smooth global form.
- **(b)** is an *obstruction*: if additionally `i\simeq\text{const}`, then `\omega` *cannot* be closed. The
  difficulty is recognizing that closedness of `\omega` would turn `\int_X i^*\omega` into a **homotopy
  invariant** of `i`. Since a constant map pulls back every positive-degree form to `0`, that invariant would
  be `0` — but it equals `\operatorname{vol}(X)>0`. The contradiction is the whole content, and it hinges on
  the volume form representing a *nonzero* top cohomology class while `i` is *homotopically trivial*.

The crux is that a closed extension would make the volume of `X` detectable from the (trivial) homotopy class
of its inclusion — impossible.

## The Key Insight

- **(a)** Use a tubular neighborhood `T\supseteq X` with normal projection `\pi:T\to X` (`\pi\circ i=
  \mathrm{id}_X`) and a bump `\rho` with `\rho\equiv1` near `X`, `\operatorname{supp}\rho\subset T`. Then
  `\omega:=\rho\,\pi^*\eta` (extended by `0`) is a global `k`-form on `Y` with `i^*\omega=\eta`.
- **(b)** If `\omega` were closed, then since `i\simeq c` (constant), pullback by homotopic maps agrees in
  cohomology: `[\eta]=[i^*\omega]=[c^*\omega]=0` in `H^k_{dR}(X)` (a constant map kills the positive-degree
  `\omega`). So `\eta` would be exact, forcing `\int_X\eta=0` by Stokes — contradicting
  `\int_X\eta=\operatorname{vol}(X)>0`. Hence `\omega` is not closed.

## Complete Proof

Let `X` be a nonempty compact oriented smooth submanifold of `Y` with `k:=\dim X>0`, `\eta` its volume form
(a nowhere-zero `k`-form compatible with the orientation, so `\int_X\eta=\operatorname{vol}(X)>0`), and
`i:X\hookrightarrow Y` the inclusion.

### (a) An extension `\omega` exists

Since `X` is a compact embedded submanifold of `Y`, it has a **tubular neighborhood**: an open set `T` with
`X\subseteq T\subseteq Y` and a smooth retraction (the normal-bundle projection) `\pi:T\to X` satisfying
`\pi|_X=\mathrm{id}_X`, i.e. `\pi\circ i=\mathrm{id}_X`.

Pull `\eta` back to `T`: `\pi^*\eta` is a smooth `k`-form on `T`, and restricting to `X`,
$$
i^*(\pi^*\eta) = (\pi\circ i)^*\eta = \mathrm{id}_X^*\,\eta = \eta .
$$
Now cut off to a global form. Since `X` is compact and `T` is an open neighborhood of `X`, there is a smooth
bump function `\rho:Y\to[0,1]` with `\rho\equiv1` on a neighborhood of `X` and `\operatorname{supp}\rho\subset
T`. Define
$$
\omega := \begin{cases}\rho\cdot\pi^*\eta & \text{on } T,\\ 0 & \text{on } Y\setminus\operatorname{supp}\rho.\end{cases}
$$
The two definitions agree on the overlap (where `\rho=0`), so `\omega` is a well-defined smooth `k`-form on
all of `Y`. On `X` we have `\rho\equiv1` and `i^*(\pi^*\eta)=\eta`, so
$$
i^*\omega = (\rho\circ i)\cdot i^*(\pi^*\eta) = 1\cdot\eta = \eta .
$$
Thus `\omega` is a global form on `Y` with `i^*\omega=\eta`. ∎

### (b) If `i\simeq\text{const}`, then `\omega` is not closed

Suppose, for contradiction, that `\omega` is **closed** (`d\omega=0`), and that `i` is homotopic to a constant
map `c:X\to Y` (with image a single point `\{p\}`).

**A constant map kills `\omega`.** Since `c` is constant, its differential `dc\equiv0`, so for the positive-degree
form (`k\ge1`),
$$
c^*\omega = 0 .
$$

**Homotopic maps pull a closed form back to cohomologous forms.** Because `\omega` is closed, it defines a de
Rham class `[\omega]\in H^k_{dR}(Y)`, and homotopic maps induce the same homomorphism on de Rham cohomology.
Thus `i^*=c^*` on `H^k_{dR}(Y)`, giving (in `H^k_{dR}(X)`)
$$
[\,i^*\omega\,] = i^*[\omega] = c^*[\omega] = [\,c^*\omega\,] = [\,0\,] = 0 .
$$
But `i^*\omega=\eta` by part (a), so `[\eta]=0` in `H^k_{dR}(X)`: the volume form `\eta` would be **exact**,
say `\eta=d\kappa` for some `(k-1)`-form `\kappa` on `X`.

**Stokes gives the contradiction.** `X` is compact, oriented, and *without boundary* (a closed manifold), so
by Stokes' theorem,
$$
\operatorname{vol}(X) = \int_X\eta = \int_X d\kappa = \int_{\partial X}\kappa = 0 .
$$
This contradicts `\int_X\eta=\operatorname{vol}(X)>0` (the volume of a nonempty positive-dimensional oriented
manifold is strictly positive).

Therefore the assumption fails: `\omega` is **not closed**, `d\omega\ne0`. ∎

**Remark.** The argument is a clean duality between geometry and topology. Part (a) is the soft fact that any
form on a (compact) submanifold extends, via tube-pullback-then-cutoff — the extension is wildly non-unique
and a priori not closed. Part (b) shows it *cannot* be made closed under the homotopy hypothesis, because a
closed `\omega` would make the pairing `\int_X i^*\omega` a homotopy invariant of `i`; the inclusion being
null-homotopic forces that pairing to vanish (constant maps see no positive-degree form), while the volume
form has *positive* period. Equivalently: `[\eta]\ne0` generates `H^k_{dR}(X)\cong\mathbb R` (top cohomology of
a closed oriented manifold), so `\eta` is *not* exact; but a closed extension would exhibit `\eta=i^*\omega`
as the pullback of a class through the trivial map `i\simeq\text{const}`, making it exact — impossible. The
phenomenon is exactly why a homologically essential cycle cannot bound: here `X` integrates a closed form to
something nonzero, so it represents a nontrivial class, incompatible with `i` being null-homotopic *unless*
the extending form fails to be closed.

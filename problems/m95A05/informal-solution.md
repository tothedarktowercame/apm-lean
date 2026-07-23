<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95A05: Lax–Milgram in operator form — coercivity gives a unique solution on a reflexive Banach space

## Why It's Hard

This is the **Lax–Milgram theorem**, but stated in a setting that strips away the usual comforts. The
classical proof lives in a *Hilbert* space and leans on the Riesz representation theorem to invert the
form; here `V` is only a **reflexive Banach** space, there is no inner product, and `A` is *not assumed
symmetric*. So one cannot minimize an energy functional (no symmetry) and cannot use Riesz (no Hilbert
structure). You must prove that `A : V \to V'` is a bijection using only boundedness, coercivity, and
the one structural feature available — reflexivity.

The difficulty concentrates in **surjectivity**. Injectivity and closedness of the range come fairly
directly from coercivity, but showing the range is *all* of `V'` requires ruling out the possibility
that `A` misses some directions. The only tool for that is Hahn–Banach, which produces a functional on
`V'` annihilating the range — and the whole proof hinges on being able to interpret that functional as
an actual *vector* in `V` against which coercivity can be tested. That reinterpretation is exactly what
**reflexivity** (`V'' = V`) buys.

## The Key Insight

Coercivity does two jobs through one squeeze. The duality pairing satisfies
`\langle Av, v\rangle \le \|Av\|_{V'}\|v\|_V`, so combined with `\langle Av, v\rangle \ge c\|v\|^2`,

$$c\,\|v\|_V^2 \le \langle Av, v\rangle \le \|Av\|_{V'}\,\|v\|_V \ \Longrightarrow\ \|Av\|_{V'} \ge c\,\|v\|_V.$$

This **lower bound** makes `A` injective with closed range — half the battle. For the other half, if the
range were not dense there would be a nonzero `\Phi \in (V')'` vanishing on it; reflexivity identifies
`\Phi` with some `w \in V`, `w \ne 0`, so that `\langle Av, w\rangle = 0` for all `v`. Testing at `v = w`
gives `\langle Aw, w\rangle = 0`, contradicting `\langle Aw, w\rangle \ge c\|w\|^2 > 0`. Coercivity thus
forbids the range from being a proper subspace. Closed plus dense equals everything: `A` is a bijection,
and `\|u\| \le \|f\|/c`.

## Complete Proof

Let `A \in L(V, V')` with `\langle Av, v\rangle \ge c\|v\|^2` for all `v \in V` (`c > 0`), `V` reflexive,
and `f \in V'`. We show `Au = f` has a unique solution `u \in V`.

**Step 1 — `A` is bounded below (hence injective).** For every `v \in V`, the definition of the dual
norm gives `\langle Av, v\rangle \le \|Av\|_{V'}\|v\|_V`. Coercivity then yields

$$c\,\|v\|_V^2 \le \langle Av, v\rangle \le \|Av\|_{V'}\,\|v\|_V,$$

so dividing by `\|v\|_V` (trivial if `v=0`),

$$\|Av\|_{V'} \ge c\,\|v\|_V \qquad \text{for all } v \in V. \tag{$\ast$}$$

In particular `Av = 0 \Rightarrow v = 0`, so `A` is **injective** — this already gives **uniqueness**.

**Step 2 — The range `R(A)` is closed.** Suppose `Au_n \to g` in `V'`. Then `(Au_n)` is Cauchy, and by
`(\ast)`, `\|u_n - u_m\|_V \le \tfrac1c\|A u_n - A u_m\|_{V'}`, so `(u_n)` is Cauchy in the complete space
`V`; let `u_n \to u`. Since `A` is continuous, `Au_n \to Au`, whence `g = Au \in R(A)`. Thus `R(A)` is a
closed subspace of `V'`.

**Step 3 — `R(A)` is dense (this uses reflexivity).** Suppose, for contradiction, that `R(A) \ne V'`.
Being a proper closed subspace, by the Hahn–Banach theorem there exists a nonzero functional
`\Phi \in (V')' = V''` with `\Phi\big|_{R(A)} = 0`. Because `V` is **reflexive**, the canonical embedding
`J : V \to V''` is onto, so `\Phi = Jw` for some `w \in V`, `w \ne 0`. By definition of `J`,
`\Phi(g) = \langle g, w\rangle` for all `g \in V'`. The annihilation condition reads

$$\langle Av, w\rangle = \Phi(Av) = 0 \qquad \text{for all } v \in V.$$

Taking `v = w` gives `\langle Aw, w\rangle = 0`. But coercivity forces
`\langle Aw, w\rangle \ge c\|w\|^2 > 0` (as `w \ne 0`) — a contradiction. Hence `R(A)` is dense in `V'`.

**Step 4 — Existence and uniqueness.** `R(A)` is closed (Step 2) and dense (Step 3), so `R(A) = V'`:
`A` is **surjective**. Combined with injectivity (Step 1), `A : V \to V'` is a bijection. Therefore for
the given `f \in V'` there is a unique `u \in V` with

$$\boxed{\ Au = f.\ }$$

Moreover, by `(\ast)`, `\|u\|_V \le \tfrac1c \|Au\|_{V'} = \tfrac1c\|f\|_{V'}`, so the inverse `A^{-1}` is
bounded and the solution depends continuously on the data. ∎

**Remark.** This is Lax–Milgram without symmetry and without a Hilbert space: coercivity replaces both
the positive-definiteness used in the energy-minimization proof and the inner product used in the Riesz
proof. The two essential ingredients are visible in their distinct roles — the coercivity-pairing squeeze
`(\ast)` gives the *lower bound* (injectivity + closed range), and **reflexivity** is what lets the
Hahn–Banach functional on `V'` be tested back through coercivity as a vector in `V` (surjectivity). Drop
reflexivity and Step 3 breaks; drop coercivity and both steps break.

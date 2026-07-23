<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96A03: Parseval for an indicator function, and the Fredholm solvability condition

## Why It's Hard

Both parts look like they ask for hard computation but are really tests of *recognition* — spotting that
an unfamiliar expression is a familiar Hilbert-space object in disguise.

In (a), the sum `\sum_n |\int_a^t u_n(s)\,ds|^2` looks like an infinite family of integrals to evaluate
against an unknown orthonormal basis `\{u_n\}` — impossible to compute term by term. The hurdle is to
realize that `\int_a^t u_n` is exactly the Fourier coefficient of the **indicator function**
`\chi_{[a,t]}` with respect to `u_n`, so the whole sum is governed by Parseval's identity and never
depends on which basis was chosen.

In (b), the difficulty is appreciating *where the closed-range hypothesis is used*. The orthogonality
condition "`b \perp \ker A^*`" places `b` in `(\ker A^*)^\perp = \overline{\operatorname{ran} A}`, the
**closure** of the range. That `b` lies in the closure is automatic from orthogonality; that it lies in
the range *itself* — so that `Ax = b` actually has a solution — needs `\operatorname{ran} A` to be closed.
Missing this is the standard error: without closed range the condition is necessary but not sufficient.

## The Key Insight

**(a)** For fixed `t`, `\int_a^t u_n(s)\,ds = \langle \chi_{[a,t]}, u_n\rangle` is the `n`-th Fourier
coefficient of `\chi_{[a,t]} \in L^2[a,b]`. Parseval's identity (the basis is complete) gives

$$\sum_n \big|\langle \chi_{[a,t]}, u_n\rangle\big|^2 = \|\chi_{[a,t]}\|_{L^2}^2 = \int_a^b \chi_{[a,t]} = t - a.$$

**(b)** The adjoint relation `\langle A^*b, x\rangle = \langle b, Ax\rangle` makes
`\ker A^* = (\operatorname{ran} A)^\perp` immediate. Taking orthogonal complements and using that a
**closed** subspace equals its double complement,

$$(\ker A^*)^\perp = (\operatorname{ran} A)^{\perp\perp} = \overline{\operatorname{ran} A} = \operatorname{ran} A,$$

so `Ax = b` is solvable (`b \in \operatorname{ran} A`) iff `b \in (\ker A^*)^\perp`, i.e. `b \perp \ker A^*`.

## Complete Proof

### (a) `\sum_{n=1}^\infty \big|\int_a^t u_n(s)\,ds\big|^2 = t - a`

Fix `t \in [a,b]` and let `\chi = \chi_{[a,t]}` be the indicator of `[a,t]`, which lies in `L^2[a,b]` with

$$\|\chi\|_{L^2}^2 = \int_a^b |\chi(s)|^2\,ds = \int_a^t 1\,ds = t - a.$$

The `n`-th Fourier coefficient of `\chi` relative to the orthonormal basis `\{u_n\}` is

$$c_n = \langle \chi, u_n\rangle = \int_a^b \chi(s)\,\overline{u_n(s)}\,ds = \int_a^t \overline{u_n(s)}\,ds,$$

so `|c_n| = \big|\int_a^t \overline{u_n}\big| = \big|\int_a^t u_n\big|`. Because `\{u_n\}` is a **complete**
orthonormal system, **Parseval's identity** holds:

$$\sum_{n=1}^\infty |c_n|^2 = \|\chi\|_{L^2}^2.$$

Substituting both computations,

$$\boxed{\ \sum_{n=1}^\infty \Big|\int_a^t u_n(s)\,ds\Big|^2 = \sum_{n=1}^\infty |c_n|^2 = \|\chi_{[a,t]}\|_{L^2}^2 = t - a.\ }$$

This holds for every `t \in [a,b]`, independent of the particular basis. ∎

### (b) `Ax = b` is solvable iff `b \perp \ker A^*`

Let `A` be a bounded linear operator on a Hilbert space `H` with `A^*` its adjoint and
`\operatorname{ran} A` **closed**.

**Step 1 — `\ker A^* = (\operatorname{ran} A)^\perp`.** For `b \in H`,

$$b \in \ker A^* \iff A^*b = 0 \iff \langle A^*b, x\rangle = 0\ \forall x \in H
\iff \langle b, Ax\rangle = 0\ \forall x \in H \iff b \perp \operatorname{ran} A,$$

using the defining relation `\langle A^*b, x\rangle = \langle b, Ax\rangle` and that `A^*b = 0` iff it is
orthogonal to all of `H`. Hence `\ker A^* = (\operatorname{ran} A)^\perp`.

**Step 2 — take complements, using closedness.** For any subset `S`, `S^{\perp\perp} = \overline{\operatorname{span}} S`;
applied to the (closed) subspace `\operatorname{ran} A`,

$$(\ker A^*)^\perp = \big((\operatorname{ran} A)^\perp\big)^\perp = (\operatorname{ran} A)^{\perp\perp}
= \overline{\operatorname{ran} A} = \operatorname{ran} A,$$

the last equality because `\operatorname{ran} A` is closed.

**Step 3 — conclude.** The equation `Ax = b` has a solution iff `b \in \operatorname{ran} A`. By Step 2,

$$b \in \operatorname{ran} A \iff b \in (\ker A^*)^\perp \iff b \perp \ker A^*.$$

Therefore

$$\boxed{\ Ax = b \text{ is solvable} \iff b \perp \ker A^*.\ }\qquad\blacksquare$$

**Remark.** Closedness of the range is exactly what upgrades the necessary condition to a sufficient one.
In general `b \perp \ker A^*` only gives `b \in (\ker A^*)^\perp = \overline{\operatorname{ran} A}`, i.e.
`b` is a *limit* of vectors `Ax_n` — but the limit need not itself be of the form `Ax` unless the range is
closed. This is the Hilbert-space form of the **Fredholm alternative**: the cokernel `\ker A^*` is the
obstruction space, and `Ax=b` is solvable precisely when `b` avoids it.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93A06: A periodic 2-form descends to the torus, integrates to 1/4, and is not exact

## Why It's Hard

The three parts trace one cohomology class — `[\omega']\in H^2_{dR}(T^2)\cong\mathbb R` — through descent,
exactness, and Stokes, and the trap is to treat them as unrelated computations:

- **(a)** Descent of `\omega` to the torus is *not* automatic: it works **only because** the coefficient
  `\sin^2(2\pi x)\cos^2(2\pi y)` is `\mathbb Z^2`-periodic (period `1` in each variable), so `\omega` is
  invariant under the deck translations. Uniqueness comes free from `\pi` being a local diffeomorphism
  (`\pi^*` injective). The integral is then a fundamental-domain integral, where the average of `\sin^2` and
  of `\cos^2` over a period (each `\tfrac12`) does the work.
- **(b)** Finding `\eta` on `\mathbb R^2` is a one-variable antiderivative — easy, *because `\mathbb R^2` is
  contractible* (every closed form is exact there). But the `\eta` you get is **not periodic** (it carries an
  `x/2` term), so it does *not* descend. Whether `\omega'` is exact *on the torus* is a genuinely different,
  cohomological question, answered "no" by the nonzero integral from (a) — the classic place students wrongly
  assume "exact on `\mathbb R^2`" implies "exact on `T^2`."
- **(c)** The parallelogram with the given vertices is — not coincidentally — spanned by the lattice vectors
  `(1,0)` and `(1,1)` of determinant `1`, hence a **fundamental domain** for `T^2`. So Stokes turns the line
  integral into `\int_P\omega`, which equals `\int_{T^2}\omega' = \tfrac14` again.

## The Key Insight

`\omega = \sin^2(2\pi x)\cos^2(2\pi y)\,dx\wedge dy` has a `\mathbb Z^2`-periodic coefficient, so it is
deck-invariant and descends to a unique `\omega'` on `T^2`, with
$$
\int_{T^2}\omega' = \int_{[0,1]^2}\omega = \Big(\!\int_0^1\!\sin^2 2\pi x\,dx\Big)\Big(\!\int_0^1\!\cos^2 2\pi y\,dy\Big) = \tfrac12\cdot\tfrac12 = \tfrac14 \ne 0.
$$
Because this integral is nonzero, Stokes forbids `\omega'=d\eta'` on the closed surface `T^2` — `\omega'` is
**not exact** — even though `\omega = d\eta` with `\eta = \cos^2(2\pi y)\big(\tfrac x2 - \tfrac{\sin
4\pi x}{8\pi}\big)dy` on `\mathbb R^2`. For (c), the parallelogram is a fundamental domain (determinant-`1`
lattice vectors), so `\int_\gamma\eta = \int_P\omega = \int_{T^2}\omega' = \tfrac14`.

## Complete Proof

Let `\pi:\mathbb R^2\to T^2=\mathbb R^2/\mathbb Z^2`, and `\omega = f\,dx\wedge dy` with
`f(x,y)=\sin^2(2\pi x)\cos^2(2\pi y)`.

### (a) Descent and the integral

**Existence.** Under a deck translation `(x,y)\mapsto(x+m,y+n)` (`m,n\in\mathbb Z`), `\sin^2(2\pi(x+m)) =
\sin^2(2\pi x)` and `\cos^2(2\pi(y+n)) = \cos^2(2\pi y)` (both period `1`), and `dx\wedge dy` is
translation-invariant; hence `\omega` is invariant under the `\mathbb Z^2`-action. An invariant form descends
to the quotient: there is a `2`-form `\omega'` on `T^2` with `\pi^*\omega'=\omega` (define
`\omega'_{[p]} := (\pi_*)\,\omega_p` using any local inverse of `\pi`; invariance makes it independent of the
preimage).

**Uniqueness.** `\pi` is a surjective local diffeomorphism, so `\pi^*` is injective on forms: if
`\pi^*\omega'_1=\pi^*\omega'_2`, then at any `[p]\in T^2`, choosing a preimage `p` and the local inverse,
`\omega'_1=\omega'_2` at `[p]`. So `\omega'` is unique.

**Integral.** `\pi` restricts to an orientation-preserving diffeomorphism from the interior of the unit
square `[0,1]^2` onto a full-measure subset of `T^2`, so
$$
\int_{T^2}\omega' = \int_{[0,1]^2}\omega = \int_0^1\!\!\int_0^1 \sin^2(2\pi x)\cos^2(2\pi y)\,dx\,dy = \int_0^1\!\sin^2(2\pi x)\,dx\,\cdot\int_0^1\!\cos^2(2\pi y)\,dy.
$$
Each factor is the average of a squared sinusoid over one full period, `\tfrac12`. Hence
$$
\boxed{\ \int_{T^2}\omega' = \tfrac12\cdot\tfrac12 = \tfrac14.\ }
$$

### (b) A primitive on `\mathbb R^2`, but none on `T^2`

**On `\mathbb R^2`.** Seek `\eta = Q\,dy` with `\partial Q/\partial x = f`. Antidifferentiating in `x`, using
`\int_0^x\sin^2(2\pi t)\,dt = \tfrac{x}{2} - \tfrac{\sin(4\pi x)}{8\pi}` (since `\sin^2(2\pi t) =
\tfrac{1-\cos 4\pi t}{2}`),
$$
\boxed{\ \eta = \cos^2(2\pi y)\Big(\tfrac{x}{2} - \tfrac{\sin(4\pi x)}{8\pi}\Big)\,dy.\ }
$$
Check: `d\eta = \dfrac{\partial Q}{\partial x}\,dx\wedge dy = \cos^2(2\pi y)\cdot\underbrace{\big(\tfrac12 -
\tfrac{\cos 4\pi x}{2}\big)}_{=\,\sin^2(2\pi x)}\,dx\wedge dy = \omega.` (Such `\eta` exists because
`\mathbb R^2` is contractible, so the closed `2`-form `\omega` is exact — but note `\eta` contains the
non-periodic term `x/2`, so it does **not** descend to `T^2`.)

**On `T^2`.** Suppose, for contradiction, there were a `1`-form `\eta'` on `T^2` with `d\eta'=\omega'`. Since
`T^2` is a closed surface (`\partial T^2=\varnothing`), Stokes' theorem gives
$$
\int_{T^2}\omega' = \int_{T^2} d\eta' = \int_{\partial T^2}\eta' = 0,
$$
contradicting `\int_{T^2}\omega'=\tfrac14\ne0` from part (a). Therefore **no such `\eta'` exists**: `\omega'`
is closed but not exact, representing a nonzero class in `H^2_{dR}(T^2)\cong\mathbb R`.

### (c) `\int_\gamma\eta = \tfrac14`

Let `P` be the parallelogram with vertices `(0,0),(1,0),(2,1),(1,1)` and `\gamma=\partial P` traversed in
that order.

**Orientation.** By the shoelace formula the signed area is
`\tfrac12\big[(1\cdot1-2\cdot0)+(2\cdot1-1\cdot1)\big] = \tfrac12(1+1) = 1 > 0`, so `\gamma` is **positively
(counterclockwise) oriented** and bounds `P` (area `1`).

**Stokes.** Since `\eta` is smooth on `\mathbb R^2\supseteq P`,
$$
\int_\gamma\eta = \int_{\partial P}\eta = \int_P d\eta = \int_P\omega.
$$

**Evaluate `\int_P\omega`.** `P` is spanned by the vectors `(1,0)` and `(1,1)`, so parametrize `x=s+t`,
`y=t` with `(s,t)\in[0,1]^2`; the Jacobian `\det\begin{psmallmatrix}1&1\\0&1\end{psmallmatrix}=1`. Then
$$
\int_P\omega = \int_0^1\!\!\int_0^1 \sin^2\!\big(2\pi(s+t)\big)\cos^2(2\pi t)\,ds\,dt.
$$
For fixed `t`, `\int_0^1\sin^2(2\pi(s+t))\,ds = \tfrac12` (the integral of `\sin^2` over an interval of
length one full period is `\tfrac12`, independent of the shift `t`). Hence
$$
\int_P\omega = \int_0^1 \tfrac12\,\cos^2(2\pi t)\,dt = \tfrac12\cdot\tfrac12 = \tfrac14.
$$
Therefore
$$
\boxed{\ \int_\gamma\eta = \tfrac14.\ }
$$
∎

**Remark.** The recurring `\tfrac14` is no accident. The vectors `(1,0),(1,1)` generate `\mathbb Z^2`
(determinant `1`), so `P` is a **fundamental domain** for `T^2`; thus `\int_P\omega = \int_{T^2}\omega' =
\tfrac14`. The three parts are one statement read three ways: the form `\omega'` carries a nonzero de Rham
class, whose period — equivalently, its integral over the torus (a), the obstruction to exactness (b), and
the value on a fundamental-domain loop via Stokes (c) — is always `\tfrac14`. Pulling back to the
contractible `\mathbb R^2` *does* trivialize `\omega` (it becomes `d\eta`), which is exactly why the
non-closed-loop integral `\int_\gamma\eta` can be nonzero: `\gamma` is contractible in `\mathbb R^2` but its
"unrolling" wraps a fundamental cell of the torus, where `\omega'` has nonzero mass.

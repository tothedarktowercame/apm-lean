<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94A04: Fréchet derivative of a cubic Nemytskii operator L⁸ → L²

## Why It's Hard

This is a **superposition (Nemytskii) operator**, `f \mapsto \sin t + f(t)^3`, and such operators
are notoriously delicate between `L^p` spaces: differentiability is *not* automatic and depends
entirely on the relationship between the source exponent, the target exponent, and the growth of
the nonlinearity. The naive guess for the derivative — "multiply by `3f^2`" — is correct, but the
whole content is *proving* it: one must verify both that the candidate `h \mapsto 3f^2 h` is a
**bounded** linear map from `L^8` into `L^2`, and that the remainder is `o(\|h\|_{L^8})`. Each of
these is a Hölder-exponent bookkeeping problem, and if the exponents did not match (say if the
domain were `L^2` instead of `L^8`) the operator would fail to be Fréchet differentiable at all.

The reason the problem fixes `B_1 = L^8` and `B_2 = L^2` is precisely to make the cubic work:
`8 = 3\cdot 2 + 2` is the arithmetic that lets `f^2 h` and the remainder terms `f h^2`, `h^3` all
land in `L^2` with the right powers of `\|h\|_{L^8}`. Recognizing that the choice of exponents is
*load-bearing* — not incidental — is the hard part.

## The Key Insight

Expand the cubic exactly: `(f+h)^3 - f^3 = 3f^2 h + 3 f h^2 + h^3`. The first term is **linear** in
`h` (the derivative candidate); the other two are the remainder. Everything reduces to three
Hölder estimates on `[0,1]` (finite measure, so `\|\cdot\|_{L^r} \le \|\cdot\|_{L^s}` for `r\le s`):

- **Linear term** `3f^2 h`: with `f^2 \in L^4` (since `\|f^2\|_{L^4} = \|f\|_{L^8}^2`) and `h\in L^8\subset L^4`,
  `\|f^2 h\|_{L^2} \le \|f^2\|_{L^4}\|h\|_{L^4} \le \|f\|_{L^8}^2 \|h\|_{L^8}` — **bounded**.
- **Remainder** `3 f h^2`: `\|f h^2\|_{L^2} \le \|f\|_{L^8}\|h^2\|_{L^{8/3}} = \|f\|_{L^8}\|h\|_{L^{16/3}}^2 \le \|f\|_{L^8}\|h\|_{L^8}^2` — order `\|h\|^2`.
- **Remainder** `h^3`: `\|h^3\|_{L^2} = \|h\|_{L^6}^3 \le \|h\|_{L^8}^3` — order `\|h\|^3`.

The constant `\sin t` differentiates to zero. So the derivative exists at **every** `f\in L^8` and is
the pointwise multiplication operator `h \mapsto 3f^2 h`. The exponent `8` is exactly large enough
to absorb a quadratic factor of `f` and still leave room for `h` — which is why the cubic is
differentiable here but would not be as a map `L^2 \to L^2`.

## Complete Proof

Let `B_1 = L^8([0,1])`, `B_2 = L^2([0,1])`, and `(Tf)(t) = \sin t + f(t)^3`. All Hölder estimates
use that `[0,1]` has measure `1`, so `\|u\|_{L^r} \le \|u\|_{L^s}` whenever `r \le s`.

**Step 0 — `T` is well-defined `L^8 \to L^2`.** The constant `\sin t` is bounded, hence in `L^2`.
For the cubic, `\|f^3\|_{L^2}^2 = \int_0^1 |f|^6 = \|f\|_{L^6}^6 \le \|f\|_{L^8}^6 < \infty`, so
`f^3 \in L^2`. Thus `Tf \in L^2` for every `f\in L^8`.

**Step 1 — The candidate derivative.** Define `\Lambda_f : L^8 \to L^2` by `\Lambda_f h = 3f^2 h`
(pointwise multiplication). It is linear in `h`. It is bounded: by Hölder with exponents `4` and `4`
(`\tfrac12 = \tfrac14 + \tfrac14`),

$$\|\Lambda_f h\|_{L^2} = 3\|f^2 h\|_{L^2} \le 3\,\|f^2\|_{L^4}\,\|h\|_{L^4}
= 3\,\|f\|_{L^8}^2\,\|h\|_{L^4} \le 3\,\|f\|_{L^8}^2\,\|h\|_{L^8},$$

using `\|f^2\|_{L^4} = (\int |f|^8)^{1/4} = \|f\|_{L^8}^2` and `\|h\|_{L^4}\le\|h\|_{L^8}`. Hence
`\Lambda_f \in \mathcal{L}(L^8, L^2)` with `\|\Lambda_f\| \le 3\|f\|_{L^8}^2`.

**Step 2 — The remainder.** Since `\sin t` cancels,

$$T(f+h) - T(f) - \Lambda_f h = (f+h)^3 - f^3 - 3f^2 h = 3 f h^2 + h^3 =: R(h).$$

Estimate each term in `L^2`.

*Term `3 f h^2`.* By Hölder with `\tfrac12 = \tfrac18 + \tfrac38` (exponents `8` and `8/3`),

$$\|f h^2\|_{L^2} \le \|f\|_{L^8}\,\|h^2\|_{L^{8/3}} = \|f\|_{L^8}\,\|h\|_{L^{16/3}}^2
\le \|f\|_{L^8}\,\|h\|_{L^8}^2,$$

since `\|h^2\|_{L^{8/3}} = (\int |h|^{16/3})^{3/8} = \|h\|_{L^{16/3}}^2` and `\|h\|_{L^{16/3}}\le\|h\|_{L^8}`.

*Term `h^3`.* `\|h^3\|_{L^2} = (\int |h|^6)^{1/2} = \|h\|_{L^6}^3 \le \|h\|_{L^8}^3`.

Combining,

$$\|R(h)\|_{L^2} \le 3\,\|f\|_{L^8}\,\|h\|_{L^8}^2 + \|h\|_{L^8}^3.$$

**Step 3 — The remainder is `o(\|h\|)`.** Dividing,

$$\frac{\|R(h)\|_{L^2}}{\|h\|_{L^8}} \le 3\,\|f\|_{L^8}\,\|h\|_{L^8} + \|h\|_{L^8}^2
\xrightarrow[\ \|h\|_{L^8}\to 0\ ]{} 0.$$

Therefore `T` is Fréchet differentiable at `f` with derivative `\Lambda_f`.

**Conclusion.** `T` is Fréchet differentiable at **every** `f \in L^8([0,1])`, and its derivative is
the bounded linear multiplication operator

$$\boxed{\ DT(f) : L^8([0,1]) \to L^2([0,1]),\qquad \big(DT(f)\,h\big)(t) = 3\,f(t)^2\,h(t).\ }$$

The constant `\sin t` contributes nothing to the derivative, and `\|DT(f)\| \le 3\|f\|_{L^8}^2`. ∎

**Remark (why the exponents matter).** The whole computation hinges on `f\in L^8`: the linear part
needs `f^2 \in L^4` and the remainder needs `f\in L^8`, `h^2\in L^{8/3}`, `h^3\in L^{6}\subset L^2`.
These are exactly affordable when the domain exponent is `8` and the target is `2` (`8 = 3\cdot 2 + 2`).
The *same* formal operator `f\mapsto f^3` is **not** Fréchet differentiable as a map `L^2 \to L^2`:
there `3f^2 h` need not even lie in `L^2` for `f,h\in L^2`. Matching the integrability exponents to
the degree of the nonlinearity is the essential structural feature of Nemytskii operators.

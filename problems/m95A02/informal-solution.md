<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95A02: The periodic Sobolev space H¹(S¹) — Fourier basis, Hölder embedding, and weak ⇒ uniform convergence

## Why It's Hard

The space `H = W^{1,2}` of `2\pi`-periodic functions with `\langle f,g\rangle_H = \int_0^{2\pi}(f'\bar g' + f\bar g)`
is a Sobolev space, and the three parts secretly build up to one deep fact: in **one dimension** the
`H^1` norm controls not just `L^2` size but the *modulus of continuity*, so bounded sets in `H` are
compact in the **sup** norm. This is the compact embedding `H^1(S^1) \hookrightarrow C(S^1)`, and the
difficulty is that it bridges three different notions of convergence — `H`-norm, weak, and uniform —
each governed by a different tool.

Part (c) is the subtle one. "Weakly convergent" is a *weak* hypothesis (it does not even give norm
convergence in `H`), yet the conclusion is *uniform* convergence, which is strong. Bridging this gap
requires three separate ingredients working together: weak convergence gives boundedness *and*
pointwise convergence (the latter because evaluations are bounded functionals — `H` is a reproducing
kernel space), the Hölder bound from (b) gives equicontinuity, and Arzelà–Ascoli converts
boundedness + equicontinuity into sup-norm precompactness. Seeing that all three are needed, and how
they fit, is the heart of the problem.

## The Key Insight

**(a)** The exponentials `e^{inx}` are *orthogonal* in `H`: `\langle e^{inx}, e^{imx}\rangle_H = 2\pi(n^2+1)\delta_{nm}`,
because differentiation multiplies the `n`-th mode by `in`, contributing `n^2` alongside the `1` from
the `L^2` part. So `H` is the **weighted `\ell^2`** with weight `n^2+1`, and
`\{e^{inx}/\sqrt{2\pi(n^2+1)}\}` is an orthonormal basis.

**(b)** Writing `f(x)-f(y) = \int_y^x f'`, Cauchy–Schwarz gives `|f(x)-f(y)| \le |x-y|^{1/2}\|f'\|_{L^2} \le |x-y|^{1/2}\|f\|_H`.
The `\tfrac12`-Hölder exponent is the gain of "half a derivative measured in sup norm" from one
derivative in `L^2` — the 1D Morrey embedding `H^1 \hookrightarrow C^{0,1/2}`.

**(c)** A weakly convergent sequence `f_n \rightharpoonup f` is **bounded** in `H` (Banach–Steinhaus),
so by (b) it is uniformly bounded and **equicontinuous** — Arzelà–Ascoli makes it precompact in
`C(S^1)`. Weak convergence also forces **pointwise** convergence `f_n(x) \to f(x)`, since each
evaluation `f \mapsto f(x)` is a bounded functional on `H`. A precompact sequence with a unique
pointwise cluster point converges uniformly to it.

## Complete Proof

Identify `2\pi`-periodic `f` with its Fourier series `f(x) = \sum_{n\in\mathbb Z} c_n e^{inx}`.

### (a) An orthonormal basis

Let `e_n(x) = e^{inx}`, so `e_n' = in\,e^{inx}`. Then

$$\langle e_n, e_m\rangle_H = \int_0^{2\pi}\!\big(e_n'\,\overline{e_m'} + e_n\,\overline{e_m}\big)\,dx
= \int_0^{2\pi}\!\big((in)(\overline{im}) + 1\big)e^{i(n-m)x}\,dx
= (nm+1)\int_0^{2\pi} e^{i(n-m)x}\,dx.$$

Since `\int_0^{2\pi} e^{i(n-m)x}\,dx = 2\pi\,\delta_{nm}`,

$$\langle e_n, e_m\rangle_H = 2\pi(n^2+1)\,\delta_{nm}.$$

So the `e_n` are mutually orthogonal with `\|e_n\|_H^2 = 2\pi(n^2+1)`, and

$$\boxed{\ \varphi_n(x) = \frac{e^{inx}}{\sqrt{2\pi(n^2+1)}}, \quad n\in\mathbb Z,\ }$$

is an **orthonormal** system. It is complete: `\{e^{inx}\}` is complete in `L^2(0,2\pi)`, and `f\in H`
iff `\|f\|_H^2 = 2\pi\sum_n (n^2+1)|c_n|^2 < \infty`, in which case the partial sums of `\sum_n c_n e^{inx}`
converge to `f` in `H`. Hence `\{\varphi_n\}` is an orthonormal **basis** of `H`, and
`H \cong \{(c_n) : \sum (n^2+1)|c_n|^2 < \infty\}` (weighted `\ell^2`).

### (b) The Hölder estimate

Functions in `H` have absolutely continuous representatives (since `f' \in L^2 \subset L^1` on a period),
so the fundamental theorem of calculus applies. For `x, y` with `|x-y| \le 2\pi`,

$$|f(x) - f(y)| = \Big|\int_y^x f'(t)\,dt\Big|
\le \Big(\int_y^x 1\,dt\Big)^{1/2}\Big(\int_y^x |f'(t)|^2\,dt\Big)^{1/2}
= |x-y|^{1/2}\Big(\int_y^x |f'|^2\Big)^{1/2}$$

by Cauchy–Schwarz. Because `[y,x] \subseteq [y, y+2\pi]` and `|f'|^2 \ge 0` is `2\pi`-periodic,
`\int_y^x |f'|^2 \le \int_y^{y+2\pi}|f'|^2 = \int_0^{2\pi}|f'|^2`. Therefore

$$\boxed{\ |f(x) - f(y)| \le |x-y|^{1/2}\Big(\int_0^{2\pi}|f'|^2\Big)^{1/2}
\le |x-y|^{1/2}\Big(\int_0^{2\pi}(|f'|^2 + |f|^2)\Big)^{1/2} = |x-y|^{1/2}\,\|f\|_H.\ }$$

(By periodicity the estimate extends to all `x,y` after reducing modulo `2\pi`.) A consequence we use
in (c): `f` is bounded with `\|f\|_\infty \le C\|f\|_H`. Indeed, some `x_0` has
`|f(x_0)|^2 \le \frac{1}{2\pi}\int_0^{2\pi}|f|^2 \le \frac{1}{2\pi}\|f\|_H^2` (a value below the mean),
so for any `x`, `|f(x)| \le |f(x_0)| + |f(x)-f(x_0)| \le \big(\tfrac{1}{\sqrt{2\pi}} + \sqrt{2\pi}\big)\|f\|_H =: C\|f\|_H`.

### (c) Weak convergence implies uniform convergence

Let `f_n \rightharpoonup f` weakly in `H`.

**Step 1 — uniform bound and equicontinuity.** A weakly convergent sequence is bounded (Banach–Steinhaus):
`\|f_n\|_H \le M` for all `n`. By (b), the family `\{f_n\}` is then
- *uniformly bounded:* `\|f_n\|_\infty \le C\|f_n\|_H \le CM`, and
- *equicontinuous:* `|f_n(x)-f_n(y)| \le |x-y|^{1/2}\|f_n\|_H \le M\,|x-y|^{1/2}`, a single modulus of
  continuity independent of `n`.

By the **Arzelà–Ascoli theorem** on the compact circle `S^1`, `\{f_n\}` is precompact in `(C(S^1), \|\cdot\|_\infty)`:
every subsequence has a uniformly convergent further subsequence.

**Step 2 — weak convergence gives pointwise convergence.** For each fixed `x`, the evaluation
`L_x : f \mapsto f(x)` is a *bounded* linear functional on `H`, since `|f(x)| \le \|f\|_\infty \le C\|f\|_H`.
By weak convergence, `L_x(f_n) \to L_x(f)`, i.e.

$$f_n(x) \to f(x) \qquad \text{for every } x.$$

(Equivalently, `H` is a reproducing kernel Hilbert space: `L_x = \langle \cdot, h_x\rangle_H`, and
`f_n \rightharpoonup f` gives `\langle f_n, h_x\rangle \to \langle f, h_x\rangle`.)

**Step 3 — assemble.** Let `(f_{n_k})` be any subsequence. By Step 1 it has a sub-subsequence
`f_{n_{k_j}} \to g` uniformly for some `g \in C(S^1)`. Uniform convergence implies pointwise
convergence, so `g = f` by the uniqueness of the pointwise limit from Step 2. Thus *every* subsequence
of `(f_n)` has a further subsequence converging uniformly to the *same* limit `f`. A sequence in a
metric space with this property converges:

$$\boxed{\ \|f_n - f\|_\infty \to 0.\ }$$

Hence every weakly convergent sequence in `H` converges in the maximum-norm topology. ∎

**Remark.** Parts (a)–(c) are the compact embedding `H^1(S^1) \hookrightarrow\hookrightarrow C(S^1)` in
action. The engine is (b): one derivative in `L^2` buys a `\tfrac12`-Hölder modulus in sup norm, which
is exactly the equicontinuity Arzelà–Ascoli needs. Weak convergence supplies the two remaining
ingredients — boundedness and (via the reproducing kernel) pointwise convergence — and compactness
upgrades them to uniform convergence. The result fails in higher dimensions, where `H^1` does not embed
into `C^0`; the `\tfrac12` exponent is a one-dimensional gift.

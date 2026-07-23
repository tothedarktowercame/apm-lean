<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m97A01: Polar decomposition A = U|A|, and the compactness of the adjoint

## Why It's Hard

This is the **polar decomposition** of an operator — the Hilbert-space analogue of writing a complex
number `z = e^{i\theta}|z|` as phase times modulus. The modulus `|A| = \sqrt{A^*A}` is a positive
operator and `U` is a partial isometry, but building them rigorously is delicate. Defining `|A|` requires
the existence *and uniqueness* of a positive square root (the spectral theorem / functional calculus).
Defining `U` is even trickier: the natural formula `U(|A|x) = Ax` is only a *recipe on the range of `|A|`*,
and one must show it is **well defined** (different `x` giving the same `|A|x` must give the same `Ax`),
isometric, and extendable to the closure `Y`. The hinge for all of this is a single pointwise norm
identity `\||A|x\| = \|Ax\|`.

Part (c) then asks to deduce that `A^*` is compact *using* the decomposition. The conceptual point is that
**compactness is a property of the modulus**: it lives in `|A| = \sqrt{A^*A}`, and since `A^* = |A|U^*`
also has `|A|` as a factor, compactness transfers. The work is in routing it through the compact-operator
ideal property without circularity.

## The Key Insight

`A^*A` is positive, so it has a unique positive square root `|A| = (A^*A)^{1/2}`, and

$$\||A|x\|^2 = \langle |A|^2 x, x\rangle = \langle A^*A x, x\rangle = \|Ax\|^2 \ \Longrightarrow\ \||A|x\| = \|Ax\|.$$

This identity is the engine. It says `|A|` and `A` have *exactly the same kernel and the same pointwise
size*, so the map `U : |A|x \mapsto Ax` is forced to be a well-defined isometry on `\operatorname{ran}|A|`
(if `|A|x_1 = |A|x_2` then `\|A(x_1-x_2)\| = \||A|(x_1-x_2)\| = 0`, so `Ax_1 = Ax_2`), and it extends by
continuity to an isometry on `Y = \overline{\operatorname{ran}|A|}`. Finally, `A = U|A|` gives
`A^* = |A|U^*`, and since `A` compact `\Rightarrow A^*A` compact `\Rightarrow |A| = \sqrt{A^*A}` compact,
the product `A^* = |A|U^*` (compact `\times` bounded) is compact.

## Complete Proof

### (a) The modulus `|A|`

`A^*A` is **positive**: it is Hermitian (`(A^*A)^* = A^*A`), and `\langle A^*Ax, x\rangle = \langle Ax, Ax\rangle = \|Ax\|^2 \ge 0`.
By the spectral theorem (continuous functional calculus applied to `t \mapsto \sqrt t` on the spectrum
`\sigma(A^*A) \subseteq [0, \|A\|^2]`), the positive operator `A^*A` has a **unique** positive square root

$$|A| := (A^*A)^{1/2}, \qquad |A| \ge 0, \quad |A|^2 = A^*A.$$

*Uniqueness:* if `B \ge 0` and `B^2 = A^*A`, then `B` commutes with `A^*A`, hence with every continuous
function of `A^*A`, in particular with `|A|`; two commuting positive operators with the same square are
equal, so `B = |A|`. This is the uniqueness of the positive square root.

*The norm identity:* using that `|A|` is Hermitian and `|A|^2 = A^*A`,

$$\||A|x\|^2 = \langle |A|x, |A|x\rangle = \langle |A|^2 x, x\rangle = \langle A^*A x, x\rangle = \langle Ax, Ax\rangle = \|Ax\|^2,$$

so `\boxed{\||A|x\| = \|Ax\|}` for all `x \in X`. ∎

### (b) The partial isometry `U`

Let `Y = \overline{\operatorname{ran}|A|}`. Following the hint, define `U` on `\operatorname{ran}|A|` by

$$U(|A|x) = Ax.$$

**Well defined.** If `|A|x_1 = |A|x_2`, then `|A|(x_1 - x_2) = 0`, so by part (a)
`\|A(x_1 - x_2)\| = \||A|(x_1 - x_2)\| = 0`, i.e. `Ax_1 = Ax_2`. So `U(|A|x)` depends only on `|A|x`, not on
`x`. It is linear on `\operatorname{ran}|A|` (immediate from linearity of `A` and `|A|`).

**Isometric.** For `y = |A|x`, `\|Uy\| = \|Ax\| = \||A|x\| = \|y\|` by part (a). So `U` preserves the norm
on `\operatorname{ran}|A|`; in particular it is bounded (`\|U\| = 1` there).

**Extension and uniqueness.** A bounded operator on the dense subspace `\operatorname{ran}|A|` of `Y`
extends **uniquely** to a bounded operator `U : Y \to X`, and an isometry on a dense subspace extends to
an isometry, so

$$\boxed{\|Uy\| = \|y\| \quad \forall y \in Y.}$$

By construction `U|A|x = Ax` for all `x`, i.e. `A = U|A|`. Uniqueness of `U`: the relation `A = U|A|`
forces `Uy = Ax` for `y = |A|x`, determining `U` on the dense set `\operatorname{ran}|A|`; a bounded
operator is determined by its values on a dense set, so `U` is unique. ∎

(Extending `U` by `0` on `Y^\perp` makes `U : X \to X` a partial isometry with `A = U|A|`; we use this in (c).)

### (c) `A^*` is compact

**`|A|` is compact.** Since `A` is compact and `A^*` is bounded, the **ideal property** of compact
operators gives that `A^*A = A^* \circ A` is compact (bounded `\circ` compact). It is also positive and
self-adjoint, so by the spectral theorem for compact self-adjoint operators
`A^*A = \sum_n \mu_n \langle \cdot, e_n\rangle e_n` with `\mu_n \ge 0`, `\mu_n \to 0`, and `\{e_n\}`
orthonormal. Then

$$|A| = (A^*A)^{1/2} = \sum_n \sqrt{\mu_n}\,\langle \cdot, e_n\rangle e_n,$$

and `\sqrt{\mu_n} \to 0`, so `|A|` is a norm limit of finite-rank operators (the partial sums), hence
**compact**.

**`A^*` is compact.** Taking adjoints of `A = U|A|` (with `U` extended to `X`, and `|A| = |A|^*`),

$$A^* = (U|A|)^* = |A|^* U^* = |A|\,U^*.$$

Here `|A|` is compact and `U^*` is bounded, so by the ideal property `A^* = |A|U^*` is **compact**. ∎

**Remark.** The decomposition `A = U|A|` separates `A` into a *modulus* `|A| = \sqrt{A^*A}` (its size) and a
*partial isometry* `U` (its phase), exactly as `z = e^{i\theta}|z|`. Compactness is a property of the
modulus — it is encoded in the decay `\mu_n \to 0` of the singular values — and since `A^* = |A|U^*` shares
the factor `|A|`, it inherits compactness. The pointwise identity `\||A|x\| = \|Ax\|` is the keystone: it
is what makes the phase `U` a genuine (well-defined, isometric) operator, by guaranteeing that `A` and its
modulus annihilate and stretch vectors identically.

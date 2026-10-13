# Blueprint for m95J05

## Triage

Verdict: **true and faithful** after the reopened statement's change from the
analytic regularity index `ω` to the smooth index `∞`.

The source asks for a fundamental solution of `d/dt + λ` and for the causal
convolution solution against an arbitrary compactly supported smooth test
function.  The Lean definitions now say exactly this.  In particular,

```lean
ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
```

is the smooth (`C^∞`) condition intended by the source.  The previous
unscoped `ContDiff ℝ ⊤` selected the analytic order `ω`; its proof that every
compactly supported test function vanished is therefore deliberately not
reused.

I tried the relevant degeneracies.  For `φ = 0`, the integral and both sides
of the ODE vanish.  For `λ = 0`, the formula reduces to the usual primitive
`∫ s in Iic t, φ s`, whose derivative is `φ t`.  If `t` is strictly below the
compact support, the integral is zero locally and again has the claimed
derivative.  None of these cases exposes a boundary-point or sign error.  The
jump at zero in the fundamental kernel is already handled by the compiled
weak fundamental-solution proof retained in `Blueprint.lean`.

No current solve-loop cache or problem-specific solve-loop record was
available.  The proof before commit `5e475969d` was inspected: its
fundamental-kernel proof remains valid and is retained verbatim (apart from
the necessary coercion disambiguation), while its analytic-collapse portion
is discarded.

## Remaining lemmas

### `apm_m95J05_solution_hasDerivAt`

**Statement in words.**  At every `t`, the causal convolution has derivative
`φ(t) - λ v(t)`.

**Why true.**  Factor the integrand as

`exp (-λ(t-s)) φ(s) = exp (-λt) (exp (λs) φ(s))`.

The weighted test function `s ↦ exp (λs) φ(s)` is continuous and compactly
supported, hence integrable by
`Continuous.integrable_of_hasCompactSupport`.  Fix an anchor `a`.  The
difference of its two `Iic` integrals is the interval integral from `a` to
`t`, by `intervalIntegral.integral_Iic_sub_Iic`.  Its derivative is the
weighted integrand by
`intervalIntegral.integral_hasDerivAt_right`.  Apply the product rule to the
outer factor `exp (-λt)` and simplify with `Real.exp_ne_zero` and
`Real.exp_add`.

**Expected size.** 70–120 lines.

**Dependencies.** Only the definitions block and Mathlib; it does not depend
on the smoothness lemma.

**Truth check.** For `λ = 0` this is FTC-1.  For `φ = 0` it says the zero
function has derivative zero.  Direct differentiation of
`e^{-λt} ∫_{-∞}^t e^{λs}φ(s) ds` gives exactly the displayed expression,
confirming the sign.

### `apm_m95J05_solution_contDiff`

**Statement in words.**  The causal convolution of the kernel with any
smooth compactly supported test function is smooth.

**Why true.**  Use the same weighted-primitive representation as above.
FTC-1 first gives differentiability of the primitive and identifies its
derivative with the smooth weighted test function.  Prove finite-order
smoothness inductively using `contDiff_succ_iff_deriv`; the derivative side
is smooth because products and scalar multiples preserve `ContDiff`.
Finally apply `contDiff_infty`, whose right side asks for every finite order,
and multiply by the smooth exponential factor.  This proof can establish its
own local FTC fact and therefore need not import the other blueprint lemma.

**Expected size.** 90–160 lines.

**Dependencies.** Only the definitions block and Mathlib; independent of
`apm_m95J05_solution_hasDerivAt`.

**Truth check.** Below the support the function is locally zero.  Above the
support it is a constant multiple of `exp (-λt)`, hence smooth.  Across the
support boundary, compactly supported smooth `φ` and all its derivatives
match zero, while FTC supplies the same conclusion globally.  At `λ = 0`
this is the standard fact that the indefinite integral of a `C^∞` function
is `C^∞`.

## Assembly

The main theorem uses the retained
`apm_m95J05_fundamental_isFundamentalKernel` for its first conjunct and the
two lemmas above for its second conjunct.  Rewriting `deriv` with
`HasDerivAt.deriv` leaves only ring arithmetic.  The main theorem itself has
no `sorry`.

## Dependency layers

* **Layer 1 (parallel):** `apm_m95J05_solution_hasDerivAt`,
  `apm_m95J05_solution_contDiff`.
* **Layer 2 (already compiled, no seat needed):** assembly of `apm_m95j05`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m95J05/Blueprint.lean
```

The final output of `#print axioms apm_m95j05` was:

```text
'apm_m95j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 lemmas.

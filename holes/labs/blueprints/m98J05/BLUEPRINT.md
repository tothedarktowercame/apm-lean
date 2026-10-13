# Blueprint for m98J05

## Triage

Verdict: **true and faithful**.

The formal statement fixes the Fourier convention

`F f ξ = ∫ x, f x * exp (-i ξ x)`

and minimally supplies the regularity and integrability hypotheses omitted by
the informal exercise.  It expresses the initial value as a right-hand limit,
which is the correct formulation because the displayed heat-kernel formula is
defined only for positive time.

I checked the likely normalization and endpoint failures:

* At `ξ = 0`, the compiled Gaussian transform is one, agreeing with the
  compiled unit-mass identity.
* At `t → 0⁺`, a constant local value is preserved by unit mass; the far
  Gaussian tail vanishes.
* For zero data, the heat solution and every claimed derivative are zero.
* For odd data at `x = 0`, the even Gaussian convolution is zero, consistent
  with pointwise convergence.
* The derivative multiplier is `iξ`; applying it twice gives `-ξ²`, matching
  the time derivative of `exp(-tξ²)`.
* The kernel normalization is
  `1/(2 sqrt(πt)) exp(-x²/(4t))`; the cached proof computes both its integral
  and Fourier transform exactly, eliminating a possible `2π` error.

No solve-loop counterexample was recorded.

## Reused completed work

The best cached attempt is preserved in full.  It already proves:

* identification of the custom transform with Mathlib's scaled transform;
* the Fourier differentiation rule via `Real.fourier_deriv`;
* nonnegativity, integrability, and unit mass of the heat kernel;
* absolute integrability of every heat-solution convolution integrand;
* the exact Fourier transform of the normalized Gaussian;
* absolute integrability of the two-variable Fubini integrand;
* the Fourier transform of the convolution; and
* the frequency-side multiplier ODE and final theorem assembly.

Only the two independent analytic bridges below remain.

## Remaining lemmas

### `apm_m98J05_bridge_1`

**Statement in words.** For continuous integrable complex data, convolution
with the positive unit-mass heat kernels converges pointwise to the datum as
time tends to zero from the right.

**Why true.** Rewrite the error, after translating the integration variable,
as

`∫ z, (f (x-z) - f x) * G_t z`.

Use continuity at `x` to choose `δ` so the factor is small for `|z|<δ`; unit
mass bounds the near integral.  For the far part, in the original `y`
variable bound the kernel on `|x-y|≥δ` by

`(2 sqrt(πt))⁻¹ exp(-δ²/(4t))`.

Its product with `∫ ‖f‖` tends to zero.  The remaining constant `f x` term is
controlled by the Gaussian tail mass, which tends to zero by scaling to a
fixed Gaussian and sending `δ/(2√t)` to infinity.  Combine the near/far
bounds with `Metric.tendsto_atTop` or an explicit epsilon proof.  The compiled
lemmas `apm_m98J05_heatKernel_nonneg`,
`apm_m98J05_heatKernel_integral`, and
`apm_m98J05_heatKernel_integrable` provide exactly the mass facts.

**Expected size:** 140–220 lines.

**Dependencies:** definitions and proved cached lemmas only.

**Truth check:** for `f = 0` the assertion is immediate.  For a continuous
function equal to a constant near `x`, only the Gaussian tail contributes to
the error, and its explicit exponential bound tends to zero.  This is the
same near/far argument for general continuous `f`.

### `apm_m98J05_bridge_2`

**Statement in words.** At every positive time, the time derivative of the
heat convolution equals its second spatial derivative.

**Why true.** Work in a time neighborhood bounded away from zero, for example
`s ∈ (t/2, 3t/2)`.  Directly differentiate the Gaussian in time and once and
twice in space.  Each derivative is a polynomial in `x-y` times a Gaussian,
with coefficients uniformly bounded on that time neighborhood.  Polynomial-
Gaussian functions are globally bounded, so each convolution derivative is
dominated by a constant multiple of `‖f y‖`, which is integrable.  Apply
Mathlib's dominated differentiation-under-the-integral theorem separately for
the time derivative and the two spatial derivatives.  The pointwise kernel
calculation

`∂ₜ G_t(z) = ∂²_z G_t(z)`

then identifies the two integrals.  The existing project has already compiled
uses of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the exact kernel
derivatives can be discharged with `HasDerivAt` chain rules and `ring`/`field_simp`.

**Expected size:** 180–280 lines.

**Dependencies:** definitions and proved integrability lemmas only; independent
of the approximate-identity bridge.

**Truth check:** at `x = 0` the formulas reduce to the standard even Gaussian
derivatives.  For zero data both sides vanish.  Symbolically differentiating
`t⁻¹/² exp(-z²/(4t))` gives
`G_t(z)(-1/(2t)+z²/(4t²))` for both derivatives.

## Dependency layers

* **Layer 1 (parallel):** `apm_m98J05_bridge_1` and
  `apm_m98J05_bridge_2`.
* **Layer 2 (already proved):** `apm_m98j05` combines these with the completed
  Fourier/Fubini bridge and multiplier ODE.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m98J05/Blueprint.lean
```

The final output was:

```text
'apm_m98j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two `sorry` warnings are exactly the two Layer 1 bridges.  The Fourier
bridge and main theorem have no direct `sorry`.

## Doubt

I am convinced both statements are true.  The only implementation risk is
the amount of elementary real-arithmetic normalization required for the
polynomial-Gaussian dominators in `bridge_2`; no missing mathematical lemma or
normalization uncertainty remains.

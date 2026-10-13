# Blueprint for m93J05

## Triage and repair

**Verdict: the unrepaired formalization is false; the current `Main.lean` already contains the smallest warranted repair.** The source asks for Euler equations for variations inside `Lᵖ`. Such variations must themselves be `Lᵖ`. If the direction is arbitrary, the path can leave the functional's domain immediately, and Lean's `ENNReal.toReal ∞ = 0` makes the encoded real-valued expression behave spuriously.

A concrete check is `N = 0`, `p = q = 2`, `g = 1`, with minimizer `f₀ = -1/2`. An arbitrary non-`L²` direction such as `h(x)=1/x` on `(0,1]` does not define an admissible variation for nonzero `t`; one cannot assert a derivative along it. The repaired stationarity clause adds exactly `MemLp h (ENNReal.ofReal p) μ`, as the intended variational argument requires. `RevisedMain.lean` reproduces the repaired theorem already present in the canonical file.

The current treatment of the cokernel is also faithful: for an idempotent projection, the quotient by the low-frequency range is canonically represented by the complementary high-frequency kernel. The source's informal marginal sentence describing the cokernel as functions having nonzero low modes is not mathematically correct.

Other edge cases were checked. At `N = 0`, `Φ` is the mean-value projection and all clauses reduce to the constant/high-frequency splitting. The assumptions `1 < p`, `1 < q`, and `1/p+1/q=1` exclude the nonreflexive endpoints. Zero data `g=0` gives minimizer `f=0` and a zero directional derivative. Although functions are representatives rather than quotient objects, every functional in the statement is invariant under almost-everywhere equality on `[0,1]`.

## Definitions

- `apm_m93j05_cosCoeff` and `apm_m93j05_sinCoeff` are the real Fourier coefficients on `[0,1]`.
- `apm_m93j05_trunc N` is the order-`N` real Fourier projection.
- `apm_m93j05_J` is the stated energy, using the restricted Lebesgue measure and `eLpNorm`.

## Remaining lemmas

### `apm_m93j05_fourier_projection`

**Statement.** The truncation is self-adjoint for the `Lᵖ`–`Lᵠ` pairing, its kernel is exactly the simultaneous vanishing of the retained coefficients, and every function splits into a fixed low-frequency part and a kernel part.

**Proof sketch.** Establish the finite orthogonality table for `1`, `cos(2πj·)`, and `sin(2πj·)` on `[0,1]`. Finite sums and Hölder integrability then justify exchanging the truncation with the pairing, giving self-adjointness. Function extensionality plus linear independence of the finite trigonometric family proves the kernel characterization. Orthogonality also gives `Φ²=Φ`; take `u=Φf` and `v=f-Φf`. Because the statement's kernel and splitting clauses quantify over arbitrary representatives, the proof must explicitly account for Mathlib's convention that a nonintegrable Bochner integral is zero rather than silently applying integral linearity without hypotheses.

**Estimate.** 200–300 lines.

**Dependencies.** None beyond the definitions.

**Truth check.** For `N=0`, `Φf` is the constant mean, the kernel is the zero-mean functions, and `f = mean(f) + (f-mean(f))`. For `f(θ)=cos(2πkθ)`, the result fixes `f` when `k≤N` and kills it when `k>N`. Sine/cosine cross terms integrate to zero.

### `apm_m93j05_weak_lowerSemicontinuous`

**Statement.** Under the explicitly encoded weak sequential convergence, every eventual lower bound for the energies of the sequence is also a lower bound at its weak limit.

**Proof sketch.** Use the projection package to identify `J` as the sum of the `p`th power of the norm of `(I-Φ)f`, the square of the finite-dimensional low-frequency norm, and the continuous linear pairing with `g`. The two norm terms are convex and strongly lower semicontinuous; convex strong lower semicontinuity implies weak lower semicontinuity. Alternatively, use weak lower semicontinuity of `eLpNorm`, while each retained Fourier coefficient converges by testing against its bounded trigonometric basis function. The last pairing converges directly from the hypothesis by taking `h=g`.

**Estimate.** 150–250 lines.

**Dependencies.** `apm_m93j05_fourier_projection`.

**Truth check.** A constant sequence gives equality. At `N=0`, weak convergence preserves the means and lower semicontinuity of the high-frequency norm is the standard weak lsc of an `Lᵖ` norm. For `g=0`, no affine term can reverse the inequality.

### `apm_m93j05_exists_minimizer`

**Statement.** For each `g∈Lᵠ`, the energy attains its minimum on `Lᵖ`.

**Proof sketch.** Split `f=u+w` with `u=Φf` and `w=(I-Φ)f`. The high-frequency energy `‖w‖ᵖᵖ` controls `w`; on the finite-dimensional range of `Φ`, norm equivalence makes `‖u‖₂²` control `u`. Hölder bounds the linear term. Young inequalities absorb its two components, proving boundedness below and coercivity. Choose a minimizing sequence in quotient `Lp`; reflexivity for `1<p<∞` gives a weakly convergent subsequence, and the preceding weak-lsc lemma gives a minimizer. Finally choose a measurable representative to match the theorem's function-level conclusion.

**Estimate.** 200–300 lines.

**Dependencies.** `apm_m93j05_fourier_projection` and `apm_m93j05_weak_lowerSemicontinuous`.

**Truth check.** At `p=2`, completing the square gives the expected unique minimizer; with `g=0`, it is zero. Along pure kernel directions the energy grows like `|t|ᵖ`, while along the finite-dimensional range it grows quadratically, confirming coercivity in both summands.

### `apm_m93j05_stationary_at_minimizer`

**Statement.** Every admissible `Lᵖ` direction has derivative zero at a minimizing representative.

**Proof sketch.** For `h∈Lᵖ`, closure of `MemLp` under addition and scalar multiplication ensures `f₀+t h` stays admissible for every real `t`. Hence the one-variable function of `t` has a global minimum at zero. Prove differentiability there: the `p`-power norm is differentiable for `p>1`, the truncated term is a finite quadratic polynomial in its Fourier coefficients, and Hölder makes the pairing linear. Fermat's theorem then says its derivative is zero. The formal conclusion asks only for the vanishing derivative, not an explicit expanded Euler–Lagrange identity.

**Estimate.** 150–250 lines.

**Dependencies.** The truncation's linearity and basic coefficient integrability; it can be developed independently of the weak-lsc and existence seats.

**Truth check.** For `p=2`, `J(f₀+t h)` is a quadratic polynomial and its linear coefficient vanishes at a minimum. For `h=0`, the path is constant. The earlier `h(x)=1/x` counterexample is now excluded exactly when it is not an `Lᵖ` direction.

## Dependency layers

- **Layer 1, parallel:** `apm_m93j05_fourier_projection` and `apm_m93j05_stationary_at_minimizer`.
- **Layer 2:** `apm_m93j05_weak_lowerSemicontinuous` after the projection package.
- **Layer 3:** `apm_m93j05_exists_minimizer` after the projection and weak-lsc lemmas.
- **Assembly:** the final `apm_m93j05` theorem is proved from these four lemmas and has no direct `sorry`.

## Compilation and axioms

`RevisedMain.lean` and `Blueprint.lean` both compile under the prescribed 12 GB memory scope. The blueprint prints:

```text
'apm_m93j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` is introduced only by the four named lemmas.

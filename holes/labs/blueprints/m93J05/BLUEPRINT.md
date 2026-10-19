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

This lemma is now a sorry-free assembly of four parallel leaves. Mathlib was searched for `Reflexive`, weak compactness of `Lp`, `WeakDual`, and `WeakDual.isCompact_polar`. Banach--Alaoglu/compact polar infrastructure exists, but there is no usable reflexivity instance or weak sequential compactness theorem for `Lp`. Consequently the direct route is retained, with that genuinely missing bridge isolated and visibly marked LIBRARY-sized rather than hidden inside the existence theorem. The suggested dual finite-dimensional route would replace it by the comparably substantial missing theorem differentiating the dual objective under the integral and deriving all Fourier moment equations; it is not shorter in the present library.

- `apm_m93j05_exists_minimizer_coercive` (80–140 lines, independent): every finite `J`-sublevel is bounded in `Lᵖ`. Split `f=Φf+(f-Φf)` using `apm_m93j05_fourier_projection`; use `integral_mul_le_Lp_mul_Lq`, Young's inequality, `apm_m93j05_trunc_parseval`, and finite-dimensional norm equivalence (`FiniteDimensional.proper` / compact unit sphere) for the retained coefficients.

- `apm_m93j05_exists_minimizer_minimizing_sequence` (30–60 lines, independent): constructs a sequence whose tails beat every admissible competitor up to `1/(k+1)`. Use `sInf` (`csInf_le`, `lt_csInf_add_pos`) after obtaining a lower bound from the same scalar Young estimates; choice selects representatives. The statement deliberately avoids asserting convergence to a real infimum.

- `apm_m93j05_exists_minimizer_weak_subsequence` (LIBRARY, 150–300 lines, independent because coercivity and minimizing properties are explicit hypotheses): transports the bounded sequence to quotient `Lp`, proves/installs reflexivity for real `Lp` when `1<p<∞`, extracts a weakly convergent subsequence (Eberlein--Šmulian or a separable diagonal argument), and chooses a representative. Candidate Mathlib ingredients are `MemLp.toLp`, `Lp.norm_toLp`, `NormedSpace.Dual`, `WeakDual`, `WeakDual.isCompact_polar`, and separability of `Lp`; the absent reflexivity/sequential-compactness bridge is the point of this leaf.

- `apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness` (split 2026-10-19 after lemma-3's partial; assembly and `_aux_core` assembly proved, `_aux_tail` and `_aux_exponents` banked). The route avoids `(Lᵠ)* = Lᵖ`. Five independent leaves:
  - `_aux_diagonal`: countably many bounded real sequences have a common convergent subsequence (compact metrizable product, `IsCompact.tendsto_subseq`).
  - `_aux_indicator_bound`: `|∫_{[0,1]} f·1_(a,b]| ≤ ‖f‖_p` (Hölder; the indicator has `Lᵠ` norm ≤ 1).
  - `_aux_limit_rep`: limits of rational-interval pairings of a uniformly bounded sequence are the pairings of some `f₀ ∈ Lᵖ` (signed measure ≪ volume, `rnDeriv`, `Lᵖ` by testing against step functions). Largest leaf; may need a further split.
  - `_aux_step_dense`: rational step functions are dense in `Lᵠ([0,1])`.
  - `_aux_extend`: ε/3 argument from step functions to all of `Lᵠ`, given the density as a hypothesis.
  - `_aux_limit_rep` (split 2026-10-19 after lemma-3's partial; assembly proved, `_aux_tendsto_abs_le` and `_aux_add` banked, the latter repaired: it did not compile as handed back). Three leaves:
    - `_aux_step_bound`: `L` extends linearly to rational step functions with `|Λ g| ≤ R ‖g‖_q` (Hölder at each `n`, then the limit).
    - `_aux_l1_rep`: an additive interval function with that step bound is integration against some `f₀ ∈ L¹` (absolutely continuous `F t = L(0,t)`; Stieltjes measures + `rnDeriv`, or a dyadic martingale's `limitProcess`). The analytic core; may need a further split.
      Split (lemma-1 round-2 partial): `_aux_zero` banked; assembly proved from four leaves: `_aux_clip` (only the part in `[0,1]` counts), `_aux_abs_sum` (`∑|L| ≤ R(∑ length)^(1/q)` on disjoint intervals), `_aux_extend` (`L` is the increment of an `AbsolutelyContinuousOnInterval F 0 1`), `_aux_ftc` (`∫ deriv F · 1_(a,b]` = clipped increment, via Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`); `f₀ := deriv F`.
    - `_aux_memLp`: an integrable `f₀` with step pairings bounded by `R ‖·‖_q` is in `Lᵖ` (test the truncations against `sign f_M |f_M|^(p-1)`).
      Split (lemma-2 round-2 partial): `_aux_trunc_memLp` banked; assembly proved from four leaves: `_aux_step_approx` (bounded `g` is an a.e. limit of uniformly bounded rational step functions; no `f₀`), `_aux_pass_limit` (the step bound passes to that limit by dominated convergence), `_aux_trunc_bound` (from the bounded-test bound, `∫ |f_M|^p ≤ R^p`), `_aux_mono` (truncation bounds give `f₀ ∈ Lᵖ`, monotone convergence).
      `_aux_step_approx` split (lemma-2 round-2 partial): `_aux_C_nonneg`, `_aux_integrable` banked; assembly proved from `_aux_l1_steps` (bounded rational step functions within `1/(n+1)` of `g` in `L¹`, via continuous approximation and a grid) and `_aux_ae_subseq` (an a.e. convergent subsequence, via convergence in measure).

- `apm_m93j05_exists_minimizer_lsc_closure` (35–70 lines, independent): applies the supplied weak-lsc statement to the extracted subsequence at levels `J(f)+1/(k+1)`, then lets `k→∞`. Use `StrictMono.tendsto_atTop`, `Filter.Eventually.filter_mono`, and `le_of_forall_pos_le_add` (or an Archimedean `k` choice).

All four leaves are true in degenerate cases. `N=0` is the mean/high-frequency split, not an empty projection. The assumptions `1<p,q` exclude endpoint failure of reflexivity and make every `1/(k+1)` positive. Empty admissible sets cannot occur because zero is admissible (`apm_m93j05_exists_minimizer_aux_zero_memLp`). For `g=0`, zero lies in every relevant sublevel and is the eventual minimizer. Weak convergence is stated using exactly the restricted-measure pairing consumed by the proved lower-semicontinuity lemma, so there is no sign or boundary convention mismatch.

**Dependencies.** The assembly uses these four leaves and the already proved `apm_m93j05_weak_lowerSemicontinuous`; the leaves themselves mention one another only through explicit hypotheses.

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

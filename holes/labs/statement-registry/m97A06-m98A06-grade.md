# Statement fidelity grades: m97A06, m98A06

Outside grader, read-only, 2026-09-30. Graded against `problems/<id>/problem.tex`.
m97A06 graded at master HEAD `4a7a07fd`. Nothing was built or run; "no sorry" for
m97A06 is from a grep of the file, not from a compile.

| id | grade | one-line reason | repair classification |
|----|-------|-----------------|-----------------------|
| m97A06 | faithful | EL equation, energy and Hessian are the prelim's, signs included; all clauses are restricted to `Icc 0 T` / `Ioo 0 T`; parts (a),(b) assume C² on `[0,T]`, the usual regularity for a classical EL solution | HEAD's C¹ hypothesis on η in part (d): **correction** (restores the prelim's function class; not a narrowing) |
| m98A06 | faithful | all clauses are true as stated; classifications are `∀ x ∈ Icc 0 a` or a.e. on `Ioo 0 π`; `deriv` vs `ContDiffOn` on `Icc` differs only at the two endpoints, a null set; H¹₀ encoding is equivalent to H¹₀(0,π) | none needed (the documented `C¹([0,1])` → `C¹([0,a])` repair is a correction of a prelim typo) |

## m97A06 evidence

**Diff check.** `git show HEAD -- problems/m97A06/lean/Main.lean` has exactly two
removed lines: the old part (d) binder and the `sorry`.

```
-      (∀ η : ℝ → ℝ, η 0 = 0 → η T = 0 →
+      (∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Set.Icc 0 T) → η 0 = 0 → η T = 0 →
```

The five definitions (`apm_m97a06_I`, `_stationary`, `_EL`, `_energy`, `_hessian`)
have no removed or changed lines; the other additions are a docstring paragraph,
lemmas and the proof. So the η hypothesis is the only statement change.

**Classification of the change: correction.** The prelim's space is C¹ functions
on `[0,T]`, so a variation of the zero solution with fixed endpoints is a C¹ η with
η(0)=η(T)=0, which is what the clause now quantifies over. The old clause also
covered non-measurable and non-integrable η, where `apm_m97a06_I` and
`apm_m97a06_hessian` are Bochner-integral default values. I tried three such
cases by hand (nowhere-differentiable η; η' not square-integrable; unbounded step
function with η² not integrable) and in each the two sides agreed through default
values, so I did not establish that the old clause was false; it was an
over-general claim whose extra cases say nothing about the second variation.

**EL equation.** L = φ'²/2 − cos(2φ)/4, ∂L/∂φ = sin(2φ)/2, so φ'' = sin(2φ)/2.

```
def apm_m97a06_EL (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    deriv (fun s => derivWithin φ (Set.Icc 0 T) s) t = Real.sin (2 * φ t) / 2
```
Correct, sign included.

**Energy.** `derivWithin φ (Set.Icc 0 T) t ^ 2 / 2 + Real.cos (2 * φ t) / 4` is the
prelim's φ'²/2 + cos(2φ)/4. Its derivative is φ'(φ'' − sin(2φ)/2) = 0 along EL.
The clause concludes constancy on `Set.Icc 0 T`.

**Hessian.** I(εη) = ∫ ε²η'²/2 − cos(2εη)/4; d²/dε² at 0 is ∫ η'² + η² (since
∂²L/∂φ² = cos(2φ) = 1 at φ = 0).

```
noncomputable def apm_m97a06_hessian (T : ℝ) (η : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) T, deriv η t ^ 2 + η t ^ 2
```
Correct. It uses `deriv η` where `apm_m97a06_I` uses `derivWithin … (Icc 0 T)`;
for η C¹ on `Icc 0 T` these agree on `Ioo 0 T`, so the integrals agree.

**Part (c).** `apm_m97a06_EL T (fun _ => 0)`. The prelim says "find a solution"
with φ(0)=φ(T)=0; φ ≡ 0 is the expected answer (part (d) then linearises about
it), and for general T it is the only one that can be named without conditions
on T. Acceptable, not trivialising. The boundary values are not stated in the
clause but are immediate for the constant function.

**Part (a).** "Find the EL equations" is encoded as: for φ C² on `[0,T]`,
first variation vanishes against all endpoint-zero variations ↔ EL. Variations
are taken C² rather than C¹ (`apm_m97a06_stationary`); this makes the → direction
slightly stronger and the ← direction slightly weaker than the C¹ version. Minor.

**All-of-ℝ comparisons.** None. Every clause is over `Icc 0 T` or `Ioo 0 T`, and
the functional uses `derivWithin` on `Icc 0 T`.

## m98A06 evidence

**Domain of the classifications.** Verified:
```
∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi), y x = Real.cos x + B * Real.sin x
∀ x ∈ Icc (0 : ℝ) a, y x = Real.sin x / Real.sin a
y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)] fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x
```
No clause compares functions off the interval.

**`deriv` vs `ContDiffOn` on `Icc`.** `apm_m98a06_I` and `apm_m98a06_IsStationary`
integrate `deriv y` over `0..a`. For y C¹ on `Icc 0 a`, `deriv y` equals the
one-sided-extended derivative at every interior point, so the integrals have the
intended values. The reverse directions of the two iff clauses are also safe: a y
equal to the named function on `Icc` is `ContDiffOn` there (that predicate only
reads values on the set) and has the same `deriv` on the open interval. No clause
is made false by the mismatch.

**(a), a = 2π, y(0)=y(2π)=1.** Weak stationarity with y C¹ gives y''+y=0, y(0)=1,
so y = cos x + B sin x, and y(2π)=1 holds for every B. No min and no max: for
admissible y and endpoint-zero η, I(y+tη) = I(y) + t·(linear) + t²·I(η); with
η = sin(x/2), I(η) = −3π/4 < 0, and with η = sin 2x, I(η) = 3π > 0, so large t
gives strictly smaller and strictly larger values. True.

**(b), a ∉ πℤ, y(0)=0, y(a)=1.** y = B sin x with B sin a = 1. For a < π, the
candidate is stationary, I(z) = I(y) + I(z−y), and I(η) ≥ ((π/a)² − 1)∫η² ≥ 0 for
endpoint-zero η, so the clause `apm_m98a06_I a (sin/sin a) ≤ apm_m98a06_I a z` is
true. For a > π, η = sin(πx/a) has I(η) = (a/2)((π/a)² − 1) < 0 and
η = sin(kπx/a) with k > a/π has I(η) > 0, so neither extremum exists. True.

**(c).** ∫₀^π sin² = π/2, so the normalised first mode is ±√(2/π) sin x and
I = 0 there; Wirtinger gives ∫y'² ≥ ∫y² on H¹₀(0,π) with equality only on
multiples of sin x; √(2/π) sin kx gives I = k² − 1, unbounded; best constant 1
(`IsLeast {C | …} 1`: C = 1 works, and any C < 1 fails on sin x). All true.

**H¹₀ encoding.**
```
def apm_m98a06_InH10Pi (u du : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 Real.pi) ∧ u 0 = 0 ∧ u Real.pi = 0 ∧
  MemLp u 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  MemLp du 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) u du
```
u, u' ∈ L² with u' the weak derivative is H¹(0,π); the continuous representative
vanishing at both ends is the trace-zero condition. The test class
(`Function.support φ ⊆ Ioo 0 π`, compact support) admits φ whose closed support
touches 0 or π, slightly more than C_c^∞(0,π), but such φ vanish at the endpoints
and every H¹ function still satisfies the identity against them, so no H¹₀
function is excluded. The class is non-empty (sin kx), so nothing is vacuous.

**Reading choices worth recording (not defects in truth).**
1. Part (c)'s constrained problem is posed over H¹₀ rather than the preamble's
   C¹. The lower bound and equality case are then slightly stronger than the C¹
   version; the minimisers are smooth, so the answer is the same.
2. Part (c) reports only the global picture (min 0 at ±√(2/π) sin x, no max). The
   other constrained stationary points ±√(2/π) sin kx, k ≥ 2, are not classified,
   whereas (a) and (b) do classify stationary curves. They are saddles, so under
   the reading "extrema = min/max" nothing is missing.
3. Part (b) with a < π states that sin x / sin a is a minimiser but does not state
   that it is the unique minimiser or that there is no maximum (both true).

## m98A06 addendum (2026-10-13, claude-14, at closure)

The grade above was given at `ee482b3a4`. Later that day `af63c04bb` strengthened the
statement toward the prelim's "find the extrema". For `a < π` the minimiser `sin x / sin a`
is now unique on `[0, a]` and there is no maximum. In (c) the unbounded-above witnesses
must be `C¹` with `dy = deriv y`, the problem's class, not only `H¹₀`. The definitions
(`apm_m98a06_I`, `IsStationary`, `Admissible`, `InH10Pi`, `IsWeakDerivativeOn`) are
byte-identical to the graded version. The closed statement implies the graded one and
states more of the prelim's answer, so the grade stays **faithful**.

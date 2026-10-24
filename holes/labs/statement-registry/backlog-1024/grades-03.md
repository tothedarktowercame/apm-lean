| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m01J06 | stronger | The last conjunct proves genuine nonlinear bifurcation at every critical load, whereas the prelim only asks whether nontrivial solutions are expected from the linearization. | — |
| m02A02 | narrower | The periodic Poisson existence/uniqueness clause assumes the additional compatibility condition `f (0, 0) = 0`, absent from the printed question (though mathematically necessary). | correction: the initial abstract bank theorem quantified essentially unrelated arbitrary data and could not express/prove the requested periodic Sobolev claims; the concrete Fourier encoding repairs that defect. |
| m02A03 | faithful | It states local integrability of `(2π)⁻¹ log ‖x-y‖` and the distributional identity against every compactly supported smooth test function. | neutral: changing `ℝ × ℝ` to the definitionally equivalent two-dimensional Euclidean-space model does not change the claim. |
| m02A05 | faithful | It gives the Euler–Lagrange system, characterizes all interval extremals, proves the global minimum, and proves unboundedness above (hence no maximum). | correction: the bank statement demanded equality of total functions outside the interval; replacing this with `Set.EqOn ... (Icc 0 (π/2))` fixes the stated smooth-bump counterexample. |
| m02A06 | narrower | Existence and uniqueness are proved only for `ε < 1 / (4*(1+C))`, and uniqueness only among solutions bounded by `2*(1+C)`; the prelim claims uniqueness for every `ε > 0`. | correction: the later repair replaces false `∃!` equality of total functions (unconstrained on `(-∞,0)`) by agreement on `Ici 0`; it does not remove the pre-existing small-ε/bounded-ball narrowing. |
| m02J01 | faithful | The three conjuncts exactly encode the zero-integral test-function primitive criterion, existence of distributional primitives, and uniqueness modulo constants. | — |
| m02J03 | faithful | It proves boundedness, strong convergence iff norm convergence under weak convergence, and strongly convergent strict convex combinations of initial segments. | — |
| m02J04 | faithful | Under standard smoothness assumptions it states Euler–Lagrange, the autonomous Beltrami identity, and global area minimality of the catenary among admissible radius curves. | correction: the bank Beltrami clause lacked regularity and was false for the discontinuous-spike example documented in the file; adding `a < b` and `C²` hypotheses fixes it. |
| m02J06 | faithful | It encodes the intended common-support version of `K`, proves both requested mollifier estimates, and asserts compactness in `L¹`. | correction: the bank’s bare smoothness order `⊤` meant analytic rather than `C∞`; the explicit infinity order fixes this. The file also correctly repairs the printed one-point support typo and makes standard mollifier nonnegativity explicit. |
| m03J01 | faithful | It packages the Riesz minimizer continuously, gives the `H₀¹` weak Dirichlet solution, and derives a uniform `L² → H²` bound from the stated regularity assumption. | correction: changing compactly supported test functions from analytic-order `⊤` to explicit `C∞` prevents the positive-dimensional test space (and hence the Sobolev model) from collapsing. |

### Evidence

#### m01J06

The source ends by asking only whether one “expect[s]” nontrivial solutions. The Lean theorem instead includes the precise assertion
```lean
(∀ m : ℕ,
  apm_m01J06_isBifurcationLoad K (apm_m01J06_criticalLoad K m))
```
where lines 58–64 define this as existence, for every `δ > 0`, of a positive nearby load and a nontrivial nonlinear solution uniformly smaller than `δ`. The preceding conjuncts faithfully encode stationarity implying the Euler–Lagrange equation, stationarity of zero, and the critical loads. No `axiom`, `opaque`, or sorry-typed dependency was found.

#### m02A02

The load-bearing restriction is explicit at lines 772–779:
```lean
∀ (u₀ : M02A02H1) (f : M02A02L2),
  ...
  f (0, 0) = 0 →
  (∃! u : M02A02H1, ...)
```
The printed part (c) quantifies arbitrary `f ∈ L²(Ω)` and omits zero mean. This condition is necessary on the torus, but it is still an extra hypothesis relative to the question. Lines 767–782 otherwise cover density/completion, closedness/completeness, Poincaré, affine existence/uniqueness, and equivalence with the Fourier Poisson equation. The first bank theorem instead took arbitrary `H`, `mean`, energies, forcing, and `weakPoisson` with no hypotheses relating them, so the concrete rewrite is a correction. No axiom/opaque/sorry dependency was found.

#### m02A03

Lines 868–873 state:
```lean
LocallyIntegrable (apm_m02a03_kernel y) volume ∧
∀ φ : APMM02A03Plane → ℝ,
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
  (∫ x, apm_m02a03_kernel y x * apm_m02a03_laplacian φ x) = φ y
```
Here the explicitly coerced `⊤ : ℕ∞` is `C∞`, not the problematic bare analytic order. The kernel definition is `(2 * Real.pi)⁻¹ * Real.log ‖x-y‖`, so the sign and normalization match `Δu = δ_y`. No axiom/opaque/sorry dependency was found.

#### m02A05

Lines 1017–1029 state the ODE characterization on `Ioo 0 (π/2)`, equality of both extremals on `Icc 0 (π/2)`, global minimality, and arbitrarily large functional values. The key lines are
```lean
deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t
...
Set.EqOn x apm_m02a05_extremal (Icc 0 (Real.pi / 2))
...
∀ B : ℝ, ∃ x y : ℝ → ℝ, ... B < apm_m02a05_J x y
```
The repair note supplies a direct refutation of the old total-function equality: add a smooth bump supported outside the integration interval. No axiom/opaque/sorry dependency was found.

#### m02A06

Lines 1985–1998 require
```lean
(hε_small : ε < 1 / (4 * (1 + C)))
...
(∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C))
...
apm_m02a06_IsSolution ε f v →
(∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C)) →
∀ x ∈ Ici (0 : ℝ), v x = u x
```
Thus neither existence nor uniqueness has the unrestricted scope printed in the prelim. The file’s repair note also records a genuine refutation of the source for large ε: already `f=0` has no decaying solution with `u(0)=1` when `ε>3/2`. The old bank `∃! u : ℝ → ℝ` was additionally false because values for negative arguments were unconstrained. No axiom/opaque/sorry dependency was found (mentions of `sorry` occur only in comments).

#### m02J01

Lines 796–811 give exactly:
```lean
(∫ x : ℝ, φ x) = 0 ↔ ∃ ψ : TestFunction ..., ∀ x, φ x = deriv ... x
...
∃ v : Distribution ..., apm_m02j01_IsDistributionalDerivative v u
...
∃ c : ℝ, ∀ φ ..., (v₁ - v₂) φ = c * ∫ x, φ x
```
The last formula is precisely the constant distribution. No axiom/opaque/sorry dependency was found.

#### m02J03

Lines 485–500 state a uniform norm bound, the strong/norm convergence equivalence, and coefficients satisfying
```lean
∀ i : Fin (n + 1), 0 < α n i
∑ i, α n i = 1
Tendsto (fun n ↦ ∑ i : Fin (n + 1), (α n i : ℂ) • x i.val) ... x₀
```
This is the requested convex-combination conclusion with harmless zero-based indexing. Working over a complex Hilbert space is a standard valid Hilbert-space instance and does not weaken the claim’s mathematics. No axiom/opaque/sorry dependency was found.

#### m02J04

Lines 1829–1851 state Euler–Lagrange under `C²` data, the autonomous identity as derivative zero, and
```lean
(fun x ↦ Real.cosh x) ∈ apm_m02J04_admissible ∧
∀ y ∈ apm_m02J04_admissible,
  apm_m02J04_area (fun x ↦ Real.cosh x) ≤ apm_m02J04_area y
```
Lines 46–49 define admissible curves as `C¹`, nonnegative on `[0,1]`, with exactly the two required endpoint values. The documented old-statement refutation uses a nonsmooth autonomous `L` for which junk values of `deriv` make Euler–Lagrange vacuous but the Beltrami quantity discontinuous, so the smoothness repair is a correction. No axiom/opaque/sorry dependency was found.

#### m02J06

Lines 25–30 define `K` with the intended norm bound, translation modulus, and uniform support:
```lean
(∀ h : ℝ, 0 < h → ∫ x, |f (x + h) - f x| ... ≤ Real.sqrt h) ∧
(∀ x : ℝ, 1 ≤ |x| → f x = 0)
```
Lines 960–979 state the two exact estimates and `IsCompact apm_m02J06_KL1`. The source’s printed `|x|=0 ⇒ f(x)=0` would make compactness false by translations; the file transparently follows the intended `|x|≥1` condition. Current line 962 uses explicit `C∞`; the bank’s `ContDiff ℝ ⊤ φ` was analytic in this Mathlib. No axiom/opaque/sorry dependency was found.

#### m03J01

Lines 1739–1770 include the continuous linear Riesz map and all minimization/representation properties, weak-solution existence and a.e. uniqueness, and a finite constant bounding `apm_m03J01_H2size` by the `L²` norm of `F`. The regularity premise is exactly
```lean
(∀ (F ...) ... (u ...), apm_m03J01_weakSolution F u →
  ∃ H, apm_m03J01_weakHessian u.grad H) →
∃ C : ENNReal, C < ⊤ ∧ ...
```
Lines 34–37 now define test functions using explicit `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. `C∞`. The history note explains that the earlier analytic order forced compactly supported analytic test functions to vanish in positive dimension, collapsing the intended `H₀¹` construction; that semantic repair is a correction. No axiom/opaque/sorry dependency was found.

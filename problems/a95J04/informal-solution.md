# APM a95J04: Meromorphic extension past the circle of convergence — poles on boundary, bounded coefficients

## 1. Informal proof

**Why it's hard.** Part (a) seems obvious (the radius of convergence is 1, so something must go wrong on $\partial\Delta$), but needs careful argument: if $f$ extends meromorphically to $D \supset \bar{\Delta}$ with no poles on $\partial\Delta$, then $f$ would be analytic on an open set containing $\bar{\Delta}$, giving radius of convergence $> 1$. Part (b) requires extracting coefficient bounds from the order of the poles — connecting local singularity structure to global coefficient asymptotics.

**The key insight.** (a) If there were no poles on $\partial\Delta$, $f$ would be holomorphic on $D$ (which contains $\bar{\Delta}$), so the power series would converge on a disk of radius $> 1$, contradicting $R = 1$. (b) Subtract the principal parts at the simple poles on $\partial\Delta$: the remainder is holomorphic on a disk of radius $> 1$, so its coefficients decay geometrically. Each principal part $c/(z - \zeta)$ with $|\zeta| = 1$ contributes Taylor coefficients $-c/\zeta^{n+1}$, which are bounded. Sum of bounded + decaying = bounded.

**Proof.**

**(a) $f$ has at least one pole on $\partial\Delta$.**

Suppose $f$ has no poles on $\partial\Delta$. Since $f$ is meromorphic on $D \supset \bar{\Delta}$, the set of poles in $D$ is discrete. Poles in $\bar{\Delta}$ form a finite set (compact + discrete = finite). If none are on $\partial\Delta$, all poles of $f$ in $\bar{\Delta}$ are in the interior $\Delta$. But wait — $f$ is analytic on $\Delta$ (given), so $f$ has no poles in $\Delta$ either. So $f$ has no poles in $\bar{\Delta}$ at all, meaning $f$ is holomorphic on $D \supset \bar{\Delta}$. Since $D$ is open and contains $\bar{\Delta}$, there exists $r > 1$ with $D(0,r) \subseteq D$. Then $f$ is analytic on $D(0,r)$, so the radius of convergence $\geq r > 1$, contradicting $R = 1$. ✓

**(b) Simple poles on $\partial\Delta$ imply $a(n)$ is bounded.**

Let $\zeta_{1}, \ldots, \zeta_{m}$ be the poles of $f$ on $\partial\Delta$, each of order 1 with residues $c_{1}, \ldots, c_{m}$. Define the principal part:

$P(z) = \sum_{j} c_{j}/(z - \zeta_{j})$.

Then $g(z) = f(z) - P(z)$ is meromorphic on $D$ with no poles on $\partial\Delta$ (the poles at $\zeta_{j}$ are cancelled). By part (a)'s logic in reverse: since $g$ has no poles on $\partial\Delta$ and any remaining poles are in $D \setminus \bar{\Delta}$ (far from the boundary), $g$ is holomorphic on some disk $D(0, R')$ with $R' > 1$.

*Coefficients of $g$:* $g(z) = \sum b(n)z^n$ with $R' > 1$. By the Cauchy estimates: $|b(n)| \leq M/R'^n \to 0$ exponentially.

*Coefficients of $P$:* For each term $c_{j}/(z - \zeta_{j})$ with $|\zeta_{j}| = 1$:

$c_{j}/(z - \zeta_{j}) = -c_{j}/\zeta_{j} \cdot 1/(1 - z/\zeta_{j}) = -\sum_{n} (c_{j}/\zeta_{j}^{n+1}) z^n$ for $|z| < 1$.

The $n$-th coefficient is $-c_{j}/\zeta_{j}^{n+1}$, which satisfies $|-c_{j}/\zeta_{j}^{n+1}| = |c_{j}|$ (since $|\zeta_{j}| = 1$). So bounded.

*Total:* $a(n) = b(n) + \sum_{j} (-c_{j}/\zeta_{j}^{n+1})$. Each term is bounded:
- $|b(n)| \leq M/R'^n \to 0$ (bounded by $M$).
- $|\sum c_{j}/\zeta_{j}^{n+1}| \leq \sum|c_{j}|$ (constant).

So $|a(n)| \leq M + \sum|c_{j}|$ for all $n$. The sequence $a(n)$ is bounded. ✓ ∎

**What connects.** This is a fundamental result in analytic combinatorics and singularity analysis: the asymptotic behaviour of Taylor coefficients is governed by the singularities nearest to the origin. Part (a) says the "obstruction" to a larger radius of convergence must manifest as a pole on $\partial\Delta$ (if the extension is meromorphic). Part (b) says simple poles give bounded coefficients (in fact, $a(n)$ converges to $-\sum c_{j}/\zeta_{j}^{n+1}$, which oscillates but stays bounded). Poles of higher order $k$ would give $|a(n)| = O(n^{k-1})$ — polynomial growth in $n$. This connects to the transfer theorems of Flajolet-Odlyzko in analytic combinatorics, where singularity type determines coefficient asymptotics.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Metric Set

noncomputable section

/-- (a) f must have at least one pole on ∂Δ. -/
theorem exists_pole_on_boundary
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_mero : ∀ z ∈ D, z ∉ sphere (0 : ℂ) 1 →
      DifferentiableAt ℂ f z ∨ ∃ n : ℕ, 0 < n ∧ DifferentiableAt ℂ (fun w => (w - z) ^ n * f w) z)
    (hR : FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (iteratedDeriv n f 0 / ↑(n !))) = 1) :
    ∃ ζ ∈ sphere (0 : ℂ) 1, ¬DifferentiableAt ℂ f ζ := by
  sorry

/-- (b) Simple poles on ∂Δ imply bounded coefficients. -/
theorem coefficients_bounded_of_simple_poles
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_simple : ∀ ζ ∈ sphere (0 : ℂ) 1, ¬DifferentiableAt ℂ f ζ →
      DifferentiableAt ℂ (fun w => (w - ζ) * f w) ζ) :
    ∃ M : ℝ, ∀ n : ℕ, ‖iteratedDeriv n f 0 / ↑(n !)‖ ≤ M := by
  sorry

/-- If f is holomorphic on D ⊃ Δ̄, radius of convergence > 1. -/
lemma radius_gt_one_of_holo_on_nbhd
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) :
    1 < FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (iteratedDeriv n f 0 / ↑(n !))) := by
  sorry

/-- Taylor coefficients of 1/(z - ζ) with |ζ| = 1 are bounded. -/
lemma coefficients_bounded_simple_pole
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c : ℂ} :
    ∃ M, ∀ n : ℕ, ‖-c / ζ ^ (n + 1)‖ ≤ M := by
  sorry

/-- Cauchy bound: coefficients of f holomorphic on D(0, R') with R' > 1
    decay geometrically. -/
lemma coefficients_decay_of_larger_radius
    {g : ℂ → ℂ} {R' : ℝ} (hR' : 1 < R')
    (hg : DifferentiableOn ℂ g (ball 0 R')) :
    ∃ M : ℝ, ∀ n : ℕ, ‖iteratedDeriv n g 0 / ↑(n !)‖ ≤ M / R' ^ n := by
  sorry

/-- The poles on the compact set ∂Δ form a finite set. -/
lemma poles_on_circle_finite
    {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf_mero : ∀ z ∈ D, DifferentiableAt ℂ f z ∨
      ∃ n, 0 < n ∧ DifferentiableAt ℂ (fun w => (w-z)^n * f w) z) :
    Set.Finite {ζ ∈ sphere (0 : ℂ) 1 | ¬DifferentiableAt ℂ f ζ} := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `FormalMultilinearSeries.radius` — radius of convergence
- `DifferentiableOn ℂ f S` / `DifferentiableAt ℂ f z` — analyticity
- `iteratedDeriv n f z` — $n$-th derivative (for Taylor coefficients $a(n) = f^{(n)}(0)/n!$)
- `Metric.sphere (0 : ℂ) 1` — unit circle $\partial\Delta$
- `Metric.closedBall (0 : ℂ) 1` — closed unit disk

**Key lemmas:**
- `FormalMultilinearSeries.le_radius_of_bound` — if $|a_{n}| \leq M/R^{n}$ then radius $\geq R$ (for part (a) contrapositive)
- `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` — Cauchy estimates: $|f^{(n)}(0)/n!| \leq \max|f|/R^{n}$ (for the remainder $g$)
- `isCompact_sphere` — $\partial\Delta$ is compact (for finiteness of poles)
- `IsCompact.finite` — finite discrete subset of compact set
- `norm_pow` — $\|\zeta^n\| = \|\zeta\|^n = 1$ when $|\zeta| = 1$ (for bounding pole coefficients)
- `norm_div` — $\|c/\zeta^{n+1}\| = |c|/|\zeta|^{n+1} = |c|$
- `geom_series_def` — $1/(1-z/\zeta) = \sum (z/\zeta)^n$ (for Taylor expansion of principal part)
- `DifferentiableOn.sub` — $f - P$ is differentiable

**Tactic hints:**
- `by_contra h; push_neg at h` — for part (a) contrapositive
- `have := radius_gt_one_of_holo_on_nbhd hD hD_contains (by exact ...)` — contradiction with $R=1$
- `refine ⟨M_g + ∑ j, ‖c j‖, fun n => ?_⟩` — providing the bound in part (b)
- `calc ‖a(n)‖ = ‖b(n) + Σ ...‖ ≤ ‖b(n)‖ + Σ ‖...‖ ≤ ...` — triangle inequality chain
- `simp [norm_pow, hζ]` — simplifying $|\zeta^n| = 1$
- `gcongr` — monotonicity steps
- `linarith` — combining bounds
- `exact?` — finding Cauchy estimate or radius lemma

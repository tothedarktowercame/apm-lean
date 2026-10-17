

# APM a92J04: A self-map of the disk tangent to the identity must be the identity

## 1. Informal proof

**Why it's hard.** The function $f(z) = z + \sum_{n\geq 2} a_{n}z^{n}$ maps $\Delta$ into $\Delta$ (since $|f(z)| < 1$ for $|z| < 1$), fixes the origin with $f'(0) = 1$. The Schwarz lemma gives $|f(z)| \leq |z|$ for self-maps fixing 0 with $|f'(0)| \leq 1$, but equality $|f'(0)| = 1$ in the Schwarz lemma only tells us $f$ is a rotation $f(z) = e^{i\theta}z$ — and here $\theta = 0$ since $f'(0) = 1$. The difficulty is that the power series has no linear correction (the coefficient of $z$ is exactly 1), and we must show all higher-order terms vanish. This requires the rigidity case of the Schwarz lemma.

**The key insight.** Apply the Schwarz lemma to $f(z)/z$. Since $f(0) = 0$ and $|f(z)| < 1$ for $|z| < 1$, the Schwarz lemma gives $|f(z)| \leq |z|$, with equality at any interior point iff $f(z) = e^{i\theta}z$. Since $f'(0) = 1$, we get $\theta = 0$ and $f(z) = z$ identically.

**Proof.**

Define $f(z) = z + \sum_{n=2}^\infty a_{n}z^{n}$ for $z \in \Delta$. The absolute convergence of the series in $\Delta$ means $f$ is analytic on $\Delta$.

*Step 1: $f$ maps $\Delta$ into $\Delta$.* By hypothesis, $|f(z)| < 1$ for all $z \in \Delta$. Also $f(0) = 0$.

*Step 2: Apply the Schwarz lemma.* Since $f : \Delta \to \Delta$ is analytic with $f(0) = 0$, the Schwarz lemma states:
- $|f(z)| \leq |z|$ for all $z \in \Delta$, and
- $|f'(0)| \leq 1$, with equality in either condition iff $f(z) = e^{i\theta}z$ for some real $\theta$.

*Step 3: Check the equality case.* We have $f'(0) = 1$, so $|f'(0)| = 1$. By the equality case of the Schwarz lemma, $f(z) = e^{i\theta}z$ for some $\theta \in \mathbb{R}$. Since $f'(0) = e^{i\theta} = 1$, we get $\theta = 0$, hence $f(z) = z$ for all $z \in \Delta$.

*Step 4: Conclude.* $f(z) = z$ means $z + \sum_{n\geq 2} a_{n}z^{n} = z$, so $\sum_{n\geq 2} a_{n}z^{n} = 0$ for all $z \in \Delta$. By the identity theorem for power series (or by evaluating derivatives at 0), $a_{n} = 0$ for all $n \geq 2$. ∎

**Theorems used:** The Schwarz lemma (including its equality/rigidity case) and the identity theorem for analytic functions.

**What connects.** This problem is about the rigidity of holomorphic self-maps of the disk. The Schwarz lemma is the foundational rigidity result: a disk self-map fixing the origin is at most a rotation, and only a rotation if $|f'(0)| = 1$. The condition $f'(0) = 1$ (not just $|f'(0)| = 1$) pins the rotation angle to zero, forcing $f = \mathrm{id}$. This is the infinitesimal version of the fact that the automorphism group of the disk is $PSU(1,1)$, a three-real-parameter group, and fixing a point with a specified derivative leaves no freedom. The result generalises: if $f : \Delta \to \Delta$ is analytic with $f(0) = 0$ and $f(z) = z + O(z^{k+1})$, then $f(z) = z$ (no higher-order tangency to the identity is possible for disk self-maps). This connects to the Denjoy-Wolff theorem and iteration theory of holomorphic maps.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open Complex Metric Set Filter

noncomputable section

/-- Schwarz lemma with equality case: if f : Δ → Δ is analytic,
    f(0) = 0, and |f'(0)| = 1, then f(z) = e^{iθ}z. -/
lemma schwarz_equality
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1) :
    ∃ θ : ℝ, ∀ z ∈ ball (0 : ℂ) 1, f z = exp (I * θ) * z := by
  sorry

/-- Main theorem: if f(z) = z + Σ_{n≥2} aₙzⁿ maps Δ into Δ,
    then aₙ = 0 for all n ≥ 2, i.e., f(z) = z. -/
theorem disk_selfmap_tangent_identity
    {a : ℕ → ℂ}
    (hconv : ∀ z ∈ ball (0 : ℂ) 1,
      Summable (fun n => a n * z ^ n))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1,
      ‖z + ∑' n, a (n + 2) * z ^ (n + 2)‖ < 1) :
    ∀ n, 2 ≤ n → a n = 0 := by
  sorry

/-- Equivalent formulation: f = id on the disk. -/
theorem disk_selfmap_tangent_identity'
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : deriv f 0 = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = z := by
  sorry

/-- The Schwarz lemma: |f'(0)| ≤ 1 for disk self-maps fixing 0. -/
lemma schwarz_deriv_le_one
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf_zero : f 0 = 0) :
    ‖deriv f 0‖ ≤ 1 := by
  sorry

/-- Vanishing of power series coefficients from the identity f = id. -/
lemma power_series_eq_zero_of_tsum_eq_zero
    {a : ℕ → ℂ}
    (hconv : ∀ z ∈ ball (0 : ℂ) 1, Summable (fun n => a n * z ^ n))
    (hzero : ∀ z ∈ ball (0 : ℂ) 1, ∑' n, a n * z ^ n = 0) :
    ∀ n, a n = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f (ball 0 1)` — holomorphicity on the disk
- `MapsTo f (ball 0 1) (ball 0 1)` — $f$ maps $\Delta$ into $\Delta$
- `Summable` — absolute convergence of the power series
- `tsum` — the infinite sum $\sum a_{n}z^{n}$
- `Metric.ball (0 : ℂ) 1` — the open unit disk
- `Complex.exp`, `Complex.I` — for the rotation $e^{i\theta}$

**Key lemmas:**
- `Complex.norm_le_norm_of_mapsTo_ball_self` — Schwarz lemma: $|f(z)| \leq |z|$. In `Mathlib.Analysis.Complex.Schwarz`
- `Complex.norm_deriv_le_one_of_mapsTo_ball_self` — $|f'(0)| \leq 1$. In `Mathlib.Analysis.Complex.Schwarz`
- `Complex.eq_smul_of_mapsTo_ball_self` — equality case: $|f'(0)| = 1 \Longrightarrow f(z) = cz$ with $|c| = 1$. In `Mathlib.Analysis.Complex.Schwarz`
- `HasFPowerSeriesOnBall.eq_zero_of_eventually` / `AnalyticAt.eq_of_eventuallyEq` — identity theorem for analytic functions / power series
- `tsum_eq_zero_iff` — conditions for a tsum to vanish
- `HasSum.unique` — uniqueness of power series coefficients
- `FormalMultilinearSeries.coeff_eq_zero` — extracting individual coefficients
- `Complex.ofReal_cos`, `Complex.ofReal_sin` — for $e^{i\theta} = \cos \theta + i \sin \theta$
- `norm_eq_one_iff_ne_zero` — for $|f'(0)| = 1$

**Tactic hints:**
- `have h_schwarz := Complex.eq_smul_of_mapsTo_ball_self hf_holo hf_maps hf_zero hf_deriv` — invoke the Schwarz equality case
- `obtain ⟨θ, hθ⟩ := h_schwarz` — extract the rotation angle
- `have : exp (I * θ) = 1 := by ...` — use $f'(0) = 1$ to pin $\theta = 0$
- `simp [mul_comm, one_mul] at hθ` — simplify $f(z) = 1 \cdot z = z$
- `ext` — for power series coefficient comparison
- `exact?` — finding the right Schwarz lemma variant
- `norm_num` — for $|1| = 1$
- `ring` — for algebraic simplifications
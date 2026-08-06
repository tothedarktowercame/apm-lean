import Mathlib

/-!
# APM a97J05: Coefficients controlled by a simple pole

## Statement repairs

None.

## Encoding questions

None. The generic complex-analysis API in this Mathlib build does not expose a
standalone residue function, so “simple pole with residue `A`” is defined by
its exact local Laurent principal part: `A ≠ 0` and
`f(z) = A/(z-z₀) + g(z)` punctured-locally for an analytic `g`. This retains
both pole order one and the residue rather than replacing either by a weaker
surrogate.
-/

open Filter Metric Set Topology

noncomputable section

/-- `f` has a pole of order one at `z₀`, with residue `A`. -/
def apm_a97J05_hasSimplePoleWithResidue
    (f : ℂ → ℂ) (z₀ A : ℂ) : Prop :=
  A ≠ 0 ∧ ∃ g : ℂ → ℂ,
    AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z = A / (z - z₀) + g z

theorem apm_a97j05
    (f : ℂ → ℂ) (A : ℂ) (a : ℕ → ℂ)
    (hanalytic : AnalyticOn ℂ f (ball 0 2 \ ({1} : Set ℂ)))
    (hpole : apm_a97J05_hasSimplePoleWithResidue f 1 A)
    (hseries : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n : ℕ => a n * z ^ n) (f z)) :
    Tendsto a atTop (𝓝 (-A)) := by
  obtain ⟨hA_ne, g₀, hg₀, heq_pole⟩ := hpole
  -- It suffices to show a n + A → 0, then a n → -A.
  suffices hb : Tendsto (fun n => a n + A) atTop (𝓝 (0 : ℂ)) by
    have hlim : Tendsto (fun n => (a n + A) + (-A)) atTop (𝓝 (0 + (-A))) :=
      hb.add tendsto_const_nhds
    have h0A : (0 : ℂ) + (-A) = -A := by ring
    have heq : (fun n => (a n + A) + (-A)) =ᶠ[atTop] a := by
      filter_upwards with n; ring
    exact h0A ▸ Tendsto.congr' heq hlim
  -- Now prove: a n + A → 0.
  -- Key idea: f is AnalyticOnNhd on ball 0 2 \ {1}, so f is AnalyticAt at 0.
  -- f has a power series q at 0 with some positive radius R.
  -- On ball 0 1, both f(z) = ∑ a_n z^n (from hseries) and f(z) = ∑ q.coeff(n) z^n.
  -- By uniqueness, q.coeff(n) = a_n.
  -- Similarly, A/(z-1) has power series ofScalars (-A) at 0 with radius 1.
  -- So h = f - A/(z-1) has power series with coefficients q.coeff(n) - (-A) = a_n + A at 0,
  -- with radius = min(R, 1) (initially).
  -- But h extends analytically past z=1 (since h = g₀ near 1), so h is AnalyticAt at 1.
  -- This means the radius of convergence of h's series is > 1.
  -- Then a_n + A → 0.

  -- Step 1: f is AnalyticAt at 0.
  have h_isOpen_punctured : IsOpen (ball (0 : ℂ) 2 \ ({1} : Set ℂ)) :=
    isOpen_ball.sdiff isClosed_singleton
  have f_analyticAt_0 : AnalyticAt ℂ f 0 := by
    have h00 : (0 : ℂ) ∈ ball (0 : ℂ) 2 \ ({1} : Set ℂ) := by
      simp [mem_ball]
    exact h_isOpen_punctured.analyticOn_iff_analyticOnNhd.mp hanalytic 0 h00
  -- Step 2: Build the extended function G on ball 0 2 that is analytic everywhere.
  -- G(z) = f(z) - A/(z-1) for z ≠ 1, and G(1) = g₀(1).
  -- Show G is AnalyticOnNhd on ball 0 2.
  obtain ⟨ρ, ρ_pos, hρ⟩ := hg₀.exists_ball_analyticOnNhd
  -- ρ > 0, g₀ is AnalyticOnNhd on ball 1 ρ.
  -- Define G as g₀ on ball 1 (ρ/2) and f(z) - A/(z-1) elsewhere.
  -- Actually, simpler: we know h(z) = f(z) - A/(z-1) = g₀(z) on 𝓝[≠] 1 ∩ ball 1 ρ.
  -- So g₀ is the analytic continuation of h across z=1.
  -- Let's work with g₀ directly. g₀ is AnalyticAt at 1, and near 0, g₀ agrees with h.
  -- But wait — g₀ and h only agree NEAR z=1, not near z=0.
  -- We need to show g₀ agrees with h on a connected set.

  -- Let me try yet another approach: show h is AnalyticAt at 0 with radius > 1.
  -- The radius of h's power series at 0 is at least as large as the distance
  -- from 0 to the nearest singularity of h. Since h has no singularities in ball 0 2,
  -- the radius is ≥ 2 > 1.

  -- Key lemma: if h is AnalyticOnNhd on a set containing a path from 0 to z,
  -- then h is AnalyticAt at z. Actually, what I really need is:
  -- h's power series at 0 has radius ≥ 2.

  -- Actually, the simplest approach: h is analytic on ball 0 2 (after extending at 1).
  -- So h has HasFPowerSeriesOnBall on ball 0 r for any r < 2.
  -- Pick r = 3/2. Then h's coefficients → 0.
  -- And on ball 0 1, h(z) = ∑ (a n + A) z^n, so by uniqueness,
  -- h's coefficients are a n + A.
  -- Therefore a n + A → 0.

  -- To make this work, I need:
  -- (a) h is analytic on ball 0 2 (the extension).
  -- (b) On ball 0 1, h(z) = ∑ (a n + A) z^n.

  -- For (b): h(z) = f(z) - A/(z-1) = ∑ a n z^n - (-A) ∑ z^n = ∑ (a n + A) z^n.
  -- Need: A/(z-1) = -A * (1/(1-z)) = -A * ∑ z^n on ball 0 1.

  -- For (a): this is the gluing argument.
  -- On ball 0 2 \ {1}: h = f - A/(z-1), both analytic.
  -- Near z = 1: h = g₀ (eventually), g₀ analytic.
  -- Define G piecewise and show AnalyticOnNhd.

  -- PARTIAL (closer hop 2): bridge still open. All APIs confirmed available.
  -- Assembly attempted but exceeds budget. Enriched boundary below.
  --
  -- Detailed step-by-step with Mathlib API names:
  --
  -- Step A: h(z) := f(z) - A/(z-1) is differentiable on ball 0 2 \\ {1}.
  --   Need: `DifferentiableOn ℂ h (ball 0 2 \\ {1})`.
  --   From: `hanalytic` gives DifferentiableOn f on ball 0 2 \\ {1}.
  --   And: z ↦ A/(z-1) is differentiable on ball 0 2 \\ {1} (elementary).
  --   So: h = f - A/(z-1) is differentiable there by `DifferentiableOn.sub`.
  --
  -- Step B: h̃(z) = update h 1 (g₀ 1) is analytic at 1.
  --   Use `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`:
  --   - h̃ is differentiable on a punctured nhd of 1 (from Step A + update)
  --   - h̃ is continuous at 1 (since h = g₀ near 1, and update sets h̃(1) = g₀(1))
  --   ⟹ h̃ is AnalyticAt at 1.
  --
  -- Step C: h̃ is AnalyticOn ℂ on all of ball 0 2.
  --   On ball 0 2 \\ {1}: h̃ = h, differentiable.
  --   At 1: h̃ is AnalyticAt from Step B.
  --   Combine via `AnalyticOn` definition.
  --
  -- Step D: Apply a96J09's `apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk`:
  --   closedBall 0 1 ⊆ ball 0 2, h̃ is AnalyticOn on ball 0 2 (open).
  --   ⟹ ‖iteratedDeriv n h̃ 0‖ / n! → 0.
  --
  -- Step E: Identify coefficients. On ball 0 1:
  --   h̃(z) = f(z) - A/(z-1) = (∑ aₙzⁿ) - (-A)(∑ zⁿ) = ∑(aₙ+A)zⁿ.
  --   By uniqueness of power series: iteratedDeriv n h̃ 0 / n! = aₙ + A.
  --   From Step D: aₙ + A → 0.
  --
  -- Blocker: Step B requires careful handling of Function.update and the
  -- `∀ᶠ z in 𝓝[≠] 1, f z = A/(z-1) + g z` hypothesis to extract
  -- continuity of h̃ at 1. Step E requires power series uniqueness
  -- (`HasSum.geometric` for 1/(1-z) + coefficient comparison).
  -- Each is individually tractable (~15 lines) but the total is ~60-80 lines
  -- and requires imports from a96J09 + RemovableSingularity.
  sorry

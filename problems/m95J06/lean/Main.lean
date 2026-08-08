import Mathlib

open Filter

/-!
# APM m95J06 — finite-dimensional `ℓᵖ` limits and Hilbert norms

## Statement repairs

None.
-/

noncomputable def apm_m95j06_lpNorm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.rpow (∑ i, Real.rpow |x i| p) (1 / p)

noncomputable def apm_m95j06_linfNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun i => |x i|)

/-- On a nonempty finite coordinate type, the supremum in the custom
`ℓ∞` norm is attained by one of the coordinates. -/
lemma apm_m95J06_exists_abs_eq_linfNorm {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    ∃ i, |x i| = apm_m95j06_linfNorm x := by
  let i₀ : Fin n := ⟨0, hn⟩
  letI : Nonempty (Fin n) := ⟨i₀⟩
  have hrange_nonempty : (Set.range fun i : Fin n => |x i|).Nonempty :=
    Set.range_nonempty _
  have hrange_finite : (Set.range fun i : Fin n => |x i|).Finite :=
    Set.finite_range _
  have hmem : sSup (Set.range fun i : Fin n => |x i|) ∈
      Set.range fun i : Fin n => |x i| :=
    hrange_nonempty.csSup_mem hrange_finite
  rcases hmem with ⟨i, hi⟩
  exact ⟨i, hi⟩

/-- Every coordinate is bounded by the custom finite `ℓ∞` norm. -/
lemma apm_m95J06_abs_le_linfNorm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ apm_m95j06_linfNorm x := by
  exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩

/-- The cardinality factor occurring in the finite power-mean upper bound
tends to one for a real exponent. -/
lemma apm_m95J06_tendsto_card_rpow_one_div (n : ℕ) (hn : 0 < n) :
    Tendsto (fun p : ℝ => Real.rpow (n : ℝ) (1 / p)) atTop (nhds 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : Tendsto (fun p : ℝ => (1 : ℝ) / p) atTop (nhds 0) :=
    by simpa [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun p : ℝ => p⁻¹) atTop (nhds 0))
  have hmul : Tendsto (fun p : ℝ => Real.log (n : ℝ) * (1 / p)) atTop
      (nhds 0) := by
    convert tendsto_const_nhds.mul hdiv using 1 <;> simp
  convert Real.continuous_exp.continuousAt.tendsto.comp hmul using 1
  · funext p
    change (n : ℝ) ^ (1 / p) = _
    rw [Real.rpow_def_of_pos hnR]
    rfl
  · simp

/-- For nonnegative real exponents, the finite power sum is bounded by the
number of coordinates times the corresponding power of the attained maximum.
This is the inner inequality needed for the upper half of the squeeze. -/
lemma apm_m95J06_sum_rpow_le_card_mul_linfNorm_rpow {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) {p : ℝ} (hp : 0 ≤ p) :
    (∑ i, Real.rpow |x i| p) ≤
      (n : ℝ) * Real.rpow (apm_m95j06_linfNorm x) p := by
  obtain ⟨i₀, hi₀⟩ := apm_m95J06_exists_abs_eq_linfNorm hn x
  have hmax_nonneg : 0 ≤ apm_m95j06_linfNorm x := by
    rw [← hi₀]
    exact abs_nonneg _
  calc
    (∑ i, Real.rpow |x i| p) ≤
        ∑ _i : Fin n, Real.rpow (apm_m95j06_linfNorm x) p := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (abs_nonneg _)
        (apm_m95J06_abs_le_linfNorm x i) hp
    _ = (n : ℝ) * Real.rpow (apm_m95j06_linfNorm x) p := by simp

/-- In a real inner-product space, the norm is differentiable away from the
origin. This is the identity-map specialization of Mathlib's chain rule for
the Hilbert norm. -/
lemma apm_m95J06_differentiableAt_norm
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : H) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : H => ‖y‖) x := by
  exact differentiableAt_id.norm ℝ hx

theorem apm_m95j06 :
    (∀ (n : ℕ), 0 < n → ∀ x : Fin n → ℝ,
      Tendsto (fun p : ℝ => apm_m95j06_lpNorm p x) atTop
        (nhds (apm_m95j06_linfNorm x))) ∧
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
      ∀ x : H, x ≠ 0 → DifferentiableAt ℝ (fun y : H => ‖y‖) x) := by
  constructor
  ·
  -- SKIPPED: two-part finite-dimensional norm problem.
  -- (a) ‖x‖_p → ‖x‖_∞ as p→∞: the p-norm approaches the max norm.
  -- (b) Differentiability of norm at x≠0 in inner product space: ‖·‖ is
  --     differentiable away from 0, with derivative x/‖x‖.
  -- Blocker: (a) needs limit computation for (∑|x_i|^p)^{1/p} as p→∞.
  -- (b) might be tractable — norm is differentiable at x≠0 via inner product.
  -- APIs: `Real.rpow`, `sSup`, `DifferentiableAt`, `InnerProductSpace`.
  --
  -- Closer hop 1 closes the second conjunct independently as
  -- `apm_m95J06_differentiableAt_norm`, by specializing Mathlib's
  -- `DifferentiableAt.norm` to the identity map.
  --
  -- For the first conjunct, proved sibling `a93J04` contains the general
  -- finite-measure theorem `tendsto_eLpNorm_atTop`, while `bpm-1-3-1` contains
  -- a direct finite power-mean squeeze for natural exponents. Neither is
  -- importable here in the exact custom encoding: one must identify the
  -- counting-measure `eLpNorm` with this real-exponent finite sum, identify its
  -- essential supremum with the `sSup` of the finite range, and transport the
  -- ENNReal exponent limit back to real `p → atTop`. Searches of
  -- `LEMMA-INDEX.md`, Mathlib, `ConstructionTargets/`, other siblings, and git
  -- history found no compiled bridge performing those conversions. The frozen
  -- statement is unchanged.
  --
  -- CLOSER HOP 2: the finite-supremum and real-exponent asymptotic pieces now
  -- compile locally. `apm_m95J06_exists_abs_eq_linfNorm` proves that the
  -- custom `sSup` is attained, `apm_m95J06_abs_le_linfNorm` bounds every
  -- coordinate by it, and `apm_m95J06_tendsto_card_rpow_one_div` proves the
  -- cardinality factor `n^(1/p) → 1` directly for `p : ℝ`. This goes beyond
  -- the previous representation-only search and leaves precisely the two
  -- eventual power-mean inequalities for `Real.rpow`, including the zero-max
  -- branch and the positive-max factorization. No packaged lemma was found
  -- for that final custom-sum squeeze, so the first conjunct remains open.
  --
  -- CLOSER HOP 3 compiles the inner upper power-mean inequality as
  -- `apm_m95J06_sum_rpow_le_card_mul_linfNorm_rpow`. It uses attainment of
  -- the maximum from hop 2, coordinatewise `Real.rpow_le_rpow`, and a finite
  -- sum comparison to show `Σ |xᵢ|^p ≤ n · ‖x‖∞^p` for every `p ≥ 0`.
  -- Passing this inequality through the outer real power still requires the
  -- separate zero-maximum and positive-maximum normalization branches. The
  -- lower bound and final squeeze therefore remain open without an unproved
  -- assertion; the frozen statement is unchanged.
    sorry
  · intro H _ _ x hx
    exact apm_m95J06_differentiableAt_norm H x hx

/-
! # APM a92J02: Convergence in measure implies a.e. convergence of a subsequence

Let f₁, f₂, … and f be Lebesgue measurable functions. We say fₙ converges to f
in measure if for each ε > 0 there exists N such that for n > N,
m({x | |fₙ(x) - f(x)| > ε}) < ε. Show that if fₙ converges to f in measure,
then some subsequence converges to f almost everywhere.

## Proof strategy

Mathlib's `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` proves exactly
this result for Mathlib's notion of convergence in measure (which uses `edist`
and `≤` rather than `|· - ·|` and `>`). We:

1. Define `ConvergesInMeasure` matching the problem's ε-N formulation.
2. Bridge: `ConvergesInMeasure` ⟺ Mathlib's `TendstoInMeasure`.
3. Apply `exists_seq_tendsto_ae` to extract the a.e.-convergent subsequence.
-/

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter Set Topology

open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Convergence in measure (problem statement formulation):

    For each ε > 0, there exists N such that for all n > N,
    μ({x | |fₙ(x) - f(x)| > ε}) < ε. -/
def ConvergesInMeasure (f : ℕ → α → ℝ) (g : α → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → μ {x | ε < |f n x - g x|} < ENNReal.ofReal ε

/-- The problem's convergence-in-measure implies Mathlib's `TendstoInMeasure`. -/
lemma convergesInMeasure.tendstoInMeasure
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hcm : ConvergesInMeasure (μ := μ) f g) :
    TendstoInMeasure μ f atTop g := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro b hb
  by_cases hb_top : b = ⊤
  · -- If b = ⊤, trivially done: μ(...) ≤ ⊤
    exact ⟨0, fun n _ => by rw [hb_top]; exact le_top⟩
  -- b ≠ ⊤, b > 0, so b.toReal > 0.
  have hb0 : b ≠ 0 := hb.ne'
  have hb_real : 0 < b.toReal := ENNReal.toReal_pos hb0 hb_top
  -- Pick δ: 0 < δ < ε, δ ≤ b.toReal
  obtain ⟨δ, hδ_pos, hδ_lt_ε, hδ_le_btr⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ ≤ b.toReal := by
    refine ⟨min ε b.toReal / 2, ?_, ?_, ?_⟩
    · exact div_pos (lt_min hε hb_real) (by norm_num)
    · linarith [min_le_left ε b.toReal]
    · linarith [min_le_right ε b.toReal]
  have hδ_le_b : ENNReal.ofReal δ ≤ b := by
    rw [ENNReal.ofReal_le_iff_le_toReal hb_top]
    exact hδ_le_btr
  obtain ⟨N₀, hN₀⟩ := hcm δ hδ_pos
  -- Output N₀ as witness; for n ≥ N₀, if n = N₀ it still works because
  -- the set with ε ≤ dist is contained in the set with δ < dist.
  -- But hN₀ requires N₀ < n. So output N₀ + 1... actually n ≥ N₀ doesn't give N₀ < n.
  -- Instead, output N₀ itself; for n ≥ N₀ we have n > N₀ when n ≥ N₀ + 1.
  -- Actually ENNReal.tendsto_atTop_zero asks ∀ n ≥ N. So we need N such that for n ≥ N.
  -- hN₀ gives: N₀ < n → bound. So for n ≥ N₀ + 1, bound holds. Use N₀ + 1.
  -- But wait: the sets use dist, not |· - ·|. On ℝ, dist a b = |a - b|.
  refine ⟨N₀ + 1, fun n hn => ?_⟩
  -- hn : n ≥ N₀ + 1, so N₀ < n
  have hN₀n : N₀ < n := by omega
  -- On ℝ: dist (f n x) (g x) = |f n x - g x|
  -- {x | ε ≤ dist (f n x) (g x)} = {x | ε ≤ |f n x - g x|}
  have h_set_subset :
      {x | ε ≤ dist (f n x) (g x)} ⊆ {x | δ < |f n x - g x|} := by
    intro x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    rw [Real.dist_eq] at hx
    exact lt_of_lt_of_le hδ_lt_ε hx
  calc μ {x | ε ≤ dist (f n x) (g x)}
      ≤ μ {x | δ < |f n x - g x|} := measure_mono h_set_subset
    _ ≤ ENNReal.ofReal δ := (hN₀ n hN₀n).le
    _ ≤ b := hδ_le_b

/-- Conversely, Mathlib's `TendstoInMeasure` implies the problem's
    convergence-in-measure. -/
lemma tendstoInMeasure.convergesInMeasure
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (htm : TendstoInMeasure μ f atTop g) :
    ConvergesInMeasure (μ := μ) f g := by
  intro ε hε
  have hε2_pos : 0 < ε / 2 := by linarith
  -- {x | ε < |fₙ x - g x|} ⊆ {x | ε/2 ≤ |fₙ x - g x|} since ε/2 < ε
  have h_key : ∀ n, {x | ε < |f n x - g x|} ⊆ {x | ε / 2 ≤ |f n x - g x|} := by
    intro n x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    exact le_of_lt (lt_trans (by linarith) hx)
  -- From TendstoInMeasure at threshold ENNReal.ofReal(ε/2):
  have h_tendsto := htm (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr hε2_pos)
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr hε2_pos)
  -- hN : ∀ n ≥ N, μ {x | ENNReal.ofReal (ε/2) ≤ edist (f n x) (g x)} ≤ ofReal ε
  -- Need: ∀ n > N, μ {x | ε < |f n x - g x|} < ofReal ε
  refine ⟨N, fun n hn => ?_⟩
  -- On ℝ: edist a b = ofReal (dist a b) and dist a b = |a - b|
  have h_set_eq :
      {x | ENNReal.ofReal (ε / 2) ≤ edist (f n x) (g x)} = {x | ε / 2 ≤ |f n x - g x|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg, Real.dist_eq]
  -- hn : N < n, hN expects n ≥ N
  have hNn : N ≤ n := le_of_lt hn
  calc μ {x | ε < |f n x - g x|}
      ≤ μ {x | ε / 2 ≤ |f n x - g x|} := measure_mono (h_key n)
    _ = μ {x | ENNReal.ofReal (ε / 2) ≤ edist (f n x) (g x)} := by rw [h_set_eq]
    _ ≤ ENNReal.ofReal (ε / 2) := hN n hNn
    _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith)

/-- **Main theorem**: convergence in measure implies a.e. convergence
    of a subsequence.

    Direct application of Mathlib's
    `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`. -/
theorem convergesInMeasure.exists_subseq_ae_tendsto
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hcm : ConvergesInMeasure (μ := μ) f g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => f (φ k) x) atTop (𝓝 (g x)) :=
  (convergesInMeasure.tendstoInMeasure hcm).exists_seq_tendsto_ae

end

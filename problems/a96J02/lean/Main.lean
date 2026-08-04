/-
! # APM a96J02: A+B contains an open interval when μ(A),μ(B) > 0

## Problem

Let A and B be Lebesgue measurable subsets of ℝ having positive Lebesgue
measure. Prove that A+B = {a+b | a∈A, b∈B} contains a nonempty open interval.

## Proof (Steinhaus's theorem)

Step 1: Reduce to finite measure. Since A = ⋃_n (A ∩ [-n,n]) and μ(A) > 0,
some A' := A ∩ [-n,n] has 0 < μ(A') < ∞. Similarly find B' ⊂ B.

Step 2: Define f(x) = μ(A' ∩ (x - B')).

Step 3: By Fubini, ∫ f(x) dx = μ(A')μ(B') > 0.

Step 4: f is continuous (L¹ translation continuity via DCT).

Step 5: Since ∫f > 0, f(x₀) > 0 for some x₀. By continuity, f > 0 on an
open neighborhood of x₀. f(x) > 0 ⟹ A' ∩ (x - B') ≠ ∅ ⟹ x ∈ A' + B' ⊂ A+B.

## Dependencies

- DCT for continuity of convolution
  (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
- Monotone approximation for bounded subset reduction
  (Memory: math-informal/monotone-approximation)
-/

import Mathlib

open Set MeasureTheory Filter Topology Pointwise ENNReal

noncomputable section

/-- If A has positive measure, then A ∩ Icc(-n,n) has positive measure for
some n. -/
lemma exists_pos_measure_bounded_subset (A : Set ℝ) (hA : MeasurableSet A)
    (hApos : 0 < volume A) :
    ∃ n : ℕ, 0 < volume (A ∩ Set.Icc (-(n : ℝ)) n) := by
  have hcover : A ⊆ ⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n := by
    intro x hx
    simp only [mem_iUnion]
    refine ⟨Nat.ceil (abs x + 1), ⟨hx, ?_, ?_⟩⟩
    · have : (abs x : ℝ) ≤ Nat.ceil (abs x + 1) := by
        apply le_trans (by linarith : abs x ≤ abs x + 1)
        exact Nat.le_ceil (abs x + 1)
      linarith [neg_abs_le x]
    · apply le_trans (le_abs_self x)
      exact le_trans (by linarith : abs x ≤ abs x + 1) (Nat.le_ceil (abs x + 1))
  have hpos_union : 0 < volume (⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n) :=
    hApos.trans_le (measure_mono hcover)
  by_contra h
  push_neg at h
  have hzero : ∀ n : ℕ, volume (A ∩ Set.Icc (-(n : ℝ)) n) = 0 := fun n =>
    le_antisymm (h n) bot_le
  have hle : volume (⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n) ≤
      ∑' n : ℕ, volume (A ∩ Set.Icc (-(n : ℝ)) n) :=
    measure_iUnion_le _
  rw [show ∑' n : ℕ, volume (A ∩ Set.Icc (-(n : ℝ)) n) = 0 from by simp [hzero]] at hle
  have : volume (⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n) = 0 :=
    le_antisymm hle bot_le
  rw [this] at hpos_union
  exact absurd hpos_union (lt_irrefl 0)

/-- Integrability of indicator of a finite-measure measurable set. -/
lemma integrable_indicator_of_finite_measure (s : Set ℝ) (hs : MeasurableSet s)
    (hsfin : volume s < ⊤) :
    Integrable (indicator s (1 : ℝ → ℝ)) volume := by
  rw [integrable_indicator_iff hs]
  refine ⟨aestronglyMeasurable_const, ?_⟩
  unfold HasFiniteIntegral
  simp [hsfin]

/-- **Steinhaus's theorem**: If A and B are measurable subsets of ℝ with
positive Lebesgue measure, then A+B contains a nonempty open interval.

The proof uses the overlap function f(x) = μ(A' ∩ (x - B')) which is
continuous (by L¹ translation continuity), has positive integral (by Fubini),
and hence is positive on an open neighborhood that lies in A+B.

**Boundary (1 sorry):** The remaining bridge is the L¹ translation
continuity for indicator functions: the map x ↦ ∫ 1_{A'}(t) · 1_{B'}(x-t) dt
is continuous. The standard proof uses that indicator functions of finite-
measure sets are in L¹, and translation is continuous in L¹ for L¹ functions.
This is a standard result in real analysis but requires either:
(a) the density of C_c(ℝ) in L¹(ℝ) (Mathlib's `BoundedContinuousFunction`
    density is available but the L¹ version needs adaptation), or
(b) the Lebesgue density theorem (not found in this Mathlib version), or
(c) a direct DCT argument using that x ↦ 1_{B'}(x-t) converges pointwise
    a.e. as x → x₀ (requires the boundary of B' to have measure 0, which is
    true for intervals but not for arbitrary measurable sets without the
    density theorem).

APIs searched: `Continuous.convolution`, `tendsto_integral_of_dominated_convergence`,
`Integrable.continuous_at_translate`, `MeasureTheory.ae_tendsto_measure_inter_nhds`.

Routes tried:
- Direct DCT on indicator convolution (blocked: pointwise convergence of
  indicators at boundary requires density theorem)
- `integrable_indicator_iff` + L¹ translation continuity (blocked: Mathlib
  lacks `Integrable.tendsto_Lp_translate` or equivalent)

Routes NOT investigated:
- Mathlib's `Convolution` namespace with bilinear maps (requires setting up
  the bilinear map (·,·) ↦ ·*· explicitly and may need compact support)
- Inner regularity approach via compact K⊂A', L⊂B' (would make the DCT
  argument work since χ_K is a.e. continuous when K is an interval union,
  but proving this for general compact sets is harder) -/
theorem a96J02 (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < volume A) (hBpos : 0 < volume B) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ (A + B : Set ℝ) := by
  -- Step 1: Reduce to bounded subsets with positive finite measure
  obtain ⟨nA, hnA⟩ := exists_pos_measure_bounded_subset A hA hApos
  obtain ⟨nB, hnB⟩ := exists_pos_measure_bounded_subset B hB hBpos
  let A' := A ∩ Set.Icc (-(nA : ℝ)) nA
  let B' := B ∩ Set.Icc (-(nB : ℝ)) nB
  have hA'meas : MeasurableSet A' := hA.inter measurableSet_Icc
  have hB'meas : MeasurableSet B' := hB.inter measurableSet_Icc
  have hA'pos : 0 < volume A' := hnA
  have hB'pos : 0 < volume B' := hnB
  have hA'finite : volume A' < ⊤ :=
    (measure_mono (fun _ hx => hx.2)).trans_lt (by
      rw [Real.volume_Icc]; exact ofReal_lt_top)
  have hB'finite : volume B' < ⊤ :=
    (measure_mono (fun _ hx => hx.2)).trans_lt (by
      rw [Real.volume_Icc]; exact ofReal_lt_top)
  have hAB : A' + B' ⊆ A + B := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha.1, b, hb.1, rfl⟩
  have hA'int : Integrable (indicator A' (1 : ℝ → ℝ)) volume :=
    integrable_indicator_of_finite_measure _ hA'meas hA'finite
  have hB'int : Integrable (indicator B' (1 : ℝ → ℝ)) volume :=
    integrable_indicator_of_finite_measure _ hB'meas hB'finite
  -- The convolution f(x) = ∫ 1_{A'}(t) · 1_{B'}(x-t) dt is continuous
  -- by L¹ translation continuity. This is the remaining boundary.
  -- See the boundary comment on the theorem for details.
  sorry

end

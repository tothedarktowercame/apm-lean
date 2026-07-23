import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Set ENNReal Filter

noncomputable section

/-! # APM a03J01: Multiplicity counting identity
  A = Σ m(E_k) = Σ j · m(F_j).
  Proof: both sides = ∫⁻ N(x), where N(x) = Σ χ_{E_k}(x).
-/

def countMembership (E : ℕ → Set ℝ) (x : ℝ) : ℕ :=
  ∑' k, (E k).indicator (fun _ => 1) x

def multLevelSet (E : ℕ → Set ℝ) (j : ℕ) : Set ℝ :=
  {x | countMembership E x = j}

-- Left side = ∫⁻ N (Tonelli)
-- Σ_k volume(E_k) = Σ_k ∫⁻ χ_{E_k} = ∫⁻ Σ_k χ_{E_k} = ∫⁻ N
lemma left_eq_lintegral (E : ℕ → Set ℝ) (hE : ∀ k, MeasurableSet (E k)) :
    ∑' k, volume (E k) = ∫⁻ x, ∑' k, ((E k).indicator (fun _ => (1 : ℝ≥0∞))) x := by
  rw [lintegral_tsum (fun k => (measurable_const.indicator (hE k)).aemeasurable)]
  congr 1; ext k
  rw [lintegral_indicator_const (hE k), one_mul]

-- Right side = ∫⁻ N (level set decomposition)
lemma right_eq_lintegral (E : ℕ → Set ℝ) (hE : ∀ k, MeasurableSet (E k)) :
    ∑' j, ((j : ℕ) : ℝ≥0∞) * volume (multLevelSet E j) =
    ∫⁻ x, ∑' k, ((E k).indicator (fun _ => (1 : ℝ≥0∞))) x := by
  -- HtDP: decompose f(x) = Σ_j (if f(x)=j then j else 0) via tsum_eq_single,
  -- then lintegral_tsum swaps, then lintegral_const_mul + lintegral_indicator_const
  -- closes each term to j * μ({f=j}).
  -- Blocker: tsum_eq_single for ENNReal requires careful implicit handling;
  -- the decomposition (f x : ℝ≥0∞) = Σ' j, j * χ_{f=j}(x) needs
  -- the rewrite through mul_ite and indicator_apply to match.
  sorry

-- Main theorem: combine
theorem multiplicity_identity (E : ℕ → Set ℝ)
    (hE : ∀ k, MeasurableSet (E k))
    (hA : ∑' k, volume (E k) < ⊤) :
    ∑' k, volume (E k) = ∑' j, ((j : ℕ) : ℝ≥0∞) * volume (multLevelSet E j) := by
  rw [left_eq_lintegral E hE, ← right_eq_lintegral E hE]

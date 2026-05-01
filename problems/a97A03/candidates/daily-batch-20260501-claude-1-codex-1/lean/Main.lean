import Mathlib

open MeasureTheory Set Filter

noncomputable section

variable {a b : ℝ} (hab : a ≤ b)

/-- Forward direction: Lipschitz implies a.e. bounded derivative. -/
theorem apm_a97A03_lip_to_bounded_deriv
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε)
    (B : ℝ) (hB : 0 < B)
    (hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ B * |x - y|) :
    ∃ C > 0, ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      DifferentiableAt ℝ f x → |deriv f x| ≤ C := by sorry

/-- Reverse direction: AC + a.e. bounded derivative implies Lipschitz. -/
theorem apm_a97A03_bounded_deriv_to_lip
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), |deriv f x| ≤ C) :
    ∃ B > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ B * |x - y| := by sorry

/-- Key lemma: AC functions satisfy the Fundamental Theorem of Calculus. -/
theorem apm_a97A03_ftc_for_ac
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    f y - f x = ∫ t in x..y, deriv f t := by sorry

/-- Main theorem: equivalence of Lipschitz and a.e. bounded derivative for
    absolutely continuous functions on a compact interval. -/
theorem apm_a97A03_main
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε) :
    (∃ B > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ B * |x - y|) ↔
    (∃ C > 0, ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
        DifferentiableAt ℝ f x ∧ |deriv f x| ≤ C) := by sorry

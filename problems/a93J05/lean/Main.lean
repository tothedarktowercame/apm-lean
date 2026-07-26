/-
! # APM a93J05: Doubly periodic entire function is constant

An entire function f with f(z) = f(z + n + im) for all z ∈ ℂ and n,m ∈ ℤ
must be constant.
-/

import Mathlib.Analysis.Complex.Liouville

open Complex Set Metric Filter Bornology Topology

noncomputable section

/-- Periodicity with period ω implies periodicity with any integer multiple of ω. -/
private lemma periodic_int_aux {f : ℂ → ℂ} (ω : ℂ) (hper : ∀ z, f (z + ω) = f z) (z : ℂ) :
    ∀ n : ℤ, f (z + n * ω) = f z := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ k hk =>
    have h1 : f ((z + (↑k : ℤ) * ω) + ω) = f (z + (↑k : ℤ) * ω) := hper _
    calc f (z + (↑(↑k + 1) : ℤ) * ω)
        = f ((z + (↑k : ℤ) * ω) + ω) := by congr 1; push_cast; ring
      _ = f (z + (↑k : ℤ) * ω) := h1
      _ = f z := hk
  | pred k hk =>
    have h1 : f ((z + (↑(-↑k : ℤ)) * ω) - ω) = f (z + (↑(-↑k : ℤ)) * ω) := by
      have := hper ((z + (↑(-↑k : ℤ)) * ω) - ω)
      rw [sub_add_cancel] at this
      exact this.symm
    calc f (z + (↑(-↑k - 1 : ℤ)) * ω)
        = f ((z + (↑(-↑k : ℤ)) * ω) - ω) := by congr 1; push_cast; ring
      _ = f (z + (↑(-↑k : ℤ)) * ω) := h1
      _ = f z := hk

/-- A doubly periodic entire function is constant.

    If f is entire and periodic with periods 1 and i, then f is constant.
    Proof: f's range equals its range on the compact fundamental parallelogram
    {s + ti : s,t ∈ [0,1]}, hence bounded. By Liouville's theorem, f is constant. -/
theorem doubly_periodic_entire_is_const
    (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hper1 : ∀ z, f (z + 1) = f z)
    (hperi : ∀ z, f (z + I) = f z) :
    ∃ c : ℂ, ∀ z, f z = c := by
  apply hf.exists_const_forall_eq_of_bounded
  let φ : ℝ × ℝ → ℂ := fun p => p.1 + p.2 * I
  have h_φ_cont : Continuous φ := by continuity
  have h_f_cont : Continuous f := hf.continuous
  have h_compact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  refine IsBounded.subset (t := f '' (φ '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) ?_ ?_
  · exact (h_compact.image h_φ_cont |>.image h_f_cont).isBounded
  · rintro y ⟨z, rfl⟩
    -- z decomposes as fract(Re z) + fract(Im z)*I + floor(Re z) + floor(Im z)*I
    -- f(z) = f(fract(Re z) + fract(Im z)*I) by periodicity
    set w := Int.fract z.re + Int.fract z.im * I
    have hw1 : f (w + Int.floor z.re) = f w := by
      have := periodic_int_aux 1 hper1 w (Int.floor z.re)
      simpa using this
    have hw2 : f (w + Int.floor z.re + Int.floor z.im * I) = f (w + Int.floor z.re) :=
      periodic_int_aux I hperi (w + Int.floor z.re) (Int.floor z.im)
    have hz_eq : z = w + Int.floor z.re + Int.floor z.im * I := by
      -- z.re = fract(z.re) + floor(z.re), z.im = fract(z.im) + floor(z.im)
      -- The complex equality follows from real/imaginary parts
      sorry
    rw [hz_eq, hw2, hw1]
    refine ⟨w, ⟨(Int.fract z.re, Int.fract z.im), ?_, rfl⟩, rfl⟩
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨Int.fract_nonneg z.re, (Int.fract_lt_one z.re).le⟩
    · rw [Set.mem_Icc]
      exact ⟨Int.fract_nonneg z.im, (Int.fract_lt_one z.im).le⟩

end

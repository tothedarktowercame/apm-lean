import Mathlib

open Complex Set

noncomputable section

/-- The open upper half-plane in ℂ. -/
def UHP : Set ℂ := {z : ℂ | 0 < z.im}

/-- The open right half-plane in ℂ. -/
def RHP : Set ℂ := {z : ℂ | 0 < z.re}

/-- The Cayley-type map (w - 1)/(w + 1) sends the right half-plane to the
    open unit disk. -/
theorem apm_a97A05_cayley_maps_RHP_to_disk
    (w : ℂ) (hw : 0 < w.re) :
    ‖(w - 1) / (w + 1)‖ < 1 := by
  have hsq : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_add]
    norm_num
    linarith
  have hlt : ‖w - 1‖ < ‖w + 1‖ := by
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  have hne : w + 1 ≠ 0 := by
    intro h
    have hre : w.re = -1 := by
      have := congrArg Complex.re h
      simp at this
      linarith
    linarith
  rw [norm_div]
  have hw1 : 0 < ‖w + 1‖ := norm_pos_iff.mpr hne
  exact (div_lt_one hw1).2 (by simpa using hlt)

/-- Helper: shifting f by (M + 1) sends Re(f) ≥ -M into RHP. -/
theorem apm_a97A05_shift_to_RHP
    (f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    ∀ z ∈ UHP, 0 < ((f z) + (M + 1)).re := by
  intro z hz
  have hbound := hbdd z hz
  have hlow : -M ≤ (f z).re := by
    have habs := abs_le.mp hbound
    linarith
  have : 0 < (f z).re + (M + 1) := by linarith
  simpa [UHP, add_assoc, add_comm, add_left_comm] using this

/-- Auxiliary bounded function ψ = (f₁ - 1)/(f₁ + 1) where f₁ = f + (M+1). -/
def apm_a97A05_psi (f : ℂ → ℂ) (M : ℝ) (z : ℂ) : ℂ :=
  ((f z) + M) / ((f z) + (M + 2))

theorem apm_a97A05_psi_bdd
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    ∀ z ∈ UHP, ‖apm_a97A05_psi f M z‖ < 1 := by
  intro z hz
  have hzR : 0 < ((f z) + (M + 1)).re := apm_a97A05_shift_to_RHP f M hM hbdd z hz
  have hC := apm_a97A05_cayley_maps_RHP_to_disk ((f z) + (M + 1)) hzR
  have hnum : ((f z) + (M + 1)) - 1 = (f z) + M := by ring
  have hden : ((f z) + (M + 1)) + 1 = (f z) + (M + 2) := by ring
  rw [hnum, hden] at hC
  simpa [apm_a97A05_psi] using hC

theorem apm_a97A05_psi_analytic
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    AnalyticOn ℂ (apm_a97A05_psi f M) UHP := by
  have hnum : AnalyticOn ℂ (fun z => (f z) + M) UHP := hf.add analyticOn_const
  have hden : AnalyticOn ℂ (fun z => (f z) + (M + 2)) UHP := hf.add analyticOn_const
  refine hnum.div hden ?_
  intro z hz
  have hzR : 0 < ((f z) + (M + 1)).re := apm_a97A05_shift_to_RHP f M hM hbdd z hz
  intro hzero
  have hre0 : ((f z) + (M + 2)).re = 0 := by
    have := congrArg Complex.re hzero
    simpa using this
  have hre1 : ((f z) + (M + 1)).re = -1 := by
    simp at hre0 ⊢
    linarith
  linarith

/-- Main theorem: an analytic function on H with bounded real part is the
    quotient of two bounded analytic functions on H. -/
theorem apm_a97A05_main
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    ∃ (g h : ℂ → ℂ) (Cg Ch : ℝ),
      AnalyticOn ℂ g UHP ∧
      AnalyticOn ℂ h UHP ∧
      (∀ z ∈ UHP, ‖g z‖ ≤ Cg) ∧
      (∀ z ∈ UHP, ‖h z‖ ≤ Ch) ∧
      (∀ z ∈ UHP, h z ≠ 0) ∧
      (∀ z ∈ UHP, f z = g z / h z) := by
  let ψ : ℂ → ℂ := apm_a97A05_psi f M
  let g : ℂ → ℂ := fun z => ((M + 2 : ℝ) : ℂ) * ψ z - M
  let h : ℂ → ℂ := fun z => 1 - ψ z
  refine ⟨g, h, ‖((M + 2 : ℝ) : ℂ)‖ + ‖(M : ℂ)‖, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [g, ψ]
    exact (analyticOn_const.mul (apm_a97A05_psi_analytic f hf M hM hbdd)).sub analyticOn_const
  · dsimp [h, ψ]
    exact analyticOn_const.sub (apm_a97A05_psi_analytic f hf M hM hbdd)
  · intro z hz
    have hψle : ‖ψ z‖ ≤ 1 := le_of_lt (apm_a97A05_psi_bdd f hf M hM hbdd z hz)
    dsimp [g]
    calc
      ‖(((M + 2 : ℝ) : ℂ) * ψ z) - ↑M‖ ≤ ‖((M + 2 : ℝ) : ℂ) * ψ z‖ + ‖(M : ℂ)‖ := norm_sub_le _ _
      _ = ‖((M + 2 : ℝ) : ℂ)‖ * ‖ψ z‖ + ‖(M : ℂ)‖ := by rw [norm_mul]
      _ ≤ ‖((M + 2 : ℝ) : ℂ)‖ * 1 + ‖(M : ℂ)‖ := by gcongr
      _ = ‖((M + 2 : ℝ) : ℂ)‖ + ‖(M : ℂ)‖ := by ring
  · intro z hz
    have hψle : ‖ψ z‖ ≤ 1 := le_of_lt (apm_a97A05_psi_bdd f hf M hM hbdd z hz)
    dsimp [h]
    calc
      ‖1 - ψ z‖ ≤ ‖(1 : ℂ)‖ + ‖ψ z‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
        have hone : ‖(1 : ℂ)‖ = 1 := by norm_num
        nlinarith
      _ = 2 := by norm_num
  · intro z hz
    dsimp [h, ψ]
    intro hhzero
    have hpsi1 : apm_a97A05_psi f M z = 1 := by
      have := sub_eq_zero.mp hhzero
      simpa using this.symm
    have : ‖(1 : ℂ)‖ < 1 := by simpa [hpsi1] using apm_a97A05_psi_bdd f hf M hM hbdd z hz
    norm_num at this
  · intro z hz
    dsimp [g, h, ψ, apm_a97A05_psi]
    have hne : f z + (M + 2) ≠ 0 := by
      have hzR : 0 < ((f z) + (M + 1)).re := apm_a97A05_shift_to_RHP f M hM hbdd z hz
      intro hzero
      have hre0 : ((f z) + (M + 2)).re = 0 := by
        have := congrArg Complex.re hzero
        simpa using this
      have hre1 : ((f z) + (M + 1)).re = -1 := by
        simp at hre0 ⊢
        linarith
      linarith
    have hhnz : 1 - (f z + ↑M) / (f z + (↑M + 2)) ≠ 0 := by
      intro hhzero
      have hpsi1 : (f z + ↑M) / (f z + (↑M + 2)) = 1 := by
        have := sub_eq_zero.mp hhzero
        simpa using this.symm
      have : ‖(1 : ℂ)‖ < 1 := by simpa [apm_a97A05_psi, hpsi1] using apm_a97A05_psi_bdd f hf M hM hbdd z hz
      norm_num at this
    have hgfrac :
        (((M + 2 : ℝ) : ℂ) * ((f z + ↑M) / (f z + (↑M + 2))) - ↑M) =
          (2 : ℂ) * f z / (f z + (↑M + 2)) := by
      field_simp [hne]
      have hcast : (((M + 2 : ℝ) : ℂ)) = (M : ℂ) + 2 := by simp
      rw [hcast]
      ring
    have hhfrac :
        1 - (f z + ↑M) / (f z + (↑M + 2)) = (2 : ℂ) / (f z + (↑M + 2)) := by
      field_simp [hne]
      ring_nf
    rw [hgfrac, hhfrac]
    field_simp [hne]

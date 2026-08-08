import Mathlib

/-!
# APM a99J08: A square-root bound at a mixed-boundary corner

## Statement repairs

1. The source writes `D = {z : |z| < 1}` followed by `Im(z) = y > 0`.
   This is interpreted as the open upper half-disk, as required for the two
   stated conditions to be boundary conditions.
2. The quotient `|g(z)| / |z|^(1/2)` is undefined at `z = 0`, although the
   source asks for boundedness on all of `closure D`. We state the equivalent
   global estimate `|g(z)| ≤ C * sqrt |z|`, which is meaningful at the corner.

## Encoding questions

None.
-/

open Set Complex Filter Topology

noncomputable section

/-- The open upper half of the complex unit disk. -/
def apm_a99J08_upperHalfDisk : Set ℂ :=
  Metric.ball 0 1 ∩ {z | 0 < z.im}

/-- Squaring converts a purely imaginary boundary value into a real one. -/
lemma apm_a99J08_sq_im_eq_zero_of_re_eq_zero (z : ℂ) (hz : z.re = 0) :
    (z ^ 2).im = 0 := by
  simp [pow_two, Complex.mul_im, hz]

/-- Squaring preserves reality of a boundary value. -/
lemma apm_a99J08_sq_im_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) :
    (z ^ 2).im = 0 := by
  simp [pow_two, Complex.mul_im, hz]

/-- The mixed boundary conditions become one real-boundary condition after
squaring, away from the corner. -/
lemma apm_a99J08_sq_real_on_punctured_diameter
    (g : ℂ → ℂ)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) (hx₀ : x ≠ 0) :
    ((g x) ^ 2).im = 0 := by
  rcases lt_or_gt_of_ne hx₀ with hx | hx
  · exact apm_a99J08_sq_im_eq_zero_of_im_eq_zero _ (hneg x hx₁ hx)
  · exact apm_a99J08_sq_im_eq_zero_of_re_eq_zero _ (hpos x hx hx₂)

lemma apm_a99J08_real_mem_closure_upperHalfDisk
    {x : ℝ} (hx : |x| < 1) :
    (x : ℂ) ∈ closure apm_a99J08_upperHalfDisk := by
  have him : (x : ℂ) ∈ closure {z : ℂ | 0 < z.im} := by
    rw [show {z : ℂ | 0 < z.im} = Complex.im ⁻¹' Ioi 0 from rfl,
      Complex.closure_preimage_im, closure_Ioi]
    simp
  have hball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hmem : (x : ℂ) ∈ closure ({z : ℂ | 0 < z.im} ∩ Metric.ball 0 1) :=
    Metric.isOpen_ball.closure_inter ⟨him, hball⟩
  simpa [apm_a99J08_upperHalfDisk, inter_comm] using hmem

lemma apm_a99J08_corner_zero
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    g 0 = 0 := by
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzero : (0 : ℂ) ∈ closure apm_a99J08_upperHalfDisk :=
    apm_a99J08_real_mem_closure_upperHalfDisk (by norm_num)
  have hposmem : ∀ᶠ n in atTop,
      (u n : ℂ) ∈ closure apm_a99J08_upperHalfDisk := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply apm_a99J08_real_mem_closure_upperHalfDisk
    dsimp [u]
    rw [abs_of_pos (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    norm_num
    exact_mod_cast hn
  have hnegmem : ∀ᶠ n in atTop,
      ((-u n : ℝ) : ℂ) ∈ closure apm_a99J08_upperHalfDisk := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply apm_a99J08_real_mem_closure_upperHalfDisk
    rw [abs_neg]
    dsimp [u]
    rw [abs_of_pos (by positivity)]
    rw [div_lt_iff₀ (by positivity)]
    norm_num
    exact_mod_cast hn
  have hup : Tendsto (fun n => (u n : ℂ)) atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  have hun : Tendsto (fun n => ((-u n : ℝ) : ℂ)) atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (by simpa using hu.neg)
  have hgpos : Tendsto (fun n => g (u n)) atTop (nhds (g 0)) :=
    (show Tendsto g (nhdsWithin 0 (closure apm_a99J08_upperHalfDisk)) (nhds (g 0))
      from hgcont 0 hzero).comp (tendsto_nhdsWithin_iff.2 ⟨hup, hposmem⟩)
  have hgneg : Tendsto (fun n => g ((-u n : ℝ) : ℂ)) atTop (nhds (g 0)) :=
    (show Tendsto g (nhdsWithin 0 (closure apm_a99J08_upperHalfDisk)) (nhds (g 0))
      from hgcont 0 hzero).comp (tendsto_nhdsWithin_iff.2 ⟨hun, hnegmem⟩)
  apply Complex.ext
  · have hre := Complex.continuous_re.continuousAt.tendsto.comp hgpos
    have hre0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    have heq : (fun n => (g (u n)).re) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply hpos
      · dsimp [u]
        positivity
      · dsimp [u]
        rw [div_lt_iff₀ (by positivity)]
        norm_num
        exact_mod_cast hn
    exact tendsto_nhds_unique hre (hre0.congr' heq.symm)
  · have him := Complex.continuous_im.continuousAt.tendsto.comp hgneg
    have him0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    have heq : (fun n => (g ((-u n : ℝ) : ℂ)).im) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply hneg
      · dsimp [u]
        rw [neg_lt_neg_iff, div_lt_iff₀ (by positivity)]
        norm_num
        exact_mod_cast hn
      · dsimp [u]
        rw [neg_lt_zero]
        positivity
    exact tendsto_nhds_unique him (him0.congr' heq.symm)

/-- After the corner value is identified, the squared function is real on the
entire open diameter, including the formerly missing origin. -/
lemma apm_a99J08_sq_real_on_diameter
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) :
    ((g x) ^ 2).im = 0 := by
  by_cases hx₀ : x = 0
  · subst x
    have hz : g ((0 : ℝ) : ℂ) = 0 := by
      simpa using apm_a99J08_corner_zero g hgcont hpos hneg
    rw [hz]
    simp
  · exact apm_a99J08_sq_real_on_punctured_diameter g hpos hneg hx₁ hx₂ hx₀

/-- The function to be reflected is continuous up to the boundary and
holomorphic in the upper half-disk. -/
lemma apm_a99J08_sq_regular
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk) :
    ContinuousOn (fun z => g z ^ 2) (closure apm_a99J08_upperHalfDisk) ∧
      DifferentiableOn ℂ (fun z => g z ^ 2) apm_a99J08_upperHalfDisk := by
  exact ⟨hgcont.pow 2, hgholo.pow 2⟩

theorem apm_a99j08
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closure apm_a99J08_upperHalfDisk,
        ‖g z‖ ≤ C * Real.sqrt ‖z‖ := by
  /-
  PARTIAL boundary (closer hop 3).  The geometric and corner-continuity steps
  are now compiled above. `apm_a99J08_real_mem_closure_upperHalfDisk` uses
  `Complex.closure_preimage_im` and `IsOpen.closure_inter` to put every point
  of the open real diameter in the half-disk closure.  Then
  `apm_a99J08_corner_zero` applies `hgcont` to the explicit sequences
  `±1/(n+1)`; the two boundary hypotheses force respectively the real and
  imaginary parts of the common limit to vanish, proving `g 0 = 0`.

  A renewed Mathlib search found Morera infrastructure in
  `Analysis.Complex.HasPrimitives` and conjugation-differentiability lemmas in
  `Analysis.Calculus.Deriv.Star`, but no theorem gluing the two reflected
  pieces continuously across a line into a holomorphic function.  The Morera
  API requires proving vanishing wedge/rectangle integrals for the piecewise
  function, which is essentially the missing Schwarz-reflection theorem.
  `ConstructionTargets.HerglotzRigidity.conj_apply_conj_eq` still applies only
  to an already entire function. Thus the remaining bridge is precisely the
  local reflection of `g²`; once available, its now-proved zero at the corner
  permits division by `z`, a local quotient bound, and compactness away from
  zero. No weaker continuity-only argument suffices to obtain a square-root
  rate from `g 0 = 0`.

  CLOSER HOP 3: `apm_a99J08_sq_real_on_diameter` combines the corner-zero
  theorem with the punctured result, proving that `g²` is real on the entire
  open diameter with no exceptional point. `apm_a99J08_sq_regular` packages
  continuity of `g²` on the closed upper half-disk and holomorphicity in its
  interior. Thus every local hypothesis of Schwarz reflection is now a
  compiled lemma in the exact frozen geometry. Renewed searches of
  `HasPrimitives`, Morera, conjugation derivatives, and all construction
  modules still found no theorem turning precisely these hypotheses into a
  holomorphic reflected function. The reflection/gluing theorem, followed by
  factorization at its zero and compact quotient bounds, remains open.
  -/
  sorry

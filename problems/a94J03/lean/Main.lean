import Mathlib

/-!
# APM a94J03

## Statement repairs

None.

## Encoding questions

None. “Maps open sets onto open sets” is Mathlib's `IsOpenMap`, and strict
monotonicity allows either global orientation: `StrictMono f ∨ StrictAnti f`.
-/

lemma apm_a94J03_not_isMaxOn_of_isOpenMap
    {f : ℝ → ℝ} (hf : IsOpenMap f) {s : Set ℝ} (hs : IsOpen s)
    {x : ℝ} (hx : x ∈ s) : ¬IsMaxOn f s x := by
  intro hmax
  have himg : IsOpen (f '' s) := hf s hs
  have hfx : f x ∈ f '' s := ⟨x, hx, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg (f x) hfx
  have hnear : f x + ε / 2 ∈ Metric.ball (f x) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨y, hy, hfy⟩ := hball hnear
  have := hmax hy
  change f y ≤ f x at this
  rw [hfy] at this
  linarith

lemma apm_a94J03_not_isMinOn_of_isOpenMap
    {f : ℝ → ℝ} (hf : IsOpenMap f) {s : Set ℝ} (hs : IsOpen s)
    {x : ℝ} (hx : x ∈ s) : ¬IsMinOn f s x := by
  intro hmin
  have himg : IsOpen (f '' s) := hf s hs
  have hfx : f x ∈ f '' s := ⟨x, hx, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg (f x) hfx
  have hnear : f x - ε / 2 ∈ Metric.ball (f x) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨y, hy, hfy⟩ := hball hnear
  have := hmin hy
  change f x ≤ f y at this
  rw [hfy] at this
  linarith

lemma apm_a94J03_injective_of_continuous_isOpenMap
    {f : ℝ → ℝ} (hf : Continuous f) (hopen : IsOpenMap f) :
    Function.Injective f := by
  have hpair : ∀ {a b : ℝ}, a < b → f a ≠ f b := by
    intro a b hab heq
    obtain ⟨c, hc, hext⟩ :=
      exists_Ioo_extr_on_Icc hab hf.continuousOn heq
    rcases hext with hmin | hmax
    · exact apm_a94J03_not_isMinOn_of_isOpenMap hopen isOpen_Ioo hc
        (fun _ hx ↦ hmin (Set.Ioo_subset_Icc_self hx))
    · exact apm_a94J03_not_isMaxOn_of_isOpenMap hopen isOpen_Ioo hc
        (fun _ hx ↦ hmax (Set.Ioo_subset_Icc_self hx))
  intro a b hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact (hpair hlt hab).elim
  · exact heq
  · exact (hpair hgt hab.symm).elim

theorem apm_a94j03 (f : ℝ → ℝ) (hf : Continuous f) (hopen : IsOpenMap f) :
    StrictMono f ∨ StrictAnti f := by
  -- `Continuous.strictMono_of_inj` is Mathlib's global orientation theorem;
  -- the preceding lemma supplies its missing injectivity hypothesis.
  exact hf.strictMono_of_inj
    (apm_a94J03_injective_of_continuous_isOpenMap hf hopen)

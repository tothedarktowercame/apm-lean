import Mathlib

/-! # APM t94A01: the weighted metric on the countable cube

## Statement repairs

The source's coordinates indexed by `1,2,…` are reindexed by `ℕ`; consequently
the weight is `2⁻(i+1)`.

## Encoding questions

The product topology is Mathlib's topology on the dependent function type
`∀ i : ℕ, Set.Icc (0 : ℝ) 1`.  Rather than install a second global metric
instance, metric openness is stated directly using the concrete `rho` balls.
-/

abbrev APMT94A01.Cube := ∀ _ : ℕ, Set.Icc (0 : ℝ) 1

noncomputable def APMT94A01.rho (f g : APMT94A01.Cube) : ℝ :=
  ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * |(f i : ℝ) - (g i : ℝ)|

lemma abs_sub_le_one (f g : APMT94A01.Cube) (i : ℕ) : |(f i : ℝ) - (g i : ℝ)| ≤ 1 := by
  obtain ⟨a1, a2⟩ := (f i).2
  obtain ⟨b1, b2⟩ := (g i).2
  rw [abs_le]; constructor <;> linarith

lemma term_le (f g : APMT94A01.Cube) (i : ℕ) : ‖(1 / 2 : ℝ) ^ (i + 1) * |(f i : ℝ) - (g i : ℝ)|‖ ≤ (1/2 : ℝ) ^ (i+1) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ (1 / 2 : ℝ) ^ (i + 1) * 1 := by gcongr; exact abs_sub_le_one f g i
    _ = _ := mul_one _

lemma summable_geom' : Summable (fun i : ℕ => (1/2 : ℝ) ^ (i+1)) := by
  have h := (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).mul_left (1/2)
  refine h.congr (fun i => ?_)
  rw [pow_succ, mul_comm]

lemma summable_terms (f g : APMT94A01.Cube) :
    Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1) * |(f i : ℝ) - (g i : ℝ)|) :=
  Summable.of_norm_bounded summable_geom' (term_le f g)

lemma single_le (f g : APMT94A01.Cube) (i : ℕ) :
    (1 / 2 : ℝ) ^ (i + 1) * |(f i : ℝ) - (g i : ℝ)| ≤ APMT94A01.rho f g :=
  (summable_terms f g).le_tsum i (fun j _ => by positivity)

lemma continuous_rho (f : APMT94A01.Cube) : Continuous (fun g => APMT94A01.rho f g) := by
  unfold APMT94A01.rho
  refine continuous_tsum (fun i => ?_) summable_geom' (fun i g => term_le f g i)
  fun_prop

theorem apm_t94a01 (U : Set APMT94A01.Cube) :
    IsOpen U ↔
      ∀ f ∈ U, ∃ ε > (0 : ℝ),
        {g | APMT94A01.rho f g < ε} ⊆ U := by
  constructor
  · intro hU f hf
    have hn : U ∈ nhds f := hU.mem_nhds hf
    rw [nhds_pi, Filter.mem_pi] at hn
    obtain ⟨I, hI, t, ht, hsub⟩ := hn
    have hδ : ∀ i, ∃ δ > (0:ℝ), Metric.ball (f i) δ ⊆ t i := fun i => Metric.mem_nhds_iff.1 (ht i)
    choose δ hδpos hδsub using hδ
    have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ i ∈ I, ε < (1/2 : ℝ)^(i+1) * δ i :=
      (Filter.eventually_all_finite hI).2 (fun i _ =>
        nhdsWithin_le_nhds (eventually_lt_nhds (by have := hδpos i; positivity)))
    obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
    refine ⟨ε, hεpos, fun g hg => hsub (fun i hi => hδsub i ?_)⟩
    have h1 := single_le f g i
    have h2 := hε i hi
    have hp : (0:ℝ) < (1/2)^(i+1) := by positivity
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    have : (1/2 : ℝ)^(i+1) * |(f i : ℝ) - g i| < (1/2)^(i+1) * δ i := by
      simp only [Set.mem_setOf_eq] at hg; linarith
    exact lt_of_mul_lt_mul_left this hp.le
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro f hf
    obtain ⟨ε, hε, hsub⟩ := h f hf
    refine Filter.mem_of_superset ?_ hsub
    have hf0 : APMT94A01.rho f f = 0 := by simp [APMT94A01.rho]
    exact (continuous_rho f).isOpen_preimage _ isOpen_Iio |>.mem_nhds (by simpa [hf0] using hε)

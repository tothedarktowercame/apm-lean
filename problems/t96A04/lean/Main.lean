import Mathlib

/-!
# APM t96A04 — the unit-interval function space is not compact

`C` is represented by bundled continuous maps and carries the uniform metric.
-/

noncomputable section

local notation "I" => Set.Icc (0 : ℝ) 1
local notation "C" => ContinuousMap I I

theorem apm_t96a04 : ¬ IsCompact (Set.univ : Set C) := by
  intro hc
  let f : ℕ → C := fun n => ⟨fun x => ⟨(x : ℝ) ^ n, pow_nonneg x.2.1 n, pow_le_one₀ x.2.1 x.2.2⟩,
    by fun_prop⟩
  obtain ⟨g, -, φ, hφ, hlim⟩ := hc.tendsto_subseq (x := f) (fun _ => Set.mem_univ _)
  have hpt : ∀ x : I, Filter.Tendsto (fun n => ((f (φ n)) x : ℝ)) Filter.atTop (nhds (g x : ℝ)) :=
    fun x => (continuous_subtype_val.tendsto _).comp ((continuous_eval_const x).tendsto g |>.comp hlim)
  have h0 : ∀ x : I, (x : ℝ) < 1 → (g x : ℝ) = 0 := by
    intro x hx
    have h1 : Filter.Tendsto (fun n => ((f (φ n)) x : ℝ)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one x.2.1 hx).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique (hpt x) h1
  have h1 : (g ⟨1, by norm_num⟩ : ℝ) = 1 := by
    have : Filter.Tendsto (fun n => ((f (φ n)) ⟨1, by norm_num⟩ : ℝ)) Filter.atTop (nhds 1) := by
      simp [f]
    exact tendsto_nhds_unique (hpt _) this
  -- continuity of g at 1
  have hc1 : ContinuousWithinAt (fun x : ℝ => (g (Set.projIcc 0 1 zero_le_one x) : ℝ)) (Set.Iio 1) 1 :=
    ((continuous_subtype_val.comp g.continuous).comp (continuous_projIcc (h := zero_le_one))).continuousWithinAt
  have hlim0 : Filter.Tendsto (fun x : ℝ => (g (Set.projIcc 0 1 zero_le_one x) : ℝ)) (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Set.projIcc_of_mem _ ⟨hx.1.le, hx.2.le⟩, h0 _ hx.2]
  have hlim1 : Filter.Tendsto (fun x : ℝ => (g (Set.projIcc 0 1 zero_le_one x) : ℝ)) (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 1) := by
    have := ((continuous_subtype_val.comp g.continuous).comp (continuous_projIcc (h := zero_le_one))).tendsto (1 : ℝ)
    have e : ((Subtype.val ∘ ⇑g) ∘ Set.projIcc (0:ℝ) 1 zero_le_one) 1 = 1 := by
      simp only [Function.comp_apply, Set.projIcc_right]; exact h1
    rw [e] at this
    exact this.mono_left nhdsWithin_le_nhds
  haveI : (nhdsWithin (1:ℝ) (Set.Ioo 0 1)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]; simp
  exact zero_ne_one (tendsto_nhds_unique hlim0 hlim1)

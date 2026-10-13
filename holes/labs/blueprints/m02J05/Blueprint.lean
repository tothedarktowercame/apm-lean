import Mathlib

/-!
# APM m02J05

## Statement repairs

Measurable functions are taken modulo almost-everywhere equality. Without this
standard identification, the displayed Luxemburg functional is only a
seminorm, since it cannot distinguish functions differing on a null set.

## Encoding questions

The inverse `β` of `α` is supplied explicitly, with its two inverse identities
on the nonnegative half-line. This avoids extending a half-line homeomorphism
arbitrarily to all of `ℝ`.
-/

open Filter MeasureTheory Set intervalIntegral

/-- Measurable functions on the interval, modulo equality almost everywhere
for the measure actually used by the modular. -/
abbrev apm_m02J05_Fun := ℝ →ₘ[volume.restrict (Icc (0 : ℝ) 1)] ℝ

/-- The Young function obtained by integrating `α` from zero. -/
noncomputable def apm_m02J05_young (α : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, α s

/-- The convex modular class `K_A`, on `[0,1]`, modulo a.e. equality. -/
def apm_m02J05_K (α : ℝ → ℝ) : Set apm_m02J05_Fun :=
  {u | IntegrableOn
    (fun x ↦ apm_m02J05_young α |u x|) (Icc (0 : ℝ) 1) volume}

/-- The Orlicz class consisting of functions with some nonzero rescaling in `K_A`. -/
def apm_m02J05_L (α : ℝ → ℝ) : Set apm_m02J05_Fun :=
  {u | ∃ c : ℝ, c ≠ 0 ∧ c • u ∈ apm_m02J05_K α}

/-- The Luxemburg functional associated to `α`.

The sublevel set carries an explicit `IntegrableOn` conjunct. Without it the
condition `∫ ... ≤ 1` is vacuous when the modular integral diverges: the
real-valued Lebesgue integral of a nonnegative measurable function with
infinite integral is `0` in Mathlib, so every small `c` would be admissible,
the infimum would collapse to `0` for every `u`, and definiteness modulo
a.e. equality would fail. With the integrability conjunct the set is the
classical one: nonempty on `apm_m02J05_L α` by monotone convergence, and the
Luxemburg gauge laws hold. -/
noncomputable def apm_m02J05_lux (α : ℝ → ℝ) (u : apm_m02J05_Fun) : ℝ :=
  sInf {c : ℝ | 0 < c ∧
    IntegrableOn (fun x ↦ apm_m02J05_young α (|u x| / c)) (Icc (0 : ℝ) 1) volume ∧
    ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / c) ∂volume ≤ 1}

lemma apm_m02J05_young_zero (α : ℝ → ℝ) :
    apm_m02J05_young α 0 = 0 := by
  simp [apm_m02J05_young]

lemma apm_m02J05_zero_mem_K (α : ℝ → ℝ) :
    (0 : apm_m02J05_Fun) ∈ apm_m02J05_K α := by
  change IntegrableOn (fun x ↦ apm_m02J05_young α |(0 : apm_m02J05_Fun) x|)
    (Icc (0 : ℝ) 1) volume
  apply integrableOn_zero.congr
  filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
    (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
  rw [hx]
  simp [apm_m02J05_young_zero]

lemma apm_m02J05_zero_mem_L (α : ℝ → ℝ) :
    (0 : apm_m02J05_Fun) ∈ apm_m02J05_L α := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa using apm_m02J05_zero_mem_K α

/-- The Young primitive is nonnegative on the nonnegative half-line. -/
lemma apm_m02J05_young_nonneg
    {α : ℝ → ℝ} (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ apm_m02J05_young α t := by
  unfold apm_m02J05_young
  exact intervalIntegral.integral_nonneg ht (fun x hx => hα x hx.1)

/-- Monotonicity of the primitive follows directly by enlarging its interval
of integration; continuity supplies interval integrability. -/
lemma apm_m02J05_young_mono
    {α : ℝ → ℝ} (hc : ContinuousOn α (Ici 0))
    (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    apm_m02J05_young α s ≤ apm_m02J05_young α t := by
  unfold apm_m02J05_young
  apply intervalIntegral.integral_mono_interval (le_refl 0) hs hst
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hα x hx.1.le
  · have ht : 0 ≤ t := hs.trans hst
    have hi : ContinuousOn α (uIcc (0 : ℝ) t) := by
      simpa [uIcc_of_le ht] using hc.mono Icc_subset_Ici_self
    exact hi.intervalIntegrable

def apm_m02J05_YoungShapeFact (α : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Ici 0) (apm_m02J05_young α) ∧
    MonotoneOn (apm_m02J05_young α) (Ici 0)

def apm_m02J05_luxSublevel (α : ℝ → ℝ) (u : apm_m02J05_Fun) : Set ℝ :=
  {c : ℝ | 0 < c ∧
    IntegrableOn (fun x ↦ apm_m02J05_young α (|u x| / c)) (Icc (0 : ℝ) 1) volume ∧
    ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / c) ∂volume ≤ 1}

theorem apm_m02J05_young_shape
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    apm_m02J05_YoungShapeFact α := by
  have hcont : ContinuousOn (apm_m02J05_young α) (Ici 0) := by
    intro x hx
    have hxb : x < x + 1 := by linarith
    have hi : IntegrableOn α (uIcc (0 : ℝ) (x + 1)) := by
      rw [uIcc_of_le (hx.trans (le_of_lt hxb))]
      exact (hc.mono Icc_subset_Ici_self).integrableOn_Icc
    have hlocal : ContinuousOn (apm_m02J05_young α) (Icc 0 (x + 1)) := by
      simpa [apm_m02J05_young, uIcc_of_le (hx.trans (le_of_lt hxb))] using
        (intervalIntegral.continuousOn_primitive_interval hi)
    apply (hlocal x ⟨hx, hxb.le⟩).mono_of_mem_nhdsWithin (s := Ici 0)
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Iio (x + 1), Iio_mem_nhds hxb, ?_⟩
    rintro y ⟨hy, hy0⟩
    exact ⟨hy0, hy.le⟩
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (apm_m02J05_young α) (α x) x := by
    intro x hx
    have hcx : ContinuousAt α x := hc.continuousAt (Ici_mem_nhds hx)
    have hi : IntervalIntegrable α volume 0 x :=
      (hc.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hx.le
    exact intervalIntegral.integral_hasDerivAt_right hi
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun y hy => hc.continuousAt (Ici_mem_nhds hy)) x hx) hcx
  constructor
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) hcont
      (by
        rw [interior_Ici]
        intro x hx
        exact (hderiv x hx).differentiableAt.differentiableWithinAt)
    rw [interior_Ici]
    exact (hmono.monotoneOn.mono Ioi_subset_Ici_self).congr
      (fun x hx => (hderiv x hx).deriv.symm)
  · intro s hs t ht hst
    exact apm_m02J05_young_mono hc hnonneg hs hst

/-- Why this unblocks `apm_m02j05`: this packages the missing convexity of
the modular class and closure of its rescalable hull under the vector-space
operations on `AEEqFun`. These are the two structural conjuncts preceding the
Luxemburg functional laws. -/
lemma apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_smul
    (α : ℝ → ℝ) (r : ℝ) (u : apm_m02J05_Fun)
    (hu : u ∈ apm_m02J05_L α) : r • u ∈ apm_m02J05_L α := by
  by_cases hr : r = 0
  · subst r
    simpa using apm_m02J05_zero_mem_L α
  · obtain ⟨c, hc, hcu⟩ := hu
    refine ⟨c / r, div_ne_zero hc hr, ?_⟩
    convert hcu using 1
    rw [smul_smul]
    field_simp

lemma apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add_aux_pointwise
    (α : ℝ → ℝ) (hshape : apm_m02J05_YoungShapeFact α)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (U V : ℝ) :
    apm_m02J05_young α |(p * q / (p + q)) * (U + V)| ≤
      (q / (p + q)) * apm_m02J05_young α |p * U| +
        (p / (p + q)) * apm_m02J05_young α |q * V| := by
  have hpq : 0 < p + q := add_pos hp hq
  let r : ℝ := q / (p + q)
  let s : ℝ := p / (p + q)
  have hr : 0 ≤ r := (div_pos hq hpq).le
  have hs : 0 ≤ s := (div_pos hp hpq).le
  have hrs : r + s = 1 := by
    dsimp [r, s]
    field_simp
    ring
  have habs : |(p * q / (p + q)) * (U + V)| ≤
      r * |p * U| + s * |q * V| := by
    calc
      |(p * q / (p + q)) * (U + V)| =
          |r * (p * U) + s * (q * V)| := by
            congr 1
            dsimp [r, s]
            field_simp
      _ ≤ |r * (p * U)| + |s * (q * V)| := abs_add_le _ _
      _ = r * |p * U| + s * |q * V| := by
        simp only [abs_mul, abs_of_nonneg hr, abs_of_nonneg hs]
  calc
    apm_m02J05_young α |(p * q / (p + q)) * (U + V)| ≤
        apm_m02J05_young α (r * |p * U| + s * |q * V|) :=
      hshape.2 (mem_Ici.mpr (abs_nonneg _))
        (mem_Ici.mpr <| add_nonneg (mul_nonneg hr (abs_nonneg _))
          (mul_nonneg hs (abs_nonneg _))) habs
    _ ≤ r * apm_m02J05_young α |p * U| +
        s * apm_m02J05_young α |q * V| :=
      hshape.1.2 (mem_Ici.mpr (abs_nonneg _)) (mem_Ici.mpr (abs_nonneg _)) hr hs hrs
    _ = _ := rfl

lemma apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add_aux_continuous
    (α : ℝ → ℝ) (hc : ContinuousOn α (Ici 0)) :
    Continuous (fun t : ℝ ↦ apm_m02J05_young α |t|) := by
  have ham : Continuous (fun x : ℝ ↦ α (max x 0)) :=
    hc.comp_continuous (continuous_id.max continuous_const)
      (fun x ↦ mem_Ici.mpr (le_max_right _ _))
  have hp : Continuous (fun t : ℝ ↦ ∫ x in (0 : ℝ)..t, α (max x 0)) :=
    continuous_primitive (fun a b ↦ ham.intervalIntegrable a b) 0
  have heq : (fun t : ℝ ↦ apm_m02J05_young α |t|) =
      fun t ↦ ∫ x in (0 : ℝ)..|t|, α (max x 0) := by
    funext t
    unfold apm_m02J05_young
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (abs_nonneg t)] at hx
    simp [max_eq_left hx.1]
  rw [heq]
  exact hp.comp continuous_abs

lemma apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (hshape : apm_m02J05_YoungShapeFact α)
    (u v : apm_m02J05_Fun)
    (hu : u ∈ apm_m02J05_L α) (hv : v ∈ apm_m02J05_L α) :
    u + v ∈ apm_m02J05_L α := by
  obtain ⟨a, ha, hau⟩ := hu
  obtain ⟨b, hb, hbv⟩ := hv
  set p := |a| with hpdef
  set q := |b| with hqdef
  have hp : 0 < p := abs_pos.2 ha
  have hq : 0 < q := abs_pos.2 hb
  have hpq : 0 < p + q := add_pos hp hq
  set c := p * q / (p + q) with hcdef
  have hc0 : c ≠ 0 := (div_pos (mul_pos hp hq) hpq).ne'
  refine ⟨c, hc0, ?_⟩
  have hY := apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add_aux_continuous α hc
  have hYnn : ∀ t, 0 ≤ apm_m02J05_young α |t| := fun t =>
    intervalIntegral.integral_nonneg (abs_nonneg t) (fun x hx => hnonneg x hx.1)
  have hF := hau
  have hG := hbv
  unfold apm_m02J05_K at hF hG ⊢
  simp only [Set.mem_setOf_eq] at hF hG ⊢
  have hdom : Integrable (fun x => (q / (p + q)) * apm_m02J05_young α |(a • u) x| +
      (p / (p + q)) * apm_m02J05_young α |(b • v) x|) (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hF.const_mul _).add (hG.const_mul _)
  refine hdom.mono' ((hY.comp_aestronglyMeasurable (c • (u + v)).aestronglyMeasurable)) ?_
  filter_upwards [AEEqFun.coeFn_smul c (u + v), AEEqFun.coeFn_add u v,
    AEEqFun.coeFn_smul a u, AEEqFun.coeFn_smul b v] with x h1 h2 h3 h4
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (hYnn _), h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have hpa : |p * u x| = |a * u x| := by rw [abs_mul, abs_mul, hpdef, abs_abs]
  have hqb : |q * v x| = |b * v x| := by rw [abs_mul, abs_mul, hqdef, abs_abs]
  have := apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add_aux_pointwise α hshape p q hp hq (u x) (v x)
  rw [hpa, hqb] at this
  exact this

lemma apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_convex
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (hshape : apm_m02J05_YoungShapeFact α) :
    Convex ℝ (apm_m02J05_K α) := by
  intro u hu v hv a b ha hb hab
  have hY :=
    apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add_aux_continuous α hc
  have hYnn : ∀ t, 0 ≤ apm_m02J05_young α |t| := fun t =>
    intervalIntegral.integral_nonneg (abs_nonneg t) (fun x hx => hnonneg x hx.1)
  unfold apm_m02J05_K at hu hv ⊢
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  have hdom : Integrable (fun x =>
      a * apm_m02J05_young α |u x| + b * apm_m02J05_young α |v x|)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hu.const_mul a).add (hv.const_mul b)
  refine hdom.mono'
    (hY.comp_aestronglyMeasurable (a • u + b • v).aestronglyMeasurable) ?_
  filter_upwards [AEEqFun.coeFn_add (a • u) (b • v),
    AEEqFun.coeFn_smul a u, AEEqFun.coeFn_smul b v] with x hadd hau hbv
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (hYnn _), hadd, Pi.add_apply, hau, hbv, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  have habs : |a * u x + b * v x| ≤ a * |u x| + b * |v x| := by
    calc
      |a * u x + b * v x| ≤ |a * u x| + |b * v x| := abs_add_le _ _
      _ = a * |u x| + b * |v x| := by
        simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    apm_m02J05_young α |a * u x + b * v x| ≤
        apm_m02J05_young α (a * |u x| + b * |v x|) :=
      hshape.2 (mem_Ici.mpr (abs_nonneg _))
        (mem_Ici.mpr <| add_nonneg (mul_nonneg ha (abs_nonneg _))
          (mul_nonneg hb (abs_nonneg _))) habs
    _ ≤ a * apm_m02J05_young α |u x| + b * apm_m02J05_young α |v x| :=
      hshape.1.2 (mem_Ici.mpr (abs_nonneg _)) (mem_Ici.mpr (abs_nonneg _)) ha hb hab

theorem apm_m02J05_bridge_convex_and_submodule_of_young_shape
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (hshape : apm_m02J05_YoungShapeFact α) :
    Convex ℝ (apm_m02J05_K α) ∧
      ∃ S : Submodule ℝ apm_m02J05_Fun,
        (S : Set apm_m02J05_Fun) = apm_m02J05_L α := by
  refine ⟨apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_convex
    α hc hnonneg hshape, ?_⟩
  let S : Submodule ℝ apm_m02J05_Fun :=
    { carrier := apm_m02J05_L α
      zero_mem' := apm_m02J05_zero_mem_L α
      add_mem' := fun hu hv ↦
        apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add
          α hc hnonneg hshape _ _ hu hv
      smul_mem' := fun r _ hu ↦
        apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_smul α r _ hu }
  exact ⟨S, rfl⟩

/-- Why this unblocks `apm_m02j05`: this is the complete `sInf` theory for
the Luxemburg gauge on the rescalable modular class: nonnegativity,
definiteness modulo a.e. equality, absolute homogeneity, and the triangle
inequality. -/
lemma apm_m02J05_lux_sublevel_attained_aux_bdd
    (α : ℝ → ℝ) (u : apm_m02J05_Fun) :
    BddBelow (apm_m02J05_luxSublevel α u) := by
  refine ⟨0, ?_⟩
  intro c hc
  exact hc.1.le

lemma apm_m02J05_lux_sublevel_attained_aux_nonneg
    (α : ℝ → ℝ) (u : apm_m02J05_Fun)
    (hne : (apm_m02J05_luxSublevel α u).Nonempty) :
    0 ≤ apm_m02J05_lux α u := by
  unfold apm_m02J05_lux
  exact le_csInf hne (fun c hc ↦ hc.1.le)

lemma apm_m02J05_lux_sublevel_attained_aux_zero_mem
    (α : ℝ → ℝ) :
    (1 : ℝ) ∈ apm_m02J05_luxSublevel α (0 : apm_m02J05_Fun) := by
  refine ⟨one_pos, ?_, ?_⟩
  · apply integrableOn_zero.congr
    filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
      (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
    rw [hx]
    simp [apm_m02J05_young_zero]
  · have hz : (fun x ↦ apm_m02J05_young α
        (|(0 : apm_m02J05_Fun) x| / (1 : ℝ))) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] 0 := by
      filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
        (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
      rw [hx]
      simp [apm_m02J05_young_zero]
    rw [integral_congr_ae hz]
    norm_num

lemma apm_m02J05_lux_sublevel_attained_aux_core
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    ∀ u ∈ apm_m02J05_L α,
      (apm_m02J05_luxSublevel α u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel α u) ∧
      0 ≤ apm_m02J05_lux α u ∧
      (u ≠ 0 → apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u) := by
  sorry

theorem apm_m02J05_lux_sublevel_attained
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    ∀ u ∈ apm_m02J05_L α,
      (apm_m02J05_luxSublevel α u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel α u) ∧
      0 ≤ apm_m02J05_lux α u ∧
      (u ≠ 0 → apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u) := by
  exact apm_m02J05_lux_sublevel_attained_aux_core α hc hmono hzero hinfty hnonneg

theorem apm_m02J05_lux_definite
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    ∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0 := by
  sorry

theorem apm_m02J05_lux_homogeneous
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    ∀ u ∈ apm_m02J05_L α, ∀ c : ℝ,
      apm_m02J05_lux α (c • u) = |c| * apm_m02J05_lux α u := by
  sorry

theorem apm_m02J05_lux_triangle_of_facts
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (hshape : apm_m02J05_YoungShapeFact α)
    (hsublevel : ∀ u ∈ apm_m02J05_L α,
      (apm_m02J05_luxSublevel α u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel α u) ∧
      0 ≤ apm_m02J05_lux α u ∧
      (u ≠ 0 → apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u)) :
    ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L α,
      apm_m02J05_lux α (u + v) ≤
        apm_m02J05_lux α u + apm_m02J05_lux α v := by
  sorry

theorem apm_m02J05_bridge_convex_and_submodule
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    Convex ℝ (apm_m02J05_K α) ∧
      ∃ S : Submodule ℝ apm_m02J05_Fun,
        (S : Set apm_m02J05_Fun) = apm_m02J05_L α := by
  exact apm_m02J05_bridge_convex_and_submodule_of_young_shape α hc hmono
    hzero hinfty hnonneg (apm_m02J05_young_shape α hc hmono hzero hnonneg)

theorem apm_m02J05_bridge_luxemburg_laws
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    (∀ u ∈ apm_m02J05_L α, 0 ≤ apm_m02J05_lux α u) ∧
      (∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0) ∧
      (∀ u ∈ apm_m02J05_L α, ∀ c : ℝ,
        apm_m02J05_lux α (c • u) = |c| * apm_m02J05_lux α u) ∧
      ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L α,
        apm_m02J05_lux α (u + v) ≤
          apm_m02J05_lux α u + apm_m02J05_lux α v := by
  have hshape := apm_m02J05_young_shape α hc hmono hzero hnonneg
  have hsub := apm_m02J05_lux_sublevel_attained α hc hmono hzero hinfty hnonneg
  exact ⟨fun u hu ↦ (hsub u hu).2.2.1,
    apm_m02J05_lux_definite α hc hmono hzero hinfty hnonneg,
    apm_m02J05_lux_homogeneous α hc hmono hzero hinfty hnonneg,
    apm_m02J05_lux_triangle_of_facts α hc hmono hzero hinfty hnonneg hshape hsub⟩

/-- Why this unblocks `apm_m02j05`: this packages the complementary integral
identity for inverse functions into pointwise Young's inequality and the
resulting normalized Orlicz--Hölder estimate. It supplies the final two
conjuncts of the frozen theorem. -/
theorem apm_m02J05_inverse_partner_lux_facts
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    (∀ u ∈ apm_m02J05_L β,
      (apm_m02J05_luxSublevel β u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel β u) ∧
      0 ≤ apm_m02J05_lux β u ∧
      (u ≠ 0 → apm_m02J05_lux β u ∈ apm_m02J05_luxSublevel β u)) ∧
    (∀ u ∈ apm_m02J05_L β, apm_m02J05_lux β u = 0 ↔ u = 0) := by
  sorry

theorem apm_m02J05_bridge_complementary_young_holder_of_lux_facts
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t)
    (hsubα : ∀ u ∈ apm_m02J05_L α,
      (apm_m02J05_luxSublevel α u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel α u) ∧
      0 ≤ apm_m02J05_lux α u ∧
      (u ≠ 0 → apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u))
    (hsubβ : ∀ u ∈ apm_m02J05_L β,
      (apm_m02J05_luxSublevel β u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel β u) ∧
      0 ≤ apm_m02J05_lux β u ∧
      (u ≠ 0 → apm_m02J05_lux β u ∈ apm_m02J05_luxSublevel β u))
    (hdefα : ∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0)
    (hdefβ : ∀ u ∈ apm_m02J05_L β, apm_m02J05_lux β u = 0 ↔ u = 0) :
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t) ∧
      ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L β,
        ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume ≤
          2 * apm_m02J05_lux α u * apm_m02J05_lux β v := by
  sorry

theorem apm_m02J05_bridge_complementary_young_holder
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t) ∧
      ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L β,
        ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume ≤
          2 * apm_m02J05_lux α u * apm_m02J05_lux β v := by
  have hαnonneg : ∀ t, 0 ≤ t → 0 ≤ α t := fun t ht ↦ (hnonneg t ht).1
  have hsubα := apm_m02J05_lux_sublevel_attained α hαc hαmono hαzero
    hαinfty hαnonneg
  have hdefα := apm_m02J05_lux_definite α hαc hαmono hαzero hαinfty hαnonneg
  have hβfacts := apm_m02J05_inverse_partner_lux_facts α β hαc hαmono
    hαzero hαinfty hβc hnonneg hβα hαβ
  exact apm_m02J05_bridge_complementary_young_holder_of_lux_facts α β hαc
    hαmono hαzero hαinfty hβc hnonneg hβα hαβ hsubα hβfacts.1 hdefα hβfacts.2

theorem apm_m02j05 :
    ∀ (α β : ℝ → ℝ),
      ContinuousOn α (Ici 0) →
      StrictMonoOn α (Ici 0) →
      α 0 = 0 →
      Tendsto α atTop atTop →
      ContinuousOn β (Ici 0) →
      (∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t) →
      (∀ t, 0 ≤ t → β (α t) = t) →
      (∀ t, 0 ≤ t → α (β t) = t) →
      Convex ℝ (apm_m02J05_K α) ∧
      (∃ S : Submodule ℝ apm_m02J05_Fun,
        (S : Set apm_m02J05_Fun) = apm_m02J05_L α) ∧
      ((∀ u ∈ apm_m02J05_L α, 0 ≤ apm_m02J05_lux α u) ∧
        (∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0) ∧
        (∀ u ∈ apm_m02J05_L α, ∀ c : ℝ,
          apm_m02J05_lux α (c • u) = |c| * apm_m02J05_lux α u) ∧
        (∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L α,
          apm_m02J05_lux α (u + v) ≤
            apm_m02J05_lux α u + apm_m02J05_lux α v)) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t) ∧
      (∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L β,
        ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume ≤
          2 * apm_m02J05_lux α u * apm_m02J05_lux β v) := by
  /-
  CLOSER HOP 1 (partial). The zero-value infrastructure is now compiled:
  `apm_m02J05_young_zero`, `apm_m02J05_zero_mem_K`, and
  `apm_m02J05_zero_mem_L` establish the base cases required by convexity and
  the proposed submodule structure.

  Searches of Mathlib and compiled
  siblings found no packaged Young-function, complementary-function, Orlicz
  space, or Luxemburg-norm API. The available theorems named
  `young_inequality` concern Hölder-conjugate powers, not the general inverse
  pair `α`, `β` used here.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib, prior
  solved problems, and git history found no stronger general-purpose bridge.
  A proof must therefore build the remaining theory in this file: convexity and
  monotonicity of the interval-integral primitive from `StrictMonoOn α`,
  stability and common rescaling of `AEEqFun`s, nonemptiness and attainment of
  the `sInf` modular sublevel set (dominated convergence plus Fatou),
  definiteness modulo a.e. equality, homogeneity and the triangle inequality,
  and finally the complementary-integral Young identity followed by the
  normalized integral estimate. No solved sibling supplies that combined
  bridge, so no sibling code was reused and the frozen statement was left
  unchanged.

  Closer hop 3 starts the missing primitive theory directly.
  `apm_m02J05_young_nonneg` proves nonnegativity of the interval-integral
  Young function, and `apm_m02J05_young_mono` proves its monotonicity on the
  nonnegative half-line using `intervalIntegral.integral_mono_interval` and
  continuity for interval integrability. Searches additionally inspected
  Mathlib's convex-integral and Fenchel/Young inequalities; the latter remain
  specialized to power conjugates and do not apply to the supplied inverse
  pair. The remaining bridge is still broad: upgrade primitive monotonicity
  to convexity, build the rescaling submodule on `AEEqFun`, establish the
  `sInf` attainment/definiteness/homogeneity/triangle theory, and prove the
  complementary integral identity. This final hop did not complete that
  self-contained Orlicz development.
  -/
  intro α β hαc hαmono hαzero hαinfty hβc hnonneg hβα hαβ
  have hαnonneg : ∀ t, 0 ≤ t → 0 ≤ α t := fun t ht ↦ (hnonneg t ht).1
  have hstruct := apm_m02J05_bridge_convex_and_submodule α hαc hαmono
    hαzero hαinfty hαnonneg
  have hlux := apm_m02J05_bridge_luxemburg_laws α hαc hαmono
    hαzero hαinfty hαnonneg
  have hcomp := apm_m02J05_bridge_complementary_young_holder α β hαc
    hαmono hαzero hαinfty hβc hnonneg hβα hαβ
  exact ⟨hstruct.1, hstruct.2, hlux, hcomp.1, hcomp.2⟩

#print axioms apm_m02j05

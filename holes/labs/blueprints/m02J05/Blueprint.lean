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

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_scale
    (α : ℝ → ℝ) (hshape : apm_m02J05_YoungShapeFact α)
    {θ t : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ht : 0 ≤ t) :
    apm_m02J05_young α (θ * t) ≤ θ * apm_m02J05_young α t := by
  have hc := hshape.1.2 (show (0 : ℝ) ∈ Ici 0 by simp)
    (show t ∈ Ici 0 by exact ht) (sub_nonneg.mpr hθ1) hθ0 (by ring)
  simpa [apm_m02J05_young_zero] using hc

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty_aux_continuous
    (α : ℝ → ℝ) (hc : ContinuousOn α (Ici 0)) :
    ContinuousOn (apm_m02J05_young α) (Ici 0) := by
  intro x hx
  have hxb : x < x + 1 := by linarith
  have hi : IntegrableOn α (uIcc (0 : ℝ) (x + 1)) := by
    rw [uIcc_of_le (hx.trans hxb.le)]
    exact (hc.mono Icc_subset_Ici_self).integrableOn_Icc
  have hlocal : ContinuousOn (apm_m02J05_young α) (Icc 0 (x + 1)) := by
    simpa [apm_m02J05_young, uIcc_of_le (hx.trans hxb.le)] using
      (intervalIntegral.continuousOn_primitive_interval hi)
  apply (hlocal x ⟨hx, hxb.le⟩).mono_of_mem_nhdsWithin (s := Ici 0)
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    ⟨Iio (x + 1), Iio_mem_nhds hxb, ?_⟩
  rintro y ⟨hy, hy0⟩
  exact ⟨hy0, hy.le⟩

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty_aux_scaled
    (α : ℝ → ℝ) (hshape : apm_m02J05_YoungShapeFact α)
    {c M z w : ℝ} (hc : c ≠ 0) (hM : 1 ≤ M) (hz : 0 ≤ z)
    (hw : |w| = |c| * z) :
    apm_m02J05_young α (z / (M / |c|)) ≤
      (1 / M) * apm_m02J05_young α |w| := by
  have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hc
  have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM)
  have heq : z / (M / |c|) = (1 / M) * |w| := by
    rw [hw]
    field_simp
  rw [heq]
  exact apm_m02J05_lux_sublevel_attained_aux_core_aux_scale α hshape
    (by positivity) ((div_le_one (by linarith : 0 < M)).2 hM)
    (abs_nonneg w)

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) :
    (apm_m02J05_luxSublevel α u).Nonempty := by
  rcases hu with ⟨c, hcn, hcu⟩
  let F : ℝ → ℝ := fun x ↦ apm_m02J05_young α |(c • u) x|
  let A : ℝ := ∫ x in Icc (0 : ℝ) 1, F x
  let M : ℝ := max 1 A
  let lam : ℝ := M / |c|
  have hM : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hcabs : 0 < |c| := abs_pos.mpr hcn
  have hlam : 0 < lam := div_pos hMpos hcabs
  have hshape := apm_m02J05_young_shape α hc hmono hzero hnonneg
  have hdom : (fun x ↦ apm_m02J05_young α (|u x| / lam)) ≤ᵐ[
      volume.restrict (Icc (0 : ℝ) 1)] fun x ↦ (1 / M) * F x := by
    filter_upwards [AEEqFun.coeFn_smul c u] with x hx
    apply apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty_aux_scaled
      α hshape hcn hM (abs_nonneg (u x))
    rw [hx]
    simp [abs_mul]
  have hF : Integrable F (volume.restrict (Icc (0 : ℝ) 1)) := hcu
  have hright : Integrable (fun x ↦ (1 / M) * F x)
      (volume.restrict (Icc (0 : ℝ) 1)) := hF.const_mul _
  have hYcont :=
    apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty_aux_continuous α hc
  have hYmax : Continuous (fun t : ℝ ↦ apm_m02J05_young α (max t 0)) := by
    simpa only [Function.comp_apply] using hYcont.comp_continuous
      (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)
  have harg : AEStronglyMeasurable (fun x ↦ |u x| / lam)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (continuous_abs.div_const lam).comp_aestronglyMeasurable u.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun x ↦ apm_m02J05_young α (|u x| / lam))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    rcases hYmax.comp_aestronglyMeasurable harg with ⟨g, hg, heq⟩
    refine ⟨g, hg, ?_⟩
    filter_upwards [heq] with x hx
    simpa [max_eq_left (div_nonneg (abs_nonneg _) hlam.le)] using hx
  have hleft : Integrable (fun x ↦ apm_m02J05_young α (|u x| / lam))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply hright.mono' hmeas
    filter_upwards [hdom] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (apm_m02J05_young_nonneg hnonneg (div_nonneg (abs_nonneg _) hlam.le))]
    exact hx
  refine ⟨lam, hlam, hleft, ?_⟩
  calc
    (∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / lam))
        ≤ ∫ x in Icc (0 : ℝ) 1, (1 / M) * F x :=
          integral_mono_ae hleft hright hdom
    _ = (1 / M) * A := by rw [MeasureTheory.integral_const_mul]
    _ ≤ 1 := by
      have hAM : A ≤ M := le_max_right _ _
      calc
        (1 / M) * A ≤ (1 / M) * M := mul_le_mul_of_nonneg_left hAM (by positivity)
        _ = 1 := by field_simp

lemma apm_m02J05_lux_definite_aux_nonzero_aux_young_lower
    (α : ℝ → ℝ) (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    {t : ℝ} (ht : 1 ≤ t) :
    (t - 1) * α 1 ≤ apm_m02J05_young α t := by
  have hi01 : IntervalIntegrable α volume 0 1 :=
    (hc.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc zero_le_one
  have hi1t : IntervalIntegrable α volume 1 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    exact hc.mono (fun x hx => mem_Ici.mpr (zero_le_one.trans hx.1))
  have hconst : IntervalIntegrable (fun _ : ℝ => α 1) volume 1 t :=
    _root_.intervalIntegrable_const
  have htail : (t - 1) * α 1 ≤ ∫ x in (1 : ℝ)..t, α x := by
    have heq : (∫ _x in (1 : ℝ)..t, α 1) = (t - 1) * α 1 := by
      simp
    rw [← heq]
    apply intervalIntegral.integral_mono_on ht hconst hi1t
    intro x hx
    exact hmono.monotoneOn (mem_Ici.mpr zero_le_one)
      (mem_Ici.mpr (zero_le_one.trans hx.1)) hx.1
  have hhead : 0 ≤ ∫ x in (0 : ℝ)..1, α x :=
    intervalIntegral.integral_nonneg zero_le_one (fun x hx => hnonneg x hx.1)
  unfold apm_m02J05_young
  rw [← intervalIntegral.integral_add_adjacent_intervals hi01 hi1t]
  linarith

lemma apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_small
    (α : ℝ → ℝ) (u : apm_m02J05_Fun)
    (hne : (apm_m02J05_luxSublevel α u).Nonempty)
    (hz : apm_m02J05_lux α u = 0) :
    ∀ δ : ℝ, 0 < δ → ∃ c ∈ apm_m02J05_luxSublevel α u, c < δ := by
  intro δ hδ
  apply exists_lt_of_csInf_lt hne
  change sInf (apm_m02J05_luxSublevel α u) = 0 at hz
  rw [hz]
  exact hδ

lemma apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_level
    (u : apm_m02J05_Fun) (hu0 : u ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      0 < volume.restrict (Icc (0 : ℝ) 1) {x | ε < |u x|} := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let s : ℕ → Set ℝ := fun n => {x | (1 : ℝ) / (n + 1) < |u x|}
  have hs_union : (⋃ n, s n) = {x | u x ≠ 0} := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩ hux
      dsimp [s] at hn
      rw [hux, abs_zero] at hn
      exact (not_lt_of_ge (by positivity)) hn
    · intro hux
      have habs : 0 < |u x| := abs_pos.mpr hux
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt habs
      exact ⟨n, hn⟩
  have hμunion : μ (⋃ n, s n) ≠ 0 := by
    intro hz
    have hae : ∀ᵐ x ∂μ, u x = 0 := by
      rw [ae_iff]
      simpa [hs_union] using hz
    apply hu0
    apply AEEqFun.ext
    filter_upwards [hae, AEEqFun.coeFn_zero (α := ℝ) (β := ℝ) (μ := μ)]
      with x hx hz0
    exact hx.trans hz0.symm
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hμunion
  refine ⟨(1 : ℝ) / (n + 1), by positivity, ?_⟩
  exact hn

lemma apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_contradiction_aux_alpha_one
    (α : ℝ → ℝ) (hmono : StrictMonoOn α (Ici 0)) (hzero : α 0 = 0) :
    0 < α 1 := by
  rw [← hzero]
  exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one) zero_lt_one

lemma apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_contradiction_aux_integral
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) (hu0 : u ≠ 0) :
    apm_m02J05_lux α u ≠ 0 := by
  intro hz
  obtain ⟨ε, hε, hm⟩ := apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_level u hu0
  have hne := apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty α hc hmono hzero hinfty
    hnonneg u hu
  have hα1 : 0 < α 1 := by
    have := hmono (Set.left_mem_Ici) (show (1 : ℝ) ∈ Ici (0 : ℝ) from Set.mem_Ici.2 zero_le_one) zero_lt_one
    rwa [hzero] at this
  set μ := volume.restrict (Icc (0 : ℝ) 1) with hμ
  set S := {x | ε < |u x|} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const (u.stronglyMeasurable.measurable.abs)
  have hfin : μ S < ⊤ := by
    calc μ S ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = volume (Icc (0 : ℝ) 1) := by simp [hμ]
      _ < ⊤ := by simp
  set mR := (μ S).toReal with hmR
  have hmRpos : 0 < mR := ENNReal.toReal_pos hm.ne' hfin.ne
  set δ := ε / (2 + 1 / (mR * α 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨c, hcS, hcδ⟩ := apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_small α u hne hz δ hδpos
  obtain ⟨hc0, hcint, hcle⟩ := hcS
  have hcε : c < ε := lt_of_lt_of_le hcδ (div_le_self hε.le (by
    have : 0 ≤ 1 / (mR * α 1) := by positivity
    linarith))
  set K := (ε / c - 1) * α 1 with hK
  have hYnn : ∀ t, 0 ≤ t → 0 ≤ apm_m02J05_young α t := fun t ht =>
    intervalIntegral.integral_nonneg ht (fun x hx => hnonneg x hx.1)
  have hpt : ∀ x, S.indicator (fun _ => K) x ≤ apm_m02J05_young α (|u x| / c) := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      have hx' : ε < |u x| := hx
      have h1 : 1 ≤ |u x| / c := by
        rw [le_div_iff₀ hc0]; linarith
      refine le_trans ?_ (apm_m02J05_lux_definite_aux_nonzero_aux_young_lower α hc hmono hnonneg h1)
      apply mul_le_mul_of_nonneg_right _ hα1.le
      have : ε / c ≤ |u x| / c := div_le_div_of_nonneg_right hx'.le hc0.le
      linarith
    · rw [Set.indicator_of_notMem hx]
      exact hYnn _ (div_nonneg (abs_nonneg _) hc0.le)
  have hlow : K * mR ≤ ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / c) ∂volume := by
    have := integral_mono ((integrable_const K).indicator hSmeas |>.mono_measure le_rfl) hcint hpt
    rw [integral_indicator_const _ hSmeas, smul_eq_mul] at this
    convert this using 1
    rw [hmR, measureReal_def, mul_comm]
  have hK1 : 1 < K * mR := by
    have hεc : ε / δ < ε / c := div_lt_div_of_pos_left hε hc0 hcδ
    have hεδ : ε / δ = 2 + 1 / (mR * α 1) := by
      rw [hδ]; field_simp
    have : 1 + 1 / (mR * α 1) < ε / c - 1 + 0 := by linarith
    have hpos : 0 < mR * α 1 := mul_pos hmRpos hα1
    calc (1 : ℝ) < (1 + 1 / (mR * α 1)) * (mR * α 1) := by
          rw [add_mul, one_div, inv_mul_cancel₀ hpos.ne']; nlinarith
      _ ≤ (ε / c - 1) * (mR * α 1) := by
          apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
      _ = K * mR := by rw [hK]; ring
  linarith

lemma apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_contradiction
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) (hu0 : u ≠ 0) :
    apm_m02J05_lux α u ≠ 0 := by
  exact apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_contradiction_aux_integral
    α hc hmono hzero hinfty hnonneg u hu hu0

lemma apm_m02J05_lux_definite_aux_nonzero_aux_core
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) (hu0 : u ≠ 0) :
    apm_m02J05_lux α u ≠ 0 := by
  exact apm_m02J05_lux_definite_aux_nonzero_aux_core_aux_contradiction
    α hc hmono hzero hinfty hnonneg u hu hu0

lemma apm_m02J05_lux_definite_aux_nonzero
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) (hu0 : u ≠ 0) :
    apm_m02J05_lux α u ≠ 0 := by
  exact apm_m02J05_lux_definite_aux_nonzero_aux_core α hc hmono hzero hinfty hnonneg
    u hu hu0

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_bounds
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) :
    (apm_m02J05_luxSublevel α u).Nonempty ∧
      BddBelow (apm_m02J05_luxSublevel α u) ∧
      0 ≤ apm_m02J05_lux α u ∧
      ∀ c ∈ apm_m02J05_luxSublevel α u, apm_m02J05_lux α u ≤ c := by
  have hne := apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty
    α hc hmono hzero hinfty hnonneg u hu
  have hb := apm_m02J05_lux_sublevel_attained_aux_bdd α u
  refine ⟨hne, hb, apm_m02J05_lux_sublevel_attained_aux_nonneg α u hne, ?_⟩
  intro c hcsub
  exact csInf_le hb hcsub

/-- Coercivity at zero: a nonzero a.e.-class has strictly positive Luxemburg
gauge because `α → ∞`, hence its Young primitive diverges along every set on
which `|u|` is bounded below by a positive constant. -/
lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_pos
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α) (hu0 : u ≠ 0) :
    0 < apm_m02J05_lux α u := by
  exact lt_of_le_of_ne (apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_bounds α hc hmono hzero hinfty hnonneg u hu).2.2.1
    (apm_m02J05_lux_definite_aux_nonzero α hc hmono hzero hinfty hnonneg u hu hu0).symm

/-- Sequential closedness of the modular sublevel at its positive infimum,
using monotone convergence for `young (|u| / cₙ)` as `cₙ ↓ sInf`. -/
lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed_aux_sequence
    (α : ℝ → ℝ) (u : apm_m02J05_Fun)
    (hne : (apm_m02J05_luxSublevel α u).Nonempty)
    (hb : BddBelow (apm_m02J05_luxSublevel α u)) :
    ∃ c : ℕ → ℝ, ∀ n,
      c n ∈ apm_m02J05_luxSublevel α u ∧
      apm_m02J05_lux α u ≤ c n ∧
      c n < apm_m02J05_lux α u + 1 / (n + 1 : ℝ) := by
  have hex : ∀ n : ℕ, ∃ c ∈ apm_m02J05_luxSublevel α u,
      c < apm_m02J05_lux α u + 1 / (n + 1 : ℝ) := by
    intro n
    apply exists_lt_of_csInf_lt hne
    unfold apm_m02J05_lux
    have hp : 0 < (1 / (n + 1 : ℝ)) := by positivity
    exact lt_add_of_pos_right _ hp
  choose c hc hclt using hex
  refine ⟨c, fun n ↦ ⟨hc n, ?_, hclt n⟩⟩
  unfold apm_m02J05_lux
  exact csInf_le hb (hc n)

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed_aux_sequence_tendsto
    (α : ℝ → ℝ) (u : apm_m02J05_Fun) (c : ℕ → ℝ)
    (hc : ∀ n, apm_m02J05_lux α u ≤ c n ∧
      c n < apm_m02J05_lux α u + 1 / (n + 1 : ℝ)) :
    Tendsto c atTop (nhds (apm_m02J05_lux α u)) := by
  have hupp : Tendsto (fun n : ℕ ↦ apm_m02J05_lux α u + 1 / (n + 1 : ℝ))
      atTop (nhds (apm_m02J05_lux α u)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
  · exact fun n ↦ (hc n).1
  · exact fun n ↦ (hc n).2.le

/-- Fatou closedness for the modular along a positive minimizing sequence. -/
lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed_aux_fatou
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun)
    (hpos : 0 < apm_m02J05_lux α u)
    (c : ℕ → ℝ) (hcsub : ∀ n, c n ∈ apm_m02J05_luxSublevel α u)
    (hct : Tendsto c atTop (nhds (apm_m02J05_lux α u))) :
    apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let lam := apm_m02J05_lux α u
  let F : ℝ → ℝ := fun x ↦ apm_m02J05_young α (|u x| / lam)
  let Fn : ℕ → ℝ → ℝ := fun n x ↦ apm_m02J05_young α (|u x| / c n)
  have hYcont :=
    apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty_aux_continuous α hc
  have hYmax : Continuous (fun t : ℝ ↦ apm_m02J05_young α (max t 0)) := by
    simpa only [Function.comp_apply] using hYcont.comp_continuous
      (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)
  have hcpos : ∀ n, 0 < c n := fun n ↦ (hcsub n).1
  have hFn_nonneg : ∀ n, 0 ≤ᵐ[μ] Fn n := fun n ↦
    Eventually.of_forall fun x ↦ apm_m02J05_young_nonneg hnonneg
      (div_nonneg (abs_nonneg _) (hcpos n).le)
  have hF_nonneg : 0 ≤ᵐ[μ] F := Eventually.of_forall fun x ↦
    apm_m02J05_young_nonneg hnonneg (div_nonneg (abs_nonneg _) hpos.le)
  have hFn_meas : ∀ n, AEStronglyMeasurable (Fn n) μ := by
    intro n
    have ha := (continuous_abs.div_const (c n)).comp_aestronglyMeasurable
      u.aestronglyMeasurable
    rcases hYmax.comp_aestronglyMeasurable ha with ⟨g, hg, heq⟩
    refine ⟨g, hg, ?_⟩
    filter_upwards [heq] with x hx
    simpa [Fn, max_eq_left (div_nonneg (abs_nonneg _) (hcpos n).le)] using hx
  have hF_meas : AEStronglyMeasurable F μ := by
    have ha := (continuous_abs.div_const lam).comp_aestronglyMeasurable
      u.aestronglyMeasurable
    rcases hYmax.comp_aestronglyMeasurable ha with ⟨g, hg, heq⟩
    refine ⟨g, hg, ?_⟩
    filter_upwards [heq] with x hx
    simpa [F, lam, max_eq_left (div_nonneg (abs_nonneg _) hpos.le)] using hx
  have hlim (x : ℝ) : Tendsto (fun n ↦ ENNReal.ofReal (Fn n x)) atTop
      (nhds (ENNReal.ofReal (F x))) := by
    have hdiv : Tendsto (fun n ↦ |u x| / c n) atTop
        (nhds (|u x| / lam)) := by
      exact tendsto_const_nhds.div (by simpa [lam] using hct) (ne_of_gt hpos)
    have hym := hYmax.continuousAt.tendsto.comp hdiv
    have hy : Tendsto (fun n ↦ Fn n x) atTop (nhds (F x)) := by
      have hym' : Tendsto (fun n ↦ apm_m02J05_young α (|u x| / c n)) atTop
          (nhds (apm_m02J05_young α (max (|u x| / lam) 0))) := by
        apply hym.congr'
        exact Eventually.of_forall fun n ↦ by
          simp [max_eq_left (div_nonneg (abs_nonneg _) (hcpos n).le)]
      rw [max_eq_left (div_nonneg (abs_nonneg _) hpos.le)] at hym'
      simpa [Fn, F] using hym'
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hy
  have hfatou := lintegral_liminf_le' (μ := μ)
    (fun n ↦ (hFn_meas n).aemeasurable.ennreal_ofReal)
  have hleft : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤
      liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (Fn n x) ∂μ) atTop := by
    rw [show (∫⁻ x, ENNReal.ofReal (F x) ∂μ) =
        ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (Fn n x)) atTop ∂μ by
      apply lintegral_congr
      intro x
      exact (hlim x).liminf_eq.symm]
    exact hfatou
  have heach : ∀ n, (∫⁻ x, ENNReal.ofReal (Fn n x) ∂μ) ≤ 1 := by
    intro n
    have hi : Integrable (Fn n) μ := (hcsub n).2.1
    rw [← ofReal_integral_eq_lintegral_ofReal hi (hFn_nonneg n)]
    change ENNReal.ofReal (∫ x in Icc (0 : ℝ) 1,
      apm_m02J05_young α (|u x| / c n)) ≤ 1
    simpa using ENNReal.ofReal_le_ofReal ((hcsub n).2.2)
  have hright : liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (Fn n x) ∂μ) atTop ≤ 1 :=
    liminf_le_of_frequently_le (Frequently.of_forall heach)
  have hlin : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ 1 := hleft.trans hright
  have hFint : Integrable F μ := ⟨hF_meas,
    (hasFiniteIntegral_iff_ofReal hF_nonneg).2 (hlin.trans_lt ENNReal.one_lt_top)⟩
  refine ⟨hpos, hFint, ?_⟩
  have hint : (∫ x, F x ∂μ) = (∫⁻ x, ENNReal.ofReal (F x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF_nonneg hF_meas
  rw [show (fun x ↦ apm_m02J05_young α (|u x| / apm_m02J05_lux α u)) = F by
    rfl, hint]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hlin)

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α)
    (hpos : 0 < apm_m02J05_lux α u) :
    apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u := by
  have hne := apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty
    α hc hmono hzero hinfty hnonneg u hu
  have hb := apm_m02J05_lux_sublevel_attained_aux_bdd α u
  obtain ⟨c, hcsub⟩ :=
    apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed_aux_sequence
      α u hne hb
  apply apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed_aux_fatou
    α hc hmono hzero hnonneg u hpos c (fun n ↦ (hcsub n).1)
  exact apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed_aux_sequence_tendsto
    α u c (fun n ↦ ⟨(hcsub n).2.1, (hcsub n).2.2⟩)

lemma apm_m02J05_lux_sublevel_attained_aux_core_aux_attained
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (u : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α)
    (hu0 : u ≠ 0) :
    apm_m02J05_lux α u ∈ apm_m02J05_luxSublevel α u := by
  apply apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_closed
    α hc hmono hzero hinfty hnonneg u hu
  exact apm_m02J05_lux_sublevel_attained_aux_core_aux_attained_aux_pos
    α hc hmono hzero hinfty hnonneg u hu hu0

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
  intro u hu
  have hne := apm_m02J05_lux_sublevel_attained_aux_core_aux_nonempty
    α hc hmono hzero hinfty hnonneg u hu
  exact ⟨hne, apm_m02J05_lux_sublevel_attained_aux_bdd α u,
    apm_m02J05_lux_sublevel_attained_aux_nonneg α u hne,
    apm_m02J05_lux_sublevel_attained_aux_core_aux_attained
      α hc hmono hzero hinfty hnonneg u hu⟩

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

lemma apm_m02J05_lux_definite_aux_zero
    (α : ℝ → ℝ) : apm_m02J05_lux α (0 : apm_m02J05_Fun) = 0 := by
  unfold apm_m02J05_lux
  rw [show {c : ℝ | 0 < c ∧
      IntegrableOn (fun x ↦ apm_m02J05_young α
        (|(0 : apm_m02J05_Fun) x| / c)) (Icc (0 : ℝ) 1) volume ∧
      ∫ x in Icc (0 : ℝ) 1,
        apm_m02J05_young α (|(0 : apm_m02J05_Fun) x| / c) ∂volume ≤ 1} =
      Ioi 0 by
    ext c
    simp only [mem_setOf_eq, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro hc
      refine ⟨hc, ?_, ?_⟩
      · apply integrableOn_zero.congr
        filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
          (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
        rw [hx]
        simp [apm_m02J05_young_zero]
      · have heq : (fun x ↦ apm_m02J05_young α
            (|(0 : apm_m02J05_Fun) x| / c)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
            (fun _ => 0) := by
          filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
            (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
          rw [hx]
          simp [apm_m02J05_young_zero]
        rw [MeasureTheory.integral_congr_ae heq]
        simp]
  exact csInf_Ioi

theorem apm_m02J05_lux_definite
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    ∀ u ∈ apm_m02J05_L α, apm_m02J05_lux α u = 0 ↔ u = 0 := by
  intro u hu
  constructor
  · intro hlux
    by_contra hu0
    exact apm_m02J05_lux_definite_aux_nonzero α hc hmono hzero hinfty hnonneg
      u hu hu0 hlux
  · intro hu0
    subst u
    exact apm_m02J05_lux_definite_aux_zero α

lemma apm_m02J05_lux_homogeneous_aux_abs_div
    (c x d : ℝ) (hc : c ≠ 0) :
    |c * x| / (|c| * d) = |x| / d := by
  rw [abs_mul]
  field_simp [abs_ne_zero.mpr hc]

-- For c ≠ 0 the Luxemburg sublevel of c • u is the |c|-dilate of that of u
-- (use the banked apm_m02J05_lux_homogeneous_aux_abs_div and a.e. congruence (c • u) x = c * u x).
open scoped Pointwise in
local instance : SMul ℝ (Set ℝ) := Set.smulSet

lemma apm_m02J05_lux_homogeneous_aux_sublevel_smul_aux_ae
    (α : ℝ → ℝ) (u : apm_m02J05_Fun) (c d : ℝ) (hc : c ≠ 0) :
    (fun x ↦ apm_m02J05_young α (|(c • u) x| / (|c| * d)))
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
    (fun x ↦ apm_m02J05_young α (|u x| / d)) := by
  filter_upwards [AEEqFun.coeFn_smul c u] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul,
    apm_m02J05_lux_homogeneous_aux_abs_div c (u x) d hc]

lemma apm_m02J05_lux_homogeneous_aux_sublevel_smul_aux_core
    (α : ℝ → ℝ) (u : apm_m02J05_Fun) (c : ℝ) (hc : c ≠ 0) :
    {c' : ℝ | 0 < c' ∧
      IntegrableOn (fun x ↦ apm_m02J05_young α (|(c • u) x| / c')) (Icc (0 : ℝ) 1) volume ∧
      ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|(c • u) x| / c') ∂volume ≤ 1} =
    |c| • {c' : ℝ | 0 < c' ∧
      IntegrableOn (fun x ↦ apm_m02J05_young α (|u x| / c')) (Icc (0 : ℝ) 1) volume ∧
      ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / c') ∂volume ≤ 1} := by
  have habs : 0 < |c| := abs_pos.2 hc
  ext c'
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨hpos, hint, hle⟩
    have hae := apm_m02J05_lux_homogeneous_aux_sublevel_smul_aux_ae α u c (c' / |c|) hc
    have hcc : |c| * (c' / |c|) = c' := by field_simp
    rw [hcc] at hae
    refine ⟨c' / |c|, ⟨div_pos hpos habs, ?_, ?_⟩, by simp [smul_eq_mul, hcc]⟩
    · exact hint.congr hae
    · rw [← integral_congr_ae hae]; exact hle
  · rintro ⟨d, ⟨hpos, hint, hle⟩, rfl⟩
    have hae := apm_m02J05_lux_homogeneous_aux_sublevel_smul_aux_ae α u c d hc
    simp only [smul_eq_mul]
    refine ⟨mul_pos habs hpos, hint.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae]; exact hle

lemma apm_m02J05_lux_homogeneous_aux_sublevel_smul
    (α : ℝ → ℝ) (u : apm_m02J05_Fun) (c : ℝ) (hc : c ≠ 0) :
    {c' : ℝ | 0 < c' ∧
      IntegrableOn (fun x ↦ apm_m02J05_young α (|(c • u) x| / c')) (Icc (0 : ℝ) 1) volume ∧
      ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|(c • u) x| / c') ∂volume ≤ 1} =
    |c| • {c' : ℝ | 0 < c' ∧
      IntegrableOn (fun x ↦ apm_m02J05_young α (|u x| / c')) (Icc (0 : ℝ) 1) volume ∧
      ∫ x in Icc (0 : ℝ) 1, apm_m02J05_young α (|u x| / c') ∂volume ≤ 1} := by
  exact apm_m02J05_lux_homogeneous_aux_sublevel_smul_aux_core α u c hc

lemma apm_m02J05_lux_homogeneous_aux_core
    (alpha : ℝ → ℝ)
    (hc : ContinuousOn alpha (Ici 0))
    (hmono : StrictMonoOn alpha (Ici 0))
    (hzero : alpha 0 = 0)
    (hinfty : Tendsto alpha atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ alpha t) :
    ∀ u ∈ apm_m02J05_L alpha, ∀ c : ℝ,
      apm_m02J05_lux alpha (c • u) = |c| * apm_m02J05_lux alpha u := by
  intro u _ c
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_smul, apm_m02J05_lux_definite_aux_zero, abs_zero, zero_mul]
  · unfold apm_m02J05_lux
    rw [apm_m02J05_lux_homogeneous_aux_sublevel_smul alpha u c hc0, Real.sInf_smul_of_nonneg (abs_nonneg c), smul_eq_mul]

theorem apm_m02J05_lux_homogeneous
    (α : ℝ → ℝ)
    (hc : ContinuousOn α (Ici 0))
    (hmono : StrictMonoOn α (Ici 0))
    (hzero : α 0 = 0)
    (hinfty : Tendsto α atTop atTop)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t) :
    ∀ u ∈ apm_m02J05_L α, ∀ c : ℝ,
      apm_m02J05_lux α (c • u) = |c| * apm_m02J05_lux α u := by
  exact apm_m02J05_lux_homogeneous_aux_core α hc hmono hzero hinfty hnonneg

lemma apm_m02J05_lux_triangle_of_facts_aux_sum_mem
    (α : ℝ → ℝ) (hc : ContinuousOn α (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t)
    (hshape : apm_m02J05_YoungShapeFact α)
    (u v : apm_m02J05_Fun) (hu : u ∈ apm_m02J05_L α)
    (hv : v ∈ apm_m02J05_L α) :
    u + v ∈ apm_m02J05_L α := by
  exact apm_m02J05_bridge_convex_and_submodule_of_young_shape_aux_add
    α hc hnonneg hshape u v hu hv

lemma apm_m02J05_lux_triangle_of_facts_aux_core
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
  exact apm_m02J05_lux_triangle_of_facts_aux_core
    α hc hmono hzero hinfty hnonneg hshape hsublevel

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

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_beta_zero
    (α β : ℝ → ℝ) (hαzero : α 0 = 0)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t) : β 0 = 0 := by
  simpa [hαzero] using hβα 0 le_rfl

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_beta_strictMono
    (α β : ℝ → ℝ)
    (hαmono : StrictMonoOn α (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ β t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    StrictMonoOn β (Ici 0) := by
  intro s hs t ht hst
  have hβs : β s ∈ Ici (0 : ℝ) := mem_Ici.mpr (hnonneg s (mem_Ici.mp hs))
  have hβt : β t ∈ Ici (0 : ℝ) := mem_Ici.mpr (hnonneg t (mem_Ici.mp ht))
  by_contra hnot
  have hle : β t ≤ β s := le_of_not_gt hnot
  have hale : α (β t) ≤ α (β s) := hαmono.monotoneOn hβt hβs hle
  rw [hαβ t (mem_Ici.mp ht), hαβ s (mem_Ici.mp hs)] at hale
  exact (not_le.mpr hst) hale

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_beta_atTop
    (α β : ℝ → ℝ)
    (hαmono : StrictMonoOn α (Ici 0))
    (hnonnegα : ∀ t, 0 ≤ t → 0 ≤ α t)
    (hnonnegβ : ∀ t, 0 ≤ t → 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    Tendsto β atTop atTop := by
  have hβmono : MonotoneOn β (Ici 0) :=
    (apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_beta_strictMono
      α β hαmono hnonnegβ hαβ).monotoneOn
  rw [tendsto_atTop_atTop]
  intro b
  let r : ℝ := max b 0
  refine ⟨α r, ?_⟩
  intro x hx
  have hr : 0 ≤ r := le_max_right _ _
  have hαr : 0 ≤ α r := hnonnegα r hr
  calc
    b ≤ r := le_max_left _ _
    _ = β (α r) := (hβα r hr).symm
    _ ≤ β x := hβmono (mem_Ici.mpr hαr) (mem_Ici.mpr (hαr.trans hx)) hx

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_galois
    (α β : ℝ → ℝ)
    (hαmono : StrictMonoOn α (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    β t ≤ s ↔ t ≤ α s := by
  have hβ0 : 0 ≤ β t := (hnonneg t ht).2
  constructor
  · intro h
    rw [← hαβ t ht]
    exact hαmono.monotoneOn (mem_Ici.mpr hβ0) (mem_Ici.mpr hs) h
  · intro h
    by_contra hn
    have hsb : s < β t := lt_of_not_ge hn
    have halt := hαmono (mem_Ici.mpr hs) (mem_Ici.mpr hβ0) hsb
    rw [hαβ t ht] at halt
    exact (not_lt_of_ge h) halt

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_diagonal_aux_integrable
    (α β : ℝ → ℝ) (hαc : ContinuousOn α (Ici 0))
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable α volume 0 b ∧ IntervalIntegrable β volume 0 (α b) := by
  constructor
  · apply ContinuousOn.intervalIntegrable_of_Icc hb
    exact hαc.mono (Icc_subset_Ici_self)
  · have hab : 0 ≤ α b := (hnonneg b hb).1
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact hβc.mono (Icc_subset_Ici_self)

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_diagonal_aux_zero
    (α β : ℝ → ℝ) (hαzero : α 0 = 0) :
    0 * α 0 ≤ apm_m02J05_young α 0 + apm_m02J05_young β (α 0) := by
  simp [apm_m02J05_young, hαzero]

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_diagonal_aux_pos
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t)
    {b : ℝ} (hb : 0 < b) :
    b * α b ≤ apm_m02J05_young α b + apm_m02J05_young β (α b) := by
  sorry

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_diagonal
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    ∀ b : ℝ, 0 ≤ b →
      b * α b ≤ apm_m02J05_young α b + apm_m02J05_young β (α b) := by
  intro b hb
  rcases hb.eq_or_lt with rfl | hb
  · exact
      apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_diagonal_aux_zero
        α β hαzero
  · exact
      apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_diagonal_aux_pos
        α β hαc hαmono hαzero hβc hnonneg hβα hαβ hb

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_finish
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t := by
  sorry

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t := by
  exact
    apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area_aux_finish
      α β hαc hαmono hαzero hαinfty hβc hnonneg hβα hαβ

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young
    (α β : ℝ → ℝ)
    (hαc : ContinuousOn α (Ici 0))
    (hαmono : StrictMonoOn α (Ici 0))
    (hαzero : α 0 = 0)
    (hαinfty : Tendsto α atTop atTop)
    (hβc : ContinuousOn β (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ α t ∧ 0 ≤ β t)
    (hβα : ∀ t, 0 ≤ t → β (α t) = t)
    (hαβ : ∀ t, 0 ≤ t → α (β t) = t) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t := by
  exact
    apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young_aux_area
      α β hαc hαmono hαzero hαinfty hβc hnonneg hβα hαβ

lemma apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_holder
    (α β : ℝ → ℝ)
    (hyoung : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s * t ≤ apm_m02J05_young α s + apm_m02J05_young β t)
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
    ∀ u ∈ apm_m02J05_L α, ∀ v ∈ apm_m02J05_L β,
      ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume ≤
        2 * apm_m02J05_lux α u * apm_m02J05_lux β v := by
  intro u hu v hv
  by_cases hu0 : u = 0
  · subst u
    have hz : (fun x => (0 : apm_m02J05_Fun) x * v x) =ᵐ[
        volume.restrict (Icc (0 : ℝ) 1)] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
        (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
      simp [hx]
    rw [integral_congr_ae hz]
    have hlux : apm_m02J05_lux α (0 : apm_m02J05_Fun) = 0 :=
      (hdefα (0 : apm_m02J05_Fun) hu).mpr rfl
    rw [hlux]
    norm_num
  by_cases hv0 : v = 0
  · subst v
    have hz : (fun x => u x * (0 : apm_m02J05_Fun) x) =ᵐ[
        volume.restrict (Icc (0 : ℝ) 1)] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [AEEqFun.coeFn_zero (α := ℝ) (β := ℝ)
        (μ := volume.restrict (Icc (0 : ℝ) 1))] with x hx
      simp [hx]
    rw [integral_congr_ae hz]
    have hlux : apm_m02J05_lux β (0 : apm_m02J05_Fun) = 0 :=
      (hdefβ (0 : apm_m02J05_Fun) hv).mpr rfl
    rw [hlux]
    norm_num
  let a := apm_m02J05_lux α u
  let b := apm_m02J05_lux β v
  have ha0 : 0 < a := lt_of_le_of_ne (hsubα u hu).2.2.1
    (fun h => hu0 ((hdefα u hu).mp h.symm))
  have hb0 : 0 < b := lt_of_le_of_ne (hsubβ v hv).2.2.1
    (fun h => hv0 ((hdefβ v hv).mp h.symm))
  have hsa := (hsubα u hu).2.2.2 hu0
  have hsb := (hsubβ v hv).2.2.2 hv0
  have hiA : IntegrableOn (fun x => apm_m02J05_young α (|u x| / a))
      (Icc (0 : ℝ) 1) volume := hsa.2.1
  have hiB : IntegrableOn (fun x => apm_m02J05_young β (|v x| / b))
      (Icc (0 : ℝ) 1) volume := hsb.2.1
  have hiG : IntegrableOn (fun x => a * b *
      (apm_m02J05_young α (|u x| / a) +
       apm_m02J05_young β (|v x| / b))) (Icc (0 : ℝ) 1) volume :=
    (hiA.add hiB).const_mul (a * b)
  have hpoint : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      |u x| * |v x| ≤ a * b *
        (apm_m02J05_young α (|u x| / a) +
         apm_m02J05_young β (|v x| / b)) := by
    filter_upwards [] with x
    have hy := hyoung (|u x| / a) (|v x| / b)
      (div_nonneg (abs_nonneg _) ha0.le) (div_nonneg (abs_nonneg _) hb0.le)
    calc
      |u x| * |v x| = (a * b) * ((|u x| / a) * (|v x| / b)) := by field_simp
      _ ≤ (a * b) * (apm_m02J05_young α (|u x| / a) +
          apm_m02J05_young β (|v x| / b)) :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg ha0.le hb0.le)
  have hmeas : AEStronglyMeasurable (fun x => |u x| * |v x|)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (u.aestronglyMeasurable.norm.mul v.aestronglyMeasurable.norm).congr
      (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
  have hiF : IntegrableOn (fun x => |u x| * |v x|) (Icc (0 : ℝ) 1) volume :=
    hiG.mono' hmeas (hpoint.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  calc
    ∫ x in Icc (0 : ℝ) 1, u x * v x ∂volume
        ≤ ∫ x in Icc (0 : ℝ) 1, |u x| * |v x| ∂volume :=
      integral_mono_ae (hiF.mono' (u.aestronglyMeasurable.mul v.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using (le_abs_self (u x * v x)))) hiF
        (Filter.Eventually.of_forall fun x => by
          simpa [abs_mul] using (le_abs_self (u x * v x)))
    _ ≤ ∫ x in Icc (0 : ℝ) 1, a * b *
          (apm_m02J05_young α (|u x| / a) +
           apm_m02J05_young β (|v x| / b)) ∂volume :=
      integral_mono_ae hiF hiG hpoint
    _ = a * b * ((∫ x in Icc (0 : ℝ) 1,
          apm_m02J05_young α (|u x| / a) ∂volume) +
        ∫ x in Icc (0 : ℝ) 1,
          apm_m02J05_young β (|v x| / b) ∂volume) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hiA hiB]
    _ ≤ a * b * 2 := mul_le_mul_of_nonneg_left (by linarith [hsa.2.2, hsb.2.2])
      (mul_nonneg ha0.le hb0.le)
    _ = 2 * apm_m02J05_lux α u * apm_m02J05_lux β v := by
      dsimp [a, b]
      ring

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
  have hyoung :=
    apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_young
      α β hαc hαmono hαzero hαinfty hβc hnonneg hβα hαβ
  exact ⟨hyoung,
    apm_m02J05_bridge_complementary_young_holder_of_lux_facts_aux_holder
      α β hyoung hsubα hsubβ hdefα hdefβ⟩

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

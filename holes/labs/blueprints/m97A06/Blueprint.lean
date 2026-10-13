import Mathlib


open MeasureTheory

/-!
# APM m97A06 — Euler–Lagrange equation, energy, and Hessian

## Statement repairs

The former part (a) restated the definition of `apm_m97a06_EL` and did not
connect the functional to its Euler–Lagrange equation.  It is replaced by the
first-variation characterization of stationary paths under smooth variations
that vanish at both endpoints.

Part (d) assumes the variation `η` is `C¹` on `[0, T]`, the function class
the problem states. Until 2026-09-30 the clause quantified over every
`η : ℝ → ℝ` with `η 0 = η T = 0`, including non-measurable and
non-integrable ones, where both sides are Lean junk values and the identity
is not a statement about the second variation.
-/

noncomputable def apm_m97a06_I (T : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) T,
    derivWithin φ (Set.Icc 0 T) t ^ 2 / 2 - Real.cos (2 * φ t) / 4

def apm_m97a06_stationary (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Set.Icc 0 T) → η 0 = 0 → η T = 0 →
    DifferentiableAt ℝ
      (fun ε : ℝ => apm_m97a06_I T (fun t => φ t + ε * η t)) 0 ∧
    deriv (fun ε : ℝ => apm_m97a06_I T (fun t => φ t + ε * η t)) 0 = 0

def apm_m97a06_EL (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    deriv (fun s => derivWithin φ (Set.Icc 0 T) s) t = Real.sin (2 * φ t) / 2

noncomputable def apm_m97a06_energy (T : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  derivWithin φ (Set.Icc 0 T) t ^ 2 / 2 + Real.cos (2 * φ t) / 4

noncomputable def apm_m97a06_hessian (T : ℝ) (η : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) T, deriv η t ^ 2 + η t ^ 2

lemma apm_m97A06_zero_EL (T : ℝ) :
    apm_m97a06_EL T (fun _ ↦ 0) := by
  intro t ht
  simp [apm_m97a06_EL]

/-- Along a classical solution, the derivative of the mechanical energy
vanishes at every interior point. -/
lemma apm_m97A06_energy_hasDerivAt_zero
    {T : ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 T))
    (hEL : apm_m97a06_EL T φ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (apm_m97a06_energy T φ) 0 t := by
  have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hφd : HasDerivAt φ (derivWithin φ (Set.Icc 0 T) t) t := by
    have hd := hφ.differentiableOn (by norm_num) t ht'
    exact hd.hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hdd : HasDerivAt (fun s ↦ derivWithin φ (Set.Icc 0 T) s)
      (Real.sin (2 * φ t) / 2) t := by
    have hcd : ContDiffOn ℝ 1 (fun s ↦ derivWithin φ (Set.Icc 0 T) s)
        (Set.Icc 0 T) := hφ.derivWithin
      (uniqueDiffOn_Icc (by linarith [ht.1, ht.2])) (by norm_num)
    have hd := hcd.differentiableOn (by norm_num) t ht'
    have ha := hd.differentiableAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivAt
    convert ha using 1
    exact (hEL t ht).symm
  change HasDerivAt (fun x ↦ derivWithin φ (Set.Icc 0 T) x ^ 2 / 2 +
    Real.cos (2 * φ x) / 4) 0 t
  convert ((hdd.pow 2).div_const 2).add
    (((Real.hasDerivAt_cos (2 * φ t)).comp t (hφd.const_mul 2)).div_const 4) using 1
  all_goals ring

lemma apm_m97A06_energy_constant
    {T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 T))
    (hEL : apm_m97a06_EL T φ) :
    ∃ E, ∀ t ∈ Set.Icc (0 : ℝ) T, apm_m97a06_energy T φ t = E := by
  let E := apm_m97a06_energy T φ (T / 2)
  have hmid : T / 2 ∈ Set.Ioo (0 : ℝ) T := by constructor <;> linarith
  have hd : DifferentiableOn ℝ (apm_m97a06_energy T φ) (Set.Ioo 0 T) :=
    fun t ht ↦ (apm_m97A06_energy_hasDerivAt_zero hφ hEL ht).differentiableAt.differentiableWithinAt
  have heq : Set.EqOn (apm_m97a06_energy T φ) (fun _ ↦ E) (Set.Ioo 0 T) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo 0 T).isPreconnected hd
      (differentiableOn_const E)
    · intro t ht
      rw [(apm_m97A06_energy_hasDerivAt_zero hφ hEL ht).deriv]
      simp
    · exact hmid
    · rfl
  have hdφ : ContDiffOn ℝ 1 (fun t ↦ derivWithin φ (Set.Icc 0 T) t)
      (Set.Icc 0 T) :=
    hφ.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hcont : ContinuousOn (apm_m97a06_energy T φ) (Set.Icc 0 T) := by
    exact ((hdφ.continuousOn.pow 2).div_const 2).add
      ((Real.continuous_cos.comp_continuousOn
        (hφ.continuousOn.const_mul 2)).div_const 4)
  refine ⟨E, ?_⟩
  exact heq.of_subset_closure hcont continuousOn_const Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])

/-- The kinetic part of the action along a scalar line is exactly quadratic,
without any regularity assumption on the direction. -/
lemma apm_m97A06_kinetic_smul (T ε : ℝ) (η : ℝ → ℝ) :
    (∫ t in Set.Icc (0 : ℝ) T,
      derivWithin (ε • η) (Set.Icc 0 T) t ^ 2 / 2) =
      ε ^ 2 / 2 * ∫ t in Set.Icc (0 : ℝ) T, derivWithin η (Set.Icc 0 T) t ^ 2 := by
  change (∫ t in Set.Icc (0 : ℝ) T,
      derivWithin (fun x ↦ ε * η x) (Set.Icc 0 T) t ^ 2 / 2) = _
  simp_rw [derivWithin_const_mul_field]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  ring

lemma apm_m97A06_kinetic_secondDeriv (T : ℝ) (η : ℝ → ℝ) :
    deriv (deriv (fun ε : ℝ ↦ ∫ t in Set.Icc (0 : ℝ) T,
      derivWithin (ε • η) (Set.Icc 0 T) t ^ 2 / 2)) 0 =
      ∫ t in Set.Icc (0 : ℝ) T, derivWithin η (Set.Icc 0 T) t ^ 2 := by
  have heq : (fun ε : ℝ ↦ ∫ t in Set.Icc (0 : ℝ) T,
      derivWithin (ε • η) (Set.Icc 0 T) t ^ 2 / 2) =
      fun ε ↦ ε ^ 2 / 2 * ∫ t in Set.Icc (0 : ℝ) T,
        derivWithin η (Set.Icc 0 T) t ^ 2 := by
    funext ε
    exact apm_m97A06_kinetic_smul T ε η
  rw [heq]
  let A := ∫ t in Set.Icc (0 : ℝ) T, derivWithin η (Set.Icc 0 T) t ^ 2
  have hder : deriv (fun ε : ℝ ↦ ε ^ 2 / 2 * A) = fun ε ↦ ε * A := by
    funext ε
    simpa [id, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (((((hasDerivAt_id (x := ε)).pow 2).div_const 2).mul_const A).deriv)
  change deriv (deriv (fun ε : ℝ ↦ ε ^ 2 / 2 * A)) 0 = A
  rw [hder]
  convert ((hasDerivAt_id (x := (0 : ℝ))).mul_const A).deriv using 1 <;> ring

/-- Integration by parts in the exact within-derivative form used by the
first variation. -/
lemma apm_m97A06_integrationByParts
    {T : ℝ} (hT : 0 < T) {φ η : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 T))
    (hη : ContDiffOn ℝ 2 η (Set.Icc 0 T))
    (hη0 : η 0 = 0) (hηT : η T = 0) :
    (∫ t in Set.Icc (0 : ℝ) T,
      derivWithin φ (Set.Icc 0 T) t * derivWithin η (Set.Icc 0 T) t) =
      -∫ t in Set.Icc (0 : ℝ) T,
        derivWithin (fun s ↦ derivWithin φ (Set.Icc 0 T) s) (Set.Icc 0 T) t * η t := by
  let u := fun t ↦ derivWithin φ (Set.Icc 0 T) t
  let u' := fun t ↦ derivWithin u (Set.Icc 0 T) t
  let v' := fun t ↦ derivWithin η (Set.Icc 0 T) t
  have hu : ContDiffOn ℝ 1 u (Set.Icc 0 T) :=
    hφ.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have huu' : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt u (u' x) (Set.Icc 0 T) x := by
    intro x hx
    exact (hu.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hvv' : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt η (v' x) (Set.Icc 0 T) x := by
    intro x hx
    exact (hη.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hu'int : IntervalIntegrable u' volume 0 T :=
    (hu.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)).intervalIntegrable_of_Icc hT.le
  have hv'int : IntervalIntegrable v' volume 0 T :=
    (hη.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)).intervalIntegrable_of_Icc hT.le
  have huu'' : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivWithinAt u (u' x) (Set.uIcc 0 T) x := by
    simpa [Set.uIcc_of_le hT.le] using huu'
  have hvv'' : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivWithinAt η (v' x) (Set.uIcc 0 T) x := by
    simpa [Set.uIcc_of_le hT.le] using hvv'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    huu'' hvv'' hu'int hv'int
  rw [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hibp
  change (∫ t in Set.Icc (0 : ℝ) T, u t * v' t) = -∫ t in Set.Icc (0 : ℝ) T, u' t * η t
  rw [hibp, hη0, hηT]
  ring

/-- Pointwise parameter derivative of the Lagrangian along an affine
variation. This is the derivative used by dominated differentiation. -/
lemma apm_m97A06_lagrangian_hasDerivAt
    (T ε t : ℝ) (φ η : ℝ → ℝ)
    (hφt : DifferentiableWithinAt ℝ φ (Set.Icc 0 T) t)
    (hηt : DifferentiableWithinAt ℝ η (Set.Icc 0 T) t) :
    HasDerivAt
      (fun e : ℝ ↦
        derivWithin (fun x ↦ φ x + e * η x) (Set.Icc 0 T) t ^ 2 / 2 -
          Real.cos (2 * (φ t + e * η t)) / 4)
      (derivWithin (fun x ↦ φ x + ε * η x) (Set.Icc 0 T) t *
          derivWithin η (Set.Icc 0 T) t +
        Real.sin (2 * (φ t + ε * η t)) * η t / 2) ε := by
  have hlin : (fun e : ℝ ↦
      derivWithin (fun x ↦ φ x + e * η x) (Set.Icc 0 T) t) =
      fun e ↦ derivWithin φ (Set.Icc 0 T) t +
        e * derivWithin η (Set.Icc 0 T) t := by
    funext e
    change derivWithin (φ + e • η) (Set.Icc 0 T) t = _
    rw [derivWithin_add hφt (hηt.const_smul e), derivWithin_const_smul_field]
    rfl
  change HasDerivAt
    (fun e : ℝ ↦
      (fun e ↦ derivWithin (fun x ↦ φ x + e * η x) (Set.Icc 0 T) t) e ^ 2 / 2 -
        Real.cos (2 * (φ t + e * η t)) / 4) _ ε
  rw [hlin]
  have hkin := (((hasDerivAt_const ε (derivWithin φ (Set.Icc 0 T) t)).add
    ((hasDerivAt_id ε).mul_const (derivWithin η (Set.Icc 0 T) t))).pow 2).div_const 2
  have harg : HasDerivAt (fun e : ℝ ↦ 2 * (φ t + e * η t)) (2 * η t) ε := by
    convert ((hasDerivAt_const ε (φ t)).add ((hasDerivAt_id ε).mul_const (η t))).const_mul 2
      using 1 <;> ring
  have hpot := ((Real.hasDerivAt_cos (2 * (φ t + ε * η t))).comp ε harg).div_const 4
  rw [congrFun hlin ε]
  convert hkin.sub hpot using 1 <;> simp [id] <;> ring

lemma apm_m97A06_firstVariation_hasDerivAt
    {T : ℝ} (hT : 0 < T) {φ η : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 T))
    (hη : ContDiffOn ℝ 2 η (Set.Icc 0 T)) :
    HasDerivAt (fun ε : ℝ ↦ apm_m97a06_I T (fun t ↦ φ t + ε * η t))
      (∫ t in Set.Icc (0 : ℝ) T,
        derivWithin φ (Set.Icc 0 T) t * derivWithin η (Set.Icc 0 T) t +
          Real.sin (2 * φ t) * η t / 2) 0 := by
  let μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)
  let F : ℝ → ℝ → ℝ := fun e t ↦
    derivWithin (fun x ↦ φ x + e * η x) (Set.Icc 0 T) t ^ 2 / 2 -
      Real.cos (2 * (φ t + e * η t)) / 4
  let F' : ℝ → ℝ → ℝ := fun e t ↦
    derivWithin (fun x ↦ φ x + e * η x) (Set.Icc 0 T) t *
        derivWithin η (Set.Icc 0 T) t +
      Real.sin (2 * (φ t + e * η t)) * η t / 2
  let bound : ℝ → ℝ := fun t ↦
    (|derivWithin φ (Set.Icc 0 T) t| +
      |derivWithin η (Set.Icc 0 T) t|) *
        |derivWithin η (Set.Icc 0 T) t| + |η t| / 2
  have hφd' : ContDiffOn ℝ 1 (fun t ↦ derivWithin φ (Set.Icc 0 T) t)
      (Set.Icc 0 T) := hφ.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hηd' : ContDiffOn ℝ 1 (fun t ↦ derivWithin η (Set.Icc 0 T) t)
      (Set.Icc 0 T) := hη.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hφd := hφd'.continuousOn
  have hηd := hηd'.continuousOn
  have hbound_cont : ContinuousOn bound (Set.Icc 0 T) := by
    dsimp [bound]
    exact ((hφd.abs.add hηd.abs).mul hηd.abs).add
      (hη.continuousOn.abs.div_const 2)
  have hbound_int : Integrable bound μ := by
    exact hbound_cont.integrableOn_compact isCompact_Icc
  have hdiff : ∀ᵐ t ∂μ, ∀ e ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivAt (F · t) (F' e t) e := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro e he
    exact apm_m97A06_lagrangian_hasDerivAt T e t φ η
      (hφ.differentiableOn (by norm_num) t ht)
      (hη.differentiableOn (by norm_num) t ht)
  have hbound : ∀ᵐ t ∂μ, ∀ e ∈ Set.Icc (-1 : ℝ) 1,
      ‖F' e t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro e he
    have heabs : |e| ≤ 1 := (abs_le).2 he
    have hlin : derivWithin (fun x ↦ φ x + e * η x) (Set.Icc 0 T) t =
        derivWithin φ (Set.Icc 0 T) t + e * derivWithin η (Set.Icc 0 T) t := by
      change derivWithin (φ + e • η) (Set.Icc 0 T) t = _
      rw [derivWithin_add (hφ.differentiableOn (by norm_num) t ht)
        ((hη.differentiableOn (by norm_num) t ht).const_smul e),
        derivWithin_const_smul_field]
      rfl
    dsimp [F', bound]
    rw [hlin]
    calc
      |(derivWithin φ (Set.Icc 0 T) t + e * derivWithin η (Set.Icc 0 T) t) *
          derivWithin η (Set.Icc 0 T) t +
        Real.sin (2 * (φ t + e * η t)) * η t / 2| ≤
          (|derivWithin φ (Set.Icc 0 T) t| +
            |e| * |derivWithin η (Set.Icc 0 T) t|) *
              |derivWithin η (Set.Icc 0 T) t| + |η t| / 2 := by
            calc
              _ ≤ |(derivWithin φ (Set.Icc 0 T) t + e *
                    derivWithin η (Set.Icc 0 T) t) *
                    derivWithin η (Set.Icc 0 T) t| +
                  |Real.sin (2 * (φ t + e * η t)) * η t / 2| := by
                    simpa only [Real.norm_eq_abs] using
                      norm_add_le
                        ((derivWithin φ (Set.Icc 0 T) t + e *
                          derivWithin η (Set.Icc 0 T) t) *
                          derivWithin η (Set.Icc 0 T) t)
                        (Real.sin (2 * (φ t + e * η t)) * η t / 2)
              _ ≤ _ := by
                rw [abs_mul, abs_div, abs_mul]
                norm_num
                gcongr
                · simpa only [Real.norm_eq_abs, abs_mul] using
                    norm_add_le (derivWithin φ (Set.Icc 0 T) t)
                      (e * derivWithin η (Set.Icc 0 T) t)
                · simpa only [one_mul] using
                    mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _)
                      (abs_nonneg (η t))
      _ ≤ bound t := by
        dsimp [bound]
        gcongr
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right heabs (abs_nonneg
            (derivWithin η (Set.Icc 0 T) t))
  have hFmeas : ∀ᶠ e in nhds (0 : ℝ), AEStronglyMeasurable (F e) μ := by
    filter_upwards [] with e
    apply ContinuousOn.aestronglyMeasurable
    · dsimp [F]
      have hde : ContinuousOn
          (fun t ↦ derivWithin φ (Set.Icc 0 T) t +
            e * derivWithin η (Set.Icc 0 T) t) (Set.Icc 0 T) := by
        fun_prop
      apply ContinuousOn.sub
      · apply ContinuousOn.div_const
        apply ContinuousOn.pow
        apply hde.congr
        intro t ht
        change derivWithin (φ + e • η) (Set.Icc 0 T) t = _
        rw [derivWithin_add (hφ.differentiableOn (by norm_num) t ht)
          ((hη.differentiableOn (by norm_num) t ht).const_smul e),
          derivWithin_const_smul_field]
        rfl
      · exact ((Real.continuous_cos.comp_continuousOn
          ((hφ.continuousOn.add (hη.continuousOn.const_smul e)).const_mul 2)).div_const 4)
    · exact measurableSet_Icc
  have hFint : Integrable (F 0) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp [F]
    simpa using (hφd.pow 2 |>.div_const 2).sub
      ((Real.continuous_cos.comp_continuousOn
        (hφ.continuousOn.const_mul 2)).div_const 4)
  have hF'meas : AEStronglyMeasurable (F' 0) μ := by
    apply ContinuousOn.aestronglyMeasurable
    · dsimp [F']
      simpa using (hφd.mul hηd).add
        (((Real.continuous_sin.comp_continuousOn
          (hφ.continuousOn.const_mul 2)).mul hη.continuousOn).div_const 2)
    · exact measurableSet_Icc
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := (0 : ℝ))
    (s := Set.Icc (-1 : ℝ) 1) (by exact Icc_mem_nhds (by norm_num) (by norm_num))
    hFmeas hFint hF'meas hbound hbound_int hdiff).2
  simpa [apm_m97a06_I, μ, F, F'] using hd

lemma apm_m97A06_stationary_of_EL
    {T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 T))
    (hEL : apm_m97a06_EL T φ) :
    apm_m97a06_stationary T φ := by
  intro η hη hη0 hηT
  have hd := apm_m97A06_firstVariation_hasDerivAt hT hφ hη
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have hkin := apm_m97A06_integrationByParts hT hφ hη hη0 hηT
  let u := fun t ↦ derivWithin φ (Set.Icc 0 T) t
  let u' := fun t ↦ derivWithin u (Set.Icc 0 T) t
  have hu : ContDiffOn ℝ 1 u (Set.Icc 0 T) :=
    hφ.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hu' : ContinuousOn u' (Set.Icc 0 T) :=
    hu.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hkinInt : IntegrableOn
      (fun t ↦ derivWithin φ (Set.Icc 0 T) t *
        derivWithin η (Set.Icc 0 T) t) (Set.Icc 0 T) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hu.continuousOn.mul
      (hη.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num))
  have hpotInt : IntegrableOn
      (fun t ↦ Real.sin (2 * φ t) * η t / 2) (Set.Icc 0 T) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (((Real.continuous_sin.comp_continuousOn
      (hφ.continuousOn.const_mul 2)).mul hη.continuousOn).div_const 2)
  have hresInt : IntegrableOn (fun t ↦ -(u' t * η t)) (Set.Icc 0 T) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (hu'.mul hη.continuousOn).neg
  rw [integral_add hkinInt hpotInt, hkin]
  rw [← integral_neg, ← integral_add hresInt hpotInt]
  apply integral_eq_zero_of_ae
  have haeInterior : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) T),
      t ∈ Set.Ioo (0 : ℝ) T := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [haeInterior] with t hti
  have hder : u' t = deriv u t := by
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hti.1 hti.2)
  rw [hder, hEL t hti]
  change _ = (0 : ℝ)
  ring

lemma apm_m97A06_exists_test_integral_pos
    {f : ℝ → ℝ} {T x : ℝ} (hf : ContinuousOn f (Set.Icc 0 T))
    (hx : x ∈ Set.Ioo (0 : ℝ) T) (hfx : 0 < f x) :
    ∃ η : ℝ → ℝ, ContDiff ℝ 2 η ∧ η 0 = 0 ∧ η T = 0 ∧
      0 < ∫ z in (0 : ℝ)..T, f z * η z := by
  have hfc : ContinuousAt f x := hf.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hopen : f ⁻¹' Set.Ioi 0 ∈ nhds x :=
    hfc (isOpen_Ioi.mem_nhds hfx)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hopen
  let r : ℝ := min (δ / 2) (min (x / 2) ((T - x) / 2))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hδ)
      (lt_min (half_pos hx.1) (half_pos (sub_pos.mpr hx.2)))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hr0 : r ≤ x := by
    calc r ≤ x / 2 := (min_le_right _ _).trans (min_le_left _ _)
         _ ≤ x := by linarith [hx.1]
  have hrT : r ≤ T - x := by
    calc r ≤ (T - x) / 2 := (min_le_right _ _).trans (min_le_right _ _)
         _ ≤ T - x := by linarith [hx.2]
  let η : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hηx : η x = 1 := by
    apply η.one_of_mem_closedBall
    simpa [η] using (half_pos hr).le
  have hη0 : η 0 = 0 := by
    apply η.zero_of_le_dist
    rw [Real.dist_eq, abs_of_neg (by linarith [hx.1])]
    linarith
  have hηT : η T = 0 := by
    apply η.zero_of_le_dist
    rw [Real.dist_eq, abs_of_pos (by linarith [hx.2])]
    exact hrT
  refine ⟨η, η.contDiff (n := 2), hη0, hηT, ?_⟩
  have hfpos : ∀ z, dist z x < r → 0 < f z := by
    intro z hz
    exact hball (by simpa [Metric.mem_ball] using hz.trans hrδ)
  have hnonneg : ∀ z, 0 ≤ f z * η z := by
    intro z
    by_cases hz : dist z x < r
    · exact mul_nonneg (hfpos z hz).le η.nonneg
    · rw [η.zero_of_le_dist (le_of_not_gt hz), mul_zero]
  have hfi : IntervalIntegrable (fun z ↦ f z * η z) volume 0 T :=
    (hf.mul η.continuous.continuousOn).intervalIntegrable_of_Icc
      (le_of_lt (hx.1.trans hx.2))
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hnonneg) hfi]
  refine ⟨hx.1.trans hx.2, ?_⟩
  have hs : Set.Ioo (x - r / 2) (x + r / 2) ⊆
      Function.support (fun z ↦ f z * η z) ∩ Set.Ioc 0 T := by
    intro z hz
    have hdist : dist z x < r := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2]
    have hzpos : 0 < f z * η z :=
      mul_pos (hfpos z hdist)
        (η.pos_of_mem_ball (by simpa [Metric.mem_ball, dist_comm] using hdist))
    refine ⟨Function.mem_support.mpr hzpos.ne', ?_⟩
    constructor <;> linarith [hz.1, hz.2, hr0, hrT]
  have hinterval : x - r / 2 < x + r / 2 := by linarith
  have hmeasure : 0 < volume (Set.Ioo (x - r / 2) (x + r / 2)) :=
    (Measure.measure_Ioo_pos volume).2 hinterval
  exact hmeasure.trans_le (measure_mono hs)

lemma apm_m97A06_fundamental_lemma
    {f : ℝ → ℝ} {T : ℝ} (hf : ContinuousOn f (Set.Icc 0 T))
    (hzero : ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Set.Icc 0 T) →
      η 0 = 0 → η T = 0 → (∫ x in Set.Icc (0 : ℝ) T, f x * η x) = 0) :
    ∀ x ∈ Set.Ioo (0 : ℝ) T, f x = 0 := by
  intro x hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨η, hη, hη0, hηT, hint⟩ :=
      apm_m97A06_exists_test_integral_pos hf.neg hx (neg_pos.mpr hneg)
    have hz := hzero η hη.contDiffOn hη0 hηT
    have hconv : (∫ z in (0 : ℝ)..T, (-f z) * η z) =
        -∫ z in Set.Icc (0 : ℝ) T, f z * η z := by
      rw [intervalIntegral.integral_of_le (le_of_lt (hx.1.trans hx.2)),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      simp only [neg_mul, integral_neg]
    rw [hconv, hz, neg_zero] at hint
    exact (lt_irrefl 0 hint)
  · obtain ⟨η, hη, hη0, hηT, hint⟩ :=
      apm_m97A06_exists_test_integral_pos hf hx hpos
    have hz := hzero η hη.contDiffOn hη0 hηT
    have hconv : (∫ z in (0 : ℝ)..T, f z * η z) =
        ∫ z in Set.Icc (0 : ℝ) T, f z * η z := by
      rw [intervalIntegral.integral_of_le (le_of_lt (hx.1.trans hx.2)),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [hconv, hz] at hint
    exact (lt_irrefl 0 hint)

lemma apm_m97A06_EL_of_stationary
    {T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc 0 T))
    (hstat : apm_m97a06_stationary T φ) :
    apm_m97a06_EL T φ := by
  let u := fun t ↦ derivWithin φ (Set.Icc 0 T) t
  let u' := fun t ↦ derivWithin u (Set.Icc 0 T) t
  have hu : ContDiffOn ℝ 1 u (Set.Icc 0 T) :=
    hφ.derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  have hu' : ContinuousOn u' (Set.Icc 0 T) :=
    hu.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  let residual := fun t ↦ -u' t + Real.sin (2 * φ t) / 2
  have hrescont : ContinuousOn residual (Set.Icc 0 T) := by
    dsimp [residual]
    exact hu'.neg.add
      ((Real.continuous_sin.comp_continuousOn
        (hφ.continuousOn.const_mul 2)).div_const 2)
  have hweak : ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Set.Icc 0 T) →
      η 0 = 0 → η T = 0 →
      (∫ t in Set.Icc (0 : ℝ) T, residual t * η t) = 0 := by
    intro η hη hη0 hηT
    have hd := apm_m97A06_firstVariation_hasDerivAt hT hφ hη
    have hz := (hstat η hη hη0 hηT).2
    have hfirst : (∫ t in Set.Icc (0 : ℝ) T,
        derivWithin φ (Set.Icc 0 T) t * derivWithin η (Set.Icc 0 T) t +
          Real.sin (2 * φ t) * η t / 2) = 0 := by
      rw [← hd.deriv]
      exact hz
    have hip := apm_m97A06_integrationByParts hT hφ hη hη0 hηT
    have hkinInt : IntegrableOn (fun t ↦ u t * derivWithin η (Set.Icc 0 T) t)
        (Set.Icc 0 T) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact hu.continuousOn.mul
        (hη.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num))
    have hpotInt : IntegrableOn (fun t ↦ Real.sin (2 * φ t) * η t / 2)
        (Set.Icc 0 T) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact (((Real.continuous_sin.comp_continuousOn
        (hφ.continuousOn.const_mul 2)).mul hη.continuousOn).div_const 2)
    rw [integral_add hkinInt hpotInt, hip] at hfirst
    have hrInt : IntegrableOn (fun t ↦ residual t * η t) (Set.Icc 0 T) :=
      (hrescont.mul hη.continuousOn).integrableOn_compact isCompact_Icc
    rw [show (fun t ↦ residual t * η t) =
        fun t ↦ -(u' t * η t) + Real.sin (2 * φ t) * η t / 2 by
          funext t; dsimp [residual]; ring]
    rw [integral_add]
    · rw [integral_neg]
      exact hfirst
    · exact (hu'.mul hη.continuousOn).integrableOn_compact isCompact_Icc |>.neg
    · exact hpotInt
  have hzero := apm_m97A06_fundamental_lemma hrescont hweak
  intro t ht
  have hd : u' t = deriv u t :=
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have := hzero t ht
  dsimp [residual] at this
  rw [hd] at this
  change deriv u t = Real.sin (2 * φ t) / 2
  linarith

lemma apm_m97A06_integral_derivWithin_sq_eq
    {T : ℝ} (hT : 0 < T) (η : ℝ → ℝ) :
    (∫ t in Set.Icc (0 : ℝ) T,
      derivWithin η (Set.Icc 0 T) t ^ 2) =
      ∫ t in Set.Icc (0 : ℝ) T, deriv η t ^ 2 := by
  apply integral_congr_ae
  have haeInterior : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) T),
      t ∈ Set.Ioo (0 : ℝ) T := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [haeInterior] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- The potential integrand has the required Hessian pointwise.  The only
remaining potential-side issue is exchanging these derivatives with the
interval integral for an unrestricted direction. -/
lemma apm_m97A06_potential_pointwise_secondDeriv (η : ℝ) :
    deriv (deriv (fun e : ℝ ↦ -Real.cos (2 * e * η) / 4)) 0 = η ^ 2 := by
  have hfirst : deriv (fun e : ℝ ↦ -Real.cos (2 * e * η) / 4) =
      fun e ↦ Real.sin (2 * e * η) * η / 2 := by
    funext e
    have harg : HasDerivAt (fun x : ℝ ↦ 2 * x * η) (2 * η) e := by
      convert ((hasDerivAt_id e).const_mul 2).mul_const η using 1 <;> ring
    have hcos := (Real.hasDerivAt_cos (2 * e * η)).comp e harg
    convert (hcos.neg.div_const 4).deriv using 1 <;> simp <;> ring
  rw [hfirst]
  have harg : HasDerivAt (fun x : ℝ ↦ 2 * x * η) (2 * η) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const η using 1 <;> ring
  have hsin := (Real.hasDerivAt_sin (2 * 0 * η)).comp 0 harg
  convert ((hsin.mul_const η).div_const 2).deriv using 1 <;> simp <;> ring

lemma apm_m97A06_potential_secondDeriv_of_integrable
    {T : ℝ} (η : ℝ → ℝ)
    (hsq : Integrable (fun t ↦ η t ^ 2) (volume.restrict (Set.Icc 0 T))) :
    deriv (deriv (fun e : ℝ ↦
      ∫ t in Set.Icc (0 : ℝ) T, -Real.cos (2 * e * η t) / 4)) 0 =
      ∫ t in Set.Icc (0 : ℝ) T, η t ^ 2 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) T)
  let F : ℝ → ℝ → ℝ := fun e t ↦ -Real.cos (2 * e * η t) / 4
  let F' : ℝ → ℝ → ℝ := fun e t ↦ Real.sin (2 * e * η t) * η t / 2
  let F'' : ℝ → ℝ → ℝ := fun e t ↦ Real.cos (2 * e * η t) * η t ^ 2
  have habsmeas : AEStronglyMeasurable (fun t ↦ |η t|) μ := by
    simpa only [Real.sqrt_sq_eq_abs] using
      hsq.aemeasurable.sqrt.aestronglyMeasurable
  have hcos_abs (e t : ℝ) : Real.cos (2 * e * η t) = Real.cos (2 * e * |η t|) := by
    by_cases ht : 0 ≤ η t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      rw [show 2 * e * -η t = -(2 * e * η t) by ring, Real.cos_neg]
  have hsin_mul_abs (e t : ℝ) :
      Real.sin (2 * e * η t) * η t = Real.sin (2 * e * |η t|) * |η t| := by
    by_cases ht : 0 ≤ η t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      rw [show 2 * e * -η t = -(2 * e * η t) by ring, Real.sin_neg]
      ring
  have hconst : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ := integrable_const 1
  have hbound1 : Integrable (fun t ↦ η t ^ 2 + 1) μ := hsq.add hconst
  have hFmeas : ∀ e, AEStronglyMeasurable (F e) μ := by
    intro e
    have hm : AEStronglyMeasurable
        (fun t ↦ -Real.cos (2 * e * |η t|) / 4) μ := by fun_prop
    exact hm.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp [F]
      rw [hcos_abs])
  have hF'meas : ∀ e, AEStronglyMeasurable (F' e) μ := by
    intro e
    have hm : AEStronglyMeasurable
        (fun t ↦ Real.sin (2 * e * |η t|) * |η t| / 2) μ := by fun_prop
    exact hm.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp [F']
      rw [hsin_mul_abs])
  have hF''meas : ∀ e, AEStronglyMeasurable (F'' e) μ := by
    intro e
    have hc : AEStronglyMeasurable
        (fun t ↦ Real.cos (2 * e * |η t|)) μ := by fun_prop
    have hm : AEStronglyMeasurable
        (fun t ↦ Real.cos (2 * e * |η t|) * η t ^ 2) μ :=
      hc.mul hsq.1
    exact hm.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp [F'']
      rw [hcos_abs])
  have hFint : ∀ e, Integrable (F e) μ := by
    intro e
    exact (integrable_const (1 / 4 : ℝ)).mono' (hFmeas e) (by
      filter_upwards [] with t
      dsimp [F]
      simpa [Real.norm_eq_abs, abs_div] using
        (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num : (0 : ℝ) ≤ 4)))
  have hd1 : ∀ e, HasDerivAt (fun x ↦ ∫ t, F x t ∂μ) (∫ t, F' e t ∂μ) e := by
    intro e
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := fun t ↦ η t ^ 2 + 1)
      (x₀ := e) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall hFmeas) (hFint e) (hF'meas e)
      (by
        filter_upwards [] with t x hx
        dsimp [F']
        have hs := Real.abs_sin_le_one (2 * x * η t)
        have ha : |η t| / 2 ≤ η t ^ 2 + 1 := by
          nlinarith [sq_nonneg (|η t| - 1), sq_abs (η t)]
        rw [abs_div, abs_mul]
        exact (div_le_div_of_nonneg_right
          (mul_le_of_le_one_left (abs_nonneg _) hs) (by norm_num)).trans (by simpa using ha))
      hbound1 (by
        filter_upwards [] with t x hx
        dsimp [F, F']
        have harg : HasDerivAt (fun y : ℝ ↦ 2 * y * η t) (2 * η t) x := by
          convert ((hasDerivAt_id x).const_mul 2).mul_const (η t) using 1 <;> ring
        convert (((Real.hasDerivAt_cos (2 * x * η t)).comp x harg).neg.div_const 4)
          using 1 <;> simp <;> ring)).2
  have hfirst : deriv (fun x ↦ ∫ t, F x t ∂μ) = fun e ↦ ∫ t, F' e t ∂μ := by
    funext e
    exact (hd1 e).deriv
  have hF'int : ∀ e, Integrable (F' e) μ := by
    intro e
    exact hbound1.mono' (hF'meas e) (by
      filter_upwards [] with t
      dsimp [F']
      have hs := Real.abs_sin_le_one (2 * e * η t)
      have ha : |η t| / 2 ≤ η t ^ 2 + 1 := by
        nlinarith [sq_nonneg (|η t| - 1), sq_abs (η t)]
      rw [abs_div, abs_mul]
      exact (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (abs_nonneg _) hs) (by norm_num)).trans (by simpa using ha))
  rw [show (fun e : ℝ ↦ ∫ t in Set.Icc (0 : ℝ) T,
      -Real.cos (2 * e * η t) / 4) = fun e ↦ ∫ t, F e t ∂μ by rfl,
    hfirst]
  have hd2 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F') (F' := F'') (bound := fun t ↦ η t ^ 2)
    (x₀ := (0 : ℝ)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall hF'meas) (hF'int 0)
    (hF''meas 0)
    (by
      filter_upwards [] with t x hx
      dsimp [F'']
      rw [abs_mul, abs_sq]
      exact mul_le_of_le_one_left (sq_nonneg _) (Real.abs_cos_le_one _))
    hsq
    (by
      filter_upwards [] with t x hx
      dsimp [F', F'']
      have harg : HasDerivAt (fun y : ℝ ↦ 2 * y * η t) (2 * η t) x := by
        convert ((hasDerivAt_id x).const_mul 2).mul_const (η t) using 1 <;> ring
      convert (((Real.hasDerivAt_sin (2 * x * η t)).comp x harg).mul_const (η t)).div_const 2
        using 1 <;> ring)).2
  rw [hd2.deriv]
  simp [F'', μ]

lemma apm_m97A06_potential_derivs
    {T : ℝ} (η : ℝ → ℝ)
    (hsq : Integrable (fun t ↦ η t ^ 2) (volume.restrict (Set.Icc 0 T))) :
    (∀ e : ℝ, HasDerivAt (fun x : ℝ ↦
        ∫ t in Set.Icc (0 : ℝ) T, -Real.cos (2 * x * η t) / 4)
        (∫ t in Set.Icc (0 : ℝ) T, Real.sin (2 * e * η t) * η t / 2) e) ∧
      HasDerivAt (fun e : ℝ ↦
        ∫ t in Set.Icc (0 : ℝ) T, Real.sin (2 * e * η t) * η t / 2)
        (∫ t in Set.Icc (0 : ℝ) T, η t ^ 2) 0 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) T)
  let F : ℝ → ℝ → ℝ := fun e t ↦ -Real.cos (2 * e * η t) / 4
  let F' : ℝ → ℝ → ℝ := fun e t ↦ Real.sin (2 * e * η t) * η t / 2
  let F'' : ℝ → ℝ → ℝ := fun e t ↦ Real.cos (2 * e * η t) * η t ^ 2
  have habsmeas : AEStronglyMeasurable (fun t ↦ |η t|) μ := by
    simpa only [Real.sqrt_sq_eq_abs] using
      hsq.aemeasurable.sqrt.aestronglyMeasurable
  have hcos_abs (e t : ℝ) : Real.cos (2 * e * η t) = Real.cos (2 * e * |η t|) := by
    by_cases ht : 0 ≤ η t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      rw [show 2 * e * -η t = -(2 * e * η t) by ring, Real.cos_neg]
  have hsin_mul_abs (e t : ℝ) :
      Real.sin (2 * e * η t) * η t = Real.sin (2 * e * |η t|) * |η t| := by
    by_cases ht : 0 ≤ η t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      rw [show 2 * e * -η t = -(2 * e * η t) by ring, Real.sin_neg]
      ring
  have hconst : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ := integrable_const 1
  have hbound1 : Integrable (fun t ↦ η t ^ 2 + 1) μ := hsq.add hconst
  have hFmeas : ∀ e, AEStronglyMeasurable (F e) μ := by
    intro e
    have hm : AEStronglyMeasurable
        (fun t ↦ -Real.cos (2 * e * |η t|) / 4) μ := by fun_prop
    exact hm.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp [F]
      rw [hcos_abs])
  have hF'meas : ∀ e, AEStronglyMeasurable (F' e) μ := by
    intro e
    have hm : AEStronglyMeasurable
        (fun t ↦ Real.sin (2 * e * |η t|) * |η t| / 2) μ := by fun_prop
    exact hm.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp [F']
      rw [hsin_mul_abs])
  have hF''meas : ∀ e, AEStronglyMeasurable (F'' e) μ := by
    intro e
    have hc : AEStronglyMeasurable
        (fun t ↦ Real.cos (2 * e * |η t|)) μ := by fun_prop
    have hm : AEStronglyMeasurable
        (fun t ↦ Real.cos (2 * e * |η t|) * η t ^ 2) μ :=
      hc.mul hsq.1
    exact hm.congr (Filter.Eventually.of_forall fun t ↦ by
      dsimp [F'']
      rw [hcos_abs])
  have hFint : ∀ e, Integrable (F e) μ := by
    intro e
    exact (integrable_const (1 / 4 : ℝ)).mono' (hFmeas e) (by
      filter_upwards [] with t
      dsimp [F]
      simpa [Real.norm_eq_abs, abs_div] using
        (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num : (0 : ℝ) ≤ 4)))
  have hd1 : ∀ e, HasDerivAt (fun x ↦ ∫ t, F x t ∂μ) (∫ t, F' e t ∂μ) e := by
    intro e
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := fun t ↦ η t ^ 2 + 1)
      (x₀ := e) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall hFmeas) (hFint e) (hF'meas e)
      (by
        filter_upwards [] with t x hx
        dsimp [F']
        have hs := Real.abs_sin_le_one (2 * x * η t)
        have ha : |η t| / 2 ≤ η t ^ 2 + 1 := by
          nlinarith [sq_nonneg (|η t| - 1), sq_abs (η t)]
        rw [abs_div, abs_mul]
        exact (div_le_div_of_nonneg_right
          (mul_le_of_le_one_left (abs_nonneg _) hs) (by norm_num)).trans (by simpa using ha))
      hbound1 (by
        filter_upwards [] with t x hx
        dsimp [F, F']
        have harg : HasDerivAt (fun y : ℝ ↦ 2 * y * η t) (2 * η t) x := by
          convert ((hasDerivAt_id x).const_mul 2).mul_const (η t) using 1 <;> ring
        convert (((Real.hasDerivAt_cos (2 * x * η t)).comp x harg).neg.div_const 4)
          using 1 <;> simp <;> ring)).2
  have hfirst : deriv (fun x ↦ ∫ t, F x t ∂μ) = fun e ↦ ∫ t, F' e t ∂μ := by
    funext e
    exact (hd1 e).deriv
  have hF'int : ∀ e, Integrable (F' e) μ := by
    intro e
    exact hbound1.mono' (hF'meas e) (by
      filter_upwards [] with t
      dsimp [F']
      have hs := Real.abs_sin_le_one (2 * e * η t)
      have ha : |η t| / 2 ≤ η t ^ 2 + 1 := by
        nlinarith [sq_nonneg (|η t| - 1), sq_abs (η t)]
      rw [abs_div, abs_mul]
      exact (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (abs_nonneg _) hs) (by norm_num)).trans (by simpa using ha))
  have hd2 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F') (F' := F'') (bound := fun t ↦ η t ^ 2)
    (x₀ := (0 : ℝ)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall hF'meas) (hF'int 0)
    (hF''meas 0)
    (by
      filter_upwards [] with t x hx
      dsimp [F'']
      rw [abs_mul, abs_sq]
      exact mul_le_of_le_one_left (sq_nonneg _) (Real.abs_cos_le_one _))
    hsq
    (by
      filter_upwards [] with t x hx
      dsimp [F', F'']
      have harg : HasDerivAt (fun y : ℝ ↦ 2 * y * η t) (2 * η t) x := by
        convert ((hasDerivAt_id x).const_mul 2).mul_const (η t) using 1 <;> ring
      convert (((Real.hasDerivAt_sin (2 * x * η t)).comp x harg).mul_const (η t)).div_const 2
        using 1 <;> ring)).2
  refine ⟨hd1, ?_⟩
  convert hd2 using 1
  simp [F'', μ]

theorem apm_m97a06 :
    ∀ T : ℝ, 0 < T →
      (∀ φ : ℝ → ℝ, ContDiffOn ℝ 2 φ (Set.Icc 0 T) →
        (apm_m97a06_stationary T φ ↔ apm_m97a06_EL T φ)) ∧
      (∀ φ, ContDiffOn ℝ 2 φ (Set.Icc 0 T) → apm_m97a06_EL T φ →
        ∃ E, ∀ t ∈ Set.Icc (0 : ℝ) T, apm_m97a06_energy T φ t = E) ∧
      apm_m97a06_EL T (fun _ => 0) ∧
      (∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Set.Icc 0 T) → η 0 = 0 → η T = 0 →
        deriv (deriv (fun ε : ℝ => apm_m97a06_I T (ε • η))) 0 =
          apm_m97a06_hessian T η) := by
  intro T hT
  refine ⟨?_, ?_, apm_m97A06_zero_EL T, ?_⟩
  · intro φ hφ
    constructor
    · intro hstat
      exact apm_m97A06_EL_of_stationary hT hφ hstat
    · exact apm_m97A06_stationary_of_EL hT hφ
  · intro φ hφ hEL
    exact apm_m97A06_energy_constant hT hφ hEL
  · intro η hηC hη0 hηT
    have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
    have hηc : ContinuousOn η (Set.Icc 0 T) := hηC.continuousOn
    have hsq : Integrable (fun t ↦ η t ^ 2) (volume.restrict (Set.Icc 0 T)) :=
      (hηc.pow 2).integrableOn_Icc
    obtain ⟨hP, hP'⟩ := apm_m97A06_potential_derivs (T := T) η hsq
    set K : ℝ := ∫ t in Set.Icc (0 : ℝ) T, derivWithin η (Set.Icc 0 T) t ^ 2 with hK
    have hsplit : ∀ ε : ℝ, apm_m97a06_I T (ε • η) =
        ε ^ 2 / 2 * K + ∫ t in Set.Icc (0 : ℝ) T, -Real.cos (2 * ε * η t) / 4 := by
      intro ε
      have hεC : ContDiffOn ℝ 1 (ε • η) (Set.Icc 0 T) := hηC.const_smul ε
      have hd : ContinuousOn (derivWithin (ε • η) (Set.Icc 0 T)) (Set.Icc 0 T) :=
        hεC.continuousOn_derivWithin hu le_rfl
      have hi1 : Integrable (fun t ↦ derivWithin (ε • η) (Set.Icc 0 T) t ^ 2 / 2)
          (volume.restrict (Set.Icc 0 T)) := ((hd.pow 2).div_const 2).integrableOn_Icc
      have hi2 : Integrable (fun t ↦ Real.cos (2 * (ε • η) t) / 4)
          (volume.restrict (Set.Icc 0 T)) :=
        ((Real.continuous_cos.comp_continuousOn
          ((hηc.const_smul ε).const_smul (2 : ℝ))).div_const 4).integrableOn_Icc
      unfold apm_m97a06_I
      rw [MeasureTheory.integral_sub hi1 hi2, apm_m97A06_kinetic_smul, ← hK,
        sub_eq_add_neg, ← MeasureTheory.integral_neg]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [mul_assoc, neg_div]
    have hfun : (fun ε : ℝ ↦ apm_m97a06_I T (ε • η)) = fun ε ↦
        ε ^ 2 / 2 * K + ∫ t in Set.Icc (0 : ℝ) T, -Real.cos (2 * ε * η t) / 4 :=
      funext hsplit
    have hd1 : ∀ e : ℝ, HasDerivAt (fun ε : ℝ ↦
        ε ^ 2 / 2 * K + ∫ t in Set.Icc (0 : ℝ) T, -Real.cos (2 * ε * η t) / 4)
        (e * K + ∫ t in Set.Icc (0 : ℝ) T, Real.sin (2 * e * η t) * η t / 2) e := by
      intro e
      have h1 : HasDerivAt (fun ε : ℝ ↦ ε ^ 2 / 2 * K) (e * K) e := by
        convert (((hasDerivAt_pow 2 e).div_const 2).mul_const K) using 1
        simp
      exact h1.add (hP e)
    have hderiv : deriv (fun ε : ℝ ↦ apm_m97a06_I T (ε • η)) = fun e ↦
        e * K + ∫ t in Set.Icc (0 : ℝ) T, Real.sin (2 * e * η t) * η t / 2 := by
      rw [hfun]; funext e; exact (hd1 e).deriv
    have hd2 : HasDerivAt (fun e : ℝ ↦
        e * K + ∫ t in Set.Icc (0 : ℝ) T, Real.sin (2 * e * η t) * η t / 2)
        (K + ∫ t in Set.Icc (0 : ℝ) T, η t ^ 2) 0 := by
      have h1 : HasDerivAt (fun e : ℝ ↦ e * K) K 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const K
      exact h1.add hP'
    rw [hderiv, hd2.deriv, hK, apm_m97A06_integral_derivWithin_sq_eq hT η]
    unfold apm_m97a06_hessian
    have hdW : ContinuousOn (derivWithin η (Set.Icc 0 T)) (Set.Icc 0 T) :=
      hηC.continuousOn_derivWithin hu le_rfl
    have hiW : IntegrableOn (fun t ↦ derivWithin η (Set.Icc 0 T) t ^ 2) (Set.Icc 0 T) :=
      (hdW.pow 2).integrableOn_Icc
    have hiD : IntegrableOn (fun t ↦ deriv η t ^ 2) (Set.Icc 0 T) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioo] at hiW ⊢
      refine hiW.congr_fun (fun t ht ↦ ?_) measurableSet_Ioo
      show derivWithin η (Set.Icc 0 T) t ^ 2 = deriv η t ^ 2
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact (MeasureTheory.integral_add hiD hsq).symm


#print axioms apm_m97a06

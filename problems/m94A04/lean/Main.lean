import Mathlib

/-!
# APM m94A04

## Statement repairs

None.

## Encoding notes

Both domain and codomain are genuine quotient `Lp` spaces over `[0,1]`.
The Nemytskii operator and its derivative are characterized almost everywhere,
so their definitions do not depend on representatives of `Lp` classes.
-/

open MeasureTheory Set

/-- Exact pointwise remainder for the cubic Nemytskii map. -/
lemma apm_m94a04_cubic_remainder (a b : ℝ) :
    (a + b) ^ 3 - a ^ 3 - 3 * a ^ 2 * b = 3 * a * b ^ 2 + b ^ 3 := by
  ring

noncomputable abbrev apm_m94a04_measure : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

local instance apm_m94a04_holder_884 : ENNReal.HolderTriple 8 8 4 := by
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal (by finiteness)
    (by rw [ENNReal.inv_ne_top]; norm_num)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_inv]
  simp
  norm_num

/-- The first heterogeneous Hölder stage: squaring an `L⁸` class produces a
well-defined `L⁴` class. -/
noncomputable def apm_m94a04_square
    (f : Lp ℝ 8 apm_m94a04_measure) : Lp ℝ 4 apm_m94a04_measure :=
  f • f

/-- The quotient-level square has the expected representative almost
everywhere. -/
lemma apm_m94a04_square_coeFn
    (f : Lp ℝ 8 apm_m94a04_measure) :
    (apm_m94a04_square f : ℝ → ℝ) =ᵐ[apm_m94a04_measure]
      fun t ↦ (f t) ^ 2 := by
  filter_upwards [Lp.coeFn_lpSMul (r := 4) f f] with t ht
  simpa [apm_m94a04_square, pow_two] using ht

/-- Hölder gives the sharp quotient norm estimate for the square stage. -/
lemma apm_m94a04_norm_square_le
    (f : Lp ℝ 8 apm_m94a04_measure) :
    ‖apm_m94a04_square f‖ ≤ ‖f‖ ^ 2 := by
  simpa [apm_m94a04_square, pow_two] using
    (Lp.norm_smul_le (r := 4) f f)

local instance apm_m94a04_holder_84eightThirds :
    ENNReal.HolderTriple 8 4 (8 / 3) := by
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal (by finiteness)
    (by rw [ENNReal.inv_ne_top, ENNReal.div_ne_zero]; norm_num)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_inv]
  simp
  norm_num

/-- The second heterogeneous Hölder stage constructs the cubic term in
`L^(8/3)` directly on quotient classes. -/
noncomputable def apm_m94a04_cube
    (f : Lp ℝ 8 apm_m94a04_measure) :
    Lp ℝ (8 / 3) apm_m94a04_measure :=
  f • apm_m94a04_square f

/-- The quotient-level cube has the expected representative almost
everywhere. -/
lemma apm_m94a04_cube_coeFn (f : Lp ℝ 8 apm_m94a04_measure) :
    (apm_m94a04_cube f : ℝ → ℝ) =ᵐ[apm_m94a04_measure]
      fun t ↦ (f t) ^ 3 := by
  filter_upwards [Lp.coeFn_lpSMul (r := 8 / 3) f (apm_m94a04_square f),
    apm_m94a04_square_coeFn f] with t hmul hsquare
  change ((f • apm_m94a04_square f : Lp ℝ (8 / 3) apm_m94a04_measure) :
    ℝ → ℝ) t = (f t) ^ 3
  rw [hmul]
  change f t * apm_m94a04_square f t = (f t) ^ 3
  rw [hsquare]
  ring

/-- Hölder and the square estimate give the cubic norm bound. -/
lemma apm_m94a04_norm_cube_le (f : Lp ℝ 8 apm_m94a04_measure) :
    ‖apm_m94a04_cube f‖ ≤ ‖f‖ ^ 3 := by
  have hf0 : 0 ≤ ‖f‖ := by
    rw [Lp.norm_def]
    exact ENNReal.toReal_nonneg
  calc
    ‖apm_m94a04_cube f‖ ≤ ‖f‖ * ‖apm_m94a04_square f‖ :=
      Lp.norm_smul_le (r := 8 / 3) f (apm_m94a04_square f)
    _ ≤ ‖f‖ * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left
      (apm_m94a04_norm_square_le f) hf0
    _ = ‖f‖ ^ 3 := by ring

def apm_m94a04_IsOperator
    (T : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →
      Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) : Prop :=
  ∀ f : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      T f t = Real.sin t + (f t) ^ 3

def apm_m94a04_IsFrechetDerivative
    (T : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →
      Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (f : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)))
    (L : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ h : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
    eLpNorm (L h) 2 (volume.restrict (Icc (0 : ℝ) 1)) ≤
      ENNReal.ofReal C * eLpNorm h 8 (volume.restrict (Icc (0 : ℝ) 1))) ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
    eLpNorm h 8 (volume.restrict (Icc (0 : ℝ) 1)) < ENNReal.ofReal δ →
    eLpNorm ((T (f + h) : ℝ → ℝ) - (T f : ℝ → ℝ) - (L h : ℝ → ℝ)) 2
        (volume.restrict (Icc (0 : ℝ) 1)) ≤
      ENNReal.ofReal ε * eLpNorm h 8 (volume.restrict (Icc (0 : ℝ) 1))

/-- Why this unblocks `apm_m94a04`: this is the missing finite-measure
inclusion from `L^(8/3)` into `L²`, bundled linearly and preserving the same
representative.  It turns the already-constructed cubic and mixed Hölder
products into elements of the frozen codomain. -/
theorem apm_m94A04_bridge_downgrade_eightThirds_to_two :
    ∃ D : Lp ℝ (8 / 3) apm_m94a04_measure →ₗ[ℝ]
        Lp ℝ 2 apm_m94a04_measure,
      (∀ g, (D g : ℝ → ℝ) =ᵐ[apm_m94a04_measure] (g : ℝ → ℝ)) ∧
      ∀ g, eLpNorm (D g) 2 apm_m94a04_measure ≤
        eLpNorm g (8 / 3) apm_m94a04_measure := by
  letI : IsProbabilityMeasure apm_m94a04_measure :=
    ⟨by
      simp [apm_m94a04_measure, Real.volume_Icc]⟩
  have hpq : (2 : ENNReal) ≤ 8 / 3 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_div]
    norm_num
  let D : Lp ℝ (8 / 3) apm_m94a04_measure →ₗ[ℝ]
      Lp ℝ 2 apm_m94a04_measure :=
    { toFun := fun g ↦ ⟨g.1, Lp.antitone (E := ℝ) hpq g.2⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  refine ⟨D, ?_, ?_⟩
  · intro g
    exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · intro g
    exact eLpNorm_le_eLpNorm_of_exponent_le hpq
      (g : ℝ →ₘ[apm_m94a04_measure] ℝ).stronglyMeasurable.aestronglyMeasurable

/-- Why this unblocks `apm_m94a04`: it packages the quotient-level operator
and the bounded linear map `h ↦ 3 f² h`, including exactly the a.e. formula
needed by the theorem.  The first conjunct is the boundedness half of the
custom Fréchet-derivative predicate. -/
theorem apm_m94A04_bridge_operator_and_linearization :
    ∃ T : Lp ℝ 8 apm_m94a04_measure → Lp ℝ 2 apm_m94a04_measure,
      apm_m94a04_IsOperator T ∧
      ∀ f : Lp ℝ 8 apm_m94a04_measure,
        ∃ L : Lp ℝ 8 apm_m94a04_measure →ₗ[ℝ]
            Lp ℝ 2 apm_m94a04_measure,
          (∃ C : ℝ, 0 ≤ C ∧ ∀ h : Lp ℝ 8 apm_m94a04_measure,
            eLpNorm (L h) 2 apm_m94a04_measure ≤
              ENNReal.ofReal C * eLpNorm h 8 apm_m94a04_measure) ∧
          ∀ h : Lp ℝ 8 apm_m94a04_measure,
            ∀ᵐ t ∂apm_m94a04_measure, L h t = 3 * (f t) ^ 2 * h t := by
  obtain ⟨D, hDcoe, hDnorm⟩ :=
    apm_m94A04_bridge_downgrade_eightThirds_to_two
  letI : Fact (1 ≤ (8 / 3 : ENNReal)) :=
    ⟨by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_div]
      norm_num⟩
  letI : Fact (1 ≤ (8 : ENNReal)) := ⟨by norm_num⟩
  letI : IsProbabilityMeasure apm_m94a04_measure :=
    ⟨by simp [apm_m94a04_measure, Real.volume_Icc]⟩
  have hsin_mem : MemLp (fun t : ℝ ↦ Real.sin t) 2 apm_m94a04_measure :=
    MemLp.of_bound Real.continuous_sin.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun t ↦ by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one t)
  let sinLp : Lp ℝ 2 apm_m94a04_measure :=
    hsin_mem.toLp (fun t : ℝ ↦ Real.sin t)
  let T : Lp ℝ 8 apm_m94a04_measure → Lp ℝ 2 apm_m94a04_measure :=
    fun f ↦ sinLp + D (apm_m94a04_cube f)
  have hD_norm_le (g : Lp ℝ (8 / 3) apm_m94a04_measure) :
      ‖D g‖ ≤ ‖g‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (hDnorm g)
  refine ⟨T, ?_, ?_⟩
  · intro f
    filter_upwards [Lp.coeFn_add sinLp (D (apm_m94a04_cube f)),
      hsin_mem.coeFn_toLp, hDcoe (apm_m94a04_cube f),
      apm_m94a04_cube_coeFn f] with t hadd hsin hD hcube
    change (sinLp + D (apm_m94a04_cube f)) t = _
    rw [hadd]
    change sinLp t + D (apm_m94a04_cube f) t = _
    change (hsin_mem.toLp (fun t : ℝ ↦ Real.sin t)) t + _ = _
    rw [hsin, hD, hcube]
  · intro f
    let L : Lp ℝ 8 apm_m94a04_measure →ₗ[ℝ]
        Lp ℝ 2 apm_m94a04_measure :=
      { toFun := fun h ↦ D ((3 : ℝ) • (h • apm_m94a04_square f))
        map_add' := by
          intro x y
          rw [Lp.smul_add, smul_add, map_add]
        map_smul' := by
          intro c x
          simp only [Lp.smul_assoc, map_smul]
          simpa only [RingHom.id_apply] using
            (smul_comm (3 : ℝ) c (D (x • apm_m94a04_square f))) }
    refine ⟨L, ?_, ?_⟩
    · refine ⟨3 * ‖f‖ ^ 2, by positivity, ?_⟩
      intro h
      have hnorm : ‖L h‖ ≤ (3 * ‖f‖ ^ 2) * ‖h‖ := by
        calc
          ‖L h‖ ≤ ‖((3 : ℝ) • (h • apm_m94a04_square f) :
              Lp ℝ (8 / 3) apm_m94a04_measure)‖ := hD_norm_le _
          _ = 3 * ‖(h • apm_m94a04_square f :
              Lp ℝ (8 / 3) apm_m94a04_measure)‖ := by
                rw [norm_smul]
                norm_num
          _ ≤ 3 * (‖h‖ * ‖apm_m94a04_square f‖) := by
            gcongr
            exact Lp.norm_smul_le (r := 8 / 3) h (apm_m94a04_square f)
          _ ≤ 3 * (‖h‖ * ‖f‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (apm_m94a04_norm_square_le f)
                (norm_nonneg h)) (by norm_num)
          _ = (3 * ‖f‖ ^ 2) * ‖h‖ := by ring
      have hLnorm : eLpNorm (L h) 2 apm_m94a04_measure =
          ENNReal.ofReal ‖L h‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (L h))]
      have hhnorm : eLpNorm h 8 apm_m94a04_measure =
          ENNReal.ofReal ‖h‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h)]
      rw [hLnorm, hhnorm]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hnorm
    · intro h
      filter_upwards [hDcoe ((3 : ℝ) • (h • apm_m94a04_square f)),
        Lp.coeFn_smul (3 : ℝ) (h • apm_m94a04_square f),
        Lp.coeFn_lpSMul (r := 8 / 3) h (apm_m94a04_square f),
        apm_m94a04_square_coeFn f] with t hD hthree hmul hsquare
      change D ((3 : ℝ) • (h • apm_m94a04_square f)) t = _
      rw [hD]
      change ((3 : ℝ) • (h • apm_m94a04_square f) :
        Lp ℝ (8 / 3) apm_m94a04_measure) t = _
      rw [hthree]
      change 3 * (h • apm_m94a04_square f :
        Lp ℝ (8 / 3) apm_m94a04_measure) t = _
      rw [hmul]
      change 3 * (h t * apm_m94a04_square f t) = _
      rw [hsquare]
      ring

/-- Why this unblocks `apm_m94a04`: the exact cubic identity and mixed Hölder
bounds imply this uniform small-increment estimate.  Combined with the first
conjunct supplied by the preceding bridge, it is precisely
`apm_m94a04_IsFrechetDerivative T f L`. -/
theorem apm_m94A04_bridge_remainder_estimate
    (T : Lp ℝ 8 apm_m94a04_measure → Lp ℝ 2 apm_m94a04_measure)
    (hT : apm_m94a04_IsOperator T)
    (f : Lp ℝ 8 apm_m94a04_measure)
    (L : Lp ℝ 8 apm_m94a04_measure →ₗ[ℝ]
      Lp ℝ 2 apm_m94a04_measure)
    (hL : ∀ h : Lp ℝ 8 apm_m94a04_measure,
      ∀ᵐ t ∂apm_m94a04_measure, L h t = 3 * (f t) ^ 2 * h t) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : Lp ℝ 8 apm_m94a04_measure,
      eLpNorm h 8 apm_m94a04_measure < ENNReal.ofReal δ →
      eLpNorm ((T (f + h) : ℝ → ℝ) - (T f : ℝ → ℝ) -
        (L h : ℝ → ℝ)) 2 apm_m94a04_measure ≤
        ENNReal.ofReal ε * eLpNorm h 8 apm_m94a04_measure := by
  obtain ⟨D, hDcoe, hDnorm⟩ :=
    apm_m94A04_bridge_downgrade_eightThirds_to_two
  letI : Fact (1 ≤ (8 / 3 : ENNReal)) :=
    ⟨by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_div]
      norm_num⟩
  letI : Fact (1 ≤ (8 : ENNReal)) := ⟨by norm_num⟩
  have hD_norm_le (g : Lp ℝ (8 / 3) apm_m94a04_measure) :
      ‖D g‖ ≤ ‖g‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (hDnorm g)
  intro ε hε
  let A : ℝ := 3 * ‖f‖ + 1
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨min 1 (ε / A), by positivity, ?_⟩
  intro h hh
  have hdelta : 0 < min 1 (ε / A) := by positivity
  have hhnorm : eLpNorm h 8 apm_m94a04_measure =
      ENNReal.ofReal ‖h‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h)]
  have hhsmall : ‖h‖ < min 1 (ε / A) := by
    rw [hhnorm] at hh
    exact (ENNReal.ofReal_lt_ofReal_iff hdelta).mp hh
  let R : Lp ℝ 2 apm_m94a04_measure :=
    D ((3 : ℝ) • (f • apm_m94a04_square h) + apm_m94a04_cube h)
  have hRae :
      ((T (f + h) : ℝ → ℝ) - (T f : ℝ → ℝ) -
          (L h : ℝ → ℝ)) =ᵐ[apm_m94a04_measure] (R : ℝ → ℝ) := by
    filter_upwards [hT (f + h), hT f, hL h, Lp.coeFn_add f h,
      hDcoe ((3 : ℝ) • (f • apm_m94a04_square h) + apm_m94a04_cube h),
      Lp.coeFn_add ((3 : ℝ) • (f • apm_m94a04_square h))
        (apm_m94a04_cube h),
      Lp.coeFn_smul (3 : ℝ) (f • apm_m94a04_square h),
      Lp.coeFn_lpSMul (r := 8 / 3) f (apm_m94a04_square h),
      apm_m94a04_square_coeFn h, apm_m94a04_cube_coeFn h]
      with t hTfh hTf hLh hfh hDR hadd hthree hmul hsquare hcube
    change T (f + h) t - T f t - L h t = R t
    rw [hTfh, hTf, hLh, hfh]
    change _ = D ((3 : ℝ) • (f • apm_m94a04_square h) +
      apm_m94a04_cube h) t
    rw [hDR]
    change _ = (((3 : ℝ) • (f • apm_m94a04_square h) +
      apm_m94a04_cube h : Lp ℝ (8 / 3) apm_m94a04_measure) : ℝ → ℝ) t
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hthree]
    change _ = 3 * (f • apm_m94a04_square h :
      Lp ℝ (8 / 3) apm_m94a04_measure) t + apm_m94a04_cube h t
    rw [hmul]
    change _ = 3 * (f t * apm_m94a04_square h t) + apm_m94a04_cube h t
    rw [hsquare, hcube]
    ring
  have hRnorm : ‖R‖ ≤ 3 * ‖f‖ * ‖h‖ ^ 2 + ‖h‖ ^ 3 := by
    calc
      ‖R‖ ≤ ‖(3 : ℝ) • (f • apm_m94a04_square h) +
          apm_m94a04_cube h‖ := hD_norm_le _
      _ ≤ ‖(3 : ℝ) • (f • apm_m94a04_square h)‖ +
          ‖apm_m94a04_cube h‖ := norm_add_le _ _
      _ = 3 * ‖(f • apm_m94a04_square h :
          Lp ℝ (8 / 3) apm_m94a04_measure)‖ + ‖apm_m94a04_cube h‖ := by
            rw [norm_smul]
            norm_num
      _ ≤ 3 * (‖f‖ * ‖apm_m94a04_square h‖) + ‖h‖ ^ 3 := by
        gcongr
        · exact Lp.norm_smul_le (r := 8 / 3) f (apm_m94a04_square h)
        · exact apm_m94a04_norm_cube_le h
      _ ≤ 3 * (‖f‖ * ‖h‖ ^ 2) + ‖h‖ ^ 3 := by
        gcongr
        exact apm_m94a04_norm_square_le h
      _ = 3 * ‖f‖ * ‖h‖ ^ 2 + ‖h‖ ^ 3 := by ring
  have hh_one : ‖h‖ < 1 := lt_of_lt_of_le hhsmall (min_le_left _ _)
  have hh_eps : ‖h‖ < ε / A := lt_of_lt_of_le hhsmall (min_le_right _ _)
  have hfinal : ‖R‖ ≤ ε * ‖h‖ := by
    have hn : 0 ≤ ‖h‖ := norm_nonneg h
    have hf : 0 ≤ ‖f‖ := norm_nonneg f
    have hquot : A * ‖h‖ < ε := by
      simpa [mul_comm] using (lt_div_iff₀ hA).mp hh_eps
    dsimp [A] at hquot
    nlinarith [hRnorm]
  rw [eLpNorm_congr_ae hRae]
  have hRnorm' : eLpNorm R 2 apm_m94a04_measure = ENNReal.ofReal ‖R‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top R)]
  rw [hRnorm', hhnorm, ← ENNReal.ofReal_mul hε.le]
  exact ENNReal.ofReal_le_ofReal hfinal

theorem apm_m94a04 :
    ∃ T : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →
        Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
      apm_m94a04_IsOperator T ∧
      ∀ f : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
        ∃ L : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →ₗ[ℝ]
            Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
          apm_m94a04_IsFrechetDerivative T f L ∧
          ∀ h : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
            ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
              L h t = 3 * (f t) ^ 2 * h t := by
  obtain ⟨T, hT, hlinear⟩ := apm_m94A04_bridge_operator_and_linearization
  refine ⟨T, hT, ?_⟩
  intro f
  obtain ⟨L, hbound, hL⟩ := hlinear f
  refine ⟨L, ?_, hL⟩
  exact ⟨hbound,
    apm_m94A04_bridge_remainder_estimate T hT f L hL⟩

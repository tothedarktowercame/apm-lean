import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Complex Filter
open scoped Real

/-- Target statement for apm-a01J04 (currently a skeleton). -/
lemma residue_limit_statement
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (lam : ℂ) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      T^n * Complex.abs ((-1 : ℂ)^n *
        (iteratedDeriv n (fun z => lam / (z - 1) + g z)) 2 / (Nat.factorial n) - lam))
      atTop (𝓝 0) := by
  classical
  have hg_cont : Continuous g := hg.continuous
  have h_iter_split (n : ℕ) :
      (iteratedDeriv n (fun z : ℂ => lam / (z - 1) + g z)) 2
        = (iteratedDeriv n (fun z : ℂ => lam / (z - 1)) + iteratedDeriv n g) 2 := by
    simpa using
      iteratedDeriv_add (fun z : ℂ => lam / (z - 1))
        (fun z : ℂ => g z)
        (by fun_prop) (hg.contDiff.contDiffAt)
  have h_const_mul (n : ℕ) :
      iteratedDeriv n (fun z : ℂ => lam / (z - 1))
        = fun z => lam * iteratedDeriv n (fun z : ℂ => (z - 1)⁻¹) z := by
    simpa [funext_iff, mul_comm, mul_left_comm, mul_assoc] using
      iteratedDeriv_const_mul_field (n := n) (c := lam)
        (f := fun z : ℂ => (z - 1)⁻¹)
  have h_principal (n : ℕ) :
      (-1 : ℂ)^n *
          (iteratedDeriv n (fun z : ℂ => lam / (z - 1))) 2 / Nat.factorial n
        = lam := by
    have :=
      iteratedDeriv_inv_shift (n := n)
    have h_eval :=
      congrArg (fun t => lam * t) (by simpa using this)
    have h_free :
        (iteratedDeriv n (fun z : ℂ => lam / (z - 1))) 2 =
          lam * ((-1 : ℂ)^n * Nat.factorial n) := by
      simpa [h_const_mul, h_eval, sub_eq_add_neg, one_zsmul]
    have h_nonzero : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have h_pow : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = (1 : ℂ) := by simpa using sq_negOne_pow_eq_one (n := n)
    field_simp [h_free, h_pow, h_nonzero]
  have h_remainder (n : ℕ) :
      (-1 : ℂ)^n *
          (iteratedDeriv n (fun z : ℂ => lam / (z - 1) + g z)) 2 / Nat.factorial n - lam
        = (-1 : ℂ)^n * (iteratedDeriv n g) 2 / Nat.factorial n := by
    have := congrArg (fun t => (-1 : ℂ)^n * t / Nat.factorial n)
      (by simpa [Pi.add_apply, h_iter_split] using
        congrArg (fun (x : (ℂ → ℂ)) => x 2) (funext fun _ => rfl))
    simpa [h_principal n, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  set R : ℝ := T + 1 with hRdef
  have hR_pos : 0 < R := add_pos_of_nonneg_of_pos (le_of_lt hT) one_pos
  have hTR : T / R < 1 := by
    have hR_gt : T < R := by
      simpa [hRdef] using lt_add_of_pos_right T one_pos
    have hRpos : 0 < R := hR_pos
    exact div_lt_one_of_lt_of_pos hR_gt hRpos
  have hg_diffCont : DiffContOnCl ℂ g (ball (2 : ℂ) R) :=
    (Differentiable.diffContOnCl (s := ball (2 : ℂ) R) hg)
  have h_bound_cont :
      ContinuousOn (fun z : ℂ => ‖g z‖) (sphere (2 : ℂ) R) :=
    (hg_cont.norm).continuousOn
  obtain ⟨z₀, hz₀, hz₀_max⟩ :=
    (isCompact_sphere (2 : ℂ) R).exists_isMaxOn (nonempty_sphere.2 (le_of_lt hR_pos)) h_bound_cont
  set C : ℝ := ‖g z₀‖
  have hC_bound : ∀ z ∈ sphere (2 : ℂ) R, ‖g z‖ ≤ C := by
    intro z hz
    simpa [C] using hz₀_max hz
  have h_norm_bound (n : ℕ) :
      ‖iteratedDeriv n g 2‖ ≤ Nat.factorial n * C / R ^ n := by
    simpa [RCLike.norm_nsmul, Complex.norm_eq_abs]
      using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        (n := n) (c := (2 : ℂ)) (R := R) (C := C)
        hR_pos hg_diffCont hC_bound
  have h_abs_iter (n : ℕ) :
      Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n)
        ≤ C / R ^ n := by
    have h_nonzero : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have h_iter_bound :
        Complex.abs ((iteratedDeriv n g) 2) ≤ Nat.factorial n * C / R ^ n := by
      simpa [Complex.norm_eq_abs] using h_norm_bound n
    have h_fact_nonneg : 0 ≤ (Nat.factorial n : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_div :=
      div_le_div_of_nonneg_right h_iter_bound h_fact_nonneg
    have h_div_simplify :
        Complex.abs ((iteratedDeriv n g) 2) / Nat.factorial n ≤ C / R ^ n := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using h_div
    have h_abs_eq :
        Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n)
          = Complex.abs ((iteratedDeriv n g) 2) / Nat.factorial n := by
      simp [Complex.abs_mul, Complex.abs_div, h_nonzero]
    simpa [h_abs_eq] using h_div_simplify
  have h_norm_le (n : ℕ) :
      ‖T ^ n *
          Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n)‖
        ≤ C * (T / R) ^ n := by
    have h_pow_nonneg : 0 ≤ T ^ n := pow_nonneg (le_of_lt hT) n
    have h_abs_nonneg :
        0 ≤ Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n) :=
      abs_nonneg _
    have h_seq_nonneg :
        0 ≤
          T ^ n *
            Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n) :=
      mul_nonneg h_pow_nonneg h_abs_nonneg
    have h_mul_le :
        T ^ n *
            Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n)
          ≤ T ^ n * (C / R ^ n) :=
      mul_le_mul_of_nonneg_left (h_abs_iter n) h_pow_nonneg
    have h_ratio :
        T ^ n * (C / R ^ n) = C * (T / R) ^ n := by
      have hR_ne : (R : ℝ) ≠ 0 := by exact ne_of_gt hR_pos
      simp [div_eq_mul_inv, div_pow, hR_ne, mul_comm, mul_left_comm, mul_assoc]
        at *
    have h_norm_eq :
        ‖T ^ n *
            Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n)‖
          =
          T ^ n *
            Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n) := by
      simp [Real.norm_eq_abs, abs_of_nonneg h_seq_nonneg]
    simpa [h_norm_eq, h_ratio] using h_mul_le
  have h_geom :
      Tendsto (fun n : ℕ => (T / R) ^ n) atTop (𝓝 0) :=
    Real.tendsto_pow_atTop_nhds_0_of_abs_lt_1
      (by simpa [abs_of_nonneg (le_of_lt hTR), abs_of_nonneg (le_of_lt hTR)] using hTR)
  have h_const :
      Tendsto (fun n : ℕ => (C : ℝ) * (T / R) ^ n) atTop (𝓝 0) :=
    by
      have := h_geom
      simpa using this.const_mul C
  have h_norm_tendsto :
      Tendsto (fun n : ℕ =>
        ‖T ^ n *
            Complex.abs ((-1 : ℂ) ^ n * (iteratedDeriv n g) 2 / Nat.factorial n)‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall h_norm_le)
    exact h_const
  refine
    (tendsto_of_norm_tendsto_zero h_norm_tendsto).congr'
      (eventually_of_forall fun n =>
        by
          simp [h_remainder n, Complex.abs_mul, Complex.abs_div,
            Complex.abs_of_nonneg (by positivity)])
  simpa using h_const

/-- Derivative of the model pole term: still a skeleton. -/
lemma iteratedDeriv_inv_shift (n : ℕ) :
    (iteratedDeriv n (fun z : ℂ => (z - 1)⁻¹)) 2
      = (-1 : ℂ)^n * Nat.factorial n * (2 - 1) ^ (-(n + 1 : ℤ)) := by
  classical
  have hshift :
      iteratedDeriv n (fun z : ℂ => (z - 1)⁻¹)
        = fun t => iteratedDeriv n (fun w : ℂ => w⁻¹) (t - 1) :=
    iteratedDeriv_comp_sub_const (n := n) (f := fun w : ℂ => w⁻¹) (s := (1 : ℂ))
  have h_eval :
      (iteratedDeriv n (fun z : ℂ => (z - 1)⁻¹)) 2
        = iteratedDeriv n (fun w : ℂ => w⁻¹) 1 := by
    simpa [hshift] 
  have hs : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne (continuous_id.sub continuous_const)
  have h_within :
      iteratedDeriv n (fun w : ℂ => w⁻¹) 1
        = iteratedDerivWithin n (fun w : ℂ => w⁻¹) {z : ℂ | z ≠ 0} 1 := by
    simpa using congrArg (fun F => F 1)
      (iteratedDerivWithin_of_isOpen (n := n)
        (f := fun w : ℂ => w⁻¹) hs)
  have h_one_mem : (1 : ℂ) ∈ {z : ℂ | z ≠ 0} := by simp
  have h_formula :
      iteratedDerivWithin n (fun w : ℂ => w⁻¹) {z : ℂ | z ≠ 0} 1 =
        (-1 : ℂ)^n * (Nat.factorial n) * (1 : ℂ) ^ (-(n + 1 : ℤ)) := by
    have := (iteratedDerivWithin_one_div (k := n)
        (s := {z : ℂ | z ≠ 0}) hs) h_one_mem
    simpa using this
  have h_pow : (1 : ℂ) ^ (-(n + 1 : ℤ)) = (2 - 1 : ℂ) ^ (-(n + 1 : ℤ)) := by simp
  simpa [h_eval, h_within, h_formula, h_pow] 

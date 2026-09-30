import Mathlib

/-!
# APM m94J05 — a small nonlinear Euler boundary-value problem

## Statement repairs

The source's unrestricted uniqueness claim is false: even at zero forcing the
associated superlinear two-point Dirichlet problem has a nonzero large branch.
The conclusion is therefore stated as existence and uniqueness in a uniform
sup-norm ball, which is exactly the small branch controlled by the hinted
contraction argument.

Solutions are represented by ambient functions `ℝ → ℝ` to use Mathlib's
derivatives.  Consequently uniqueness is stated with `Set.EqOn` on `[1,2]`;
values outside the source interval are intentionally irrelevant.

## Encoding questions

None.
-/

open Set

def IsM94J05Solution (f x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 1 2) ∧
  x 1 = 0 ∧ x 2 = 0 ∧
  ∀ t ∈ Icc (1 : ℝ) 2,
    t ^ 2 * iteratedDeriv 2 x t + 2 * t * deriv x t = f t + (x t) ^ 2

/-- The zero function is the small solution at zero forcing. -/
lemma IsM94J05Solution_zero :
    IsM94J05Solution (fun _ ↦ 0) (fun _ ↦ 0) := by
  refine ⟨contDiffOn_const, rfl, rfl, ?_⟩
  intro t ht
  simp [iteratedDeriv_const_zero]

/-- On a radius-`r` ball, the quadratic nonlinearity has Lipschitz constant
`2r`. -/
lemma m94J05_sq_lipschitz_on_ball {r u v : ℝ}
    (hu : |u| ≤ r) (hv : |v| ≤ r) :
    |u ^ 2 - v ^ 2| ≤ 2 * r * |u - v| := by
  rw [sq_sub_sq, abs_mul]
  have huv : |u + v| ≤ 2 * r := by
    calc
      |u + v| ≤ |u| + |v| := abs_add_le _ _
      _ ≤ r + r := add_le_add hu hv
      _ = 2 * r := by ring
  exact mul_le_mul_of_nonneg_right huv (abs_nonneg _)

/-- Dirichlet Green kernel on the transformed interval `[1/2,1]`. -/
noncomputable def m94J05_green (s q : ℝ) : ℝ :=
  if s ≤ q then 2 * (s - 1 / 2) * (1 - q)
  else 2 * (q - 1 / 2) * (1 - s)

/-- A concrete nontrivial value of the transformed Green kernel. -/
lemma m94J05_green_midpoint :
    m94J05_green (3 / 4) (3 / 4) = (1 / 8 : ℝ) := by
  norm_num [m94J05_green]

lemma m94J05_green_nonneg {s q : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1) (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
    0 ≤ m94J05_green s q := by
  simp only [m94J05_green]
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hs.1))
      (sub_nonneg.mpr hq.2)
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hq.1))
      (sub_nonneg.mpr hs.2)

lemma m94J05_green_le_eighth {s q : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1) (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
    m94J05_green s q ≤ (1 / 8 : ℝ) := by
  simp only [m94J05_green]
  split_ifs with hsq
  · have hprod : (s - 1 / 2) * (1 - q) ≤
        (q - 1 / 2) * (1 - q) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hq.2])
    have hsq' : 0 ≤ (q - 3 / 4) ^ 2 := sq_nonneg _
    nlinarith
  · have hqs : q ≤ s := le_of_not_ge hsq
    have hprod : (q - 1 / 2) * (1 - s) ≤
        (s - 1 / 2) * (1 - s) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hs.2])
    have hsq' : 0 ≤ (s - 3 / 4) ^ 2 := sq_nonneg _
    nlinarith

/-- For fixed `s`, the two affine branches glue continuously at `q = s`. -/
lemma m94J05_continuous_green_right (s : ℝ) :
    Continuous (m94J05_green s) := by
  unfold m94J05_green
  apply continuous_if_le continuous_const continuous_id <;> try fun_prop
  intro q hq
  dsimp
  have hqs : s = q := by simpa using hq
  rw [hqs]

/-- Sharp polynomial bound for the total Green-kernel mass. -/
lemma m94J05_green_mass_polynomial_le (s : ℝ) :
    (s - 1 / 2) * (1 - s) / 2 ≤ (1 / 32 : ℝ) := by
  have hsquare : 0 ≤ (s - 3 / 4) ^ 2 := sq_nonneg _
  nlinarith

/-- Exact total mass of the transformed Green kernel. -/
lemma m94J05_green_mass {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    (∫ q in (1 / 2 : ℝ)..1, m94J05_green s q) =
      (s - 1 / 2) * (1 - s) / 2 := by
  have hcont := m94J05_continuous_green_right s
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (1 / 2) s)
    (hcont.intervalIntegrable s 1)]
  have hleft :
      (∫ q in (1 / 2 : ℝ)..s, m94J05_green s q) =
        ∫ q in (1 / 2 : ℝ)..s, 2 * (q - 1 / 2) * (1 - s) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hs.1] at hq
    simp only [m94J05_green]
    split_ifs with hsq
    · have : q = s := le_antisymm hq.2 hsq
      subst q
      ring
    · rfl
  have hright :
      (∫ q in s..1, m94J05_green s q) =
        ∫ q in s..1, 2 * (s - 1 / 2) * (1 - q) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hs.2] at hq
    simp only [m94J05_green]
    rw [if_pos hq.1]
  have hA :
      (∫ q in (1 / 2 : ℝ)..s, q - 1 / 2) = (s - 1 / 2) ^ 2 / 2 := by
    norm_num [intervalIntegral.integral_sub, integral_id] <;> ring
  have hB :
      (∫ q in s..1, 1 - q) = (1 - s) ^ 2 / 2 := by
    calc
      (∫ q in s..1, 1 - q) =
          (∫ q in s..1, (fun _ : ℝ ↦ 1) q) -
            ∫ q in s..1, (fun q : ℝ ↦ q) q := by
              exact intervalIntegral.integral_sub
                (continuous_const.intervalIntegrable _ _)
                (continuous_id.intervalIntegrable _ _)
      _ = (1 - s) ^ 2 / 2 := by simp [integral_id]; ring
  rw [hleft, hright]
  rw [show (∫ q in (1 / 2 : ℝ)..s, 2 * (q - 1 / 2) * (1 - s)) =
      2 * (1 - s) * ∫ q in (1 / 2 : ℝ)..s, q - 1 / 2 by
        calc
          (∫ q in (1 / 2 : ℝ)..s, 2 * (q - 1 / 2) * (1 - s)) =
              ∫ q in (1 / 2 : ℝ)..s, (2 * (1 - s)) * (q - 1 / 2) := by
                apply intervalIntegral.integral_congr
                intro q _
                ring
          _ = 2 * (1 - s) * ∫ q in (1 / 2 : ℝ)..s, q - 1 / 2 := by
                rw [intervalIntegral.integral_const_mul]]
  rw [show (∫ q in s..1, 2 * (s - 1 / 2) * (1 - q)) =
      (2 * (s - 1 / 2)) * ∫ q in s..1, 1 - q by
        rw [intervalIntegral.integral_const_mul]]
  rw [hA, hB]
  ring

lemma m94J05_green_mass_le {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    (∫ q in (1 / 2 : ℝ)..1, m94J05_green s q) ≤ (1 / 32 : ℝ) := by
  rw [m94J05_green_mass hs]
  exact m94J05_green_mass_polynomial_le s

/-- Integral operator associated to the transformed Dirichlet kernel. -/
noncomputable def m94J05_greenOperator (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * h q

/-- Concrete non-vacuity check for the Green operator. -/
lemma m94J05_greenOperator_one_midpoint :
    m94J05_greenOperator (fun _ ↦ 1) (3 / 4) = (1 / 32 : ℝ) := by
  rw [m94J05_greenOperator]
  simp only [mul_one]
  rw [m94J05_green_mass (by norm_num)]
  norm_num

lemma m94J05_greenOperator_zero :
    m94J05_greenOperator (fun _ ↦ 0) = 0 := by
  funext s
  simp [m94J05_greenOperator]

lemma m94J05_greenOperator_left (h : ℝ → ℝ) :
    m94J05_greenOperator h (1 / 2) = 0 := by
  rw [m94J05_greenOperator]
  calc
    (∫ q in (1 / 2 : ℝ)..1, m94J05_green (1 / 2) q * h q) =
        ∫ _q in (1 / 2 : ℝ)..1, 0 := by
          apply intervalIntegral.integral_congr
          intro q hq
          rw [uIcc_of_le (by norm_num)] at hq
          simp only [m94J05_green]
          rw [if_pos hq.1]
          ring
    _ = 0 := by simp

lemma m94J05_greenOperator_right (h : ℝ → ℝ) :
    m94J05_greenOperator h 1 = 0 := by
  rw [m94J05_greenOperator]
  calc
    (∫ q in (1 / 2 : ℝ)..1, m94J05_green 1 q * h q) =
        ∫ _q in (1 / 2 : ℝ)..1, 0 := by
          apply intervalIntegral.integral_congr
          intro q hq
          rw [uIcc_of_le (by norm_num)] at hq
          simp only [m94J05_green]
          split_ifs with hone
          · have : q = 1 := le_antisymm hq.2 hone
            subst q
            norm_num
          · norm_num
    _ = 0 := by simp

lemma m94J05_greenOperator_abs_le {h : ℝ → ℝ} {M s : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1)
    (hM : 0 ≤ M)
    (hhc : ContinuousOn h (Icc (1 / 2 : ℝ) 1))
    (hh : ∀ q ∈ Icc (1 / 2 : ℝ) 1, |h q| ≤ M) :
    |m94J05_greenOperator h s| ≤ (1 / 32 : ℝ) * M := by
  have hgcont : ContinuousOn (fun q => m94J05_green s q) (Icc (1 / 2 : ℝ) 1) :=
    (m94J05_continuous_green_right s).continuousOn
  have hprod : IntervalIntegrable
      (fun q => m94J05_green s q * h q) MeasureTheory.volume (1 / 2) 1 :=
    (hgcont.mul hhc).intervalIntegrable_of_Icc (by norm_num)
  have habs : IntervalIntegrable
      (fun q => |m94J05_green s q * h q|) MeasureTheory.volume (1 / 2) 1 :=
    hprod.norm
  have hmajor : IntervalIntegrable
      (fun q => m94J05_green s q * M) MeasureTheory.volume (1 / 2) 1 :=
    hgcont.mul continuousOn_const |>.intervalIntegrable_of_Icc (by norm_num)
  rw [m94J05_greenOperator]
  change ‖∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * h q‖ ≤ _
  calc
    ‖∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * h q‖ ≤
        ∫ q in (1 / 2 : ℝ)..1, |m94J05_green s q * h q| :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * M := by
      apply intervalIntegral.integral_mono_on (by norm_num) habs hmajor
      intro q hq
      rw [abs_mul, abs_of_nonneg (m94J05_green_nonneg hs hq)]
      exact mul_le_mul_of_nonneg_left (hh q hq) (m94J05_green_nonneg hs hq)
    _ = M * ∫ q in (1 / 2 : ℝ)..1, m94J05_green s q := by
      rw [intervalIntegral.integral_mul_const]
      ring
    _ ≤ M * (1 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_left (m94J05_green_mass_le hs) hM
    _ = (1 / 32 : ℝ) * M := by ring

lemma m94J05_greenOperator_sub {h k : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1))
    (hk : ContinuousOn k (Icc (1 / 2 : ℝ) 1)) :
    m94J05_greenOperator (fun q => h q - k q) =
      m94J05_greenOperator h - m94J05_greenOperator k := by
  funext s
  change (∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * (h q - k q)) =
    (∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * h q) -
      ∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * k q
  have hg : ContinuousOn (fun q => m94J05_green s q)
      (Icc (1 / 2 : ℝ) 1) := (m94J05_continuous_green_right s).continuousOn
  have hhi : IntervalIntegrable (fun q => m94J05_green s q * h q)
      MeasureTheory.volume (1 / 2) 1 :=
    (hg.mul hh).intervalIntegrable_of_Icc (by norm_num)
  have hki : IntervalIntegrable (fun q => m94J05_green s q * k q)
      MeasureTheory.volume (1 / 2) 1 :=
    (hg.mul hk).intervalIntegrable_of_Icc (by norm_num)
  rw [show (∫ q in (1 / 2 : ℝ)..1, m94J05_green s q * (h q - k q)) =
      ∫ q in (1 / 2 : ℝ)..1,
        (m94J05_green s q * h q - m94J05_green s q * k q) by
      apply intervalIntegral.integral_congr
      intro q _
      ring]
  exact intervalIntegral.integral_sub hhi hki

lemma m94J05_greenOperator_sub_abs_le {h k : ℝ → ℝ} {M s : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1)
    (hM : 0 ≤ M)
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1))
    (hk : ContinuousOn k (Icc (1 / 2 : ℝ) 1))
    (hsub : ∀ q ∈ Icc (1 / 2 : ℝ) 1, |h q - k q| ≤ M) :
    |m94J05_greenOperator h s - m94J05_greenOperator k s| ≤
      (1 / 32 : ℝ) * M := by
  have heq := congrFun (m94J05_greenOperator_sub hh hk) s
  change m94J05_greenOperator (fun q => h q - k q) s =
    m94J05_greenOperator h s - m94J05_greenOperator k s at heq
  rw [← heq]
  exact m94J05_greenOperator_abs_le hs hM (hh.sub hk) hsub

lemma m94J05_inv_mem_Icc {q : ℝ} (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
    1 / q ∈ Icc (1 : ℝ) 2 := by
  constructor
  · exact (le_div_iff₀ (by linarith [hq.1])).2 (by linarith [hq.2])
  · exact (div_le_iff₀ (by linarith [hq.1])).2 (by linarith [hq.1])

lemma m94J05_inv_sq_le_four {q : ℝ} (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
    1 / q ^ 2 ≤ 4 := by
  have hqpos : 0 < q := by linarith [hq.1]
  apply (div_le_iff₀ (sq_pos_of_pos hqpos)).2
  nlinarith [mul_self_le_mul_self (by norm_num : 0 ≤ (1 / 2 : ℝ)) hq.1]

lemma m94J05_weighted_input_abs_le {f u : ℝ → ℝ} {ε r q : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hq : q ∈ Icc (1 / 2 : ℝ) 1)
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ ε)
    (hu : ∀ y ∈ Icc (1 / 2 : ℝ) 1, |u y| ≤ r) :
    |(f (1 / q) + (u q) ^ 2) / q ^ 2| ≤ 4 * (ε + r ^ 2) := by
  have hqpos : 0 < q ^ 2 := sq_pos_of_pos (by linarith [hq.1])
  rw [abs_div, abs_of_pos hqpos]
  have hnum : |f (1 / q) + (u q) ^ 2| ≤ ε + r ^ 2 := by
    calc
      |f (1 / q) + (u q) ^ 2| ≤ |f (1 / q)| + |(u q) ^ 2| := abs_add_le _ _
      _ ≤ ε + r ^ 2 := by
        apply add_le_add (hf _ (m94J05_inv_mem_Icc hq))
        rw [abs_sq]
        calc
          (u q) ^ 2 = |u q| ^ 2 := by rw [sq_abs]
          _ ≤ r ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr (hu q hq))
              (add_nonneg hr (abs_nonneg (u q)))]
  calc
    |f (1 / q) + (u q) ^ 2| / q ^ 2 ≤ (ε + r ^ 2) / q ^ 2 :=
      (div_le_div_iff_of_pos_right hqpos).2 hnum
    _ = (1 / q ^ 2) * (ε + r ^ 2) := by ring
    _ ≤ 4 * (ε + r ^ 2) :=
      mul_le_mul_of_nonneg_right (m94J05_inv_sq_le_four hq)
        (add_nonneg hε (sq_nonneg r))

lemma m94J05_weighted_input_sub_abs_le {f u v : ℝ → ℝ} {r q : ℝ}
    (hr : 0 ≤ r)
    (hq : q ∈ Icc (1 / 2 : ℝ) 1)
    (hu : ∀ y ∈ Icc (1 / 2 : ℝ) 1, |u y| ≤ r)
    (hv : ∀ y ∈ Icc (1 / 2 : ℝ) 1, |v y| ≤ r) :
    |(f (1 / q) + (u q) ^ 2) / q ^ 2 -
      (f (1 / q) + (v q) ^ 2) / q ^ 2| ≤
        8 * r * |u q - v q| := by
  have hqpos : 0 < q ^ 2 := sq_pos_of_pos (by linarith [hq.1])
  rw [← sub_div, add_sub_add_left_eq_sub, abs_div, abs_of_pos hqpos]
  calc
    |(u q) ^ 2 - (v q) ^ 2| / q ^ 2 ≤
        (2 * r * |u q - v q|) / q ^ 2 :=
      (div_le_div_iff_of_pos_right hqpos).2
        (m94J05_sq_lipschitz_on_ball (hu q hq) (hv q hq))
    _ = (1 / q ^ 2) * (2 * r * |u q - v q|) := by ring
    _ ≤ 4 * (2 * r * |u q - v q|) := by
      apply mul_le_mul_of_nonneg_right (m94J05_inv_sq_le_four hq)
      positivity
    _ = 8 * r * |u q - v q| := by ring

lemma m94J05_greenOperator_eq_split {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1)
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) :
    m94J05_greenOperator h s =
      (∫ q in (1 / 2 : ℝ)..s, 2 * (q - 1 / 2) * (1 - s) * h q) +
      ∫ q in s..1, 2 * (s - 1 / 2) * (1 - q) * h q := by
  have hc : ContinuousOn (fun q => m94J05_green s q * h q)
      (Icc (1 / 2 : ℝ) 1) :=
    (m94J05_continuous_green_right s).continuousOn.mul hh
  have hleft : IntervalIntegrable (fun q => m94J05_green s q * h q)
      MeasureTheory.volume (1 / 2) s :=
    (hc.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
  have hright : IntervalIntegrable (fun q => m94J05_green s q * h q)
      MeasureTheory.volume s 1 :=
    (hc.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2
  rw [m94J05_greenOperator,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  congr 1
  · apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hs.1] at hq
    simp only [m94J05_green]
    split_ifs with hsq
    · have : q = s := le_antisymm hq.2 hsq
      subst q
      ring
    · ring
  · apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le hs.2] at hq
    simp only [m94J05_green, if_pos hq.1]

lemma m94J05_greenOperator_eq_primitives {h : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1)
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) :
    m94J05_greenOperator h s =
      2 * (1 - s) * (∫ q in (1 / 2 : ℝ)..s, (q - 1 / 2) * h q) +
      2 * (s - 1 / 2) * (∫ q in s..1, (1 - q) * h q) := by
  rw [m94J05_greenOperator_eq_split hs hh]
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    ring

lemma m94J05_continuousOn_greenOperator {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) :
    ContinuousOn (m94J05_greenOperator h) (Icc (1 / 2 : ℝ) 1) := by
  let A : ℝ → ℝ := fun q => (q - 1 / 2) * h q
  let B : ℝ → ℝ := fun q => (1 - q) * h q
  have hAc : ContinuousOn A (Icc (1 / 2 : ℝ) 1) :=
    (continuousOn_id.sub continuousOn_const).mul hh
  have hBc : ContinuousOn B (Icc (1 / 2 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).mul hh
  have hAi : MeasureTheory.IntegrableOn A (Icc (1 / 2 : ℝ) 1)
      MeasureTheory.volume := hAc.integrableOn_Icc
  have hBi : MeasureTheory.IntegrableOn B (Icc (1 / 2 : ℝ) 1)
      MeasureTheory.volume := hBc.integrableOn_Icc
  have hPAset := intervalIntegral.continuousOn_primitive hAi
  have hPBset := intervalIntegral.continuousOn_primitive hBi
  have hPA : ContinuousOn (fun s => ∫ q in (1 / 2 : ℝ)..s, A q)
      (Icc (1 / 2 : ℝ) 1) := by
    apply hPAset.congr
    intro s hs
    dsimp only
    rw [intervalIntegral.integral_of_le hs.1]
  have hPB : ContinuousOn (fun s => ∫ q in (1 / 2 : ℝ)..s, B q)
      (Icc (1 / 2 : ℝ) 1) := by
    apply hPBset.congr
    intro s hs
    dsimp only
    rw [intervalIntegral.integral_of_le hs.1]
  have hQB : ContinuousOn (fun s => ∫ q in s..1, B q)
      (Icc (1 / 2 : ℝ) 1) := by
    have hd : ContinuousOn
        (fun s => (∫ q in (1 / 2 : ℝ)..1, B q) -
          ∫ q in (1 / 2 : ℝ)..s, B q) (Icc (1 / 2 : ℝ) 1) :=
      continuousOn_const.sub hPB
    apply hd.congr
    intro s hs
    have hBas : IntervalIntegrable B MeasureTheory.volume (1 / 2) s :=
      (hBc.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    have hBs1 : IntervalIntegrable B MeasureTheory.volume s 1 :=
      (hBc.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2
    rw [← intervalIntegral.integral_add_adjacent_intervals hBas hBs1]
    ring
  have hexpr : ContinuousOn (fun s =>
      2 * (1 - s) * (∫ q in (1 / 2 : ℝ)..s, A q) +
      2 * (s - 1 / 2) * (∫ q in s..1, B q))
      (Icc (1 / 2 : ℝ) 1) := by
    fun_prop
  apply hexpr.congr
  intro s hs
  simpa [A, B] using m94J05_greenOperator_eq_primitives hs hh

abbrev m94J05Continuous := C(Icc (1 / 2 : ℝ) 1, ℝ)

/-- Canonical continuous extension of interval data, obtained by clamping the
input to the transformed interval. -/
noncomputable def m94J05Continuous.extend (u : m94J05Continuous) : ℝ → ℝ :=
  fun q => u (projIcc (1 / 2 : ℝ) 1 (by norm_num) q)

lemma m94J05Continuous.extend_continuous (u : m94J05Continuous) :
    Continuous u.extend :=
  u.continuous.comp continuous_projIcc

lemma m94J05Continuous.extend_apply (u : m94J05Continuous) {q : ℝ}
    (hq : q ∈ Icc (1 / 2 : ℝ) 1) :
    u.extend q = u ⟨q, hq⟩ := by
  simp [m94J05Continuous.extend, projIcc_of_mem (by norm_num) hq]

/-- Concrete normalization check for the clamped extension. -/
lemma m94J05Continuous.extend_zero :
    m94J05Continuous.extend (0 : m94J05Continuous) = 0 := by
  funext q
  rfl

noncomputable def m94J05_transformedInput (f : ℝ → ℝ)
    (u : m94J05Continuous) (q : ℝ) : ℝ :=
  (f (1 / q) + (u.extend q) ^ 2) / q ^ 2

lemma m94J05_continuousOn_transformedInput {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (1 : ℝ) 2)) (u : m94J05Continuous) :
    ContinuousOn (m94J05_transformedInput f u) (Icc (1 / 2 : ℝ) 1) := by
  have hinv : ContinuousOn (fun q : ℝ => 1 / q) (Icc (1 / 2 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro q hq hzero
    change q = 0 at hzero
    linarith [hq.1]
  have hfcomp : ContinuousOn (fun q : ℝ => f (1 / q)) (Icc (1 / 2 : ℝ) 1) :=
    hf.comp hinv (fun q hq => m94J05_inv_mem_Icc hq)
  unfold m94J05_transformedInput
  apply ContinuousOn.div (hfcomp.add (u.extend_continuous.continuousOn.pow 2))
    (continuousOn_id.pow 2)
  intro q hq hzero
  change q ^ 2 = 0 at hzero
  have : q ≠ 0 := by linarith [hq.1]
  exact (pow_ne_zero 2 this) hzero

noncomputable def m94J05_selfMap (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (1 : ℝ) 2))
    (u : m94J05Continuous) : m94J05Continuous where
  toFun s := -m94J05_greenOperator (m94J05_transformedInput f u) s
  continuous_toFun :=
    ((m94J05_continuousOn_greenOperator
      (m94J05_continuousOn_transformedInput hf u)).neg).comp_continuous
        continuous_subtype_val (fun s => s.2)

lemma m94J05_selfMap_zero :
    m94J05_selfMap (fun _ => 0) continuousOn_const (0 : m94J05Continuous) = 0 := by
  ext s
  simp [m94J05_selfMap, m94J05_transformedInput, m94J05Continuous.extend,
    m94J05_greenOperator]

lemma m94J05_selfMap_norm_le {f : ℝ → ℝ}
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    {u : m94J05Continuous} {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ ε)
    (hu : ‖u‖ ≤ r) :
    ‖m94J05_selfMap f hfcont u‖ ≤ (1 / 8 : ℝ) * (ε + r ^ 2) := by
  apply (ContinuousMap.norm_le (f := m94J05_selfMap f hfcont u) (mul_nonneg (by norm_num)
    (add_nonneg hε (sq_nonneg r)))).2
  intro s
  change |-m94J05_greenOperator (m94J05_transformedInput f u) s| ≤ _
  rw [abs_neg]
  have hinput : ∀ q ∈ Icc (1 / 2 : ℝ) 1,
      |m94J05_transformedInput f u q| ≤ 4 * (ε + r ^ 2) := by
    intro q hq
    apply m94J05_weighted_input_abs_le hε hr hq hf
    intro y hy
    rw [m94J05Continuous.extend_apply u hy]
    exact (u.norm_coe_le_norm ⟨y, hy⟩).trans hu
  have hb := m94J05_greenOperator_abs_le s.2
    (mul_nonneg (by norm_num) (add_nonneg hε (sq_nonneg r)))
    (m94J05_continuousOn_transformedInput hfcont u) hinput
  nlinarith

lemma m94J05_selfMap_sub_norm_le {f : ℝ → ℝ}
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    {u v : m94J05Continuous} {r : ℝ}
    (hr : 0 ≤ r) (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) :
    ‖m94J05_selfMap f hfcont u - m94J05_selfMap f hfcont v‖ ≤
      (r / 4) * ‖u - v‖ := by
  have hcoef : 0 ≤ r / 4 * ‖u - v‖ := mul_nonneg (div_nonneg hr (by norm_num)) (norm_nonneg _)
  apply (ContinuousMap.norm_le (f := m94J05_selfMap f hfcont u -
    m94J05_selfMap f hfcont v) hcoef).2
  intro s
  change ‖-m94J05_greenOperator (m94J05_transformedInput f u) s -
    -m94J05_greenOperator (m94J05_transformedInput f v) s‖ ≤ _
  rw [Real.norm_eq_abs, show -m94J05_greenOperator (m94J05_transformedInput f u) s -
      -m94J05_greenOperator (m94J05_transformedInput f v) s =
      -(m94J05_greenOperator (m94J05_transformedInput f u) s -
        m94J05_greenOperator (m94J05_transformedInput f v) s) by ring, abs_neg]
  have hub : ∀ q ∈ Icc (1 / 2 : ℝ) 1, |u.extend q| ≤ r := by
    intro q hq
    rw [m94J05Continuous.extend_apply u hq]
    exact (u.norm_coe_le_norm ⟨q, hq⟩).trans hu
  have hvb : ∀ q ∈ Icc (1 / 2 : ℝ) 1, |v.extend q| ≤ r := by
    intro q hq
    rw [m94J05Continuous.extend_apply v hq]
    exact (v.norm_coe_le_norm ⟨q, hq⟩).trans hv
  have hsub : ∀ q ∈ Icc (1 / 2 : ℝ) 1,
      |m94J05_transformedInput f u q - m94J05_transformedInput f v q| ≤
        8 * r * ‖u - v‖ := by
    intro q hq
    refine (m94J05_weighted_input_sub_abs_le hr hq hub hvb).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [m94J05Continuous.extend_apply u hq, m94J05Continuous.extend_apply v hq]
    exact (u - v).norm_coe_le_norm ⟨q, hq⟩
  have hb := m94J05_greenOperator_sub_abs_le s.2
    (mul_nonneg (mul_nonneg (by norm_num) hr) (norm_nonneg _))
    (m94J05_continuousOn_transformedInput hfcont u)
    (m94J05_continuousOn_transformedInput hfcont v) hsub
  nlinarith

abbrev m94J05Ball := Metric.closedBall (0 : m94J05Continuous) (1 / 2 : ℝ)

noncomputable def m94J05_ballMap (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1)
    (u : m94J05Ball) : m94J05Ball := by
  refine ⟨m94J05_selfMap f hfcont u.1, ?_⟩
  rw [mem_closedBall_zero_iff]
  have hu : ‖(u : m94J05Continuous)‖ ≤ (1 / 2 : ℝ) := by
    exact mem_closedBall_zero_iff.mp u.2
  have h := m94J05_selfMap_norm_le hfcont (by norm_num) (by norm_num) hf hu
  norm_num at h ⊢
  linarith

lemma m94J05_ballMap_zero :
    m94J05_ballMap (fun _ => 0) continuousOn_const (by simp) ⟨0, by norm_num⟩ =
      (⟨0, by norm_num⟩ : m94J05Ball) := by
  apply Subtype.ext
  exact m94J05_selfMap_zero

lemma m94J05_ballMap_contracting (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1) :
    ContractingWith (1 / 8 : NNReal) (m94J05_ballMap f hfcont hf) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  have hu : ‖(u : m94J05Continuous)‖ ≤ (1 / 2 : ℝ) :=
    mem_closedBall_zero_iff.mp u.2
  have hv : ‖(v : m94J05Continuous)‖ ≤ (1 / 2 : ℝ) :=
    mem_closedBall_zero_iff.mp v.2
  have h := m94J05_selfMap_sub_norm_le hfcont (by norm_num) hu hv
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  change ‖m94J05_selfMap f hfcont u.1 - m94J05_selfMap f hfcont v.1‖ ≤
    ((1 / 8 : NNReal) : ℝ) * ‖u.1 - v.1‖
  norm_num at h ⊢
  exact h

lemma m94J05_exists_ball_fixedPoint (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1) :
    ∃ u : m94J05Ball, m94J05_ballMap f hfcont hf u = u := by
  letI : CompleteSpace m94J05Ball :=
    Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let u0 : m94J05Ball := ⟨0, by simp [mem_closedBall_zero_iff]⟩
  rcases (m94J05_ballMap_contracting f hfcont hf).exists_fixedPoint u0 (edist_ne_top _ _) with
    ⟨u, hu, _⟩
  exact ⟨u, hu.eq⟩

lemma m94J05_exists_continuous_fixedPoint (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1) :
    ∃ u : m94J05Continuous,
      ‖u‖ ≤ (1 / 2 : ℝ) ∧
      m94J05_selfMap f hfcont u = u ∧
      u ⟨1 / 2, by norm_num⟩ = 0 ∧ u ⟨1, by norm_num⟩ = 0 := by
  obtain ⟨u, hu⟩ := m94J05_exists_ball_fixedPoint f hfcont hf
  refine ⟨u.1, mem_closedBall_zero_iff.mp u.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hu
  · have heq := congrArg (fun w : m94J05Ball =>
        (w.1 : m94J05Continuous) ⟨1 / 2, by norm_num⟩) hu
    change -m94J05_greenOperator (m94J05_transformedInput f u.1) (1 / 2) =
      u.1 ⟨1 / 2, by norm_num⟩ at heq
    rw [m94J05_greenOperator_left] at heq
    linarith
  · have heq := congrArg (fun w : m94J05Ball =>
        (w.1 : m94J05Continuous) ⟨1, by norm_num⟩) hu
    change -m94J05_greenOperator (m94J05_transformedInput f u.1) 1 =
      u.1 ⟨1, by norm_num⟩ at heq
    rw [m94J05_greenOperator_right] at heq
    linarith

lemma m94J05_leftPrimitive_hasDerivAt {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    HasDerivAt (fun x => ∫ q in (1 / 2 : ℝ)..x, (q - 1 / 2) * h q)
      ((s - 1 / 2) * h s) s := by
  let A : ℝ → ℝ := fun q => (q - 1 / 2) * h q
  have hAc : ContinuousOn A (Icc (1 / 2 : ℝ) 1) :=
    (continuousOn_id.sub continuousOn_const).mul hh
  have hAat : ContinuousAt A s :=
    (hAc s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hAi : IntervalIntegrable A MeasureTheory.volume (1 / 2) s :=
    (hAc.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le
  have hAmeas : StronglyMeasurableAtFilter A (nhds s)
      MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => (hAc x ⟨hx.1.le, hx.2.le⟩).continuousAt
        (Icc_mem_nhds hx.1 hx.2)) s hs
  simpa [A] using intervalIntegral.integral_hasDerivAt_right hAi
    hAmeas hAat

lemma m94J05_rightPrimitive_hasDerivAt {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    HasDerivAt (fun x => ∫ q in x..1, (1 - q) * h q)
      (-((1 - s) * h s)) s := by
  let B : ℝ → ℝ := fun q => (1 - q) * h q
  have hBc : ContinuousOn B (Icc (1 / 2 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).mul hh
  have hBat : ContinuousAt B s :=
    (hBc s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hBi : IntervalIntegrable B MeasureTheory.volume s 1 :=
    (hBc.mono (Icc_subset_Icc hs.1.le le_rfl)).intervalIntegrable_of_Icc hs.2.le
  have hBmeas : StronglyMeasurableAtFilter B (nhds s)
      MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => (hBc x ⟨hx.1.le, hx.2.le⟩).continuousAt
        (Icc_mem_nhds hx.1 hx.2)) s hs
  simpa [B] using intervalIntegral.integral_hasDerivAt_left hBi
    hBmeas hBat

lemma m94J05_greenOperator_hasDerivAt {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    HasDerivAt (m94J05_greenOperator h)
      (2 * ((∫ q in s..1, (1 - q) * h q) -
        ∫ q in (1 / 2 : ℝ)..s, (q - 1 / 2) * h q)) s := by
  let P : ℝ → ℝ := fun x => ∫ q in (1 / 2 : ℝ)..x, (q - 1 / 2) * h q
  let Q : ℝ → ℝ := fun x => ∫ q in x..1, (1 - q) * h q
  let R : ℝ → ℝ := fun x => 2 * (1 - x) * P x + 2 * (x - 1 / 2) * Q x
  have hP := m94J05_leftPrimitive_hasDerivAt hh hs
  have hQ := m94J05_rightPrimitive_hasDerivAt hh hs
  have hR : HasDerivAt R (2 * (Q s - P s)) s := by
    dsimp [R]
    convert (((hasDerivAt_const s (2 : ℝ)).mul
      ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).mul hP).add
      (((hasDerivAt_const s (2 : ℝ)).mul
        ((hasDerivAt_id s).sub (hasDerivAt_const s (1 / 2 : ℝ)))).mul hQ) using 1 <;>
      dsimp [P, Q] <;> ring
  have heq : m94J05_greenOperator h =ᶠ[nhds s] R := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with x hx
    exact m94J05_greenOperator_eq_primitives hx hh
  simpa [P, Q] using hR.congr_of_eventuallyEq heq

lemma m94J05_greenOperator_deriv_eq {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    deriv (m94J05_greenOperator h) s =
      2 * ((∫ q in s..1, (1 - q) * h q) -
        ∫ q in (1 / 2 : ℝ)..s, (q - 1 / 2) * h q) :=
  (m94J05_greenOperator_hasDerivAt hh hs).deriv

lemma m94J05_greenOperator_deriv_hasDerivAt {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    HasDerivAt (deriv (m94J05_greenOperator h)) (-h s) s := by
  let P : ℝ → ℝ := fun x => ∫ q in (1 / 2 : ℝ)..x, (q - 1 / 2) * h q
  let Q : ℝ → ℝ := fun x => ∫ q in x..1, (1 - q) * h q
  let D : ℝ → ℝ := fun x => 2 * (Q x - P x)
  have hP := m94J05_leftPrimitive_hasDerivAt hh hs
  have hQ := m94J05_rightPrimitive_hasDerivAt hh hs
  have hD : HasDerivAt D (-h s) s := by
    dsimp [D]
    convert (hasDerivAt_const s (2 : ℝ)).mul (hQ.sub hP) using 1 <;>
      dsimp [P, Q] <;> ring
  have heq : deriv (m94J05_greenOperator h) =ᶠ[nhds s] D := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact m94J05_greenOperator_deriv_eq hh hx
  exact hD.congr_of_eventuallyEq heq

lemma m94J05_greenOperator_iteratedDeriv_two_eq {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    iteratedDeriv 2 (m94J05_greenOperator h) s = -h s := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  simpa using (m94J05_greenOperator_deriv_hasDerivAt hh hs).deriv

lemma m94J05_greenOperator_contDiffOn_interior {h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc (1 / 2 : ℝ) 1)) :
    ContDiffOn ℝ 2 (m94J05_greenOperator h) (Ioo (1 / 2 : ℝ) 1) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun s hs =>
      (m94J05_greenOperator_hasDerivAt hh hs).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun s hs =>
      (m94J05_greenOperator_deriv_hasDerivAt hh hs).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply (hh.mono
    (Ioo_subset_Icc_self : Ioo (1 / 2 : ℝ) 1 ⊆ Icc (1 / 2 : ℝ) 1)).neg.congr
  intro s hs
  exact (m94J05_greenOperator_deriv_hasDerivAt hh hs).deriv

/-- The primitive formula for the Green operator, using the canonical
continuous extension of interval data.  Unlike the raw kernel formula this
is a convenient ambient representative at the two endpoints. -/
noncomputable def m94J05_regularGreen (h : m94J05Continuous) (s : ℝ) : ℝ :=
  2 * (1 - s) *
      (∫ q in (1 / 2 : ℝ)..s, (q - 1 / 2) * h.extend q) +
    2 * (s - 1 / 2) *
      (∫ q in s..1, (1 - q) * h.extend q)

/-- Concrete normalization check for the regular Green representative. -/
lemma m94J05_regularGreen_zero :
    m94J05_regularGreen (0 : m94J05Continuous) = 0 := by
  funext s
  simp [m94J05_regularGreen, m94J05Continuous.extend_zero]

lemma m94J05_regularGreen_eq_greenOperator (h : m94J05Continuous) {s : ℝ}
    (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    m94J05_regularGreen h s = m94J05_greenOperator h.extend s := by
  symm
  exact m94J05_greenOperator_eq_primitives hs h.extend_continuous.continuousOn

lemma m94J05_regularGreen_left_hasDerivAt (h : m94J05Continuous) (s : ℝ) :
    HasDerivAt
      (fun x => ∫ q in (1 / 2 : ℝ)..x, (q - 1 / 2) * h.extend q)
      ((s - 1 / 2) * h.extend s) s := by
  let A : ℝ → ℝ := fun q => (q - 1 / 2) * h.extend q
  have hA : Continuous A :=
    (continuous_id.sub continuous_const).mul h.extend_continuous
  have hAm : StronglyMeasurableAtFilter A (nhds s) MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun _ _ => hA.continuousAt) s (mem_univ s)
  simpa [A] using intervalIntegral.integral_hasDerivAt_right
    (hA.intervalIntegrable _ _) hAm hA.continuousAt

lemma m94J05_regularGreen_right_hasDerivAt (h : m94J05Continuous) (s : ℝ) :
    HasDerivAt
      (fun x => ∫ q in x..1, (1 - q) * h.extend q)
      (-((1 - s) * h.extend s)) s := by
  let B : ℝ → ℝ := fun q => (1 - q) * h.extend q
  have hB : Continuous B :=
    (continuous_const.sub continuous_id).mul h.extend_continuous
  have hBm : StronglyMeasurableAtFilter B (nhds s) MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun _ _ => hB.continuousAt) s (mem_univ s)
  simpa [B] using intervalIntegral.integral_hasDerivAt_left
    (hB.intervalIntegrable _ _) hBm hB.continuousAt

lemma m94J05_regularGreen_hasDerivAt (h : m94J05Continuous) (s : ℝ) :
    HasDerivAt (m94J05_regularGreen h)
      (2 * ((∫ q in s..1, (1 - q) * h.extend q) -
        ∫ q in (1 / 2 : ℝ)..s, (q - 1 / 2) * h.extend q)) s := by
  have hP := m94J05_regularGreen_left_hasDerivAt h s
  have hQ := m94J05_regularGreen_right_hasDerivAt h s
  unfold m94J05_regularGreen
  convert (((hasDerivAt_const s (2 : ℝ)).mul
    ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).mul hP).add
    (((hasDerivAt_const s (2 : ℝ)).mul
      ((hasDerivAt_id s).sub (hasDerivAt_const s (1 / 2 : ℝ)))).mul hQ) using 1 <;>
    dsimp <;> ring

lemma m94J05_regularGreen_deriv_hasDerivAt (h : m94J05Continuous) (s : ℝ) :
    HasDerivAt (deriv (m94J05_regularGreen h)) (-h.extend s) s := by
  let P : ℝ → ℝ := fun x => ∫ q in (1 / 2 : ℝ)..x, (q - 1 / 2) * h.extend q
  let Q : ℝ → ℝ := fun x => ∫ q in x..1, (1 - q) * h.extend q
  let D : ℝ → ℝ := fun x => 2 * (Q x - P x)
  have hD : HasDerivAt D (-h.extend s) s := by
    dsimp [D]
    convert (hasDerivAt_const s (2 : ℝ)).mul
      ((m94J05_regularGreen_right_hasDerivAt h s).sub
        (m94J05_regularGreen_left_hasDerivAt h s)) using 1 <;>
      dsimp [P, Q] <;> ring
  have heq : deriv (m94J05_regularGreen h) = D := by
    funext x
    exact (m94J05_regularGreen_hasDerivAt h x).deriv
  rw [heq]
  exact hD

lemma m94J05_regularGreen_contDiff_two (h : m94J05Continuous) :
    ContDiff ℝ 2 (m94J05_regularGreen h) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun s => (m94J05_regularGreen_hasDerivAt h s).differentiableAt,
    by simp, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (m94J05_regularGreen_deriv_hasDerivAt h s).differentiableAt, ?_⟩
  apply h.extend_continuous.neg.congr
  intro s
  exact (m94J05_regularGreen_deriv_hasDerivAt h s).deriv.symm

lemma m94J05_regularGreen_iteratedDeriv_two_eq (h : m94J05Continuous) (s : ℝ) :
    iteratedDeriv 2 (m94J05_regularGreen h) s = -h.extend s := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  simpa [iteratedDeriv_one] using
    (m94J05_regularGreen_deriv_hasDerivAt h s).deriv

noncomputable def m94J05_transformedInputCM (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (1 : ℝ) 2))
    (u : m94J05Continuous) : m94J05Continuous where
  toFun q := m94J05_transformedInput f u q
  continuous_toFun :=
    (m94J05_continuousOn_transformedInput hf u).comp_continuous
      continuous_subtype_val (fun q => q.2)

lemma m94J05_transformedInputCM_apply (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (1 : ℝ) 2)) (u : m94J05Continuous)
    (q : Icc (1 / 2 : ℝ) 1) :
    m94J05_transformedInputCM f hf u q = m94J05_transformedInput f u q := rfl

/-- Concrete normalization check for the bundled transformed input. -/
lemma m94J05_transformedInputCM_zero :
    m94J05_transformedInputCM (fun _ => 0) continuousOn_const
      (0 : m94J05Continuous) = 0 := by
  ext q
  simp [m94J05_transformedInputCM, m94J05_transformedInput,
    m94J05Continuous.extend_zero]

lemma m94J05_regularGreen_transformed_eq_selfMap
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (1 : ℝ) 2))
    (u : m94J05Continuous) (q : Icc (1 / 2 : ℝ) 1) :
    -m94J05_regularGreen (m94J05_transformedInputCM f hf u) q =
      m94J05_selfMap f hf u q := by
  rw [m94J05_regularGreen_eq_greenOperator _ q.2]
  change -m94J05_greenOperator
      (m94J05_transformedInputCM f hf u).extend q =
    -m94J05_greenOperator (m94J05_transformedInput f u) q
  congr 1
  unfold m94J05_greenOperator
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hy
  change m94J05_green q y * (m94J05_transformedInputCM f hf u).extend y =
    m94J05_green q y * m94J05_transformedInput f u y
  rw [m94J05Continuous.extend_apply _ hy]
  rfl

lemma m94J05_exists_regular_transformed_solution (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1) :
    ∃ u : m94J05Continuous, ∃ U : ℝ → ℝ,
      ‖u‖ ≤ (1 / 2 : ℝ) ∧ ContDiff ℝ 2 U ∧
      (∀ q (hq : q ∈ Icc (1 / 2 : ℝ) 1), U q = u ⟨q, hq⟩) ∧
      U (1 / 2) = 0 ∧ U 1 = 0 ∧
      (∀ q, iteratedDeriv 2 U q =
        (m94J05_transformedInputCM f hfcont u).extend q) := by
  obtain ⟨u, hunorm, hfix, hleft, hright⟩ :=
    m94J05_exists_continuous_fixedPoint f hfcont hf
  let h := m94J05_transformedInputCM f hfcont u
  let U : ℝ → ℝ := fun q => -m94J05_regularGreen h q
  refine ⟨u, U, hunorm, (m94J05_regularGreen_contDiff_two h).neg, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have heval := congrArg (fun w : m94J05Continuous => w ⟨q, hq⟩) hfix
    dsimp [U, h]
    calc
      -m94J05_regularGreen (m94J05_transformedInputCM f hfcont u) q =
          m94J05_selfMap f hfcont u ⟨q, hq⟩ :=
        m94J05_regularGreen_transformed_eq_selfMap f hfcont u ⟨q, hq⟩
      _ = u ⟨q, hq⟩ := heval
  · rw [show U (1 / 2) = u ⟨1 / 2, by norm_num⟩ by
      exact m94J05_regularGreen_transformed_eq_selfMap f hfcont u
        ⟨1 / 2, by norm_num⟩ |>.trans
          (congrArg (fun w : m94J05Continuous => w ⟨1 / 2, by norm_num⟩) hfix)]
    exact hleft
  · rw [show U 1 = u ⟨1, by norm_num⟩ by
      exact m94J05_regularGreen_transformed_eq_selfMap f hfcont u
        ⟨1, by norm_num⟩ |>.trans
          (congrArg (fun w : m94J05Continuous => w ⟨1, by norm_num⟩) hfix)]
    exact hright
  · intro q
    dsimp [U]
    rw [iteratedDeriv_fun_neg, m94J05_regularGreen_iteratedDeriv_two_eq]
    simp [h]

lemma m94J05_hasDerivAt_reciprocal_comp {U : ℝ → ℝ} {U' t : ℝ}
    (hU : HasDerivAt U U' (1 / t)) (ht : t ≠ 0) :
    HasDerivAt (fun y => U (1 / y)) (-U' / t ^ 2) t := by
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / t ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht using 1 <;>
      simp only [id_eq] <;> field_simp <;> ring
  convert hU.comp t hinv using 1 <;> ring

lemma m94J05_deriv_reciprocal_comp {U : ℝ → ℝ} {t : ℝ}
    (hU : DifferentiableAt ℝ U (1 / t)) (ht : t ≠ 0) :
    deriv (fun y => U (1 / y)) t = -(deriv U (1 / t)) / t ^ 2 := by
  exact (m94J05_hasDerivAt_reciprocal_comp hU.hasDerivAt ht).deriv

lemma m94J05_reciprocal_comp_deriv_hasDerivAt {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (deriv (fun y => U (1 / y)))
      (iteratedDeriv 2 U (1 / t) / t ^ 4 +
        2 * deriv U (1 / t) / t ^ 3) t := by
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdUcd : ContDiff ℝ 1 (deriv U) := by
    have hc := (contDiff_succ_iff_deriv (n := (1 : WithTop ℕ∞))).1
      (show ContDiff ℝ ((1 : WithTop ℕ∞) + 1) U by simpa using hU)
    exact hc.2.2
  have hdUd : Differentiable ℝ (deriv U) := hdUcd.differentiable (by norm_num)
  have hA := m94J05_hasDerivAt_reciprocal_comp
    (hdUd (1 / t)).hasDerivAt ht
  have hE : HasDerivAt
      (fun y => -(deriv U (1 / y)) / y ^ 2)
      (iteratedDeriv 2 U (1 / t) / t ^ 4 +
        2 * deriv U (1 / t) / t ^ 3) t := by
    have hraw := hA.neg.div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht)
    convert hraw using 1
    · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]
      simp only [Pi.neg_apply]
      field_simp
      ring
  have heq : deriv (fun y => U (1 / y)) =ᶠ[nhds t]
      (fun y => -(deriv U (1 / y)) / y ^ 2) := by
    filter_upwards [eventually_ne_nhds ht] with y hy
    exact m94J05_deriv_reciprocal_comp (hUd (1 / y)) hy
  exact hE.congr_of_eventuallyEq heq

lemma m94J05_reciprocal_cancellation {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) {t : ℝ} (ht : t ≠ 0) :
    t ^ 2 * iteratedDeriv 2 (fun y => U (1 / y)) t +
        2 * t * deriv (fun y => U (1 / y)) t =
      iteratedDeriv 2 U (1 / t) / t ^ 2 := by
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  have h1 := m94J05_deriv_reciprocal_comp (hUd (1 / t)) ht
  have h2 := (m94J05_reciprocal_comp_deriv_hasDerivAt hU ht).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, h2, h1]
  field_simp
  ring

lemma m94J05_reciprocal_comp_deriv_hasDerivAt_local {U : ℝ → ℝ} {t : ℝ}
    (hU : ContDiffAt ℝ 2 U (1 / t)) (ht : t ≠ 0) :
    HasDerivAt (deriv (fun y => U (1 / y)))
      (iteratedDeriv 2 U (1 / t) / t ^ 4 +
        2 * deriv U (1 / t) / t ^ 3) t := by
  have hUd : DifferentiableAt ℝ U (1 / t) := hU.differentiableAt (by norm_num)
  have hdU : ContDiffAt ℝ 1 (deriv U) (1 / t) :=
    hU.derivWithin (m := (1 : WithTop ℕ∞)) (by norm_num)
  have hA := m94J05_hasDerivAt_reciprocal_comp
    (hdU.differentiableAt (by norm_num)).hasDerivAt ht
  have hE : HasDerivAt
      (fun y => -(deriv U (1 / y)) / y ^ 2)
      (iteratedDeriv 2 U (1 / t) / t ^ 4 +
        2 * deriv U (1 / t) / t ^ 3) t := by
    have hraw := hA.neg.div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht)
    convert hraw using 1
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hinvcont : ContinuousAt (fun y : ℝ => 1 / y) t :=
    continuousAt_const.div continuousAt_id ht
  have hnear : ∀ᶠ y in nhds t, ContDiffAt ℝ 2 U (1 / y) :=
    hinvcont.tendsto (hU.eventually (by norm_num))
  have heq : deriv (fun y => U (1 / y)) =ᶠ[nhds t]
      (fun y => -(deriv U (1 / y)) / y ^ 2) := by
    filter_upwards [eventually_ne_nhds ht, hnear] with y hy hUy
    exact m94J05_deriv_reciprocal_comp
      (hUy.differentiableAt (by norm_num)) hy
  exact hE.congr_of_eventuallyEq heq

lemma m94J05_reciprocal_cancellation_local {U : ℝ → ℝ} {t : ℝ}
    (hU : ContDiffAt ℝ 2 U (1 / t)) (ht : t ≠ 0) :
    t ^ 2 * iteratedDeriv 2 (fun y => U (1 / y)) t +
        2 * t * deriv (fun y => U (1 / y)) t =
      iteratedDeriv 2 U (1 / t) / t ^ 2 := by
  have h1 := m94J05_deriv_reciprocal_comp
    (hU.differentiableAt (by norm_num)) ht
  have h2 := (m94J05_reciprocal_comp_deriv_hasDerivAt_local hU ht).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, h2, h1]
  field_simp
  ring

lemma m94J05_exists_small_solution (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1) :
    ∃ x : ℝ → ℝ, IsM94J05Solution f x ∧
      ∀ t ∈ Icc (1 : ℝ) 2, |x t| ≤ (1 / 2 : ℝ) := by
  obtain ⟨u, U, hunorm, hU, hUu, hUhalf, hUone, hUtwo⟩ :=
    m94J05_exists_regular_transformed_solution f hfcont hf
  let x : ℝ → ℝ := fun t => U (1 / t)
  have hinv : ContDiffOn ℝ 2 (fun t : ℝ => 1 / t) (Icc (1 : ℝ) 2) := by
    apply ContDiffOn.div contDiffOn_const contDiffOn_id
    intro t ht hzero
    change t = 0 at hzero
    linarith [ht.1]
  have hxcd : ContDiffOn ℝ 2 x (Icc (1 : ℝ) 2) := by
    simpa [x, Function.comp_def] using
      hU.contDiffOn.comp hinv (mapsTo_univ (fun t : ℝ => 1 / t) _)
  refine ⟨x, ⟨hxcd, ?_, ?_, ?_⟩, ?_⟩
  · simpa [x] using hUone
  · norm_num [x]
    exact hUhalf
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hq : 1 / t ∈ Icc (1 / 2 : ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ (by linarith [ht.1])).2
        linarith [ht.2]
      · exact (div_le_one (by linarith [ht.1])).2 ht.1
    rw [m94J05_reciprocal_cancellation hU ht0, hUtwo,
      m94J05Continuous.extend_apply _ hq]
    change m94J05_transformedInput f u (1 / t) / t ^ 2 =
      f t + (x t) ^ 2
    rw [m94J05_transformedInput]
    rw [m94J05Continuous.extend_apply u hq, ← hUu (1 / t) hq]
    dsimp [x]
    field_simp
  · intro t ht
    have hq : 1 / t ∈ Icc (1 / 2 : ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ (by linarith [ht.1])).2
        linarith [ht.2]
      · exact (div_le_one (by linarith [ht.1])).2 ht.1
    rw [show x t = u ⟨1 / t, hq⟩ by exact hUu (1 / t) hq]
    exact (u.norm_coe_le_norm ⟨1 / t, hq⟩).trans hunorm

lemma m94J05_eq_zero_of_second_deriv_zero {w : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hw : ContDiffOn ℝ 2 w (Icc a b))
    (hwa : w a = 0) (hwb : w b = 0)
    (hsecond : ∀ x ∈ Ioo a b, iteratedDeriv 2 w x = 0) :
    ∀ x ∈ Icc a b, w x = 0 := by
  have hwopen : ContDiffOn ℝ 2 w (Ioo a b) :=
    hw.mono Ioo_subset_Icc_self
  have hdcd : ContDiffOn ℝ 1 (deriv w) (Ioo a b) :=
    hwopen.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hddiff : DifferentiableOn ℝ (deriv w) (Ioo a b) :=
    hdcd.differentiableOn (by norm_num)
  have hddzero : (Ioo a b).EqOn (deriv (deriv w)) 0 := by
    intro x hx
    have hx2 := hsecond x hx
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one] at hx2
    exact hx2
  obtain ⟨c, hc, hczero⟩ := exists_deriv_eq_zero hab hw.continuousOn (hwa.trans hwb.symm)
  have hd_zero : (Ioo a b).EqOn (deriv w) 0 := by
    intro x hx
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hddiff
      hddzero hx hc).trans hczero
  let S := Icc a b
  have hSuniq : UniqueDiffOn ℝ S := uniqueDiffOn_Icc hab
  have hdcont : ContinuousOn (derivWithin w S) S :=
    hw.continuousOn_derivWithin hSuniq (by norm_num)
  have hdWithin_zero_open : (Ioo a b).EqOn (derivWithin w S) 0 := by
    intro x hx
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    exact hd_zero hx
  have hdWithin_zero : S.EqOn (derivWithin w S) 0 := by
    apply hdWithin_zero_open.of_subset_closure hdcont continuousOn_const
      Ioo_subset_Icc_self
    intro x hx
    rw [closure_Ioo hab.ne]
    exact hx
  have hconst := constant_of_derivWithin_zero
    (hw.differentiableOn (by norm_num))
    (fun x hx => hdWithin_zero ⟨hx.1, hx.2.le⟩)
  intro x hx
  rw [hconst x hx, hwa]

lemma m94J05_green_representation {v : ℝ → ℝ} (h : m94J05Continuous)
    (hv : ContDiffOn ℝ 2 v (Icc (1 / 2 : ℝ) 1))
    (hvleft : v (1 / 2) = 0) (hvright : v 1 = 0)
    (hvsecond : ∀ q ∈ Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv 2 v q = h.extend q) :
    ∀ q ∈ Icc (1 / 2 : ℝ) 1,
      v q = -m94J05_greenOperator h.extend q := by
  let R : ℝ → ℝ := fun q => -m94J05_regularGreen h q
  let w : ℝ → ℝ := fun q => v q - R q
  have hRcd : ContDiff ℝ 2 R := by
    exact (m94J05_regularGreen_contDiff_two h).neg
  have hwcd : ContDiffOn ℝ 2 w (Icc (1 / 2 : ℝ) 1) := by
    exact hv.sub hRcd.contDiffOn
  have hRleft : R (1 / 2) = 0 := by
    simp [R, m94J05_regularGreen]
  have hRright : R 1 = 0 := by
    dsimp [R]
    rw [m94J05_regularGreen_eq_greenOperator h (by norm_num)]
    simp [m94J05_greenOperator_right]
  have hwsecond : ∀ q ∈ Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv 2 w q = 0 := by
    intro q hq
    have hvAt : ContDiffAt ℝ 2 v q :=
      (hv q ⟨hq.1.le, hq.2.le⟩).contDiffAt (Icc_mem_nhds hq.1 hq.2)
    dsimp [w]
    change iteratedDeriv 2 (v - R) q = 0
    rw [iteratedDeriv_sub hvAt hRcd.contDiffAt,
      hvsecond q hq]
    have hRtwo : iteratedDeriv 2 R q = h.extend q := by
      dsimp [R]
      rw [iteratedDeriv_fun_neg,
        m94J05_regularGreen_iteratedDeriv_two_eq]
      ring
    rw [hRtwo]
    ring
  have hwzero := m94J05_eq_zero_of_second_deriv_zero
    (by norm_num : (1 / 2 : ℝ) < 1) hwcd
    (by dsimp [w]; rw [hvleft, hRleft]; ring)
    (by dsimp [w]; rw [hvright, hRright]; ring) hwsecond
  intro q hq
  have hz := hwzero q hq
  dsimp [w, R] at hz
  rw [m94J05_regularGreen_eq_greenOperator h hq] at hz
  linarith

lemma m94J05_competing_fixedPoint {f z : ℝ → ℝ}
    (hfcont : ContinuousOn f (Icc (1 : ℝ) 2))
    (hz : IsM94J05Solution f z)
    (hzbound : ∀ t ∈ Icc (1 : ℝ) 2, |z t| ≤ (1 / 2 : ℝ)) :
    ∃ v : m94J05Continuous, ‖v‖ ≤ (1 / 2 : ℝ) ∧
      m94J05_selfMap f hfcont v = v ∧
      ∀ q : Icc (1 / 2 : ℝ) 1, v q = z (1 / q) := by
  let v : m94J05Continuous :=
    ⟨fun q => z (1 / q), by
      apply hz.1.continuousOn.comp_continuous
        (continuous_const.div continuous_subtype_val (fun q => by
          have : (q : ℝ) ≠ 0 := by linarith [q.2.1]
          exact this))
      intro q
      exact m94J05_inv_mem_Icc q.2⟩
  have hvnorm : ‖v‖ ≤ (1 / 2 : ℝ) := by
    apply (ContinuousMap.norm_le (f := v) (by norm_num)).2
    intro q
    exact hzbound _ (m94J05_inv_mem_Icc q.2)
  have hvcd : ContDiffOn ℝ 2 (fun q : ℝ => z (1 / q))
      (Icc (1 / 2 : ℝ) 1) := by
    have hinv : ContDiffOn ℝ 2 (fun q : ℝ => 1 / q)
        (Icc (1 / 2 : ℝ) 1) := by
      apply ContDiffOn.div contDiffOn_const contDiffOn_id
      intro q hq hzero
      change q = 0 at hzero
      linarith [hq.1]
    exact hz.1.comp hinv (fun q hq => m94J05_inv_mem_Icc hq)
  let h := m94J05_transformedInputCM f hfcont v
  have hvsecond : ∀ q ∈ Ioo (1 / 2 : ℝ) 1,
      iteratedDeriv 2 (fun y : ℝ => z (1 / y)) q = h.extend q := by
    intro q hq
    have hq0 : q ≠ 0 := by linarith [hq.1]
    have ht : 1 / q ∈ Ioo (1 : ℝ) 2 := by
      constructor
      · exact (one_lt_div (by linarith [hq.1])).2 hq.2
      · exact (div_lt_iff₀ (by linarith [hq.1])).2 (by linarith [hq.1])
    have hzAt : ContDiffAt ℝ 2 z (1 / q) :=
      (hz.1 (1 / q) ⟨ht.1.le, ht.2.le⟩).contDiffAt
        (Icc_mem_nhds ht.1 ht.2)
    have hc := m94J05_reciprocal_cancellation_local hzAt hq0
    have hd := m94J05_deriv_reciprocal_comp
      (hzAt.differentiableAt (by norm_num)) hq0
    have hode := hz.2.2.2 (1 / q) ⟨ht.1.le, ht.2.le⟩
    rw [m94J05Continuous.extend_apply h ⟨hq.1.le, hq.2.le⟩]
    change iteratedDeriv 2 (fun y : ℝ => z (1 / y)) q =
      m94J05_transformedInput f v q
    rw [m94J05_transformedInput,
      m94J05Continuous.extend_apply _ ⟨hq.1.le, hq.2.le⟩]
    dsimp [v]
    field_simp at hc hd hode ⊢
    ring_nf at hc hd hode ⊢
    have hdmul := congrArg (fun r : ℝ => q * r) hd
    ring_nf at hdmul
    have hq2pos : 0 < q ^ 2 := sq_pos_of_ne_zero hq0
    nlinarith [sq_nonneg (q ^ 2)]
  have hvleft : (fun q : ℝ => z (1 / q)) (1 / 2) = 0 := by
    norm_num
    exact hz.2.2.1
  have hvright : (fun q : ℝ => z (1 / q)) 1 = 0 := by
    norm_num
    exact hz.2.1
  have hrepr := m94J05_green_representation h hvcd hvleft hvright hvsecond
  have hvfix : m94J05_selfMap f hfcont v = v := by
    ext q
    change -m94J05_greenOperator (m94J05_transformedInput f v) q = z (1 / q)
    calc
      -m94J05_greenOperator (m94J05_transformedInput f v) q =
          -m94J05_greenOperator h.extend q := by
        congr 1
        unfold m94J05_greenOperator
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hy
        change m94J05_green q y * m94J05_transformedInput f v y =
          m94J05_green q y * h.extend y
        rw [m94J05Continuous.extend_apply h hy]
        rfl
      _ = z (1 / q) := (hrepr q q.2).symm
  exact ⟨v, hvnorm, hvfix, fun q => rfl⟩

theorem apm_m94j05 :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ f : ℝ → ℝ,
        ContinuousOn f (Icc 1 2) →
        (∀ t ∈ Icc (1 : ℝ) 2, |f t| < ε) →
        ∃ x : ℝ → ℝ,
          IsM94J05Solution f x ∧
          (∀ t ∈ Icc (1 : ℝ) 2, |x t| ≤ r) ∧
          ∀ z : ℝ → ℝ,
            IsM94J05Solution f z →
            (∀ t ∈ Icc (1 : ℝ) 2, |z t| ≤ r) →
            EqOn z x (Icc 1 2) := by
  refine ⟨1, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro f hfcont hfstrict
  have hf : ∀ t ∈ Icc (1 : ℝ) 2, |f t| ≤ 1 := by
    intro t ht
    exact (hfstrict t ht).le
  obtain ⟨x, hxsol, hxbound⟩ := m94J05_exists_small_solution f hfcont hf
  refine ⟨x, hxsol, hxbound, ?_⟩
  intro z hzsol hzbound
  obtain ⟨v, hvnorm, hvfix, hvapply⟩ :=
    m94J05_competing_fixedPoint hfcont hzsol hzbound
  obtain ⟨u, hunorm, hufix, huapply⟩ :=
    m94J05_competing_fixedPoint hfcont hxsol hxbound
  have hcontract := m94J05_selfMap_sub_norm_le hfcont
    (r := (1 / 2 : ℝ)) (by norm_num) hvnorm hunorm
  rw [hvfix, hufix] at hcontract
  have hvueq : v = u := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hn : 0 ≤ ‖v - u‖ := norm_nonneg _
    norm_num at hcontract
    linarith
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hq : 1 / t ∈ Icc (1 / 2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ (by linarith [ht.1])).2
      linarith [ht.2]
    · exact (div_le_one (by linarith [ht.1])).2 ht.1
  have hv := hvapply ⟨1 / t, hq⟩
  have hu := huapply ⟨1 / t, hq⟩
  rw [hvueq] at hv
  have hinv : 1 / (1 / t) = t := by field_simp
  rw [hinv] at hv hu
  exact hv.symm.trans hu

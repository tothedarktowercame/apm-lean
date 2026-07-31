/-
! # APM a96A02: Hölder-1/2 continuous but not absolutely continuous piecewise linear function

f is piecewise linear on [0,1] with f(0)=0, f(1/n)=0, f(midpoint_n)=1/n.
(a) |f(x)-f(y)| ≤ A|x-y|^{1/2} (Hölder-1/2).
(b) f is not absolutely continuous.

## Proof strategy

(a) Within spike n: slope = 2(n+1), height = 1/n.
    |f(x)-f(y)|² ≤ height · slope · |x-y| = (1/n)(2(n+1))|x-y| ≤ 4|x-y|.
(b) Intervals [1/(n+1), m_n] for n=N,...,2N: total length → 0, total oscillation ≥ log(2)/2.

## Formalization

The infinitely many pieces are selected canonically by `⌊1/x⌋₊`.  At the
shared endpoint `1/(n+1)` this selects spike `n+1`; its right-ramp value is
zero, agreeing with spike `n`'s left-ramp value.

## Statement repair

The generated `spikeFunction` had a sorry in its definition and was later
hidden behind `SpikeFunctionSpec`.  The present file closes that gap with
the reciprocal-floor construction and proves that it satisfies the spec.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Real

open scoped ENNReal

noncomputable section

/-- The midpoint of the interval `[1/(n+1), 1/n]`. -/
def spikeMidpoint (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1))

/-- The index of the reciprocal interval containing a positive `x`. -/
def spikeIndex (x : ℝ) : ℕ :=
  ⌊1 / x⌋₊

/-- The triangular spike function.  On `0 < x ≤ 1`, the reciprocal floor
selects the interval `[1/(n+1), 1/n]`; outside `[0,1]` the function is zero.
At a shared endpoint `1/(n+1)`, the floor selects spike `n+1`, whose right
endpoint value is zero, agreeing with spike `n`'s left endpoint. -/
noncomputable def spikeFunction (x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ 1 then
    let n := spikeIndex x
    if x < spikeMidpoint n then
      2 * ((n : ℝ) + 1) * (x - 1 / ((n : ℝ) + 1))
    else
      2 * ((n : ℝ) + 1) * (1 / (n : ℝ) - x)
  else
    0

/-- Exact specification of the triangular spikes from the informal problem.

On spike `n`, the function rises linearly from zero to height `1/n` and then
falls linearly back to zero. -/
structure SpikeFunctionSpec (f : ℝ → ℝ) : Prop where
  at_zero : f 0 = 0
  on_left (n : ℕ) (hn : 0 < n) (x : ℝ)
      (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (spikeMidpoint n)) :
      f x = 2 * ((n : ℝ) + 1) * (x - 1 / ((n : ℝ) + 1))
  on_right (n : ℕ) (hn : 0 < n) (x : ℝ)
      (hx : x ∈ Icc (spikeMidpoint n) (1 / (n : ℝ))) :
      f x = 2 * ((n : ℝ) + 1) * (1 / (n : ℝ) - x)

/-- Within spike n: height × slope = (1/n) · 2(n+1) ≤ 4 for n ≥ 1.

This is the key bound: height × slope ≤ 4 ensures |f(x)-f(y)|² ≤ 4|x-y|
within a single spike, giving the Hölder-1/2 bound with constant A = 2.

Proof: (1/n) · 2(n+1) = 2(1 + 1/n) ≤ 2(1 + 1) = 4 for n ≥ 1. -/
lemma spike_height_slope_bound (n : ℕ) (hn : 0 < n) :
    (1 / (↑n : ℝ)) * (2 * (↑n + 1)) ≤ 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hn0).2
  nlinarith

/-- The base of spike n: |1/n - 1/(n+1)| = 1/(n(n+1)). -/
lemma spike_base_length (n : ℕ) (hn : 0 < n) :
    1 / ↑n - 1 / (↑n + 1 : ℝ) = 1 / (↑n * (↑n + 1)) := by
  field_simp
  ring

private lemma spikeMidpoint_mem (n : ℕ) (hn : 0 < n) :
    spikeMidpoint n ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have horder : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn0 (by linarith)
  have hmid :
      spikeMidpoint n =
        (1 / ((n : ℝ) + 1) + 1 / (n : ℝ)) / 2 := by
    dsimp [spikeMidpoint]
    field_simp [ne_of_gt hn0]
    ring
  rw [hmid]
  constructor <;> linarith

private lemma spikeIndex_eq_of_mem_of_ne_left (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))
    (hne : x ≠ 1 / ((n : ℝ) + 1)) :
    spikeIndex x = n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
  have hleft : 1 / ((n : ℝ) + 1) < x :=
    lt_of_le_of_ne hx.1 (Ne.symm hne)
  apply (Nat.floor_eq_iff (by positivity : 0 ≤ 1 / x)).2
  constructor
  · apply (le_div_iff₀ hx0).2
    have h := (le_div_iff₀ hn0).1 hx.2
    nlinarith
  · apply (div_lt_iff₀ hx0).2
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).1 hleft
    nlinarith

private lemma spikeIndex_at_left (n : ℕ) (hn : 0 < n) :
    spikeIndex (1 / ((n : ℝ) + 1)) = n + 1 := by
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  have hrecip : 1 / (1 / ((n : ℝ) + 1)) = (n : ℝ) + 1 := by
    field_simp
  rw [spikeIndex, hrecip, ← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]

private lemma spikeFunction_at_left (n : ℕ) (hn : 0 < n) :
    spikeFunction (1 / ((n : ℝ) + 1)) = 0 := by
  have hx0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hx1 : (1 / ((n : ℝ) + 1) : ℝ) ≤ 1 := by
    calc
      1 / ((n : ℝ) + 1) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num) (by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          linarith)
      _ = 1 := by norm_num
  have hk : spikeIndex (1 / ((n : ℝ) + 1)) = n + 1 := spikeIndex_at_left n hn
  have hmid := (spikeMidpoint_mem (n + 1) (by omega)).2
  rw [spikeFunction, if_pos ⟨hx0, hx1⟩]
  dsimp only
  rw [hk]
  have hcast : (1 / ((n : ℝ) + 1) : ℝ) = 1 / ((n + 1 : ℕ) : ℝ) := by
    norm_num
  rw [hcast, if_neg (not_lt_of_ge hmid)]
  push_cast
  ring

/-- The concrete reciprocal-floor construction realizes every triangular
spike in `SpikeFunctionSpec`; in particular, all shared endpoints are
consistent. -/
theorem spikeFunction_spec : SpikeFunctionSpec spikeFunction := by
  constructor
  · simp [spikeFunction]
  · intro n hn x hx
    by_cases hleft : x = 1 / ((n : ℝ) + 1)
    · subst x
      rw [spikeFunction_at_left n hn]
      ring
    · have hk := spikeIndex_eq_of_mem_of_ne_left n hn x
        ⟨hx.1, hx.2.trans (spikeMidpoint_mem n hn).2⟩ hleft
      have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
      have hx1 : x ≤ 1 := hx.2.trans (spikeMidpoint_mem n hn).2 |>.trans <| by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn'
      by_cases hxm : x < spikeMidpoint n
      · rw [spikeFunction, if_pos ⟨hx0, hx1⟩]
        dsimp only
        rw [hk, if_pos hxm]
      · rw [spikeFunction, if_pos ⟨hx0, hx1⟩]
        dsimp only
        rw [hk, if_neg hxm]
        have hxeq : x = spikeMidpoint n := le_antisymm hx.2 (le_of_not_gt hxm)
        rw [hxeq]
        dsimp [spikeMidpoint]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        field_simp [ne_of_gt hn0]
        ring
  · intro n hn x hx
    by_cases hleft : x = 1 / ((n : ℝ) + 1)
    · subst x
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hstrict : 1 / ((n : ℝ) + 1) < spikeMidpoint n := by
        dsimp [spikeMidpoint]
        field_simp [ne_of_gt hn0]
        nlinarith
      exact (not_lt_of_ge hx.1 hstrict).elim
    · have hk := spikeIndex_eq_of_mem_of_ne_left n hn x
        ⟨(spikeMidpoint_mem n hn).1.trans hx.1, hx.2⟩ hleft
      have hx0 : 0 < x :=
        lt_of_lt_of_le (by positivity) ((spikeMidpoint_mem n hn).1.trans hx.1)
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hx1 : x ≤ 1 := hx.2.trans <| by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn'
      rw [spikeFunction, if_pos ⟨hx0, hx1⟩]
      dsimp only
      rw [hk, if_neg (not_lt_of_ge hx.1)]

private lemma SpikeFunctionSpec.at_inv_nat {f : ℝ → ℝ}
    (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) :
    f (1 / (n : ℝ)) = 0 := by
  rw [hf.on_right n hn]
  · ring
  · exact ⟨(spikeMidpoint_mem n hn).2, le_rfl⟩

private lemma SpikeFunctionSpec.at_midpoint {f : ℝ → ℝ}
    (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) :
    f (spikeMidpoint n) = 1 / (n : ℝ) := by
  rw [hf.on_left n hn _ ⟨(spikeMidpoint_mem n hn).1, le_rfl⟩]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [spikeMidpoint]
  field_simp
  ring

private lemma exists_spike (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ 1 / ((n : ℝ) + 1) < x ∧ x ≤ 1 / (n : ℝ) := by
  let n : ℕ := ⌊1 / x⌋₊
  have hrecip_nonneg : 0 ≤ 1 / x := by positivity
  have hone : (1 : ℝ) ≤ 1 / x := by
    apply (le_div_iff₀ hx0).2
    simpa using hx1
  have hn : 0 < n := Nat.floor_pos.mpr hone
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_le : (n : ℝ) ≤ 1 / x := Nat.floor_le hrecip_nonneg
  have hlt : 1 / x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨n, hn, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
    have := (div_lt_iff₀ hx0).1 hlt
    nlinarith
  · apply (le_div_iff₀ hn0).2
    have := (le_div_iff₀ hx0).1 hn_le
    nlinarith

private lemma spike_value_bounds {f : ℝ → ℝ} (hf : SpikeFunctionSpec f)
    (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    0 ≤ f x ∧ f x ≤ 1 / (n : ℝ) := by
  have hs : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
  by_cases hxm : x ≤ spikeMidpoint n
  · rw [hf.on_left n hn x ⟨hx.1, hxm⟩]
    constructor
    · exact mul_nonneg hs (sub_nonneg.mpr hx.1)
    · calc
        2 * ((n : ℝ) + 1) * (x - 1 / ((n : ℝ) + 1)) ≤
            2 * ((n : ℝ) + 1) *
              (spikeMidpoint n - 1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_right hxm _) hs
        _ = f (spikeMidpoint n) :=
          (hf.on_left n hn _ ⟨(spikeMidpoint_mem n hn).1, le_rfl⟩).symm
        _ = 1 / (n : ℝ) := hf.at_midpoint n hn
  · have hmx : spikeMidpoint n ≤ x := le_of_not_ge hxm
    rw [hf.on_right n hn x ⟨hmx, hx.2⟩]
    constructor
    · exact mul_nonneg hs (sub_nonneg.mpr hx.2)
    · calc
        2 * ((n : ℝ) + 1) * (1 / (n : ℝ) - x) ≤
            2 * ((n : ℝ) + 1) *
              (1 / (n : ℝ) - spikeMidpoint n) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left hmx _) hs
        _ = f (spikeMidpoint n) :=
          (hf.on_right n hn _ ⟨le_rfl, (spikeMidpoint_mem n hn).2⟩).symm
        _ = 1 / (n : ℝ) := hf.at_midpoint n hn

private lemma spike_lipschitz {f : ℝ → ℝ} (hf : SpikeFunctionSpec f)
    (n : ℕ) (hn : 0 < n) {x y : ℝ}
    (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))
    (hy : y ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    |f x - f y| ≤ 2 * ((n : ℝ) + 1) * |x - y| := by
  have hs : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm x y]
    simpa [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  by_cases hym : y ≤ spikeMidpoint n
  · have hv :
        2 * ((n : ℝ) + 1) * (x - 1 / ((n : ℝ) + 1)) ≤
          2 * ((n : ℝ) + 1) * (y - 1 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hxy _) hs
    rw [hf.on_left n hn x ⟨hx.1, hxy.trans hym⟩,
      hf.on_left n hn y ⟨hy.1, hym⟩,
      abs_of_nonpos (sub_nonpos.mpr hv),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring_nf
    exact le_rfl
  by_cases hmx : spikeMidpoint n ≤ x
  · have hv :
        2 * ((n : ℝ) + 1) * (1 / (n : ℝ) - y) ≤
          2 * ((n : ℝ) + 1) * (1 / (n : ℝ) - x) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hxy _) hs
    rw [hf.on_right n hn x ⟨hmx, hx.2⟩,
      hf.on_right n hn y ⟨hmx.trans hxy, hy.2⟩,
      abs_of_nonneg (sub_nonneg.mpr hv),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring_nf
    exact le_rfl
  · have hxm : x ≤ spikeMidpoint n := le_of_not_ge hmx
    have hmy : spikeMidpoint n ≤ y := le_of_not_ge hym
    rw [hf.on_left n hn x ⟨hx.1, hxm⟩,
      hf.on_right n hn y ⟨hmy, hy.2⟩,
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    apply (abs_le).2
    have hmid :
        2 * spikeMidpoint n =
          1 / ((n : ℝ) + 1) + 1 / (n : ℝ) := by
      have hm := spikeMidpoint_mem n hn
      dsimp [spikeMidpoint]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [ne_of_gt hn0]
      ring
    constructor <;> nlinarith

private lemma holder_within_spike {f : ℝ → ℝ} (hf : SpikeFunctionSpec f)
    (n : ℕ) (hn : 0 < n) {x y : ℝ}
    (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)))
    (hy : y ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    |f x - f y| ^ 2 ≤ 4 * |x - y| := by
  let z := |f x - f y|
  have hz0 : 0 ≤ z := abs_nonneg _
  have hheight : z ≤ 1 / (n : ℝ) := by
    have hxv := spike_value_bounds hf n hn hx
    have hyv := spike_value_bounds hf n hn hy
    apply (abs_le).2
    constructor <;> linarith
  have hlip : z ≤ 2 * ((n : ℝ) + 1) * |x - y| :=
    spike_lipschitz hf n hn hx hy
  calc
    z ^ 2 = z * z := pow_two z
    _ ≤ (1 / (n : ℝ)) *
        (2 * ((n : ℝ) + 1) * |x - y|) :=
      mul_le_mul hheight hlip hz0 (by positivity)
    _ = ((1 / (n : ℝ)) * (2 * ((n : ℝ) + 1))) * |x - y| := by ring
    _ ≤ 4 * |x - y| :=
      mul_le_mul_of_nonneg_right (spike_height_slope_bound n hn) (abs_nonneg _)

private lemma holder_from_sq {z d : ℝ} (hz : 0 ≤ z) (_hd : 0 ≤ d)
    (h : z ^ 2 ≤ 4 * d) :
    z ≤ 2 * d ^ ((1 : ℝ) / 2) := by
  rw [← Real.sqrt_eq_rpow]
  calc
    z = √(z ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hz]
    _ ≤ √(4 * d) := Real.sqrt_le_sqrt h
    _ = 2 * √d := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show √(4 : ℝ) = 2 by
        exact (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2
          (by norm_num)]

private lemma holder_to_left {f : ℝ → ℝ} (hf : SpikeFunctionSpec f)
    (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    |f x| ≤ 2 * (x - 1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 2) := by
  have hzero : f (1 / ((n : ℝ) + 1)) = 0 := by
    simpa using hf.on_left n hn _ ⟨le_rfl, (spikeMidpoint_mem n hn).1⟩
  have hsq := holder_within_spike hf n hn hx
    (show 1 / ((n : ℝ) + 1) ∈
      Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) from
        ⟨le_rfl, (spikeMidpoint_mem n hn).1.trans
          (spikeMidpoint_mem n hn).2⟩)
  rw [hzero, sub_zero, abs_of_nonneg (sub_nonneg.mpr hx.1)] at hsq
  exact holder_from_sq (abs_nonneg _) (sub_nonneg.mpr hx.1) hsq

private lemma holder_to_right {f : ℝ → ℝ} (hf : SpikeFunctionSpec f)
    (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    |f x| ≤ 2 * (1 / (n : ℝ) - x) ^ ((1 : ℝ) / 2) := by
  have hzero := hf.at_inv_nat n hn
  have hsq := holder_within_spike hf n hn hx
    (show 1 / (n : ℝ) ∈
      Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) from
        ⟨(spikeMidpoint_mem n hn).1.trans
          (spikeMidpoint_mem n hn).2, le_rfl⟩)
  rw [hzero, sub_zero, abs_of_nonpos (sub_nonpos.mpr hx.2)] at hsq
  exact holder_from_sq (abs_nonneg _) (sub_nonneg.mpr hx.2)
    (by simpa only [neg_sub] using hsq)
/-- Hölder-1/2 bound: |f(x)-f(y)| ≤ 2|x-y|^{1/2}.

**Blocker:** Requires the full spike function definition and the
within-spike bound |f(x)-f(y)|² ≤ 4|x-y|, plus the cross-spike
argument using f = 0 at junction points. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require the exact
-- triangular-spike specification so this is no longer a theorem about a
-- constant-zero placeholder.
theorem spikeFunction_holderWith :
    SpikeFunctionSpec spikeFunction →
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |spikeFunction x - spikeFunction y| ≤ A * |x - y| ^ ((1:ℝ) / 2) := by
  intro hf
  refine ⟨4, by norm_num, ?_⟩
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using
      this y hy x hx (le_of_not_ge hxy)
  have hd : 0 ≤ y - x := sub_nonneg.mpr hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  simp only [neg_sub]
  by_cases hx0 : x = 0
  · subst x
    by_cases hy0 : y = 0
    · subst y
      simp
    · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
      obtain ⟨n, hn, hynl, hynr⟩ := exists_spike y hypos hy.2
      have hyn : y ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) :=
        ⟨hynl.le, hynr⟩
      rw [hf.at_zero, zero_sub, abs_neg]
      have hleft := holder_to_left hf n hn hyn
      have hdist :
          y - 1 / ((n : ℝ) + 1) ≤ y - 0 := by
        have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hrpow := Real.rpow_le_rpow
        (sub_nonneg.mpr hynl.le) hdist (by norm_num : (0 : ℝ) ≤ 1 / 2)
      calc
        |spikeFunction y| ≤
            2 * (y - 1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 2) := hleft
        _ ≤ 2 * (y - 0) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hrpow (by norm_num)
        _ ≤ 4 * (y - 0) ^ ((1 : ℝ) / 2) := by
          have := Real.rpow_nonneg (by positivity : 0 ≤ y - 0) ((1 : ℝ) / 2)
          nlinarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
    obtain ⟨nx, hnx, hxnl, hxnr⟩ := exists_spike x hxpos hx.2
    obtain ⟨ny, hny, hynl, hynr⟩ := exists_spike y hypos hy.2
    have hxs : x ∈ Icc (1 / ((nx : ℝ) + 1)) (1 / (nx : ℝ)) :=
      ⟨hxnl.le, hxnr⟩
    have hys : y ∈ Icc (1 / ((ny : ℝ) + 1)) (1 / (ny : ℝ)) :=
      ⟨hynl.le, hynr⟩
    by_cases hnxy : nx = ny
    · subst ny
      have hsquare := holder_within_spike hf nx hnx hxs hys
      have hlocal := holder_from_sq (abs_nonneg _) hd
        (by simpa [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hsquare)
      exact hlocal.trans (by
        have := Real.rpow_nonneg hd ((1 : ℝ) / 2)
        nlinarith)
    · have hny_lt : ny < nx := by
        have hny_le : ny ≤ nx := by
          by_contra hnot
          have hnx_lt : nx < ny := Nat.lt_of_not_ge hnot
          have hcast : (nx : ℝ) + 1 ≤ ny := by exact_mod_cast hnx_lt
          have hrecip :
              1 / (ny : ℝ) ≤ 1 / ((nx : ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) hcast
          linarith
        exact lt_of_le_of_ne hny_le (Ne.symm hnxy)
      have hgap_nat : ny + 1 ≤ nx := by omega
      have hgap :
          1 / (nx : ℝ) ≤ 1 / ((ny : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hgap_nat)
      have hxbound := holder_to_right hf nx hnx hxs
      have hybound := holder_to_left hf ny hny hys
      have hdx :
          1 / (nx : ℝ) - x ≤ y - x := by
        linarith
      have hdy :
          y - 1 / ((ny : ℝ) + 1) ≤ y - x := by
        linarith
      have hrx := Real.rpow_le_rpow
        (sub_nonneg.mpr hxnr) hdx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hry := Real.rpow_le_rpow
        (sub_nonneg.mpr hynl.le) hdy (by norm_num : (0 : ℝ) ≤ 1 / 2)
      calc
        |spikeFunction x - spikeFunction y| ≤
            |spikeFunction x| + |spikeFunction y| := abs_sub _ _
        _ ≤ 4 * (y - x) ^ ((1 : ℝ) / 2) := by nlinarith

/-- Not absolutely continuous on [0,1].

**Blocker:** Requires constructing the AC-violating collection of intervals. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require the exact
-- triangular-spike specification so the non-AC conclusion concerns the
-- intended function rather than the false constant-zero model.
theorem spikeFunction_not_absolutelyContinuous :
    SpikeFunctionSpec spikeFunction →
    ∃ ε > 0, ∀ δ > 0, ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i ∈ Icc 0 1) ∧ (∀ i, b i ∈ Icc 0 1) ∧
      (∀ i, a i ≤ b i) ∧
      (∀ i j, i < j → b i ≤ a j) ∧
      ∑ i, (b i - a i) < δ ∧
      ε ≤ ∑ i, |spikeFunction (b i) - spikeFunction (a i)| := by
  intro hf
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro δ hδ
  obtain ⟨N, hNδ⟩ := exists_nat_one_div_lt hδ
  let K := N + 1
  have hK : 0 < K := by omega
  have hKδ : 1 / (K : ℝ) < δ := by simpa [K] using hNδ
  let idx : Fin K → ℕ := fun i => 2 * K - i.1
  have hidx_lower (i : Fin K) : K < idx i := by
    dsimp [idx]
    omega
  have hidx_pos (i : Fin K) : 0 < idx i := lt_trans hK (hidx_lower i)
  let a : Fin K → ℝ := fun i => 1 / ((idx i : ℝ) + 1)
  let b : Fin K → ℝ := fun i => spikeMidpoint (idx i)
  refine ⟨K, a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := hidx_pos i
    have hi0 : (0 : ℝ) < idx i := by exact_mod_cast hi
    constructor
    · dsimp [a]
      positivity
    · dsimp [a]
      have hle :
          1 / ((idx i : ℝ) + 1) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by
          have : (1 : ℝ) ≤ idx i := by exact_mod_cast hi
          linarith)
      simpa using hle
  · intro i
    have hi := hidx_pos i
    have hm := spikeMidpoint_mem (idx i) hi
    constructor
    · exact le_trans (by positivity) hm.1
    · have hle : 1 / (idx i : ℝ) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hi)
      exact hm.2.trans (by simpa using hle)
  · intro i
    exact (spikeMidpoint_mem (idx i) (hidx_pos i)).1
  · intro i j hij
    have hkorder : idx j + 1 ≤ idx i := by
      dsimp [idx]
      omega
    have hpos : (0 : ℝ) < idx j + 1 := by positivity
    exact (spikeMidpoint_mem (idx i) (hidx_pos i)).2.trans
      (one_div_le_one_div_of_le hpos (by exact_mod_cast hkorder))
  · calc
      ∑ i, (b i - a i) ≤ ∑ _i : Fin K, 1 / (K : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hidx_lower i
        have hi0 : (0 : ℝ) < idx i := by exact_mod_cast hidx_pos i
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
        have hden :
            (K : ℝ) ^ 2 ≤ 2 * (idx i : ℝ) * ((idx i : ℝ) + 1) := by
          have hi' : (K : ℝ) < idx i := by exact_mod_cast hi
          nlinarith
        dsimp [a, b, spikeMidpoint]
        have hdiff :
            1 / (2 * (idx i : ℝ)) + 1 / (2 * ((idx i : ℝ) + 1)) -
                1 / ((idx i : ℝ) + 1) =
              1 / (2 * (idx i : ℝ) * ((idx i : ℝ) + 1)) := by
          field_simp [ne_of_gt hi0]
          ring
        rw [hdiff]
        exact one_div_le_one_div_of_le (sq_pos_of_pos hK0) hden
      _ = 1 / (K : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr hK.ne']
      _ < δ := hKδ
  · calc
      (1 : ℝ) / 2 = ∑ _i : Fin K, 1 / (2 * (K : ℝ)) := by
        simp [hK.ne']
      _ ≤ ∑ i, |spikeFunction (b i) - spikeFunction (a i)| := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hidx_pos i
        have hupper : idx i ≤ 2 * K := by
          dsimp [idx]
          omega
        have hpos : (0 : ℝ) < idx i := by exact_mod_cast hi
        have h2Kpos : (0 : ℝ) < 2 * K := by positivity
        have hrecip :
            1 / (2 * (K : ℝ)) ≤ 1 / (idx i : ℝ) := by
          apply one_div_le_one_div_of_le hpos
          exact_mod_cast hupper
        have ha0 : spikeFunction (a i) = 0 := by
          dsimp [a]
          simpa using hf.on_left (idx i) hi _ ⟨le_rfl,
            (spikeMidpoint_mem (idx i) hi).1⟩
        have hbval : spikeFunction (b i) = 1 / (idx i : ℝ) := by
          dsimp [b]
          exact hf.at_midpoint (idx i) hi
        rw [ha0, hbval, sub_zero, abs_of_pos (one_div_pos.mpr hpos)]
        exact hrecip

end

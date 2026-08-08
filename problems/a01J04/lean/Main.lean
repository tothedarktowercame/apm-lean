import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# APM a01J04 — decay of derivatives after subtracting a simple pole

The hypothesis explicitly pins the meromorphic function to its Laurent
principal part at `1`: `f(z) = λ/(z-1) + g(z)` with `g` entire and `λ ≠ 0`.
Thus `f` is analytic away from `1`, has a simple pole there, and has residue
`λ`.  The conclusion is the limit requested in the source.

## Statement repairs

None.

## Encoding questions

None. Complex modulus is written with the current norm notation, and the
neighbourhood filter is the explicit `Filter.nhds`.
-/

open Filter

lemma apm_a01J04_geom_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) 0 = (n.factorial : ℂ) := by
  have hcomp := congrFun
    (iteratedDeriv_comp_const_sub n (fun w : ℂ => w⁻¹) (1 : ℂ)) 0
  have hs : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hinv : iteratedDeriv n (fun w : ℂ => w⁻¹) 1 =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
    have hopen := (iteratedDerivWithin_of_isOpen (n := n)
      (f := fun w : ℂ => w⁻¹) hs) (show (1 : ℂ) ∈ {z : ℂ | z ≠ 0} by simp)
    have hformula :=
      (iteratedDerivWithin_one_div (k := n) (s := {z : ℂ | z ≠ 0}) hs)
        (show (1 : ℂ) ∈ {z : ℂ | z ≠ 0} by simp)
    rw [← hopen]
    simpa using hformula
  simp only [sub_zero, smul_eq_mul] at hcomp
  rw [hinv] at hcomp
  have hpow : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hpow, one_mul] at hcomp
  exact hcomp

lemma apm_a01J04_pole_iteratedDeriv (lam : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => lam / (z - 1)) 2 =
      lam * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) := by
  have hshift := congrFun (iteratedDeriv_comp_const_sub n
    (fun w : ℂ => (1 - w)⁻¹) (2 : ℂ)) 2
  simp only [sub_self, smul_eq_mul, apm_a01J04_geom_iteratedDeriv] at hshift
  have hfun : (fun z : ℂ => lam / (z - 1)) =
      fun z => lam * (1 - (2 - z))⁻¹ := by
    funext z
    congr 1
    ring_nf
  rw [hfun, iteratedDeriv_const_mul_field, hshift]

lemma apm_a01J04_entire_coeff_superexp
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => T ^ n *
      ‖iteratedDeriv n g 2 / (n.factorial : ℂ)‖) atTop (nhds 0) := by
  let R : ℝ := 2 * T
  have hR : 0 < R := mul_pos (by norm_num) hT
  have hcompact : IsCompact ((fun z : ℂ => ‖g z‖) '' Metric.sphere (2 : ℂ) R) :=
    (isCompact_sphere (2 : ℂ) R).image_of_continuousOn hg.continuous.norm.continuousOn
  obtain ⟨M, hM⟩ : ∃ M, ∀ a ∈ ((fun z : ℂ => ‖g z‖) '' Metric.sphere (2 : ℂ) R), a ≤ M :=
    hcompact.bddAbove
  have hC : ∀ z ∈ Metric.sphere (2 : ℂ) R, ‖g z‖ ≤ M :=
    fun z hz => hM _ ⟨z, hz, rfl⟩
  have hMn : 0 ≤ M := by
    have hz : (2 : ℂ) + R ∈ Metric.sphere (2 : ℂ) R := by
      simp [abs_of_pos hR]
    exact (norm_nonneg _).trans (hC _ hz)
  have h_est (n : ℕ) :
      T ^ n * ‖iteratedDeriv n g 2 / (n.factorial : ℂ)‖ ≤ M / 2 ^ n := by
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      n hR hg.diffContOnCl hC
    have hfact : (0 : ℝ) < n.factorial := by positivity
    have hcoeff : ‖iteratedDeriv n g 2 / (n.factorial : ℂ)‖ ≤ M / R ^ n := by
      rw [norm_div, norm_natCast, div_le_iff₀ hfact, mul_comm, ← mul_div_assoc]
      exact hcauchy
    calc
      _ ≤ T ^ n * (M / R ^ n) := mul_le_mul_of_nonneg_left hcoeff (pow_nonneg hT.le _)
      _ = M / 2 ^ n := by
        dsimp [R]
        field_simp
        ring
  have hlim : Tendsto (fun n : ℕ => M / (2 : ℝ) ^ n) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact squeeze_zero (fun n => mul_nonneg (pow_nonneg hT.le _) (norm_nonneg _)) h_est hlim

lemma apm_a01J04_error_eq_entire
    (f g : ℂ → ℂ) (lam : ℂ) (hg : Differentiable ℂ g)
    (hf : ∀ z : ℂ, f z = lam / (z - 1) + g z) (n : ℕ) :
    (-1 : ℂ) ^ n * iteratedDeriv n f 2 / (Nat.factorial n : ℂ) - lam =
      (-1 : ℂ) ^ n * (iteratedDeriv n g 2 / (Nat.factorial n : ℂ)) := by
  have hfun : f = fun z => lam / (z - 1) + g z := funext hf
  have hpole : ContDiffAt ℂ n (fun z : ℂ => lam / (z - 1)) 2 := by
    exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (by norm_num)
  have hg' : ContDiffAt ℂ n g 2 := hg.contDiff.contDiffAt
  rw [hfun, iteratedDeriv_fun_add hpole hg', apm_a01J04_pole_iteratedDeriv]
  have hfact : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  have hpow : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) - 1) * lam *
          (Nat.factorial n : ℂ) + (-1 : ℂ) ^ n * iteratedDeriv n g 2 := by ring
    _ = _ := by rw [hpow]; ring

theorem apm_a01j04
    (f g : ℂ → ℂ) (lam : ℂ)
    (hlam : lam ≠ 0)
    (hg : Differentiable ℂ g)
    (hf : ∀ z : ℂ, f z = lam / (z - 1) + g z) :
    ∀ T : ℝ, 0 < T →
      Tendsto
        (fun n : ℕ ↦
          T ^ n *
            ‖(-1 : ℂ) ^ n * iteratedDeriv n f 2 /
                (Nat.factorial n : ℂ) - lam‖)
        atTop (nhds 0) := by
  intro T hT
  have hlim := apm_a01J04_entire_coeff_superexp g hg T hT
  convert hlim using 1
  funext n
  rw [apm_a01J04_error_eq_entire f g lam hg hf n]
  simp

import Mathlib
noncomputable section
open Set

def apm_m95A03_energy (a b : ℝ) (p q f u : ℝ → ℝ) : ℝ :=
  ∫ t in a..b, p t * (deriv u t) ^ 2 + q t * (u t) ^ 2 + 2 * u t * f t
def apm_m95A03_admissible (a b α β : ℝ) : Set (ℝ → ℝ) :=
  {u | ContDiff ℝ 1 u ∧ u a = α ∧ u b = β}
def apm_m95A03_solves (a b α β : ℝ) (p q f u : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 u ∧ u a = α ∧ u b = β ∧ ∀ t ∈ Set.Icc a b,
    deriv (fun x => p x * deriv u x) t - q t * u t = f t
def apm_m95A03_boundaryLift (a b α β t : ℝ) : ℝ :=
  α + (β - α) * ((t - a) / (b - a))
def apm_m95A03_modifiedRHS (p q f w : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t - (deriv (fun x => p x * deriv w x) t - q t * w t)

def apm_m95a03_bump : ContDiffBump (2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
lemma bump_smooth : ContDiff ℝ 2 (apm_m95a03_bump : ℝ → ℝ) := by
  exact ContDiff.contDiffBump contDiff_const contDiff_const contDiff_const contDiff_id
lemma bump_out {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ∉ tsupport (apm_m95a03_bump : ℝ → ℝ) := by
  rw [ContDiffBump.tsupport_eq]
  intro h
  have hd : dist t (2 : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa [apm_m95a03_bump] using h
  rw [Real.dist_eq] at hd
  have ht1 : t ≤ 1 := ht.2
  have ha : (1 : ℝ) ≤ |t - 2| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  linarith
lemma bump_deriv_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    deriv (apm_m95a03_bump : ℝ → ℝ) t = 0 :=
  deriv_of_notMem_tsupport (bump_out ht)
lemma bump_center : apm_m95a03_bump 2 = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp [apm_m95a03_bump]
lemma perturb_deriv (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    EqOn (deriv (u + (apm_m95a03_bump : ℝ → ℝ))) (deriv u) (Icc (0 : ℝ) 1) := by
  intro t ht
  rw [deriv_add]
  · simp [bump_deriv_zero ht]
  · exact hu.differentiable (by norm_num) t
  · exact bump_smooth.differentiable (by norm_num) t
lemma perturb_energy (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    apm_m95A03_energy 0 1 1 0 0 (u + (apm_m95a03_bump : ℝ → ℝ)) =
      apm_m95A03_energy 0 1 1 0 0 u := by
  unfold apm_m95A03_energy
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simp only [Pi.one_apply, Pi.zero_apply, one_mul, zero_mul, mul_zero, add_zero]
  rw [perturb_deriv u hu ht']
lemma final_false :
    ¬ ∃! u : ℝ → ℝ, ContDiff ℝ 2 u ∧
      IsMinOn (apm_m95A03_energy 0 1 1 0 0) (apm_m95A03_admissible 0 1 0 0) u := by
  rintro ⟨u, ⟨hu, hmin⟩, huniq⟩
  let v := u + (apm_m95a03_bump : ℝ → ℝ)
  have hvcd : ContDiff ℝ 2 v := hu.add bump_smooth
  have hvmin : IsMinOn (apm_m95A03_energy 0 1 1 0 0)
      (apm_m95A03_admissible 0 1 0 0) v := by
    intro w hw
    rw [perturb_energy u hu]
    exact hmin hw
  have huv : v = u := huniq v ⟨hvcd, hvmin⟩
  have hcenter := congrFun huv 2
  dsimp [v] at hcenter
  change u 2 + apm_m95a03_bump 2 = u 2 at hcenter
  rw [bump_center] at hcenter
  linarith

theorem not_apm_m95a03 :
    ¬ ∀ (a b α β p₀ : ℝ), a < b → 0 < p₀ → ∀ (p q f : ℝ → ℝ),
      ContDiff ℝ 1 p → Continuous q → Continuous f →
      (∀ t ∈ Icc a b, p₀ ≤ p t) → (∀ t ∈ Icc a b, 0 ≤ q t) →
      ((∀ u : ℝ → ℝ, ContDiff ℝ 2 u → u a = α → u b = β →
        (apm_m95A03_solves a b α β p q f u ↔
          IsMinOn (apm_m95A03_energy a b p q f) (apm_m95A03_admissible a b α β) u)) ∧
      (∀ u : ℝ → ℝ, let w := apm_m95A03_boundaryLift a b α β
        apm_m95A03_solves a b α β p q f u ↔ apm_m95A03_solves a b 0 0 p q
          (apm_m95A03_modifiedRHS p q f w) (u - w)) ∧
      ∃! u : ℝ → ℝ, ContDiff ℝ 2 u ∧
        IsMinOn (apm_m95A03_energy a b p q f) (apm_m95A03_admissible a b 0 0) u) := by
  intro H
  have h := H 0 1 0 0 1 (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (by fun_prop) (by fun_prop) (by fun_prop) (by simp) (by simp)
  exact final_false h.2.2

#print axioms not_apm_m95a03

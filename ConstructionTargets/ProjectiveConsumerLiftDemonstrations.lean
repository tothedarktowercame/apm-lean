import ConstructionTargets.ProjectiveQuotientDescent

/-! # The projective descent API on the two motivating formulas -/

open Set Topology
open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ProjectiveQuotientDescent

noncomputable section
namespace ConstructionTargets.ProjectiveConsumerLiftDemonstrations

def t96A06Polynomial (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]

theorem t96A06Polynomial_nonzero (v : NonzeroVectors ℝ 3) :
    t96A06Polynomial v.1 ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [t96A06Polynomial] at h0 h1 h2 h3
  rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3
  all_goals
    have hz0 : v.1 0 = 0 := by nlinarith
    have hz1 : v.1 1 = 0 := by nlinarith
    have hz2 : v.1 2 = 0 := by nlinarith
    have hz3 : v.1 3 = 0 := by nlinarith
    apply v.2
    funext i
    fin_cases i <;> assumption

theorem t96A06Polynomial_orbit (t : ℝ) (v : Vectors ℝ 3) :
    t96A06Polynomial (t • v) = t ^ 2 • t96A06Polynomial v := by
  funext i
  fin_cases i <;> simp [t96A06Polynomial] <;> ring

theorem t96A06Polynomial_descends :
    ∃ f : C(Space ℝ 3, Space ℝ 3), ∀ v : NonzeroVectors ℝ 3,
      f (quotientMap ℝ 3 v) = quotientMap ℝ 3
        ⟨t96A06Polynomial v.1, t96A06Polynomial_nonzero v⟩ := by
  let lift : NonzeroVectors ℝ 3 → Space ℝ 3 := fun v =>
    quotientMap ℝ 3 ⟨t96A06Polynomial v.1, t96A06Polynomial_nonzero v⟩
  have hlift : Continuous lift := by
    apply (continuous_quotientMap ℝ 3).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hc (j : Fin 4) : Continuous (fun v : NonzeroVectors ℝ 3 => v.1 j) :=
      (continuous_apply j).comp continuous_subtype_val
    fin_cases i
    · simpa [t96A06Polynomial] using (hc 0).pow 2 |>.sub ((hc 1).pow 2)
    · simpa [t96A06Polynomial] using (continuous_const.mul (hc 0)).mul (hc 1)
    · simpa [t96A06Polynomial] using (hc 2).pow 2 |>.sub ((hc 3).pow 2)
    · simpa [t96A06Polynomial] using (continuous_const.mul (hc 2)).mul (hc 3)
  apply projectiveHomogeneousMapDescent ℝ lift hlift
  intro a b t hab
  apply (Projectivization.mk_eq_mk_iff ℝ
    (t96A06Polynomial a.1) (t96A06Polynomial b.1)
    (t96A06Polynomial_nonzero a) (t96A06Polynomial_nonzero b)).mpr
  by_cases ht : t = 0
  · subst t
    exfalso
    apply a.2
    simpa using hab
  · refine ⟨Units.mk0 (t ^ 2) (pow_ne_zero 2 ht), ?_⟩
    rw [hab, t96A06Polynomial_orbit]
    rfl

def t99J05Diagonal (n : ℕ) (v : Vectors ℂ n) : Vectors ℂ n :=
  fun i => ((i.val + 1 : ℕ) : ℂ) * v i

def t99J05DiagonalHomotopy (n : ℕ)
    (z : Vectors ℂ n × Set.Icc (0 : ℝ) 1) : Vectors ℂ n :=
  fun i => (((1 - z.2.1) + z.2.1 * (i.val + 1 : ℝ) : ℝ) : ℂ) * z.1 i

theorem t99J05Diagonal_nonzero {n : ℕ} (v : NonzeroVectors ℂ n) :
    t99J05Diagonal n v.1 ≠ 0 := by
  intro h
  apply v.2
  funext i
  have hi := congrFun h i
  have hw : (((i.val + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero i.val)
  exact (mul_eq_zero.mp hi).resolve_left hw

theorem t99J05DiagonalHomotopy_nonzero {n : ℕ}
    (v : NonzeroVectors ℂ n) (s : Set.Icc (0 : ℝ) 1) :
    t99J05DiagonalHomotopy n (v.1, s) ≠ 0 := by
  intro h
  apply v.2
  funext i
  have hi := congrFun h i
  have hw : 0 < (1 - s.1) + s.1 * (i.val + 1 : ℝ) := by
    nlinarith [s.2.1]
  have hw' : (((1 - s.1) + s.1 * (i.val + 1 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hw)
  exact (mul_eq_zero.mp hi).resolve_left hw'

theorem t99J05Diagonal_orbit (n : ℕ) (t : ℂ) (v : Vectors ℂ n) :
    t99J05Diagonal n (t • v) = t • t99J05Diagonal n v := by
  funext i
  simp [t99J05Diagonal]
  ring

theorem t99J05DiagonalHomotopy_descends (n : ℕ) :
    ∃ H : C(Space ℂ n × Set.Icc (0 : ℝ) 1, Space ℂ n),
      (∀ z : NonzeroVectors ℂ n × Set.Icc (0 : ℝ) 1,
        H (quotientMap ℂ n z.1, z.2) = quotientMap ℂ n
        ⟨t99J05DiagonalHomotopy n (z.1.1, z.2),
          t99J05DiagonalHomotopy_nonzero z.1 z.2⟩) ∧
      (∀ v, H (quotientMap ℂ n v, ⟨0, by norm_num⟩) = quotientMap ℂ n v) ∧
      (∀ v, H (quotientMap ℂ n v, ⟨1, by norm_num⟩) = quotientMap ℂ n
        ⟨t99J05Diagonal n v.1, t99J05Diagonal_nonzero v⟩) := by
  let lift : NonzeroVectors ℂ n × Set.Icc (0 : ℝ) 1 → Space ℂ n := fun z =>
    quotientMap ℂ n ⟨t99J05DiagonalHomotopy n (z.1.1, z.2),
      t99J05DiagonalHomotopy_nonzero z.1 z.2⟩
  have hlift : Continuous lift := by
    apply (continuous_quotientMap ℂ n).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hs : Continuous (fun z : NonzeroVectors ℂ n × Set.Icc (0 : ℝ) 1 => z.2.1) :=
      continuous_subtype_val.comp continuous_snd
    have hv : Continuous (fun z : NonzeroVectors ℂ n × Set.Icc (0 : ℝ) 1 => z.1.1 i) :=
      ((continuous_apply i).comp continuous_subtype_val).comp continuous_fst
    have hw : Continuous (fun z : NonzeroVectors ℂ n × Set.Icc (0 : ℝ) 1 =>
        (((1 - z.2.1) + z.2.1 * (i.val + 1 : ℝ) : ℝ) : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        ((continuous_const.sub hs).add (hs.mul continuous_const))
    simpa only [t99J05DiagonalHomotopy] using hw.mul hv
  obtain ⟨H, hH⟩ := projectiveHomogeneousHomotopyDescent ℂ lift hlift (by
    intro a b s t hab
    apply (Projectivization.mk_eq_mk_iff ℂ _ _
      (t99J05DiagonalHomotopy_nonzero a s)
      (t99J05DiagonalHomotopy_nonzero b s)).mpr
    by_cases ht : t = 0
    · subst t
      exfalso
      apply a.2
      simpa using hab
    · refine ⟨Units.mk0 t ht, ?_⟩
      rw [hab]
      funext i
      simp [t99J05DiagonalHomotopy]
      ring)
  refine ⟨H, hH, ?_, ?_⟩
  · intro v
    rw [hH (v, ⟨0, by norm_num⟩)]
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
    exact ⟨1, by ext i; simp [t99J05DiagonalHomotopy]⟩
  · intro v
    rw [hH (v, ⟨1, by norm_num⟩)]
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
    exact ⟨1, by ext i; simp [t99J05DiagonalHomotopy, t99J05Diagonal]⟩

end ConstructionTargets.ProjectiveConsumerLiftDemonstrations

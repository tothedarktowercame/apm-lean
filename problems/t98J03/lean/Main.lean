import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SphereHomology

/-!
# APM t98J03 — integral homology of spheres

## Statement repairs

None.

## Encoding questions

None. `Sⁿ` is the actual unit metric sphere in `ℝⁿ⁺¹`, and homology is
Mathlib's integral singular homology. The disconnected zero-sphere is stated
separately from the positive-dimensional formula.
-/

open CategoryTheory

noncomputable section

abbrev apm_t98J03_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev apm_t98J03_H (n k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (apm_t98J03_Sphere n)))

lemma apm_t98J03_sphere_zero_coord (x : apm_t98J03_Sphere 0) :
    (x.1 0) = 1 ∨ (x.1 0) = -1 := by
  have hs : (x.1 0) ^ 2 = (1 : ℝ) := by
    have hx := x.2
    change x.1 ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 1)) 1 at hx
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at hx
    simpa using hx
  exact sq_eq_one_iff.mp hs

/-- The sign of the unique coordinate identifies the zero-sphere with two
points at the level needed to obtain finiteness. -/
def apm_t98J03_sphereZeroSign (x : apm_t98J03_Sphere 0) : Bool :=
  decide (x.1 0 = 1)

lemma apm_t98J03_sphereZeroSign_injective :
    Function.Injective apm_t98J03_sphereZeroSign := by
  intro x y hxy
  apply Subtype.ext
  ext i
  fin_cases i
  rcases apm_t98J03_sphere_zero_coord x with hx | hx <;>
    rcases apm_t98J03_sphere_zero_coord y with hy | hy
  · exact hx.trans hy.symm

  · have hx' : apm_t98J03_sphereZeroSign x = true := by
      simp [apm_t98J03_sphereZeroSign, hx]
    have hy' : apm_t98J03_sphereZeroSign y = false := by
      simp [apm_t98J03_sphereZeroSign, hy]
      norm_num
    rw [hx', hy'] at hxy
    contradiction
  · have hx' : apm_t98J03_sphereZeroSign x = false := by
      simp [apm_t98J03_sphereZeroSign, hx]
      norm_num
    have hy' : apm_t98J03_sphereZeroSign y = true := by
      simp [apm_t98J03_sphereZeroSign, hy]
    rw [hx', hy'] at hxy
    contradiction
  · exact hx.trans hy.symm

lemma apm_t98J03_sphereZeroSign_surjective :
    Function.Surjective apm_t98J03_sphereZeroSign := by
  intro b
  let x : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.single 0 (if b then 1 else -1)
  have hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]
    cases b <;> simp [x]
  refine ⟨⟨x, hx⟩, ?_⟩
  cases b <;> simp [apm_t98J03_sphereZeroSign, x] <;> norm_num

/-- The concrete metric zero-sphere really is the two-element type. -/
noncomputable def apm_t98J03_sphereZeroEquivBool :
    apm_t98J03_Sphere 0 ≃ Bool :=
  Equiv.ofBijective apm_t98J03_sphereZeroSign
    ⟨apm_t98J03_sphereZeroSign_injective,
      apm_t98J03_sphereZeroSign_surjective⟩

noncomputable instance apm_t98J03_sphereZero_finite :
    Finite (apm_t98J03_Sphere 0) :=
  Finite.of_injective apm_t98J03_sphereZeroSign
    apm_t98J03_sphereZeroSign_injective

lemma apm_t98J03_sphereZero_positive_homology_isZero
    (k : ℕ) (hk : 0 < k) : Limits.IsZero (apm_t98J03_H 0 k) := by
  exact
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ)
      (TopCat.of (apm_t98J03_Sphere 0)) (Nat.ne_of_gt hk)

noncomputable def apm_t98J03_boolFunLinearEquivProd :
    (Bool → ℤ) ≃ₗ[ℤ] (ℤ × ℤ) where
  toFun f := (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv f := by
    funext b
    cases b <;> rfl
  right_inv p := by
    exact Prod.ext rfl rfl
  map_add' f g := rfl
  map_smul' z f := rfl

/-- Zeroth homology of the concrete metric zero-sphere is free on its two
points, normalized to the product module in the frozen statement. -/
noncomputable def apm_t98J03_sphereZeroH0Iso :
    apm_t98J03_H 0 0 ≅ ModuleCat.of ℤ (ℤ × ℤ) := by
  letI : Fintype (apm_t98J03_Sphere 0) :=
    Fintype.ofEquiv Bool apm_t98J03_sphereZeroEquivBool.symm
  exact
    AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ)
        (TopCat.of (apm_t98J03_Sphere 0)) ≪≫
      ModuleCat.coprodIsoDirectSum
        (fun _ : apm_t98J03_Sphere 0 ↦ ModuleCat.of ℤ ℤ) ≪≫
      (DirectSum.linearEquivFunOnFintype ℤ
        (apm_t98J03_Sphere 0) (fun _ ↦ ℤ)).toModuleIso ≪≫
      (LinearEquiv.piCongrLeft ℤ
        (fun _ : apm_t98J03_Sphere 0 ↦ ℤ)
        apm_t98J03_sphereZeroEquivBool.symm).symm.toModuleIso ≪≫
      apm_t98J03_boolFunLinearEquivProd.toModuleIso

theorem apm_t98j03 :
    Nonempty (apm_t98J03_H 0 0 ≅ ModuleCat.of ℤ (ℤ × ℤ)) ∧
    (∀ k : ℕ, 0 < k → Limits.IsZero (apm_t98J03_H 0 k)) ∧
    ∀ n : ℕ, 0 < n →
      Nonempty (apm_t98J03_H n 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t98J03_H n n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, k ≠ 0 → k ≠ n → Limits.IsZero (apm_t98J03_H n k) := by
  refine ⟨⟨apm_t98J03_sphereZeroH0Iso⟩,
    apm_t98J03_sphereZero_positive_homology_isZero, ?_⟩
  intro n hn
  exact ConstructionTargets.SphereHomology.positiveSphereIntegralHomology n hn

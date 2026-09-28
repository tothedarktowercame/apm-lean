import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.SingularHomologyHomotopy

noncomputable section

namespace ConstructionTargets.EvenSphereTangentFieldObstruction

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets

abbrev sphere (m : ℕ) := T02A06.euclideanUnitSphere (m + 2)

private theorem id_ne_zero (m : ℕ) :
    𝟙 ((CoefficientCoordinateReflections.H ℤ (m + 1)).obj (TopCat.of (sphere m))) ≠ 0 := by
  intro h
  have e := CoefficientFirstReflection.topIso ℤ m
  have hz : IsZero ((CoefficientCoordinateReflections.H ℤ (m + 1)).obj
      (TopCat.of (sphere m))) := (IsZero.iff_id_eq_zero _).2 h
  have hz' : IsZero (ModuleCat.of ℤ ℤ) := hz.of_iso e.symm
  have h' := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom (1 : ℤ))
    ((IsZero.iff_id_eq_zero _).1 hz')
  simp at h'

set_option maxHeartbeats 2000000 in
theorem id_not_homotopic_antipodal (m : ℕ) (hm : Odd m) :
    ¬ (ContinuousMap.id (sphere m)).Homotopic
      (CoefficientSphereAntipodal.antipodal) := by
  intro H
  have h1 := SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) H (m + 1)
  have h2 := CoefficientSphereAntipodal.antipodal_action ℤ (m + 1) (by omega)
  have hodd : Odd (m + 1 + 1) := by
    rcases hm with ⟨k, rfl⟩
    exact ⟨k + 1, by ring⟩
  change (CoefficientCoordinateReflections.H ℤ (m + 1)).map
    (TopCat.ofHom (ContinuousMap.id _)) = _ at h1
  rw [h2, hodd.neg_one_pow] at h1
  rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id] at h1
  let e := CoefficientFirstReflection.topIso ℤ m
  have h3 := congrArg (fun f => e.inv ≫ f ≫ e.hom) h1
  simp only [Category.id_comp, Iso.inv_hom_id] at h3
  have h4 := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom (1 : ℤ)) h3
  simp at h4

theorem homotopy_of_field (m : ℕ)
    (v : sphere m → EuclideanSpace ℝ (Fin (m + 2)))
    (hv : Continuous v)
    (horth : ∀ x, inner ℝ (v x) (x : EuclideanSpace ℝ (Fin (m + 2))) = 0)
    (hnz : ∀ x, v x ≠ 0) :
    (ContinuousMap.id (sphere m)).Homotopic
      (CoefficientSphereAntipodal.antipodal) := by
  let w : sphere m → EuclideanSpace ℝ (Fin (m + 2)) := fun x => ‖v x‖⁻¹ • v x
  have hwnorm (x : sphere m) : ‖w x‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hnz x))]
  have hworth (x : sphere m) :
      inner ℝ (x : EuclideanSpace ℝ (Fin (m + 2))) (w x) = 0 := by
    simp only [w, inner_smul_right]
    rw [real_inner_comm, horth]
    simp
  have hwcont : Continuous w := by
    apply Continuous.smul
    · exact (hv.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hnz x))
    · exact hv
  let H : ContinuousMap.Homotopy (ContinuousMap.id (sphere m))
      CoefficientSphereAntipodal.antipodal := {
    toFun := fun tx => ⟨
      Real.cos (Real.pi * (tx.1 : ℝ)) • (tx.2 : EuclideanSpace ℝ (Fin (m + 2))) +
        Real.sin (Real.pi * (tx.1 : ℝ)) • w tx.2,
      by
        rw [Metric.mem_sphere, dist_zero_right]
        have hxnorm : ‖(tx.2 : EuclideanSpace ℝ (Fin (m + 2)))‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using tx.2.property
        have hi : inner ℝ
            (Real.cos (Real.pi * (tx.1 : ℝ)) •
              (tx.2 : EuclideanSpace ℝ (Fin (m + 2))))
            (Real.sin (Real.pi * (tx.1 : ℝ)) • w tx.2) = 0 := by
          simp [inner_smul_left, inner_smul_right, hworth]
        have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
        rw [norm_smul, norm_smul, Real.norm_eq_abs, hxnorm, hwnorm] at hs
        have htrig := Real.sin_sq_add_cos_sq (Real.pi * (tx.1 : ℝ))
        have hnonneg := norm_nonneg
          (Real.cos (Real.pi * (tx.1 : ℝ)) •
              (tx.2 : EuclideanSpace ℝ (Fin (m + 2))) +
            Real.sin (Real.pi * (tx.1 : ℝ)) • w tx.2)
        have hc : |Real.cos (Real.pi * (tx.1 : ℝ))| *
            |Real.cos (Real.pi * (tx.1 : ℝ))| =
            Real.cos (Real.pi * (tx.1 : ℝ)) ^ 2 := by
          rw [← pow_two, sq_abs]
        have hsin : ‖Real.sin (Real.pi * (tx.1 : ℝ))‖ *
            ‖Real.sin (Real.pi * (tx.1 : ℝ))‖ =
            Real.sin (Real.pi * (tx.1 : ℝ)) ^ 2 := by
          rw [Real.norm_eq_abs, ← pow_two, sq_abs]
        norm_num [hc, hsin] at hs
        nlinarith⟩
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro x
      apply Subtype.ext
      simp
    map_one_left := by
      intro x
      apply Subtype.ext
      simp [CoefficientSphereAntipodal.antipodal]
  }
  exact ⟨H⟩

end ConstructionTargets.EvenSphereTangentFieldObstruction

#print axioms ConstructionTargets.EvenSphereTangentFieldObstruction.id_not_homotopic_antipodal
#print axioms ConstructionTargets.EvenSphereTangentFieldObstruction.homotopy_of_field

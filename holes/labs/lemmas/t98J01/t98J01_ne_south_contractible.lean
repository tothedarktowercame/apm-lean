import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CP2RationalHomology

/-! # t98J01 blueprint

The two admitted theorems are the independent topology-library boundaries:
the rational homology trace computation and the circle-reflection obstruction.
-/

open ConstructionTargets.RationalLefschetz
noncomputable section
namespace T98J01

abbrev S2 := {p : ℝ × ℝ × ℝ // p.1^2 + p.2.1^2 + p.2.2^2 = 1}
abbrev S1 := {p : ℝ × ℝ // p.1^2 + p.2^2 = 1}

def rotation (p : S2) : S2 :=
  ⟨(-p.val.1, -p.val.2.1, p.val.2.2), by simpa using p.property⟩

def reflection (p : S1) : S1 :=
  ⟨(-p.val.1, p.val.2), by simpa using p.property⟩

abbrev ProductSpace := S2 × S1 × S1

def h : C(ProductSpace, ProductSpace) where
  toFun p := (rotation p.1, reflection p.2.1, reflection p.2.2)
  continuous_toFun := by
    unfold rotation reflection
    fun_prop

end T98J01

def t98J01_rotationCM : C(T98J01.S2, T98J01.S2) :=
  ⟨T98J01.rotation, by unfold T98J01.rotation; fun_prop⟩

def t98J01_reflectionCM : C(T98J01.S1, T98J01.S1) :=
  ⟨T98J01.reflection, by unfold T98J01.reflection; fun_prop⟩

/-- Seat: rational homology of the printed two-sphere is finite-dimensional
in every degree. -/
private def t98J01_sphere_homology_finiteDimensional_aux_homeomorph :
    T98J01.S2 ≃ₜ T02A06.euclideanUnitSphere 3 where
  toFun x := ⟨WithLp.toLp 2 ![x.1.1, x.1.2.1, x.1.2.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq]
    rw [show ∑ i : Fin 3, ‖(WithLp.toLp 2 ![x.1.1, x.1.2.1, x.1.2.2] :
        EuclideanSpace ℝ (Fin 3)) i‖ ^ 2 = 1 by
      rw [show (∑ i : Fin 3, ‖(WithLp.toLp 2 ![x.1.1, x.1.2.1, x.1.2.2] :
          EuclideanSpace ℝ (Fin 3)) i‖ ^ 2) =
          ‖x.1.1‖ ^ 2 + ‖x.1.2.1‖ ^ 2 + ‖x.1.2.2‖ ^ 2 by
        norm_num [Fin.sum_univ_succ, add_assoc]]
      simpa [Real.norm_eq_abs, sq_abs, add_assoc] using x.2]
    norm_num⟩
  invFun x := ⟨(x.1 0, x.1 1, x.1 2), by
    have hx : ‖x.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_succ] at hx
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.sum_univ_zero,
      WithLp.ofLp_toLp, add_zero] at hx
    have hs : 0 ≤ ‖x.1 0‖ ^ 2 + (‖x.1 1‖ ^ 2 + ‖x.1 2‖ ^ 2) := by positivity
    have hh0 := congrArg (fun r : ℝ => r ^ 2) hx
    change (Real.sqrt (‖x.1 0‖ ^ 2 + (‖x.1 1‖ ^ 2 + ‖x.1 2‖ ^ 2))) ^ 2 = 1 ^ 2 at hh0
    rw [Real.sq_sqrt hs] at hh0
    simpa [Real.norm_eq_abs, sq_abs, add_assoc] using hh0⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

private noncomputable def t98J01_sphere_homology_finiteDimensional_aux_iso (k : ℕ) :
    ConstructionTargets.RationalLefschetz.Homology T98J01.S2 k ≅
      ConstructionTargets.CoefficientContractiblePair.H ℚ k
        (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).mapIso
    (TopCat.isoOfHomeo t98J01_sphere_homology_finiteDimensional_aux_homeomorph)

private theorem t98J01_sphere_homology_finiteDimensional_aux_of_iso
    {M N : ModuleCat ℚ} (e : M ≅ N) [FiniteDimensional ℚ N] :
    FiniteDimensional ℚ M := by
  apply FiniteDimensional.of_injective e.hom.hom
  intro x y hxy
  have := congrArg e.inv.hom hxy
  simpa using this

private theorem t98J01_sphere_homology_finiteDimensional_aux_of_isZero
    {M : ModuleCat ℚ} (h : CategoryTheory.Limits.IsZero M) :
    FiniteDimensional ℚ M := by
  letI : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  exact FiniteDimensional.of_injective
    (0 : M →ₗ[ℚ] (Fin 0 → ℚ)) (fun _ _ _ => Subsingleton.elim _ _)

theorem t98J01_sphere_homology_finiteDimensional :
    ∀ k, FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 k) := by
  intro k
  rcases k with (_ | _ | _ | k)
  · letI := t98J01_sphere_homology_finiteDimensional_aux_of_iso
      ConstructionTargets.CoefficientSphereEndpoints.rationalS2H0
    exact t98J01_sphere_homology_finiteDimensional_aux_of_iso
      (t98J01_sphere_homology_finiteDimensional_aux_iso 0)
  · letI := t98J01_sphere_homology_finiteDimensional_aux_of_iso
      ConstructionTargets.CoefficientSphereEndpoints.rationalS2H1
    exact t98J01_sphere_homology_finiteDimensional_aux_of_iso
      (t98J01_sphere_homology_finiteDimensional_aux_iso 1)
  · letI := t98J01_sphere_homology_finiteDimensional_aux_of_iso
      ConstructionTargets.CoefficientSphereEndpoints.rationalS2H2
    exact t98J01_sphere_homology_finiteDimensional_aux_of_iso
      (t98J01_sphere_homology_finiteDimensional_aux_iso 2)
  · let hz : CategoryTheory.Limits.IsZero
        (ConstructionTargets.CoefficientContractiblePair.H ℚ (k + 3)
          (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 2))) := by
      let e₁ := ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 2 (k + 2) (by omega)
      let e₀ := ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (k + 1) (by omega)
      exact (ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ (k + 1) (by omega)).of_iso
        (e₁ ≪≫ e₀)
    letI := t98J01_sphere_homology_finiteDimensional_aux_of_isZero hz
    exact t98J01_sphere_homology_finiteDimensional_aux_of_iso
      (t98J01_sphere_homology_finiteDimensional_aux_iso (k + 3))

/-- Seat: rational homology of the printed two-sphere vanishes above degree 2. -/
theorem t98J01_sphere_homology_vanishes_above_two_aux_standard
    (k : ℕ) (hk : 2 < k) :
    CategoryTheory.Limits.IsZero
      (ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 3) k) := by
  let e₂ : ConstructionTargets.RationalLefschetz.Homology
      (T02A06.euclideanUnitSphere 3) k ≅
      ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 2) (k - 1) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 2 (k - 1) (by omega))
  let e₁ : ConstructionTargets.RationalLefschetz.Homology
      (T02A06.euclideanUnitSphere 2) (k - 1) ≅
      ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 1) (k - 2) := by
    have hdeg : k - 2 + 1 = k - 1 := by omega
    simpa only [hdeg] using
      (ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (k - 2) (by omega))
  have hzero := ConstructionTargets.SphereZeroCoefficients.positive_vanishing
    ℚ (k - 2) (by omega)
  exact (hzero.of_iso e₁).of_iso e₂

noncomputable def t98J01_sphere_homology_vanishes_above_two_aux_homeomorph :
    T98J01.S2 ≃ₜ T02A06.euclideanUnitSphere 3 where
  toFun p := ⟨WithLp.toLp 2 ![p.1.1, p.1.2.1, p.1.2.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq,
      Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, WithLp.ofLp_toLp]
    rw [show ‖p.1.1‖ ^ 2 + ‖p.1.2.1‖ ^ 2 + ‖p.1.2.2‖ ^ 2 = 1 by
      simpa [Real.norm_eq_abs, sq_abs, add_assoc] using p.2]
    norm_num⟩
  invFun p := ⟨(p.1 0, p.1 1, p.1 2), by
    have hp : ‖p.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using p.2
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three] at hp
    have hs : 0 ≤ ‖p.1 0‖ ^ 2 + ‖p.1 1‖ ^ 2 + ‖p.1 2‖ ^ 2 := by positivity
    have hh : (Real.sqrt (‖p.1 0‖ ^ 2 + ‖p.1 1‖ ^ 2 + ‖p.1 2‖ ^ 2)) ^ 2 = 1 := by
      rw [hp]
      norm_num
    rw [Real.sq_sqrt hs] at hh
    simpa [Real.norm_eq_abs, sq_abs, add_assoc] using hh⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem t98J01_sphere_homology_vanishes_above_two :
    ∀ k, 2 < k → Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 k) := by
  intro k hk
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)
  let e : TopCat.of T98J01.S2 ≅ TopCat.of (T02A06.euclideanUnitSphere 3) :=
    TopCat.isoOfHomeo t98J01_sphere_homology_vanishes_above_two_aux_homeomorph
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((t98J01_sphere_homology_vanishes_above_two_aux_standard k hk).of_iso
      (F.mapIso e))

/-- Seat: the half-turn has trace `1` on rational `H₀(S²)`. -/
noncomputable def t98J01_rotation_trace_zero_aux_homeomorph :
    T98J01.S2 ≃ₜ T02A06.euclideanUnitSphere 3 where
  toFun p := ⟨WithLp.toLp 2 ![p.1.1, p.1.2.1, p.1.2.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq]
    rw [show (∑ i : Fin 3, ‖(WithLp.toLp 2 ![p.1.1, p.1.2.1, p.1.2.2] :
        EuclideanSpace ℝ (Fin 3)) i‖ ^ 2) = 1 by
      norm_num [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
      simpa [add_assoc] using p.2]
    norm_num⟩
  invFun x := ⟨(x.1 0, x.1 1, x.1 2), by
    have hx : ‖x.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [EuclideanSpace.norm_eq] at hx
    norm_num [Fin.sum_univ_succ] at hx
    have hh : (‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2 + ‖x.1 2‖ ^ 2) = 1 := by
      simpa [Real.norm_eq_abs, sq_abs, add_assoc] using hx
    simpa [Real.norm_eq_abs, sq_abs, add_assoc] using hh⟩
  left_inv p := by ext <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem t98J01_rotation_trace_zero :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 0)
      (ConstructionTargets.RationalLefschetz.induced t98J01_rotationCM 0).hom = 1 := by
  letI : PathConnectedSpace T98J01.S2 :=
    t98J01_rotation_trace_zero_aux_homeomorph.symm.surjective.pathConnectedSpace
      t98J01_rotation_trace_zero_aux_homeomorph.symm.continuous
  let p : T98J01.S2 := ⟨(0, 0, 1), by norm_num⟩
  let e := ConstructionTargets.CoefficientH0.h0Iso ℚ p
  have hmap : ConstructionTargets.RationalLefschetz.induced
      t98J01_rotationCM 0 = CategoryTheory.CategoryStruct.id _ := by
    apply (CategoryTheory.cancel_mono e.hom).mp
    simpa [e, ConstructionTargets.RationalLefschetz.induced,
      ConstructionTargets.CoefficientH0.singularPostcomposition] using
      (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℚ
        t98J01_rotationCM)
  letI : FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 0) :=
    FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective
  rw [hmap]
  change LinearMap.trace ℚ _ LinearMap.id = 1
  rw [LinearMap.trace_id]
  have he : (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 0) ≃ₗ[ℚ] ℚ :=
    e.toLinearEquiv
  rw [he.finrank_eq]
  simp

/-- Seat: the half-turn has trace `0` on rational `H₁(S²)`. -/
theorem t98J01_rotation_trace_one :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 1)
      (ConstructionTargets.RationalLefschetz.induced t98J01_rotationCM 1).hom = 0 := by
  let e := t98J01_sphere_homology_finiteDimensional_aux_iso 1 ≪≫
    ConstructionTargets.CoefficientSphereEndpoints.rationalS2H1
  letI : Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 1) :=
    ⟨fun x y => e.toLinearEquiv.injective (Subsingleton.elim _ _)⟩
  have hmap :
      (ConstructionTargets.RationalLefschetz.induced t98J01_rotationCM 1).hom = 0 :=
    Subsingleton.elim _ _
  rw [hmap]
  simp

/-- Seat: the orientation-preserving half-turn has trace `1` on `H₂(S²; ℚ)`. -/
private def t98J01_rotation_trace_two_aux_homotopy :
    ContinuousMap.Homotopy t98J01_rotationCM (ContinuousMap.id T98J01.S2) := by
  let F : unitInterval × T98J01.S2 → T98J01.S2 := fun tx =>
    let a := Real.pi * (1 - tx.1.1)
    let c := Real.cos a
    let s := Real.sin a
    ⟨(c * tx.2.1.1 - s * tx.2.1.2.1,
      s * tx.2.1.1 + c * tx.2.1.2.1, tx.2.1.2.2), by
        have htrig := Real.sin_sq_add_cos_sq a
        have hp := tx.2.2
        dsimp only [c, s]
        nlinarith⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    dsimp only [F]
    fun_prop
  refine ContinuousMap.Homotopy.mk
    (f₀ := t98J01_rotationCM) (f₁ := ContinuousMap.id T98J01.S2) ⟨F, hF⟩ ?_ ?_
  · intro x
    apply Subtype.ext
    simp [F, t98J01_rotationCM, T98J01.rotation]
  · intro x
    apply Subtype.ext
    simp [F]

theorem t98J01_rotation_trace_two :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 2)
      (ConstructionTargets.RationalLefschetz.induced t98J01_rotationCM 2).hom = 1 := by
  let M := ConstructionTargets.RationalLefschetz.Homology T98J01.S2 2
  let e : M ≅ ModuleCat.of ℚ ℚ :=
    t98J01_sphere_homology_finiteDimensional_aux_iso 2 ≪≫
      ConstructionTargets.CoefficientSphereEndpoints.rationalS2H2
  letI : FiniteDimensional ℚ M :=
    FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective
  have hmap : ConstructionTargets.RationalLefschetz.induced
      t98J01_rotationCM 2 = CategoryTheory.CategoryStruct.id M := by
    simpa [ConstructionTargets.RationalLefschetz.induced, M] using
      (ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
        (ModuleCat ℚ) (ModuleCat.of ℚ ℚ)
          ⟨t98J01_rotation_trace_two_aux_homotopy⟩ 2)
  rw [hmap]
  change LinearMap.trace ℚ M LinearMap.id = 1
  rw [LinearMap.trace_id]
  have he : M ≃ₗ[ℚ] ℚ := e.toLinearEquiv
  rw [he.finrank_eq]
  simp

/-- Sorry-free assembly of the five independent two-sphere leaves. -/
theorem t98J01_rotation_lefschetz :
    HasLefschetzNumber t98J01_rotationCM 2 := by
  refine ⟨t98J01_sphere_homology_finiteDimensional, 2, ?_, ?_⟩
  · exact t98J01_sphere_homology_vanishes_above_two
  · norm_num [Finset.sum_range_succ, t98J01_rotation_trace_zero,
      t98J01_rotation_trace_one, t98J01_rotation_trace_two]

/-- Seat: rational homology of the printed circle is finite-dimensional in
every degree. -/
private def t98J01_circle_homology_finiteDimensional_aux_homeomorph :
    T98J01.S1 ≃ₜ T02A06.euclideanUnitSphere 2 where
  toFun x := ⟨WithLp.toLp 2 ![x.1.1, x.1.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq]
    rw [show ∑ i : Fin 2, ‖(WithLp.toLp 2 ![x.1.1, x.1.2] :
        EuclideanSpace ℝ (Fin 2)) i‖ ^ 2 = 1 by
      rw [show (∑ i : Fin 2, ‖(WithLp.toLp 2 ![x.1.1, x.1.2] :
          EuclideanSpace ℝ (Fin 2)) i‖ ^ 2) = ‖x.1.1‖ ^ 2 + ‖x.1.2‖ ^ 2 by
        norm_num [Fin.sum_univ_succ]]
      simpa [Real.norm_eq_abs, sq_abs] using x.2]
    norm_num⟩
  invFun x := ⟨(x.1 0, x.1 1), by
    have hx : ‖x.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_succ] at hx
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.sum_univ_zero,
      WithLp.ofLp_toLp, add_zero] at hx
    have hs : 0 ≤ ‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2 := by positivity
    have hh := congrArg (fun r : ℝ => r ^ 2) hx
    change (Real.sqrt (‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2)) ^ 2 = 1 ^ 2 at hh
    rw [Real.sq_sqrt hs] at hh
    simpa [Real.norm_eq_abs, sq_abs] using hh⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

private noncomputable def t98J01_circle_homology_finiteDimensional_aux_iso (k : ℕ) :
    ConstructionTargets.RationalLefschetz.Homology T98J01.S1 k ≅
      ConstructionTargets.CoefficientContractiblePair.H ℚ k
        (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 1)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).mapIso
    (TopCat.isoOfHomeo t98J01_circle_homology_finiteDimensional_aux_homeomorph)

private theorem t98J01_circle_homology_finiteDimensional_aux_of_iso
    {M N : ModuleCat ℚ} (e : M ≅ N) [FiniteDimensional ℚ N] :
    FiniteDimensional ℚ M := by
  apply FiniteDimensional.of_injective e.hom.hom
  intro x y hxy
  have := congrArg e.inv.hom hxy
  simpa using this

private theorem t98J01_circle_homology_finiteDimensional_aux_of_isZero
    {M : ModuleCat ℚ} (h : CategoryTheory.Limits.IsZero M) :
    FiniteDimensional ℚ M := by
  letI : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  exact FiniteDimensional.of_injective
    (0 : M →ₗ[ℚ] (Fin 0 → ℚ)) (fun _ _ _ => Subsingleton.elim _ _)

theorem t98J01_circle_homology_finiteDimensional :
    ∀ k, FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 k) := by
  intro k
  rcases k with (_ | _ | k)
  · letI := t98J01_circle_homology_finiteDimensional_aux_of_iso
      (ConstructionTargets.CoefficientH0.sphereH0 ℚ 1)
    exact t98J01_circle_homology_finiteDimensional_aux_of_iso
      (t98J01_circle_homology_finiteDimensional_aux_iso 0)
  · letI := t98J01_circle_homology_finiteDimensional_aux_of_iso
      (ConstructionTargets.CoefficientSphereEndpoints.circleH1 ℚ)
    exact t98J01_circle_homology_finiteDimensional_aux_of_iso
      (t98J01_circle_homology_finiteDimensional_aux_iso 1)
  · let hz : CategoryTheory.Limits.IsZero
        (ConstructionTargets.CoefficientContractiblePair.H ℚ (k + 2)
          (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 1))) := by
      let e := ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (k + 1) (by omega)
      exact (ConstructionTargets.SphereZeroCoefficients.positive_vanishing ℚ (k + 1) (by omega)).of_iso e
    letI := t98J01_circle_homology_finiteDimensional_aux_of_isZero hz
    exact t98J01_circle_homology_finiteDimensional_aux_of_iso
      (t98J01_circle_homology_finiteDimensional_aux_iso (k + 2))

/-- Seat: rational homology of the printed circle vanishes above degree 1. -/
theorem t98J01_circle_homology_vanishes_above_one_aux_standard
    (k : ℕ) (hk : 1 < k) :
    CategoryTheory.Limits.IsZero
      (ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 2) k) := by
  let e : ConstructionTargets.RationalLefschetz.Homology
      (T02A06.euclideanUnitSphere 2) k ≅
      ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 1) (k - 1) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (ConstructionTargets.CoefficientSphereShift.sphereShift ℚ 1 (k - 1) (by omega))
  exact (ConstructionTargets.SphereZeroCoefficients.positive_vanishing
    ℚ (k - 1) (by omega)).of_iso e

noncomputable def t98J01_circle_homology_vanishes_above_one_aux_homeomorph :
    T98J01.S1 ≃ₜ T02A06.euclideanUnitSphere 2 where
  toFun x := ⟨WithLp.toLp 2 ![x.1.1, x.1.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq]
    rw [show ∑ i : Fin 2, ‖(WithLp.toLp 2 ![x.1.1, x.1.2] :
        EuclideanSpace ℝ (Fin 2)) i‖ ^ 2 = 1 by
      rw [show (∑ i : Fin 2, ‖(WithLp.toLp 2 ![x.1.1, x.1.2] :
          EuclideanSpace ℝ (Fin 2)) i‖ ^ 2) = ‖x.1.1‖ ^ 2 + ‖x.1.2‖ ^ 2 by
        norm_num [Fin.sum_univ_succ]]
      simpa [Real.norm_eq_abs, sq_abs] using x.2]
    norm_num⟩
  invFun x := ⟨(x.1 0, x.1 1), by
    have hx : ‖x.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_succ] at hx
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.sum_univ_zero,
      WithLp.ofLp_toLp, add_zero] at hx
    have hs : 0 ≤ ‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2 := by positivity
    have hh := congrArg (fun r : ℝ => r ^ 2) hx
    change (Real.sqrt (‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2)) ^ 2 = 1 ^ 2 at hh
    rw [Real.sq_sqrt hs] at hh
    simpa [Real.norm_eq_abs, sq_abs] using hh⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem t98J01_circle_homology_vanishes_above_one :
    ∀ k, 1 < k → Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 k) := by
  intro k hk
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)
  let e : TopCat.of T98J01.S1 ≅ TopCat.of (T02A06.euclideanUnitSphere 2) :=
    TopCat.isoOfHomeo t98J01_circle_homology_vanishes_above_one_aux_homeomorph
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((t98J01_circle_homology_vanishes_above_one_aux_standard k hk).of_iso
      (F.mapIso e))

/-- Seat: reflection has trace `1` on rational `H₀(S¹)`. -/
private noncomputable def t98J01_reflection_trace_zero_aux_homeomorph :
    T98J01.S1 ≃ₜ T02A06.euclideanUnitSphere 2 where
  toFun p := ⟨WithLp.toLp 2 ![p.1.1, p.1.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, WithLp.ofLp_toLp]
    rw [show ‖p.1.1‖ ^ 2 + ‖p.1.2‖ ^ 2 = 1 by
      simpa [Real.norm_eq_abs, sq_abs] using p.2]
    norm_num⟩
  invFun p := ⟨(p.1 0, p.1 1), by
    have hp : ‖p.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using p.2
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hp
    have hs : 0 ≤ ‖p.1 0‖ ^ 2 + ‖p.1 1‖ ^ 2 := by positivity
    have hh : (Real.sqrt (‖p.1 0‖ ^ 2 + ‖p.1 1‖ ^ 2)) ^ 2 = 1 := by
      rw [hp]
      norm_num
    rw [Real.sq_sqrt hs] at hh
    simpa [Real.norm_eq_abs, sq_abs] using hh⟩
  left_inv p := by ext <;> rfl
  right_inv p := by ext i; fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem t98J01_reflection_trace_zero :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 0)
      (ConstructionTargets.RationalLefschetz.induced t98J01_reflectionCM 0).hom = 1 := by
  letI : PathConnectedSpace T98J01.S1 :=
    t98J01_reflection_trace_zero_aux_homeomorph.symm.surjective.pathConnectedSpace
      t98J01_reflection_trace_zero_aux_homeomorph.symm.continuous
  let p : T98J01.S1 := ⟨(0, 1), by norm_num⟩
  let e := ConstructionTargets.CoefficientH0.h0Iso ℚ p
  have hmap : ConstructionTargets.RationalLefschetz.induced
      t98J01_reflectionCM 0 = CategoryTheory.CategoryStruct.id _ := by
    apply (CategoryTheory.cancel_mono e.hom).mp
    simpa [e, ConstructionTargets.RationalLefschetz.induced,
      ConstructionTargets.CoefficientH0.singularPostcomposition] using
      (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℚ
        t98J01_reflectionCM)
  letI : FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 0) :=
    FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective
  rw [hmap]
  change LinearMap.trace ℚ _ LinearMap.id = 1
  rw [LinearMap.trace_id]
  have he : (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 0) ≃ₗ[ℚ] ℚ :=
    e.toLinearEquiv
  rw [he.finrank_eq]
  simp

/-- Seat: reflection reverses the rational fundamental class of the circle. -/
noncomputable def t98J01_reflection_trace_one_aux_homeomorph :
    T98J01.S1 ≃ₜ T02A06.euclideanUnitSphere 2 where
  toFun x := ⟨WithLp.toLp 2 ![x.1.1, x.1.2], by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, WithLp.ofLp_toLp]
    rw [show ‖x.1.1‖ ^ 2 + ‖x.1.2‖ ^ 2 = 1 by
      simpa [Real.norm_eq_abs, sq_abs] using x.2]
    norm_num⟩
  invFun x := ⟨(x.1 0, x.1 1), by
    have hx : ‖x.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.2
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hx
    have hs : 0 ≤ ‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2 := by positivity
    have hh : (Real.sqrt (‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2)) ^ 2 = 1 := by
      rw [hx]
      norm_num
    rw [Real.sq_sqrt hs] at hh
    simpa [Real.norm_eq_abs, sq_abs] using hh⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

theorem t98J01_reflection_trace_one :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 1)
      (ConstructionTargets.RationalLefschetz.induced t98J01_reflectionCM 1).hom = -1 := by
  open CategoryTheory in
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 1).obj
    (ModuleCat.of ℚ ℚ)
  let e : TopCat.of T98J01.S1 ≅ TopCat.of (T02A06.euclideanUnitSphere 2) :=
    TopCat.isoOfHomeo t98J01_reflection_trace_one_aux_homeomorph
  let E := F.mapIso e
  let r := ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
    (d := 2) 0
  have hconj : (e.inv ≫ TopCat.ofHom t98J01_reflectionCM ≫ e.hom) =
      TopCat.ofHom r := by
    ext x i
    fin_cases i <;>
      simp [e, t98J01_reflection_trace_one_aux_homeomorph, r,
        t98J01_reflectionCM, T98J01.reflection,
        ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
        ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
        ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]
  have hmap : E.inv ≫ ConstructionTargets.RationalLefschetz.induced
      t98J01_reflectionCM 1 ≫ E.hom = -𝟙 _ := by
    change F.map e.inv ≫ F.map (TopCat.ofHom t98J01_reflectionCM) ≫
      F.map e.hom = -𝟙 _
    rw [← F.map_comp, ← F.map_comp, hconj]
    exact ConstructionTargets.CoefficientFirstReflection.circle_negative ℚ
  let u := ConstructionTargets.CoefficientFirstReflection.topIso ℚ 0
  letI : FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 2) 1) :=
    FiniteDimensional.of_injective u.hom.hom u.toLinearEquiv.injective
  letI : FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 1) :=
    FiniteDimensional.of_injective E.hom.hom E.toLinearEquiv.injective
  have ht := LinearMap.trace_comp_comm' E.hom.hom
    ((ConstructionTargets.RationalLefschetz.induced t98J01_reflectionCM 1).hom.comp
      E.inv.hom)
  have hmaplin : E.hom.hom.comp
      ((ConstructionTargets.RationalLefschetz.induced t98J01_reflectionCM 1).hom.comp
        E.inv.hom) = -LinearMap.id := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_neg, ModuleCat.hom_id] using
      congrArg ModuleCat.Hom.hom hmap
  rw [hmaplin] at ht
  have hinvlin : E.inv.hom.comp E.hom.hom = LinearMap.id := by
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using
      congrArg ModuleCat.Hom.hom E.hom_inv_id
  rw [LinearMap.comp_assoc, hinvlin, LinearMap.comp_id] at ht
  have hdim : Module.finrank ℚ
      (ConstructionTargets.RationalLefschetz.Homology
        (T02A06.euclideanUnitSphere 2) 1) = 1 := by
    rw [u.toLinearEquiv.finrank_eq]
    simp
  dsimp [F] at ht
  simpa [hdim] using ht

/-- Sorry-free assembly of the four independent circle leaves. -/
theorem t98J01_reflection_lefschetz :
    HasLefschetzNumber t98J01_reflectionCM 2 := by
  refine ⟨t98J01_circle_homology_finiteDimensional, 1, ?_, ?_⟩
  · exact t98J01_circle_homology_vanishes_above_one
  · norm_num [Finset.sum_range_succ, t98J01_reflection_trace_zero,
      t98J01_reflection_trace_one]

open CategoryTheory CategoryTheory.Limits

/-! ### Lefschetz numbers of chain complexes -/

abbrev t98J01_sset :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)

abbrev t98J01_chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℚ) ℕ :=
  t98J01_sset.obj (TopCat.toSSet.obj (TopCat.of X))

def t98J01_chainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    t98J01_chains X ⟶ t98J01_chains Y :=
  t98J01_sset.map (TopCat.toSSet.map (TopCat.ofHom f))

def t98J01_ComplexLefschetz (C : ChainComplex (ModuleCat ℚ) ℕ) (φ : C ⟶ C) (v : ℚ) : Prop :=
  (∀ k, FiniteDimensional ℚ (C.homology k)) ∧
  ∃ bound : ℕ, (∀ k, bound < k → Subsingleton (C.homology k)) ∧
    (∑ k ∈ Finset.range (bound + 1), (-1 : ℚ)^k *
      LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom) = v

theorem t98J01_hasLefschetzNumber_iff {X : Type} [TopologicalSpace X] (f : C(X, X)) (v : ℚ) :
    HasLefschetzNumber f v ↔ t98J01_ComplexLefschetz (t98J01_chains X) (t98J01_chainMap f) v :=
  Iff.rfl

def t98J01_selfRestrict {X : Type} [TopologicalSpace X] (φ : C(X, X)) (A : Set X)
    (h : Set.MapsTo φ A A) : C(A, A) :=
  ⟨h.restrict φ A A, φ.continuous.restrict h⟩

open ConstructionTargets.SingularExcision in
abbrev t98J01_range {X : Type} [TopologicalSpace X] (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex := ambientSubspaceRange A

theorem t98J01_range_image_le {X : Type} [TopologicalSpace X] (φ : C(X, X)) (A : Set X)
    (h : Set.MapsTo φ A A) :
    (t98J01_range A).image (TopCat.toSSet.map (TopCat.ofHom φ)) ≤ t98J01_range A := by
  change (SSet.Subcomplex.range (TopCat.toSSet.map
      (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion A))).image _ ≤
    SSet.Subcomplex.range (TopCat.toSSet.map
      (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion A))
  rw [← SSet.Subcomplex.range_comp, ← TopCat.toSSet.map_comp,
    ← ConstructionTargets.SingularExcision.subspaceMap_inclusion A A φ h,
    TopCat.toSSet.map_comp, SSet.Subcomplex.range_comp]
  exact SSet.Subcomplex.image_le_range _ _

open ConstructionTargets ConstructionTargets.ProductionOpenCoverMayerVietoris in
/-- the morphism of stored short complexes -/
def t98J01_mvSelfMap {X : Type} [TopologicalSpace X] (φ : C(X, X)) (P Q : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex)
    (hP : P.image (TopCat.toSSet.map (TopCat.ofHom φ)) ≤ P)
    (hQ : Q.image (TopCat.toSSet.map (TopCat.ofHom φ)) ≤ Q) :
    CoefficientSubcomplexMayerVietoris.shortComplex ℚ P Q ⟶
      CoefficientSubcomplexMayerVietoris.shortComplex ℚ P Q :=
  let F := TopCat.toSSet.map (TopCat.ofHom φ)
  ShortComplex.Hom.mk
    (t98J01_sset.map (subcomplexMap (P ⊓ Q) (P ⊓ Q) F
      (subcomplex_inf_image_le P Q P Q F hP hQ)))
    (biprod.map (t98J01_sset.map (subcomplexMap P P F hP))
      (t98J01_sset.map (subcomplexMap Q Q F hQ)))
    (t98J01_sset.map (subcomplexMap (P ⊔ Q) (P ⊔ Q) F
      (subcomplex_sup_image_le P Q P Q F hP hQ)))
    (by
      apply biprod.hom_ext
      · simp [CoefficientSubcomplexMayerVietoris.shortComplex, ← Functor.map_comp]
        congr 1
      · simp [CoefficientSubcomplexMayerVietoris.shortComplex, ← Functor.map_comp]
        congr 1)
    (by
      apply biprod.hom_ext'
      · simp [CoefficientSubcomplexMayerVietoris.shortComplex, ← Functor.map_comp]
        congr 1
      · simp [CoefficientSubcomplexMayerVietoris.shortComplex, ← Functor.map_comp]
        congr 1)

/-! ### Linear algebra -/

/-- Trace additivity (copied from `LefschetzCompactPolyhedron`, which carries an unrelated `sorry`). -/
theorem t98J01_trace_restrict_add_mapQ
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (φ : V →ₗ[ℚ] V) (W : Submodule ℚ V) (hW : ∀ x ∈ W, φ x ∈ W) :
    LinearMap.trace ℚ V φ =
      LinearMap.trace ℚ W (φ.restrict hW) +
        LinearMap.trace ℚ (V ⧸ W) (W.mapQ W φ (fun x hx => hW x hx)) := by
  classical
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let e : (W × U) ≃ₗ[ℚ] V := W.prodEquivOfIsCompl U hU
  let p : V →ₗ[ℚ] W := (LinearMap.fst ℚ W U).comp e.symm.toLinearMap
  let q : V →ₗ[ℚ] V ⧸ W := W.mkQ
  let s : (V ⧸ W) →ₗ[ℚ] V :=
    U.subtype.comp (W.quotientEquivOfIsCompl U hU).toLinearMap
  have hp (x : W) : p x = x := by
    change (e.symm x).1 = x
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  have hq (x : V ⧸ W) : q (s x) = x := by
    change W.mkQ (W.quotientEquivOfIsCompl U hU x) = x
    exact W.mk_quotientEquivOfIsCompl_apply U hU x
  have hdecomp : W.subtype.comp p + s.comp q = LinearMap.id := by
    ext x
    let y : W × U := e.symm x
    have hxy : e y = x := e.apply_symm_apply x
    change (p x : V) + s (q x) = x
    rw [← hxy]
    simp [p, q, s, e]
  have hφ : φ = W.subtype.comp (p.comp φ) + s.comp (q.comp φ) := by
    ext x
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      (LinearMap.congr_fun hdecomp (φ x)).symm
  calc
    LinearMap.trace ℚ V φ = LinearMap.trace ℚ V
        (W.subtype.comp (p.comp φ) + s.comp (q.comp φ)) := congrArg _ hφ
    _ = LinearMap.trace ℚ V (W.subtype.comp (p.comp φ)) +
        LinearMap.trace ℚ V (s.comp (q.comp φ)) := map_add _ _ _
    _ = _ := by
      have hfirst : (p.comp φ).comp W.subtype = φ.restrict hW := by
        ext x
        exact congrArg Subtype.val (hp ⟨φ x, hW x x.property⟩)
      have hsecond : (q.comp φ).comp s =
          W.mapQ W φ (fun x hx => hW x hx) := by
        apply LinearMap.ext
        intro x
        change q (φ (s x)) = W.mapQ W φ (fun x hx => hW x hx) x
        calc
          _ = W.mapQ W φ (fun x hx => hW x hx) (q (s x)) := by
            simp [q, Submodule.mapQ_apply]
          _ = _ := congrArg _ (hq x)
      rw [LinearMap.trace_comp_comm', hfirst,
        LinearMap.trace_comp_comm', hsecond]


/-- Seat: trace splits along kernel and range of an intertwiner. Use `t98J01_trace_restrict_add_mapQ` with `W = ker T`, then transport the quotient term along `LinearMap.quotKerEquivRange` with `LinearMap.trace_conj'`. -/
theorem t98J01_trace_ker_add_range
    {V W : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (T : V →ₗ[ℚ] W) (φ : V →ₗ[ℚ] V) (ψ : W →ₗ[ℚ] W) (hT : T ∘ₗ φ = ψ ∘ₗ T)
    (hk : ∀ x ∈ LinearMap.ker T, φ x ∈ LinearMap.ker T)
    (hr : ∀ x ∈ LinearMap.range T, ψ x ∈ LinearMap.range T) :
    LinearMap.trace ℚ V φ =
      LinearMap.trace ℚ (LinearMap.ker T) (φ.restrict hk) +
        LinearMap.trace ℚ (LinearMap.range T) (ψ.restrict hr) := by
  let e : (V ⧸ LinearMap.ker T) ≃ₗ[ℚ] LinearMap.range T :=
    T.quotKerEquivRange
  have hcomm :
      e.toLinearMap.comp ((LinearMap.ker T).mapQ (LinearMap.ker T) φ hk) =
        (ψ.restrict hr).comp e.toLinearMap := by
    ext x
    change T (φ x) = ψ (T x)
    exact LinearMap.congr_fun hT x
  have heq :
      e.conj ((LinearMap.ker T).mapQ (LinearMap.ker T) φ hk) =
        ψ.restrict hr := by
    ext x
    have h := LinearMap.congr_fun hcomm (e.symm x)
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply]
    convert congrArg Subtype.val h using 1 <;> simp
  rw [t98J01_trace_restrict_add_mapQ φ (LinearMap.ker T) hk]
  congr 1
  rw [← heq, LinearMap.trace_conj']

/-- Seat: the alternating trace vanishes along a bounded long exact sequence with compatible endomorphisms. Apply `t98J01_trace_ker_add_range` to `i k`, `j k` and `δ k`. With `d k` the trace on `range (δ k)`, `e k` on `range (i k)`, `g k` on `range (j k)`: `tr a k = d k + e k`, `tr b k = e k + g k`, `tr c (k+1) = g (k+1) + d k`, `tr c 0 = g 0` (`hj0`). The exactness equalities identify the submodules. `C (N+1)` is trivial so `d N = 0`, and the sum telescopes. -/
theorem t98J01_trace_longExact
    (A B C : ℕ → Type)
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℚ (A n)] [∀ n, FiniteDimensional ℚ (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module ℚ (B n)] [∀ n, FiniteDimensional ℚ (B n)]
    [∀ n, AddCommGroup (C n)] [∀ n, Module ℚ (C n)] [∀ n, FiniteDimensional ℚ (C n)]
    (i : ∀ n, A n →ₗ[ℚ] B n) (j : ∀ n, B n →ₗ[ℚ] C n) (δ : ∀ n, C (n + 1) →ₗ[ℚ] A n)
    (a : ∀ n, A n →ₗ[ℚ] A n) (b : ∀ n, B n →ₗ[ℚ] B n) (c : ∀ n, C n →ₗ[ℚ] C n)
    (hi : ∀ n, i n ∘ₗ a n = b n ∘ₗ i n) (hj : ∀ n, j n ∘ₗ b n = c n ∘ₗ j n)
    (hδ : ∀ n, δ n ∘ₗ c (n + 1) = a n ∘ₗ δ n)
    (ex₁ : ∀ n, LinearMap.range (i n) = LinearMap.ker (j n))
    (ex₂ : ∀ n, LinearMap.range (j (n + 1)) = LinearMap.ker (δ n))
    (ex₃ : ∀ n, LinearMap.range (δ n) = LinearMap.ker (i n))
    (hj0 : Function.Surjective (j 0))
    (N : ℕ) (hC : ∀ k, N < k → Subsingleton (C k)) :
    (∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k * LinearMap.trace ℚ (B k) (b k)) =
      (∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k * LinearMap.trace ℚ (A k) (a k)) +
      (∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k * LinearMap.trace ℚ (C k) (c k)) := by
  sorry

/-- Seat: an endomorphism swapping the two summands of a direct sum has trace zero. Conjugate by `LinearEquiv.ofBijective (coprod i₁ i₂) hbij` to `V₁ × V₂`, and write the conjugate as `inl ∘ₗ φ₂₁ ∘ₗ snd + inr ∘ₗ φ₁₂ ∘ₗ fst`. Each term has trace zero by `LinearMap.trace_comp_comm'` (`snd ∘ₗ inl = 0`, `fst ∘ₗ inr = 0`). -/
theorem t98J01_trace_offDiagonal
    {V₁ V₂ E : Type} [AddCommGroup V₁] [Module ℚ V₁] [FiniteDimensional ℚ V₁]
    [AddCommGroup V₂] [Module ℚ V₂] [FiniteDimensional ℚ V₂]
    [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (i₁ : V₁ →ₗ[ℚ] E) (i₂ : V₂ →ₗ[ℚ] E)
    (hbij : Function.Bijective (LinearMap.coprod i₁ i₂))
    (φ : E →ₗ[ℚ] E) (φ₁₂ : V₁ →ₗ[ℚ] V₂) (φ₂₁ : V₂ →ₗ[ℚ] V₁)
    (h₁ : φ ∘ₗ i₁ = i₂ ∘ₗ φ₁₂) (h₂ : φ ∘ₗ i₂ = i₁ ∘ₗ φ₂₁) :
    LinearMap.trace ℚ E φ = 0 := by
  sorry

/-! ### Chain-complex Lefschetz numbers -/

/-- Seat: the alternating sum can be taken up to any vanishing bound. Compare with the stored bound; terms above either bound vanish because the trace on a subsingleton module is zero (`LinearMap.trace_eq_zero_of_subsingleton` or similar). -/
theorem t98J01_complexLefschetz_sum_eq
    {C : ChainComplex (ModuleCat ℚ) ℕ} {φ : C ⟶ C} {v : ℚ} (h : t98J01_ComplexLefschetz C φ v)
    (N : ℕ) (hN : ∀ k, N < k → Subsingleton (C.homology k)) :
    (∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k *
      LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom) = v := by
  rcases h with ⟨hfinite, b, hb, hsum⟩
  letI (k : ℕ) := hfinite k
  let M := max N b
  have htraceN (k : ℕ) (hk : N < k) :
      LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom = 0 := by
    letI := hN k hk
    rw [Subsingleton.elim (HomologicalComplex.homologyMap φ k).hom 0]
    exact map_zero (LinearMap.trace ℚ (C.homology k))
  have htraceb (k : ℕ) (hk : b < k) :
      LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom = 0 := by
    letI := hb k hk
    rw [Subsingleton.elim (HomologicalComplex.homologyMap φ k).hom 0]
    exact map_zero (LinearMap.trace ℚ (C.homology k))
  have hNM : Finset.range (N + 1) ⊆ Finset.range (M + 1) := by
    apply Finset.range_mono
    exact Nat.succ_le_succ (le_max_left _ _)
  have hbM : Finset.range (b + 1) ⊆ Finset.range (M + 1) := by
    apply Finset.range_mono
    exact Nat.succ_le_succ (le_max_right _ _)
  have hpadN :
      (∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k *
        LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom) =
      ∑ k ∈ Finset.range (M + 1), (-1 : ℚ)^k *
        LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom := by
    apply Finset.sum_subset hNM
    intro k hkM hkN
    simp only [Finset.mem_range, not_lt] at hkM hkN
    rw [htraceN k (lt_of_lt_of_le (Nat.lt_succ_self N) hkN), mul_zero]
  have hpadb :
      (∑ k ∈ Finset.range (b + 1), (-1 : ℚ)^k *
        LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom) =
      ∑ k ∈ Finset.range (M + 1), (-1 : ℚ)^k *
        LinearMap.trace ℚ (C.homology k) (HomologicalComplex.homologyMap φ k).hom := by
    apply Finset.sum_subset hbM
    intro k hkM hkb
    simp only [Finset.mem_range, not_lt] at hkM hkb
    rw [htraceb k (lt_of_lt_of_le (Nat.lt_succ_self b) hkb), mul_zero]
  rw [hpadN, ← hpadb, hsum]

/-- Seat: a short exact sequence of chain complexes is surjective on `H₀`. In degree 0 every chain is a cycle: `S.g.f 0` is epi (`hS.epi_g`), and `homologyπ` is epi from the cycles. Lift a representative along `S.g.f 0`, lift it to cycles (the outgoing differential is zero, `ChainComplex` with `(ComplexShape.down ℕ).next 0 = 0`). -/
theorem t98J01_homologyMap_g_zero_surjective
    {S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)} (hS : S.ShortExact) :
    Function.Surjective (HomologicalComplex.homologyMap S.g 0).hom := by
  sorry

/-- Seat: additivity of the Lefschetz number on a short exact sequence. Use `hS.homology_exact₁/₂/₃`, `HomologicalComplex.HomologySequence.δ_naturality`, then `t98J01_trace_longExact` with `A = X₁.homology`, `B = X₂.homology`, `C = X₃.homology`, `N = max b₂ (b₁ + 1)`. `H_k(X₃)` is finite-dimensional because it sits between `H_k(X₂)` and `H_{k-1}(X₁)`. Zero `H₀` tail: `t98J01_homologyMap_g_zero_surjective`. Sums to `N`: `t98J01_complexLefschetz_sum_eq`. -/
theorem t98J01_complexLefschetz_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)} (hS : S.ShortExact) (φ : S ⟶ S) {a b : ℚ}
    (h₁ : t98J01_ComplexLefschetz S.X₁ φ.τ₁ a) (h₂ : t98J01_ComplexLefschetz S.X₂ φ.τ₂ b) :
    t98J01_ComplexLefschetz S.X₃ φ.τ₃ (b - a) := by
  sorry

/-- Seat: additivity on a biproduct of complexes. `CoefficientHomologyBiprodIso.homologyBiprodIso` conjugates `homologyMap (biprod.map φ ψ)` to the biproduct of the two homology maps; finish with `LinearMap.trace_prodMap'` after passing to `M × N`, and `t98J01_complexLefschetz_sum_eq` at `max` of the two bounds. -/
theorem t98J01_complexLefschetz_biprod
    {K L : ChainComplex (ModuleCat ℚ) ℕ} {φ : K ⟶ K} {ψ : L ⟶ L} {a b : ℚ}
    (h₁ : t98J01_ComplexLefschetz K φ a) (h₂ : t98J01_ComplexLefschetz L ψ b) :
    t98J01_ComplexLefschetz (K ⊞ L) (biprod.map φ ψ) (a + b) := by
  sorry

/-- Seat: the Lefschetz number is invariant under a commuting quasi-isomorphism. `asIso (homologyMap g k)` is a linear equivalence conjugating the two homology maps (`homologyMap_comp`, `hc`), then `LinearMap.trace_conj'`. Finite-dimensionality and vanishing transport along it. Same bound on both sides. -/
theorem t98J01_complexLefschetz_congr
    {C D : ChainComplex (ModuleCat ℚ) ℕ} (g : C ⟶ D)
    (hg : ∀ n, IsIso (HomologicalComplex.homologyMap g n))
    {φ : C ⟶ C} {ψ : D ⟶ D} (hc : φ ≫ g = g ≫ ψ) (v : ℚ) :
    t98J01_ComplexLefschetz C φ v ↔ t98J01_ComplexLefschetz D ψ v := by
  have hcomm (n : ℕ) :
      HomologicalComplex.homologyMap φ n ≫ HomologicalComplex.homologyMap g n =
        HomologicalComplex.homologyMap g n ≫ HomologicalComplex.homologyMap ψ n := by
    rw [← HomologicalComplex.homologyMap_comp, hc,
      HomologicalComplex.homologyMap_comp]
  have htrace (n : ℕ)
      [FiniteDimensional ℚ (C.homology n)] [FiniteDimensional ℚ (D.homology n)] :
      LinearMap.trace ℚ (C.homology n)
          (HomologicalComplex.homologyMap φ n).hom =
        LinearMap.trace ℚ (D.homology n)
          (HomologicalComplex.homologyMap ψ n).hom := by
    letI := hg n
    let e := asIso (HomologicalComplex.homologyMap g n)
    have he : (HomologicalComplex.homologyMap ψ n).hom =
        e.hom.hom.comp ((HomologicalComplex.homologyMap φ n).hom.comp e.inv.hom) := by
      apply LinearMap.ext
      intro x
      have h := congrArg ModuleCat.Hom.hom (hcomm n)
      simp only [ModuleCat.hom_comp, LinearMap.ext_iff] at h
      simpa [LinearMap.comp_apply, e] using (h (e.inv.hom x)).symm
    rw [he, LinearMap.trace_comp_comm']
    have hi : e.inv.hom.comp e.hom.hom = LinearMap.id := by
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_id] using
        congrArg ModuleCat.Hom.hom e.hom_inv_id
    rw [LinearMap.comp_assoc, hi, LinearMap.comp_id]
  constructor
  · rintro ⟨hfd, b, hb, hs⟩
    have hfdD : ∀ n, FiniteDimensional ℚ (D.homology n) := by
      intro n
      letI := hg n
      letI := hfd n
      exact FiniteDimensional.of_injective
        (inv (HomologicalComplex.homologyMap g n)).hom
        (asIso (HomologicalComplex.homologyMap g n)).symm.toLinearEquiv.injective
    refine ⟨hfdD, b, ?_, ?_⟩
    · intro n hn
      letI := hg n
      letI := hb n hn
      exact Function.Injective.subsingleton
        (asIso (HomologicalComplex.homologyMap g n)).symm.toLinearEquiv.injective
    · haveI (n : ℕ) := hfd n
      haveI (n : ℕ) := hfdD n
      simpa only [htrace] using hs
  · rintro ⟨hfd, b, hb, hs⟩
    have hfdC : ∀ n, FiniteDimensional ℚ (C.homology n) := by
      intro n
      letI := hg n
      letI := hfd n
      exact FiniteDimensional.of_injective
        (HomologicalComplex.homologyMap g n).hom
        (asIso (HomologicalComplex.homologyMap g n)).toLinearEquiv.injective
    refine ⟨hfdC, b, ?_, ?_⟩
    · intro n hn
      letI := hg n
      letI := hb n hn
      exact Function.Injective.subsingleton
        (asIso (HomologicalComplex.homologyMap g n)).toLinearEquiv.injective
    · haveI (n : ℕ) := hfdC n
      haveI (n : ℕ) := hfd n
      simpa only [htrace] using hs

/-! ### Spaces -/

/-- Seat: a homotopy equivalence induces isomorphisms on rational homology. `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic` for `e.left_inv`, `e.right_inv`, and `t98J01_chainMap_comp`-style functoriality; template in `SingularHomologyHomotopy` lines 125-135. -/
theorem t98J01_homotopyEquiv_isIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv Y X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (t98J01_chainMap e.toFun) n) := by
  have hmap : ∀ {Z : Type} [TopologicalSpace Z] {f g : C(Z, Z)},
      f.Homotopic g →
      HomologicalComplex.homologyMap (t98J01_chainMap f) n =
        HomologicalComplex.homologyMap (t98J01_chainMap g) n :=
    fun H => ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) H n
  have hcomp : ∀ {W Z : Type} [TopologicalSpace W] [TopologicalSpace Z]
      (f : C(W, Z)) (g : C(Z, W)),
      t98J01_chainMap (g.comp f) = t98J01_chainMap f ≫ t98J01_chainMap g :=
    fun f g => by
      simp only [t98J01_chainMap, ← CategoryTheory.Functor.map_comp]
      rfl
  have hid : ∀ {Z : Type} [TopologicalSpace Z],
      HomologicalComplex.homologyMap (t98J01_chainMap (ContinuousMap.id Z)) n = 𝟙 _ := by
    intro Z _
    have hcid : t98J01_chainMap (ContinuousMap.id Z) = 𝟙 (t98J01_chains Z) := by
      simp [t98J01_chainMap, t98J01_chains]
    rw [hcid, HomologicalComplex.homologyMap_id]
  have h1 : HomologicalComplex.homologyMap (t98J01_chainMap e.toFun) n ≫
      HomologicalComplex.homologyMap (t98J01_chainMap e.invFun) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← hcomp, hmap e.left_inv, hid]
  have h2 : HomologicalComplex.homologyMap (t98J01_chainMap e.invFun) n ≫
      HomologicalComplex.homologyMap (t98J01_chainMap e.toFun) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← hcomp, hmap e.right_inv, hid]
  exact CategoryTheory.Iso.isIso_hom
    (CategoryTheory.Iso.mk
      (hom := HomologicalComplex.homologyMap (t98J01_chainMap e.toFun) n)
      (inv := HomologicalComplex.homologyMap (t98J01_chainMap e.invFun) n) h1 h2)

theorem t98J01_chainMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    t98J01_chainMap (g.comp f) = t98J01_chainMap f ≫ t98J01_chainMap g := by
  simp only [t98J01_chainMap, ← Functor.map_comp]
  rfl

/-- Assembly. -/
theorem t98J01_hasLefschetz_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv Y X) (g : C(Y, Y)) (f : C(X, X))
    (hc : e.toFun.comp g = f.comp e.toFun) (v : ℚ) :
    HasLefschetzNumber g v ↔ HasLefschetzNumber f v := by
  rw [t98J01_hasLefschetzNumber_iff, t98J01_hasLefschetzNumber_iff]
  refine t98J01_complexLefschetz_congr (t98J01_chainMap e.toFun)
    (t98J01_homotopyEquiv_isIso e) ?_ v
  rw [← t98J01_chainMap_comp, ← t98J01_chainMap_comp, hc]

/-- Restriction of the ambient self-map to the range subcomplex of `A`. -/
def t98J01_rangeEndo {X : Type} [TopologicalSpace X] (φ : C(X, X))
    (P : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex)
    (hP : P.image (TopCat.toSSet.map (TopCat.ofHom φ)) ≤ P) :
    t98J01_sset.obj (P : SSet) ⟶ t98J01_sset.obj (P : SSet) :=
  t98J01_sset.map (ConstructionTargets.ProductionOpenCoverMayerVietoris.subcomplexMap
    P P (TopCat.toSSet.map (TopCat.ofHom φ)) hP)

/-- Seat: chains of a subspace compute the Lefschetz number on its range subcomplex. `t98J01_complexLefschetz_congr` with `g = (CoefficientAmbientSubspaceRangeComparison.rangeChainsIso ℚ A).inv`, which is `t98J01_sset.map (toRange ..)`. The square reduces by `Functor.map_comp` and `cancel_mono (ambientSubspaceRange A).ι` to `SingularExcision.subspaceMap_inclusion`. -/
theorem t98J01_complexLefschetz_range {X : Type} [TopologicalSpace X] (φ : C(X, X)) (A : Set X)
    (h : Set.MapsTo φ A A) {v : ℚ} (hv : HasLefschetzNumber (t98J01_selfRestrict φ A h) v) :
    t98J01_ComplexLefschetz (t98J01_sset.obj (t98J01_range A : SSet))
      (t98J01_rangeEndo φ (t98J01_range A) (t98J01_range_image_le φ A h)) v := by
  sorry

/-- Seat: the same on the infimum subcomplex that appears in Mayer–Vietoris. As `t98J01_complexLefschetz_range` for `U ∩ V`, composed with `CoefficientIntersectionRangeComparison.intersectionChainsIso ℚ U V` (from `ambientIntersectionRangeIso`). Check the square after `cancel_mono` of the inclusion into the ambient singular set. -/
theorem t98J01_complexLefschetz_inf {X : Type} [TopologicalSpace X] (φ : C(X, X)) (U V : Set X)
    (hUV : Set.MapsTo φ (U ∩ V) (U ∩ V))
    (hinf : (t98J01_range U ⊓ t98J01_range V).image (TopCat.toSSet.map (TopCat.ofHom φ)) ≤
      t98J01_range U ⊓ t98J01_range V)
    {c : ℚ} (hc : HasLefschetzNumber (t98J01_selfRestrict φ (U ∩ V) hUV) c) :
    t98J01_ComplexLefschetz (t98J01_sset.obj ((t98J01_range U ⊓ t98J01_range V :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet))
      (t98J01_rangeEndo φ _ hinf) c := by
  sorry

/-- Assembly: the union subcomplex of an open cover computes the ambient Lefschetz number. -/
theorem t98J01_hasLefschetz_of_sup {X : Type} [TopologicalSpace X] (φ : C(X, X)) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hsup : (t98J01_range U ⊔ t98J01_range V).image (TopCat.toSSet.map (TopCat.ofHom φ)) ≤
      t98J01_range U ⊔ t98J01_range V) {v : ℚ}
    (h : t98J01_ComplexLefschetz (t98J01_sset.obj ((t98J01_range U ⊔ t98J01_range V :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet))
      (t98J01_rangeEndo φ _ hsup) v) :
    HasLefschetzNumber φ v := by
  rw [t98J01_hasLefschetzNumber_iff]
  refine (t98J01_complexLefschetz_congr
    (t98J01_sset.map (t98J01_range U ⊔ t98J01_range V).ι)
    (RP3Homology.rationalMayerVietoris_aux_unionMap_isIso U V hU hV hcov) ?_ v).1 h
  simp only [t98J01_rangeEndo, t98J01_chainMap, ← Functor.map_comp]
  rfl

/-- Assembly: Lefschetz numbers add along a cover-preserving self-map. -/
theorem t98J01_hasLefschetz_mayerVietoris {X : Type} [TopologicalSpace X] (φ : C(X, X))
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hφU : Set.MapsTo φ U U) (hφV : Set.MapsTo φ V V)
    (hφW : Set.MapsTo φ (U ∩ V) (U ∩ V)) {a b c : ℚ}
    (ha : HasLefschetzNumber (t98J01_selfRestrict φ U hφU) a)
    (hb : HasLefschetzNumber (t98J01_selfRestrict φ V hφV) b)
    (hc : HasLefschetzNumber (t98J01_selfRestrict φ (U ∩ V) hφW) c) :
    HasLefschetzNumber φ (a + b - c) := by
  have hP := t98J01_range_image_le φ U hφU
  have hQ := t98J01_range_image_le φ V hφV
  let M := t98J01_mvSelfMap φ (t98J01_range U) (t98J01_range V) hP hQ
  have h₁ : t98J01_ComplexLefschetz _ M.τ₁ c := t98J01_complexLefschetz_inf φ U V hφW _ hc
  have h₂ : t98J01_ComplexLefschetz _ M.τ₂ (a + b) :=
    t98J01_complexLefschetz_biprod (t98J01_complexLefschetz_range φ U hφU ha)
      (t98J01_complexLefschetz_range φ V hφV hb)
  have h₃ := t98J01_complexLefschetz_shortExact
    (ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortExact ℚ _ _) M h₁ h₂
  exact t98J01_hasLefschetz_of_sup φ U V hU hV hcov _ h₃

/-- Inclusion of a subset as a bundled map. -/
def t98J01_incl {Y : Type} [TopologicalSpace Y] (A : Set Y) : C(A, Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Seat: a clopen decomposition splits rational homology. Take `P`, `Q` the ranges. `ambientSubspaceRange_inf` and `hdis` make `P ⊓ Q` the range of the empty set, so `t98J01_sset.obj (P ⊓ Q)` has no simplices and is a zero complex; in `CoefficientSubcomplexMayerVietoris.shortExact` the map `g` is then an isomorphism (`ShortComplex.ShortExact.isIso_g_iff` or mono+epi). Compose with `RP3Homology.rationalMayerVietoris_aux_unionMap_isIso`, `rangeChainsIso` and `homologyBiprodIso`, watching the sign in `g`: a sign on one summand does not change bijectivity. Alternative for injectivity and positive degrees: `RP3Homology.rationalMayerVietoris`. -/
theorem t98J01_clopen_homology_bijective {Y : Type} [TopologicalSpace Y] (A B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = Set.univ) (hdis : A ∩ B = ∅) (n : ℕ) :
    Function.Bijective (LinearMap.coprod (induced (t98J01_incl A) n).hom
      (induced (t98J01_incl B) n).hom) := by
  sorry

/-- Seat: a self-map swapping the two pieces of a clopen decomposition has Lefschetz number 0. `t98J01_clopen_homology_bijective` gives each `Homology Y k` finite-dimensional and zero above `N`. Each trace is zero by `t98J01_trace_offDiagonal` with `φ₁₂`, `φ₂₁` induced by the corestrictions `A → B`, `B → A`; the equations are functoriality of `induced`. -/
theorem t98J01_clopen_swap_lefschetz {Y : Type} [TopologicalSpace Y] (A B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = Set.univ) (hdis : A ∩ B = ∅)
    (φ : C(Y, Y)) (hAB : Set.MapsTo φ A B) (hBA : Set.MapsTo φ B A)
    (hfdA : ∀ k, FiniteDimensional ℚ (Homology A k))
    (hfdB : ∀ k, FiniteDimensional ℚ (Homology B k))
    (N : ℕ) (hzA : ∀ k, N < k → Subsingleton (Homology A k))
    (hzB : ∀ k, N < k → Subsingleton (Homology B k)) :
    HasLefschetzNumber φ 0 := by
  sorry

/-! ### Circle geometry -/

def T98J01.northPt : T98J01.S1 := Subtype.mk (0, 1) (by norm_num)
def T98J01.southPt : T98J01.S1 := Subtype.mk (0, -1) (by norm_num)

/-- Seat: stereographic projection `(x, y) ↦ x / (1 + y)` is a homeomorphism onto `ℝ`, with inverse `t ↦ (2t / (1 + t²), (1 - t²) / (1 + t²))`; `ℝ` is contractible, so use `Homeomorph.contractibleSpace` or similar. -/
-- BEGIN SEAT AREA
theorem t98J01_ne_south_contractible :
    ContractibleSpace ↥({q | q ≠ T98J01.southPt} : Set T98J01.S1) := by
  sorry
-- END SEAT AREA

/-- Seat: `(x, y) ↦ x / (1 - y)` as in `t98J01_ne_south_contractible`, or conjugate by `(x, y) ↦ (x, -y)`. -/
theorem t98J01_ne_north_contractible :
    ContractibleSpace ↥({q | q ≠ T98J01.northPt} : Set T98J01.S1) := by
  sorry

/-- Seat: `q ↦ q.1.2` is a homeomorphism onto the open interval `Set.Ioo (-1) 1` (inverse `y ↦ (√(1 - y²), y)`), which is convex and nonempty hence contractible (`Convex.contractibleSpace`). -/
theorem t98J01_pos_contractible :
    ContractibleSpace ↥({q | 0 < q.1.1} : Set T98J01.S1) := by
  sorry

/-- Seat: as `t98J01_pos_contractible` with `y ↦ (-√(1 - y²), y)`, or conjugate by `T98J01.reflection`. -/
theorem t98J01_neg_contractible :
    ContractibleSpace ↥({q | q.1.1 < 0} : Set T98J01.S1) := by
  sorry

/-- Seat: over a contractible subset of the circle, projection to `X` is a homotopy equivalence. Build `↥{z | z.2 ∈ T} ≃ₜ X × T`, then `X × T ≃ₕ X × Unit ≃ₜ X` via `ContinuousMap.HomotopyEquiv.prodCongr` and `contractible_iff_homotopyEquiv_punit`-style equivalence (`ConstructionTargets/SphereProductPoleOpenCover.lean` lines 90-103 is a template). Prove the formula for `e.toFun` by composing explicitly; if the composite is awkward, construct the equivalence directly with `toFun := fun z => z.1.1`, `invFun := fun x => ⟨(x, c), _⟩` for the contraction point `c`. -/
theorem t98J01_prodSubset_homotopyEquiv (X : Type) [TopologicalSpace X] (T : Set T98J01.S1)
    (hT : ContractibleSpace T) :
    ∃ e : ContinuousMap.HomotopyEquiv ↥({z | z.2 ∈ T} : Set (X × T98J01.S1)) X,
      ∀ z, e.toFun z = z.1.1 := by
  letI : ContractibleSpace T := hT
  let j : {z : X × T98J01.S1 // z.2 ∈ T} ≃ₜ X × T :=
    { toFun := fun z => (z.1.1, ⟨z.1.2, z.2⟩)
      invFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
      left_inv := by intro z; ext <;> rfl
      right_inv := by intro z; ext <;> rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let c : ContinuousMap.HomotopyEquiv T Unit :=
    Classical.choice (ContractibleSpace.hequiv_unit T)
  let e : ContinuousMap.HomotopyEquiv ↥({z | z.2 ∈ T} : Set (X × T98J01.S1)) X :=
    j.toHomotopyEquiv.trans
      ((ContinuousMap.HomotopyEquiv.refl X).prodCongr c |>.trans
        (Homeomorph.prodUnique X Unit).toHomotopyEquiv)
  refine ⟨e, ?_⟩
  intro z
  rfl

/-- The overlap `X × (S¹ ∖ {N, S})`. -/
def t98J01_overlap (X : Type) [TopologicalSpace X] : Set (X × T98J01.S1) :=
  {z | z.2 ≠ T98J01.southPt} ∩ {z | z.2 ≠ T98J01.northPt}

def t98J01_overlapPos (X : Type) [TopologicalSpace X] : Set (t98J01_overlap X) :=
  {z | 0 < z.1.2.1.1}

def t98J01_overlapNeg (X : Type) [TopologicalSpace X] : Set (t98J01_overlap X) :=
  {z | z.1.2.1.1 < 0}

/-- Seat: `↥(t98J01_overlapPos X)` is homeomorphic to `↥{z : X × S1 | z.2 ∈ {q | 0 < q.1.1}}` (the conditions `q ≠ southPt`, `q ≠ northPt` follow from `0 < q.1.1`). Compose with `t98J01_prodSubset_homotopyEquiv` and `t98J01_pos_contractible`. -/
theorem t98J01_overlapPos_homotopyEquiv (X : Type) [TopologicalSpace X] :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(t98J01_overlapPos X) X) := by
  sorry

/-- Seat: as `t98J01_overlapPos_homotopyEquiv` with `t98J01_neg_contractible`. -/
theorem t98J01_overlapNeg_homotopyEquiv (X : Type) [TopologicalSpace X] :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(t98J01_overlapNeg X) X) := by
  sorry

/-- Seat: finite-dimensionality and vanishing transport along a homotopy equivalence. -/
theorem t98J01_homology_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv Y X) (n : ℕ) :
    Nonempty (Homology Y n ≅ Homology X n) :=
  ⟨@asIso _ _ _ _ _ (t98J01_homotopyEquiv_isIso e n)⟩

/-- Seat: the product map on the overlap has Lefschetz number zero. `t98J01_clopen_swap_lefschetz` with `A = t98J01_overlapPos X`, `B = t98J01_overlapNeg X`: both open; they cover because `q ≠ northPt`, `q ≠ southPt` force `q.1.1 ≠ 0` (from `q.1.1^2 + q.1.2^2 = 1`); disjoint by sign; reflection negates `q.1.1`. Finite-dimensionality and the bound come from `hf` through `t98J01_homology_of_homotopyEquiv`. -/
theorem t98J01_overlap_lefschetz {X : Type} [TopologicalSpace X] (f : C(X, X)) {a : ℚ}
    (hf : HasLefschetzNumber f a)
    (h : Set.MapsTo (f.prodMap t98J01_reflectionCM) (t98J01_overlap X) (t98J01_overlap X)) :
    HasLefschetzNumber (t98J01_selfRestrict (f.prodMap t98J01_reflectionCM) _ h) 0 := by
  sorry

/-- Seat: reflection fixes the punctures, and the product map preserves the cover. `reflection` is an involution fixing both `southPt` and `northPt`. -/
theorem t98J01_prodMap_mapsTo {X : Type} [TopologicalSpace X] (f : C(X, X)) (p : T98J01.S1)
    (hp : p = T98J01.southPt ∨ p = T98J01.northPt) :
    Set.MapsTo (f.prodMap t98J01_reflectionCM) {z | z.2 ≠ p} {z | z.2 ≠ p} := by
  sorry

/-- Assembly: `L(f × r) = 2 L(f)`. -/
theorem t98J01_lefschetz_prod_reflection {X : Type} [TopologicalSpace X] (f : C(X, X)) {a : ℚ}
    (hf : HasLefschetzNumber f a) :
    HasLefschetzNumber (f.prodMap t98J01_reflectionCM) (2 * a) := by
  let φ := f.prodMap t98J01_reflectionCM
  let U : Set (X × T98J01.S1) := {z | z.2 ≠ T98J01.southPt}
  let V : Set (X × T98J01.S1) := {z | z.2 ≠ T98J01.northPt}
  have hφU : Set.MapsTo φ U U := t98J01_prodMap_mapsTo f _ (Or.inl rfl)
  have hφV : Set.MapsTo φ V V := t98J01_prodMap_mapsTo f _ (Or.inr rfl)
  have hUo : IsOpen U := isOpen_ne.preimage continuous_snd
  have hVo : IsOpen V := isOpen_ne.preimage continuous_snd
  have hcov : U ∪ V = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_contra hz
    push_neg at hz
    have h1 : z.2 = T98J01.southPt := by simpa [U] using hz.1
    have h2 : z.2 = T98J01.northPt := by simpa [V] using hz.2
    have := congrArg (fun q : T98J01.S1 => q.1.2) (h1.symm.trans h2)
    norm_num [T98J01.southPt, T98J01.northPt] at this
  obtain ⟨eU, heU⟩ := t98J01_prodSubset_homotopyEquiv X _ t98J01_ne_south_contractible
  obtain ⟨eV, heV⟩ := t98J01_prodSubset_homotopyEquiv X _ t98J01_ne_north_contractible
  have ha : HasLefschetzNumber (t98J01_selfRestrict φ U hφU) a :=
    (t98J01_hasLefschetz_homotopyEquiv eU _ f (by
      ext z
      change eU.toFun _ = f (eU.toFun z)
      rw [heU, heU]
      rfl) a).2 hf
  have hb : HasLefschetzNumber (t98J01_selfRestrict φ V hφV) a :=
    (t98J01_hasLefschetz_homotopyEquiv eV _ f (by
      ext z
      change eV.toFun _ = f (eV.toFun z)
      rw [heV, heV]
      rfl) a).2 hf
  have hφW : Set.MapsTo φ (U ∩ V) (U ∩ V) := hφU.inter_inter hφV
  have hc := t98J01_overlap_lefschetz f hf hφW
  have := t98J01_hasLefschetz_mayerVietoris φ U V hUo hVo hcov hφU hφV hφW ha hb hc
  convert this using 1
  ring

/-- Assembly -/
theorem t98J01_lefschetz_prodAssoc {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, X)) (g : C(Y, Y)) (h : C(Z, Z)) {v : ℚ}
    (hv : HasLefschetzNumber ((f.prodMap g).prodMap h) v) :
    HasLefschetzNumber (f.prodMap (g.prodMap h)) v := by
  let e : ContinuousMap.HomotopyEquiv ((X × Y) × Z) (X × (Y × Z)) :=
    (Homeomorph.prodAssoc X Y Z).toHomotopyEquiv
  exact (t98J01_hasLefschetz_homotopyEquiv e _ _ (by ext z <;> rfl) v).1 hv


/-- The former library boundary: apply `L(f × r) = 2 L(f)` twice to the half-turn. -/
theorem t98J01_productSphereCircle_homology_traces :
    HasLefschetzNumber T98J01.h 8 := by
  have h4 := t98J01_lefschetz_prod_reflection t98J01_rotationCM t98J01_rotation_lefschetz
  have h8 := t98J01_lefschetz_prod_reflection _ h4
  have hassoc := t98J01_lefschetz_prodAssoc _ _ _ h8
  have hmap : t98J01_rotationCM.prodMap
      (t98J01_reflectionCM.prodMap t98J01_reflectionCM) = T98J01.h := by
    ext p <;> rfl
  rw [hmap] at hassoc
  convert hassoc using 1
  norm_num

/-- Seat: a homotopy `h ≃ id` on `S2 × S1 × S1` restricts (include the middle
circle at a basepoint, project back to it) to a homotopy `reflection ≃ id`. -/
theorem t98J01_reflection_homotopic_of_h
    (hH : ContinuousMap.Homotopic T98J01.h (ContinuousMap.id T98J01.ProductSpace)) :
    ContinuousMap.Homotopic t98J01_reflectionCM (ContinuousMap.id T98J01.S1) := by
  let a : T98J01.S2 := ⟨(0, 0, 1), by norm_num⟩
  let b : T98J01.S1 := ⟨(0, 1), by norm_num⟩
  let inclusion : C(T98J01.S1, T98J01.ProductSpace) :=
    ⟨fun x => (a, x, b), by fun_prop⟩
  let projection : C(T98J01.ProductSpace, T98J01.S1) :=
    ⟨fun x => x.2.1, by fun_prop⟩
  have hrestricted := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl projection)
    (ContinuousMap.Homotopic.comp hH (ContinuousMap.Homotopic.refl inclusion))
  simpa [projection, inclusion, T98J01.h, t98J01_reflectionCM] using hrestricted

/-- Seat: transport along the homeomorphism `(x, y) ↦ toLp ![x, y]` from the
subtype circle to `euclideanUnitSphere 2`, which conjugates the reflection to
a coordinate reflection (if it lands on another coordinate, conjugate by the swap). -/
theorem t98J01_reflectionMap_homotopic_of_reflection
    (hr : ContinuousMap.Homotopic t98J01_reflectionCM (ContinuousMap.id T98J01.S1)) :
    ContinuousMap.Homotopic
      (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (d := 2) 0)
      (ContinuousMap.id (T02A06.euclideanUnitSphere 2)) := by
  let toCircle : T02A06.euclideanUnitSphere 2 → T98J01.S1 := fun x =>
    ⟨(x.1 0, x.1 1), by
      have hx : ‖x.1‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using x.2
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hx
      have hs : 0 ≤ ‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2 := by positivity
      have hh : (Real.sqrt (‖x.1 0‖ ^ 2 + ‖x.1 1‖ ^ 2)) ^ 2 = 1 := by
        rw [hx]
        norm_num
      rw [Real.sq_sqrt hs] at hh
      simpa [Real.norm_eq_abs, sq_abs] using hh⟩
  let fromCircle : T98J01.S1 → T02A06.euclideanUnitSphere 2 := fun x =>
    ⟨WithLp.toLp 2 ![x.1.1, x.1.2], by
      rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq,
        Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, WithLp.ofLp_toLp]
      rw [show ‖x.1.1‖ ^ 2 + ‖x.1.2‖ ^ 2 = 1 by
        simpa [Real.norm_eq_abs, sq_abs] using x.2]
      norm_num⟩
  let e : C(T02A06.euclideanUnitSphere 2, T98J01.S1) :=
    ⟨toCircle, by
      apply Continuous.subtype_mk
      dsimp [toCircle]
      fun_prop⟩
  let e' : C(T98J01.S1, T02A06.euclideanUnitSphere 2) :=
    ⟨fromCircle, by
      apply Continuous.subtype_mk
      dsimp [fromCircle]
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop⟩
  have hinv : e'.comp e = ContinuousMap.id _ := by
    ext x i
    fin_cases i <;> rfl
  have hconj : e'.comp (t98J01_reflectionCM.comp e) =
      ConstructionTargets.CoefficientCoordinateReflections.reflectionMap 0 := by
    ext x i
    fin_cases i <;>
      simp [e', e, fromCircle, toCircle, t98J01_reflectionCM, T98J01.reflection,
        ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
        ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
        ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]
  have hh := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl e')
    (ContinuousMap.Homotopic.comp hr (ContinuousMap.Homotopic.refl e))
  simpa only [ContinuousMap.id_comp, hconj, hinv] using hh

/-- Seat: the coordinate reflection acts by `-1` on `H₁(S¹; ℤ) ≅ ℤ`
(`CoefficientFirstReflection.circle_negative`), the identity by `+1`, and
homotopic maps agree on homology (`SingularHomologyHomotopy`).  Template:
`EvenSphereTangentFieldObstruction.id_not_homotopic_antipodal`. -/
theorem t98J01_reflectionMap_not_homotopic_id :
    ¬ ContinuousMap.Homotopic
      (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (d := 2) 0)
      (ContinuousMap.id (T02A06.euclideanUnitSphere 2)) := by
  intro h
  have hhom :=
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) h 1
  change
    (ConstructionTargets.CoefficientCoordinateReflections.H ℤ 1).map
        (TopCat.ofHom
          (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap 0)) =
      (ConstructionTargets.CoefficientCoordinateReflections.H ℤ 1).map
        (TopCat.ofHom (ContinuousMap.id _)) at hhom
  rw [ConstructionTargets.CoefficientFirstReflection.all_reflections_negative
        ℤ 1 (by decide) 0,
      TopCat.ofHom_id, CategoryTheory.Functor.map_id] at hhom
  let e := ConstructionTargets.CoefficientFirstReflection.topIso ℤ 0
  have he := by
    open CategoryTheory in
      exact congrArg (fun f => e.inv ≫ f ≫ e.hom) hhom
  simp only [CategoryTheory.Preadditive.comp_neg,
    CategoryTheory.Preadditive.neg_comp, CategoryTheory.Category.comp_id,
    CategoryTheory.Category.id_comp, CategoryTheory.Iso.inv_hom_id] at he
  have hone := congrArg (fun f => f.hom (1 : ℤ)) he
  simp at hone

/-- The reflected circle factor detects that the product map is not homotopic
to the identity (claude-14 split of the former LIBRARY lemma). -/
theorem t98J01_circle_reflection_degree_neg_one :
    ¬ ContinuousMap.Homotopic T98J01.h
      (ContinuousMap.id T98J01.ProductSpace) := fun hH =>
  t98J01_reflectionMap_not_homotopic_id
    (t98J01_reflectionMap_homotopic_of_reflection
      (t98J01_reflection_homotopic_of_h hH))

theorem apm_t98j01 :
    HasLefschetzNumber T98J01.h 8 ∧
    ¬ ContinuousMap.Homotopic T98J01.h (ContinuousMap.id T98J01.ProductSpace) := by
  exact ⟨t98J01_productSphereCircle_homology_traces,
    t98J01_circle_reflection_degree_neg_one⟩

#print axioms apm_t98j01

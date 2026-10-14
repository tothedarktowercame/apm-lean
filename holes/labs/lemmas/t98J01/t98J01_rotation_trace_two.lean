import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.SingularHomologyHomotopy

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
  sorry

/-- Seat: the orientation-preserving half-turn has trace `1` on `H₂(S²; ℚ)`. -/
-- BEGIN SEAT AREA
theorem t98J01_rotation_trace_two :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S2 2)
      (ConstructionTargets.RationalLefschetz.induced t98J01_rotationCM 2).hom = 1 := by
  sorry
-- END SEAT AREA

/-- Sorry-free assembly of the five independent two-sphere leaves. -/
theorem t98J01_rotation_lefschetz :
    HasLefschetzNumber t98J01_rotationCM 2 := by
  refine ⟨t98J01_sphere_homology_finiteDimensional, 2, ?_, ?_⟩
  · exact t98J01_sphere_homology_vanishes_above_two
  · norm_num [Finset.sum_range_succ, t98J01_rotation_trace_zero,
      t98J01_rotation_trace_one, t98J01_rotation_trace_two]

/-- Seat: rational homology of the printed circle is finite-dimensional in
every degree. -/
theorem t98J01_circle_homology_finiteDimensional :
    ∀ k, FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 k) := by
  sorry

/-- Seat: rational homology of the printed circle vanishes above degree 1. -/
theorem t98J01_circle_homology_vanishes_above_one :
    ∀ k, 1 < k → Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 k) := by
  sorry

/-- Seat: reflection has trace `1` on rational `H₀(S¹)`. -/
theorem t98J01_reflection_trace_zero :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 0)
      (ConstructionTargets.RationalLefschetz.induced t98J01_reflectionCM 0).hom = 1 := by
  sorry

/-- Seat: reflection reverses the rational fundamental class of the circle. -/
theorem t98J01_reflection_trace_one :
    LinearMap.trace ℚ
      (ConstructionTargets.RationalLefschetz.Homology T98J01.S1 1)
      (ConstructionTargets.RationalLefschetz.induced t98J01_reflectionCM 1).hom = -1 := by
  sorry

/-- Sorry-free assembly of the four independent circle leaves. -/
theorem t98J01_reflection_lefschetz :
    HasLefschetzNumber t98J01_reflectionCM 2 := by
  refine ⟨t98J01_circle_homology_finiteDimensional, 1, ?_, ?_⟩
  · exact t98J01_circle_homology_vanishes_above_one
  · norm_num [Finset.sum_range_succ, t98J01_reflection_trace_zero,
      t98J01_reflection_trace_one]

/-- LIBRARY: multiplicativity of the rational Lefschetz number under products.
This is the single large missing map-natural Künneth/trace-additivity foundation. -/
theorem t98J01_lefschetz_product
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, X)) (g : C(Y, Y)) (a b : ℚ)
    (hf : HasLefschetzNumber f a) (hg : HasLefschetzNumber g b) :
    HasLefschetzNumber (f.prodMap g) (a * b) := by
  sorry

/-- The former library boundary, now a sorry-free assembly from factor
computations and the isolated generic Künneth foundation. -/
theorem t98J01_productSphereCircle_homology_traces :
    HasLefschetzNumber T98J01.h 8 := by
  have hcircles : HasLefschetzNumber
      (t98J01_reflectionCM.prodMap t98J01_reflectionCM) 4 := by
    convert t98J01_lefschetz_product t98J01_reflectionCM
      t98J01_reflectionCM 2 2 t98J01_reflection_lefschetz
      t98J01_reflection_lefschetz using 1 <;> norm_num
  have hproduct := t98J01_lefschetz_product t98J01_rotationCM
      (t98J01_reflectionCM.prodMap t98J01_reflectionCM) 2 4
      t98J01_rotation_lefschetz hcircles
  have hmap : t98J01_rotationCM.prodMap
      (t98J01_reflectionCM.prodMap t98J01_reflectionCM) = T98J01.h := by
    ext p <;> rfl
  rw [hmap] at hproduct
  convert hproduct using 1 <;> norm_num

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

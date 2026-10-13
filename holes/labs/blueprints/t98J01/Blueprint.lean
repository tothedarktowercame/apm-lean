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

/-- LIBRARY: rational Künneth/Mayer–Vietoris and trace computation for the
explicit product map. -/
theorem t98J01_productSphereCircle_homology_traces :
    HasLefschetzNumber T98J01.h 8 := by
  sorry

/-- The circle reflection of `Main.lean` as a bundled continuous map. -/
def t98J01_reflectionCM : C(T98J01.S1, T98J01.S1) :=
  ⟨T98J01.reflection, by unfold T98J01.reflection; fun_prop⟩

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
  sorry

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

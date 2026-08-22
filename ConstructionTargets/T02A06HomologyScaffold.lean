import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.SingularSubdivision

/-!
# Typed scaffold for the homology conjunct of APM `t02A06`

This file is deliberately exploratory.  Its `sorry`s are the theorem-layer
obligations remaining after the axiom-clean small-chain quasi-isomorphism; no
declaration here is a completed construction target until those obligations
are discharged.

The scaffold fixes the intended dependency chain:

* open-cover excision plus the pair LES give the positive-degree sphere shift;
* the interval relative fundamental class supplies the bottom class;
* the shift gives `H₂(S²) ≠ 0` and off-degree vanishing for `H₂(S⁴)`;
* a section/retraction `S² ⇄ S² × S²` rules out a homeomorphism with `S⁴`.
-/

noncomputable section

namespace ConstructionTargets.T02A06HomologyScaffold

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete

abbrev EuclideanUnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

/-! ## Obligations supplied by excision and the pair LES -/

/-- Excision, applied to the two-hemisphere decomposition, gives the usual
positive-degree suspension shift.  Constructing the map-of-pairs and proving
open-cover excision are the principal missing theorem layer. -/
noncomputable def spherePositiveHomologyShift (n k : ℕ) (hk : k ≠ 0) :
    H (k + 1) (EuclideanUnitSphere (n + 1)) ≅
      H k (EuclideanUnitSphere n) := by
  sorry

/-- The relative interval class becomes the fundamental class of the circle
after identifying the interval endpoints.  This is the base use of excision. -/
noncomputable def sphereOneH1IsoInt :
    H 1 (EuclideanUnitSphere 1) ≅ AddCommGrpCat.of ℤ := by
  sorry

/-- The remaining endpoint in the sphere-vanishing induction.  This is the
degree-one portion of the pair LES after hemisphere excision. -/
theorem sphereDegreeOneHomology_isZero
    (n : ℕ) (hn : 1 < n) : IsZero (H 1 (EuclideanUnitSphere n)) := by
  sorry

/-- Positive homology below the top dimension of a sphere vanishes.  All of
the induction is formal once the shift and its degree-one endpoint exist. -/
theorem spherePositiveHomology_isZero_of_lt
    (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    IsZero (H k (EuclideanUnitSphere n)) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              exact sphereDegreeOneHomology_isZero (n + 1) (by omega)
          | succ k =>
              have hkn' : k + 1 < n := by omega
              have hz : IsZero (H (k + 1) (EuclideanUnitSphere n)) :=
                ih (k + 1) (by omega) hkn'
              have e : H (k + 1 + 1) (EuclideanUnitSphere (n + 1)) ≅
                  H (k + 1) (EuclideanUnitSphere n) :=
                spherePositiveHomologyShift n (k + 1) (by omega)
              exact hz.of_iso e

/-! ## The two computations consumed by `bridge_2` -/

noncomputable def sphereTwoH2IsoInt :
    H 2 (EuclideanUnitSphere 2) ≅ AddCommGrpCat.of ℤ :=
  spherePositiveHomologyShift 1 1 (by decide) ≪≫ sphereOneH1IsoInt

theorem sphereTwoH2_not_isZero :
    ¬ IsZero (H 2 (EuclideanUnitSphere 2)) := by
  intro h
  have hz : IsZero (AddCommGrpCat.of ℤ) := h.of_iso sphereTwoH2IsoInt.symm
  have hid : (𝟙 (AddCommGrpCat.of ℤ)) = 0 :=
    (IsZero.iff_id_eq_zero _).1 hz
  have hone := ConcreteCategory.congr_hom hid (1 : ℤ)
  norm_num at hone

theorem sphereFourH2_isZero :
    IsZero (H 2 (EuclideanUnitSphere 4)) :=
  spherePositiveHomology_isZero_of_lt 4 2 (by decide) (by decide)

/-! ## Final retract argument -/

private abbrev F :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 2).obj
    (AddCommGrpCat.of ℤ)

private noncomputable def basepoint : EuclideanUnitSphere 2 :=
  ⟨Classical.choose (NormedSpace.sphere_nonempty.mpr (by norm_num)),
    Classical.choose_spec (NormedSpace.sphere_nonempty.mpr (by norm_num))⟩

private def sectionMap :
    TopCat.of (EuclideanUnitSphere 2) ⟶
      TopCat.of (EuclideanUnitSphere 2 × EuclideanUnitSphere 2) :=
  TopCat.ofHom ⟨fun x ↦ (x, basepoint), continuous_id.prodMk continuous_const⟩

private def retractMap :
    TopCat.of (EuclideanUnitSphere 2 × EuclideanUnitSphere 2) ⟶
      TopCat.of (EuclideanUnitSphere 2) :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

private theorem section_retract : sectionMap ≫ retractMap = 𝟙 _ := by
  ext x
  rfl

/-- The exact second conjunct required by `t02A06`, obtained without Künneth:
`H₂(S²)` is a retract of `H₂(S² × S²)`, whereas `H₂(S⁴)` is zero. -/
theorem no_homeomorph_sphereTwo_prod_sphereTwo_sphereFour :
    ¬ Nonempty
      ((EuclideanUnitSphere 2 × EuclideanUnitSphere 2) ≃ₜ
        EuclideanUnitSphere 4) := by
  rintro ⟨e⟩
  let eIso : TopCat.of (EuclideanUnitSphere 2 × EuclideanUnitSphere 2) ≅
      TopCat.of (EuclideanUnitSphere 4) := TopCat.isoOfHomeo e
  have hezero : F.map eIso.hom = 0 :=
    sphereFourH2_isZero.eq_of_tgt _ _
  have hsection : F.map sectionMap = 0 := by
    apply (cancel_mono (F.map eIso.hom)).1
    rw [hezero, comp_zero, zero_comp]
  have hretract : F.map sectionMap ≫ F.map retractMap = 𝟙 _ := by
    rw [← F.map_comp, section_retract, F.map_id]
  apply sphereTwoH2_not_isZero
  rw [IsZero.iff_id_eq_zero, ← hretract, hsection, zero_comp]

#print axioms spherePositiveHomologyShift
#print axioms sphereOneH1IsoInt
#print axioms sphereDegreeOneHomology_isZero
#print axioms spherePositiveHomology_isZero_of_lt
#print axioms sphereTwoH2_not_isZero
#print axioms sphereFourH2_isZero
#print axioms no_homeomorph_sphereTwo_prod_sphereTwo_sphereFour

end ConstructionTargets.T02A06HomologyScaffold

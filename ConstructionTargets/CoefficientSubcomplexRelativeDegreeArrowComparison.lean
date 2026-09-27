import ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeLattice

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeDegreeArrowComparison

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex
open ConstructionTargets.CoefficientSubcomplexRelativeDegreeQuotients
open ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeOrder

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

/-- The ordinary quotient map induced by an inclusion of denominators. -/
def quotientInclusion {M : Type} [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (h : A ≤ B) : M ⧸ A →ₗ[R] M ⧸ B :=
  A.liftQ B.mkQ (by simpa using h)

@[simp] theorem quotientInclusion_mk {M : Type} [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (h : A ≤ B) (x : M) :
    quotientInclusion R A B h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

/-- The genuine intersection-to-left quotient arrow commutes with the degree
quotient identifications. -/
theorem intersectionToLeft_degree (n : ℕ) :
    (intersectionToLeftRelative R P Q).f n ≫ (leftDegreeIso R P n).hom =
    (intersectionDegreeIso R P Q n).hom ≫ ModuleCat.ofHom
      (quotientInclusion R _ _ ((intersectionRange_le_inf R P Q n).trans inf_le_left)) := by
  apply (cancel_epi ((cokernel.π (intersectionAmbient R P Q)).f n)).1
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    intersectionToLeftRelative_projection, leftDegreeIso_projection,
    ← Category.assoc, intersectionDegreeIso_projection]
  rfl

theorem intersectionToRight_degree (n : ℕ) :
    (intersectionToRightRelative R P Q).f n ≫ (rightDegreeIso R Q n).hom =
    (intersectionDegreeIso R P Q n).hom ≫ ModuleCat.ofHom
      (quotientInclusion R _ _ ((intersectionRange_le_inf R P Q n).trans inf_le_right)) := by
  apply (cancel_epi ((cokernel.π (intersectionAmbient R P Q)).f n)).1
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    intersectionToRightRelative_projection, rightDegreeIso_projection,
    ← Category.assoc, intersectionDegreeIso_projection]
  rfl

theorem leftToUnion_degree (n : ℕ) :
    (leftToUnionRelative R P Q).f n ≫ (unionDegreeIso R P Q n).hom =
    (leftDegreeIso R P n).hom ≫ ModuleCat.ofHom
      (quotientInclusion R _ _ (le_sup_left.trans (sup_le_unionRange R P Q n))) := by
  apply (cancel_epi ((cokernel.π (leftAmbient R P)).f n)).1
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    leftToUnionRelative_projection, unionDegreeIso_projection,
    ← Category.assoc, leftDegreeIso_projection]
  rfl

theorem rightToUnion_degree (n : ℕ) :
    (rightToUnionRelative R P Q).f n ≫ (unionDegreeIso R P Q n).hom =
    (rightDegreeIso R Q n).hom ≫ ModuleCat.ofHom
      (quotientInclusion R _ _ (le_sup_right.trans (sup_le_unionRange R P Q n))) := by
  apply (cancel_epi ((cokernel.π (rightAmbient R Q)).f n)).1
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    rightToUnionRelative_projection, unionDegreeIso_projection,
    ← Category.assoc, rightDegreeIso_projection]
  rfl

open ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeLattice
open ConstructionTargets.CoefficientSubmoduleInfQuotientDiagonal
open ConstructionTargets.CoefficientSubmoduleRelativeMayerVietorisExact

abbrev leftRange (n : ℕ) := LinearMap.range ((leftAmbient R P).f n).hom
abbrev rightRange (n : ℕ) := LinearMap.range ((rightAmbient R Q).f n).hom

noncomputable def intersectionInfEquiv (n : ℕ) :=
  (intersectionDegreeIso R P Q n).toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (intersectionRange_eq_inf R P Q n))

noncomputable def unionSupEquiv (n : ℕ) :=
  (unionDegreeIso R P Q n).toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (unionRange_eq_sup R P Q n))

noncomputable def piecesCoordinates (n : ℕ) :=
  (((biprod.fst : cokernel (leftAmbient R P) ⊞ cokernel (rightAmbient R Q) ⟶ _).f n ≫
    (leftDegreeIso R P n).hom).hom).prod
  (((biprod.snd : cokernel (leftAmbient R P) ⊞ cokernel (rightAmbient R Q) ⟶ _).f n ≫
    (rightDegreeIso R Q n).hom).hom)

/-- The actual first arrow becomes the explicit quotient diagonal. -/
theorem intersectionToPieces_degree (n : ℕ) :
    (piecesCoordinates R P Q n).comp ((intersectionToPiecesRelative R P Q).f n).hom =
      (infQuotientDiagonal R (leftRange R P n) (rightRange R Q n)).comp
        (intersectionInfEquiv R P Q n).toLinearMap := by
  have hl := intersectionToLeft_degree R P Q n
  have hr := intersectionToRight_degree R P Q n
  ext x
  · change ((intersectionToPiecesRelative R P Q).f n ≫
        (biprod.fst : _ ⟶ cokernel (leftAmbient R P)).f n ≫
        (leftDegreeIso R P n).hom) x = _
    rw [← Category.assoc, ← HomologicalComplex.comp_f]
    simp only [intersectionToPiecesRelative, biprod.lift_fst]
    rw [hl]
    change quotientInclusion R _ _ ((intersectionRange_le_inf R P Q n).trans inf_le_left) ((intersectionDegreeIso R P Q n).hom x) =
      (infQuotientDiagonal R _ _
        (Submodule.quotEquivOfEq _ _ (intersectionRange_eq_inf R P Q n) ((intersectionDegreeIso R P Q n).hom x))).1
    generalize (intersectionDegreeIso R P Q n).hom x = z
    induction z using Submodule.Quotient.induction_on with | _ z => rfl
  · change ((intersectionToPiecesRelative R P Q).f n ≫
        (biprod.snd : _ ⟶ cokernel (rightAmbient R Q)).f n ≫
        (rightDegreeIso R Q n).hom) x = _
    rw [← Category.assoc, ← HomologicalComplex.comp_f]
    simp only [intersectionToPiecesRelative, biprod.lift_snd]
    rw [hr]
    change quotientInclusion R _ _ ((intersectionRange_le_inf R P Q n).trans inf_le_right) ((intersectionDegreeIso R P Q n).hom x) =
      (infQuotientDiagonal R _ _
        (Submodule.quotEquivOfEq _ _ (intersectionRange_eq_inf R P Q n) ((intersectionDegreeIso R P Q n).hom x))).2
    generalize (intersectionDegreeIso R P Q n).hom x = z
    induction z using Submodule.Quotient.induction_on with | _ z => rfl

/-- The actual second arrow becomes the explicit signed quotient map. -/
theorem piecesToUnion_degree (n : ℕ) :
    (unionSupEquiv R P Q n).toLinearMap.comp ((piecesToUnionRelative R P Q).f n).hom =
      (piecesToSupQuotient R (leftRange R P n) (rightRange R Q n)).comp
        (piecesCoordinates R P Q n) := by
  have h : (piecesToUnionRelative R P Q).f n ≫ (unionDegreeIso R P Q n).hom =
      (biprod.fst : _ ⟶ cokernel (leftAmbient R P)).f n ≫
        (leftDegreeIso R P n).hom ≫ ModuleCat.ofHom
          (quotientInclusion R _ _ (le_sup_left.trans (sup_le_unionRange R P Q n))) -
      (biprod.snd : _ ⟶ cokernel (rightAmbient R Q)).f n ≫
        (rightDegreeIso R Q n).hom ≫ ModuleCat.ofHom
          (quotientInclusion R _ _ (le_sup_right.trans (sup_le_unionRange R P Q n))) := by
    simp only [piecesToUnionRelative, biprod.desc_eq,
      HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.neg_f_apply, Preadditive.add_comp,
      Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg,
      leftToUnion_degree, rightToUnion_degree, sub_eq_add_neg]
  ext x
  change Submodule.quotEquivOfEq _ _ (unionRange_eq_sup R P Q n)
      (((piecesToUnionRelative R P Q).f n ≫ (unionDegreeIso R P Q n).hom) x) = _
  rw [h]
  change Submodule.quotEquivOfEq _ _ (unionRange_eq_sup R P Q n)
      (quotientInclusion R _ _ (le_sup_left.trans (sup_le_unionRange R P Q n))
        ((leftDegreeIso R P n).hom ((biprod.fst : _ ⟶ cokernel (leftAmbient R P)).f n x)) -
       quotientInclusion R _ _ (le_sup_right.trans (sup_le_unionRange R P Q n))
        ((rightDegreeIso R Q n).hom ((biprod.snd : _ ⟶ cokernel (rightAmbient R Q)).f n x))) =
    piecesToSupQuotient R _ _
      ((leftDegreeIso R P n).hom ((biprod.fst : _ ⟶ cokernel (leftAmbient R P)).f n x),
       (rightDegreeIso R Q n).hom ((biprod.snd : _ ⟶ cokernel (rightAmbient R Q)).f n x))
  generalize (leftDegreeIso R P n).hom
    ((biprod.fst : _ ⟶ cokernel (leftAmbient R P)).f n x) = a
  generalize (rightDegreeIso R Q n).hom
    ((biprod.snd : _ ⟶ cokernel (rightAmbient R Q)).f n x) = b
  induction a using Submodule.Quotient.induction_on with | _ a => ?_
  induction b using Submodule.Quotient.induction_on with | _ b => ?_
  simp [← Submodule.Quotient.mk_sub]

#print axioms intersectionToLeft_degree
#print axioms intersectionToRight_degree
#print axioms leftToUnion_degree
#print axioms rightToUnion_degree
#print axioms intersectionToPieces_degree
#print axioms piecesToUnion_degree
end ConstructionTargets.CoefficientSubcomplexRelativeDegreeArrowComparison

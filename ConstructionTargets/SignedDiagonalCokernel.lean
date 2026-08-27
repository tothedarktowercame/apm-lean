import ConstructionTargets.MayerVietorisExactnessIsZero

/-!
# The cokernel of the signed diagonal

This file identifies the cokernel of `z ↦ (z, -z)` with its coefficient
object in any abelian category.  The construction records the quotient map
as the codiagonal, which is the normalization needed in degree-zero
Mayer--Vietoris calculations.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.SignedDiagonalCokernel

variable {C : Type*} [Category C] [Abelian C]

/-- The signed diagonal into two copies of an object. -/
def signedDiagonal (Z : C) : Z ⟶ Z ⊞ Z :=
  biprod.lift (𝟙 Z) (-𝟙 Z)

/-- The quotient map complementary to the signed diagonal. -/
def codiagonal (Z : C) : Z ⊞ Z ⟶ Z :=
  biprod.desc (𝟙 Z) (𝟙 Z)

@[simp]
theorem signedDiagonal_comp_codiagonal (Z : C) :
    signedDiagonal Z ≫ codiagonal Z = 0 := by
  simp [signedDiagonal, codiagonal]

/-- The codiagonal, regarded as a candidate cokernel of the signed diagonal. -/
def signedDiagonalCokernelCofork (Z : C) :
    CokernelCofork (signedDiagonal Z) :=
  CokernelCofork.ofπ (codiagonal Z)
    (signedDiagonal_comp_codiagonal Z)

/-- The codiagonal has the universal property of the cokernel of the signed
diagonal.  Its factorization sends `z` through the left biproduct inclusion;
the cokernel condition proves that the right inclusion gives the same map. -/
def signedDiagonalCokernelIsColimit (Z : C) :
    IsColimit (signedDiagonalCokernelCofork Z) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨biprod.inl ≫ s.π,
      by
        apply biprod.hom_ext'
        · simp [signedDiagonalCokernelCofork, codiagonal]
        · have hs : signedDiagonal Z ≫ s.π = 0 := by
            simpa only [zero_comp] using s.condition
          have hdecomp : s.π =
              biprod.desc (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) := by
            apply biprod.hom_ext'
            · simp
            · simp
          have hs' : biprod.inl ≫ s.π = biprod.inr ≫ s.π := by
            rw [← sub_eq_zero]
            change biprod.lift (𝟙 Z) (-𝟙 Z) ≫ s.π = 0 at hs
            rw [hdecomp, biprod.lift_desc] at hs
            simpa only [Category.id_comp, Preadditive.neg_comp,
              sub_eq_add_neg] using hs
          simpa [signedDiagonalCokernelCofork, codiagonal] using hs',
      fun {m} hm => by
        rw [← hm]
        simp [signedDiagonalCokernelCofork, codiagonal]⟩

/-- The canonical cokernel object of the signed diagonal is isomorphic to the
coefficient object itself. -/
def signedDiagonalCokernelIso (Z : C) :
    cokernel (signedDiagonal Z) ≅ Z :=
  colimit.isoColimitCocone
    ⟨signedDiagonalCokernelCofork Z,
      signedDiagonalCokernelIsColimit Z⟩

/-- Under the canonical cokernel isomorphism, the quotient projection is
literally the codiagonal. -/
theorem cokernel_π_comp_signedDiagonalCokernelIso_hom (Z : C) :
    cokernel.π (signedDiagonal Z) ≫ (signedDiagonalCokernelIso Z).hom =
      codiagonal Z := by
  exact colimit.isoColimitCocone_ι_hom
    ⟨signedDiagonalCokernelCofork Z,
      signedDiagonalCokernelIsColimit Z⟩ WalkingParallelPair.one

/-- The signed diagonal is monic. -/
instance signedDiagonal_mono (Z : C) : Mono (signedDiagonal Z) := by
  exact ConstructionTargets.MayerVietorisExactnessIsZero.mono_signedBiprodLift_of_mono_left
    (𝟙 Z) (𝟙 Z)

section Conjugated

variable {I P Q X Z : C}

/-- The quotient map for a signed lift whose two components are
isomorphisms. -/
def conjugatedCodiagonal (i : I ≅ P) (j : I ≅ Q) : P ⊞ Q ⟶ I :=
  biprod.desc i.inv j.inv

@[simp]
theorem conjugatedSignedLift_comp_codiagonal
    (i : I ≅ P) (j : I ≅ Q) :
    biprod.lift i.hom (-j.hom) ≫ conjugatedCodiagonal i j = 0 := by
  simp [conjugatedCodiagonal]

/-- The conjugated codiagonal as a cokernel cofork. -/
def conjugatedSignedLiftCokernelCofork (i : I ≅ P) (j : I ≅ Q) :
    CokernelCofork (biprod.lift i.hom (-j.hom)) :=
  CokernelCofork.ofπ (conjugatedCodiagonal i j)
    (conjugatedSignedLift_comp_codiagonal i j)

/-- The conjugated codiagonal is a cokernel of the signed lift of any two
isomorphisms with common source. -/
def conjugatedSignedLiftCokernelIsColimit (i : I ≅ P) (j : I ≅ Q) :
    IsColimit (conjugatedSignedLiftCokernelCofork i j) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.hom ≫ biprod.inl ≫ s.π,
      by
        have hs : biprod.lift i.hom (-j.hom) ≫ s.π = 0 := by
          simpa only [zero_comp] using s.condition
        have hdecomp : s.π =
            biprod.desc (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) := by
          apply biprod.hom_ext'
          · simp
          · simp
        have hs' : i.hom ≫ biprod.inl ≫ s.π =
            j.hom ≫ biprod.inr ≫ s.π := by
          rw [← sub_eq_zero]
          rw [hdecomp, biprod.lift_desc] at hs
          simpa only [Category.assoc, Preadditive.neg_comp,
            sub_eq_add_neg] using hs
        apply biprod.hom_ext'
        · simp [conjugatedSignedLiftCokernelCofork,
            conjugatedCodiagonal]
        · have h := congrArg (fun k => j.inv ≫ k) hs'
          simpa [conjugatedSignedLiftCokernelCofork,
            conjugatedCodiagonal, Category.assoc] using h,
      fun {m} hm => by
        rw [← hm]
        simp [conjugatedSignedLiftCokernelCofork,
          conjugatedCodiagonal]⟩

/-- The canonical cokernel of a signed lift of two isomorphisms is its common
source. -/
def conjugatedSignedLiftCokernelIso (i : I ≅ P) (j : I ≅ Q) :
    cokernel (biprod.lift i.hom (-j.hom)) ≅ I :=
  colimit.isoColimitCocone
    ⟨conjugatedSignedLiftCokernelCofork i j,
      conjugatedSignedLiftCokernelIsColimit i j⟩

/-- Exactness followed by an epimorphic target map identifies the target with
the common source of the two signed component isomorphisms. -/
def exactEpiSignedLiftTargetIso
    (i : I ≅ P) (j : I ≅ Q) (r : P ⊞ Q ⟶ X)
    (hr : biprod.lift i.hom (-j.hom) ≫ r = 0)
    (hex : (ShortComplex.mk (biprod.lift i.hom (-j.hom)) r hr).Exact)
    [Epi r] : X ≅ I := by
  let S := ShortComplex.mk (biprod.lift i.hom (-j.hom)) r hr
  let hR : IsColimit (CokernelCofork.ofπ r hr) :=
    (S.exact_and_epi_g_iff_g_is_cokernel.mp ⟨hex, inferInstance⟩).some
  exact hR.coconePointUniqueUpToIso
    (conjugatedSignedLiftCokernelIsColimit i j)

/-- A chosen coordinate on the common source transports the exact-epic
target identification to that coefficient object. -/
def exactEpiSignedLiftTargetIsoOfCoordinate
    (eI : I ≅ Z) (i : I ≅ P) (j : I ≅ Q) (r : P ⊞ Q ⟶ X)
    (hr : biprod.lift i.hom (-j.hom) ≫ r = 0)
    (hex : (ShortComplex.mk (biprod.lift i.hom (-j.hom)) r hr).Exact)
    [Epi r] : X ≅ Z :=
  exactEpiSignedLiftTargetIso i j r hr hex ≪≫ eI

end Conjugated

end ConstructionTargets.SignedDiagonalCokernel

#print axioms ConstructionTargets.SignedDiagonalCokernel.signedDiagonalCokernelIsColimit
#print axioms ConstructionTargets.SignedDiagonalCokernel.signedDiagonalCokernelIso
#print axioms ConstructionTargets.SignedDiagonalCokernel.cokernel_π_comp_signedDiagonalCokernelIso_hom
#print axioms ConstructionTargets.SignedDiagonalCokernel.conjugatedSignedLiftCokernelIsColimit
#print axioms ConstructionTargets.SignedDiagonalCokernel.conjugatedSignedLiftCokernelIso
#print axioms ConstructionTargets.SignedDiagonalCokernel.exactEpiSignedLiftTargetIso
#print axioms ConstructionTargets.SignedDiagonalCokernel.exactEpiSignedLiftTargetIsoOfCoordinate

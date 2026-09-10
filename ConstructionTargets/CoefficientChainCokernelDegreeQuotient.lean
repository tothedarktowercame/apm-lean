import ConstructionTargets.CoefficientSubmoduleRelativeMayerVietorisExact

noncomputable section
namespace ConstructionTargets.CoefficientChainCokernelDegreeQuotient

open CategoryTheory CategoryTheory.Limits

variable (R : Type) [CommRing R]
variable {K L : ChainComplex (ModuleCat R) ℕ} (f : K ⟶ L)

/-- A degree of a categorical chain-complex cokernel is the ordinary module
quotient by the range of the corresponding degree map. -/
noncomputable def cokernelDegreeQuotientIso (n : ℕ) :
    (cokernel f).X n ≅ ModuleCat.of R (L.X n ⧸ LinearMap.range (f.f n).hom) :=
  PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat R)
      (ComplexShape.down ℕ) n) f ≪≫
    ModuleCat.cokernelIsoRangeQuotient (f.f n)

/-- The chain-complex cokernel projection becomes the ordinary quotient map
under the degreewise identification. -/
theorem cokernelDegreeQuotientIso_projection (n : ℕ) :
    (cokernel.π f).f n ≫ (cokernelDegreeQuotientIso R f n).hom =
      ModuleCat.ofHom (LinearMap.range (f.f n).hom).mkQ := by
  dsimp [cokernelDegreeQuotientIso]
  change (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).map
      (cokernel.π f) ≫
      (PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat R)
        (ComplexShape.down ℕ) n) f).hom ≫
      (ModuleCat.cokernelIsoRangeQuotient (f.f n)).hom = _
  rw [PreservesCokernel.π_iso_hom_assoc]
  exact ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (R := R) (f.f n)

#print axioms cokernelDegreeQuotientIso
#print axioms cokernelDegreeQuotientIso_projection
end ConstructionTargets.CoefficientChainCokernelDegreeQuotient

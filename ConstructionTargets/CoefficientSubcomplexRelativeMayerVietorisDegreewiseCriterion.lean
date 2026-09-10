import ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisEpi

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisDegreewiseCriterion

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisEpi

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

/-- The remaining short-exactness proof is the elementwise injectivity and
middle exactness calculation in every chain degree; the terminal epimorphism
was proved separately. -/
theorem shortComplex_shortExact_of_degreewise
    (hinj : ∀ n, Function.Injective ((shortComplex R P Q).f.f n))
    (hexact : ∀ n, Function.Exact ((shortComplex R P Q).f.f n)
      ((shortComplex R P Q).g.f n)) :
    (shortComplex R P Q).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · apply HomologicalComplex.exact_of_degreewise_exact
    intro n
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact hexact n
  · apply HomologicalComplex.mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr (hinj n)
  · change Epi (piecesToUnionRelative R P Q)
    infer_instance

#print axioms shortComplex_shortExact_of_degreewise
end ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisDegreewiseCriterion

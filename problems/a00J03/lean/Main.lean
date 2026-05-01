import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set Lp

noncomputable section

namespace ApmCanaries.Frames.A00J03.Apm_v2_a00J03_1774991806132.Main

/-! # APM a00J03: Composition operator isometric isomorphism on Lp

  φ: X → X measurable bijection with measurable inverse, μ(φ⁻¹A) = μ(A).
  T_φ(f) = f ∘ φ is an isometric isomorphism on Lp for 1 ≤ p < ∞.

  Mathlib has this essentially built-in:
  - eLpNorm_comp_measurePreserving: ‖f∘φ‖_p = ‖f‖_p
  - isometry_compMeasurePreserving: T_φ is an isometry on Lp
  - The isomorphism follows from φ⁻¹ being measure-preserving too.
-/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ENNReal}

-- CLOSED: The isometry — this IS Mathlib's isometry_compMeasurePreserving
-- For a measure-preserving f, composition with f is an isometry on Lp.
theorem composition_isometry [Fact (1 ≤ p)]
    {φ : X → X} (hφ : MeasurePreserving φ μ μ) :
    Isometry (compMeasurePreserving φ hφ : Lp E p μ → Lp E p μ) :=
  isometry_compMeasurePreserving hφ

-- CLOSED: The norm equality (seminorm level)
-- ‖f ∘ φ‖_p = ‖f‖_p for measure-preserving φ
theorem norm_comp_eq {φ : X → X} (hφ : MeasurePreserving φ μ μ)
    {f : X → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (f ∘ φ) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf hφ

-- The isomorphism: T_φ has inverse T_{φ⁻¹}
-- For a MeasurableEquiv e with e.measurePreserving, both e and e.symm
-- give isometries, and they compose to the identity.
-- This makes T_e a surjective isometry = isometric isomorphism.

-- CLOSED: bijectivity via MeasurableEquiv
-- If e is a MeasurableEquiv that preserves measure, then
-- compMeasurePreserving e and compMeasurePreserving e.symm are mutual inverses.
theorem composition_isometric_isomorphism [Fact (1 ≤ p)]
    (e : MeasurableEquiv X X)
    (he : MeasurePreserving e μ μ)
    (he_symm : MeasurePreserving e.symm μ μ) :
    Function.Surjective (compMeasurePreserving e he : Lp E p μ → Lp E p μ) := by
  intro g
  refine ⟨compMeasurePreserving e.symm he_symm g, ?_⟩
  simpa [Function.comp] using
    (compMeasurePreserving_comp_apply (E := E) (p := p)
      (g := g) (f := e.symm) (f' := e) (hf := he_symm) (hf' := he)).symm

end ApmCanaries.Frames.A00J03.Apm_v2_a00J03_1774991806132.Main

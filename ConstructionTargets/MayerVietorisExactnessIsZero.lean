import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The exactness-to-vanishing step in a Mayer--Vietoris calculation

This file isolates the categorical last step used after the topological maps
in a Mayer--Vietoris sequence have been identified.  It does not construct a
cover, a connecting morphism, or any homology computation.
-/

noncomputable section

namespace ConstructionTargets.MayerVietorisExactnessIsZero

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]
variable {A B C' D : C}
variable (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D)
variable (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)

/-- A signed pair into a biproduct is monic as soon as either displayed
component is monic.  This is the algebra behind injectivity of the connected
`H₀` overlap map: projection to the first piece recovers its inclusion map. -/
theorem mono_signedBiprodLift_of_mono_left
    {X Y Z : C} (i : X ⟶ Y) [Mono i] (j : X ⟶ Z) :
    Mono (biprod.lift i (-j)) := by
  exact mono_of_mono_fac (biprod.lift_fst i (-j))

/-- In two consecutive exact triples, a zero object on the left and a monic
map on the right force the intervening object to be zero.

This is the algebraic shape of the degree-one Mayer--Vietoris conclusion:
`A` is the sum of the degree-one homologies of the two pieces, `B` is the
degree-one homology of their union, and `h` is the signed degree-zero map from
the overlap into the two pieces. -/
theorem isZero_middle_of_two_exact_of_isZero_left_of_mono_right
    (hex₁ : (ShortComplex.mk f g hfg).Exact)
    (hex₂ : (ShortComplex.mk g h hgh).Exact)
    (hA : IsZero A) [Mono h] : IsZero B := by
  apply hex₁.isZero_X₂
  · exact hA.eq_of_src _ _
  · exact hex₂.mono_g_iff.mp (by infer_instance)

#print axioms isZero_middle_of_two_exact_of_isZero_left_of_mono_right
#print axioms mono_signedBiprodLift_of_mono_left

end ConstructionTargets.MayerVietorisExactnessIsZero

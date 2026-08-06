import Mathlib

/-!
# APM t03J01

## Statement repairs

None.

## Encoding questions

Mathlib has no packaged predicates for a closed surface being a double torus
or for cutting an embedded curve to yield a twice-punctured sphere or two
once-punctured tori. Those geometric hypotheses are retained as typed opaque
predicates. Curves are actual subsets homeomorphic to `S¹`, and retraction is
encoded explicitly as a continuous map whose restriction to the subset is the
identity.
-/

noncomputable section

opaque apm_t03j01_IsDoubleTorus
    (X : Type*) [TopologicalSpace X] : Prop

def apm_t03j01_IsCurve
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  Nonempty (Circle ≃ₜ J)

opaque apm_t03j01_CutsIntoTwicePuncturedSphere
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop

opaque apm_t03j01_CutsIntoTwoOncePuncturedTori
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop

def apm_t03j01_RetractsOnto
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  ∃ r : C(X, J), ∀ y : J, r y = y

theorem apm_t03j01
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (hX : apm_t03j01_IsDoubleTorus X)
    (J₁ J₂ : Set X)
    (hcurve₁ : apm_t03j01_IsCurve J₁)
    (hcurve₂ : apm_t03j01_IsCurve J₂)
    (hcut₁ : apm_t03j01_CutsIntoTwicePuncturedSphere J₁)
    (hcut₂ : apm_t03j01_CutsIntoTwoOncePuncturedTori J₂) :
    apm_t03j01_RetractsOnto J₁ ∧
      ¬apm_t03j01_RetractsOnto J₂ := by
  sorry

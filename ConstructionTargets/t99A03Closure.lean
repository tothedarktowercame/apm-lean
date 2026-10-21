import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz

/-! # Closure support for t99A03

This module copies the blueprint's proved concrete models and isolates the
covering-space adapter used after construction of the `N₄ → N₃` double cover.
-/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.Surfaces

noncomputable section

namespace ConstructionTargets.t99A03Closure

def twoWedgePoint : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

abbrev FourProjectivePlanesWedge := Wedge twoWedgePoint twoWedgePoint
abbrev FourProjectivePlanesConnectedSum := Surface false 4
abbrev ThreeProjectivePlanesConnectedSum := Surface false 3

/-- The mod-two character used to select the connected double cover of the
three-crosscap presentation.  It is nonzero on the first crosscap and zero
on the other two. -/
def n3ParityGenerator : Fin 3 → Multiplicative (ZMod 2) :=
  fun i ↦ if i = 0 then Multiplicative.ofAdd 1 else 1

def n3ParityCharacter : FreeGroup (Fin 3) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift n3ParityGenerator

/-- The standard relator `a²b²c²` for the nonorientable genus-three
polygon presentation. -/
def n3CrosscapRelator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2 * FreeGroup.of 2 ^ 2

/-- The parity character kills the actual crosscap relator, so it is ready
to descend through the standard `N₃` presentation. -/
theorem n3ParityCharacter_crosscapRelator :
    n3ParityCharacter n3CrosscapRelator = 1 := by
  simp [n3ParityCharacter, n3CrosscapRelator, n3ParityGenerator]
  change Multiplicative.ofAdd ((1 : ZMod 2) + 1) = Multiplicative.ofAdd 0
  apply congrArg Multiplicative.ofAdd
  change (2 : ZMod 2) = 0
  exact CharP.cast_eq_zero (ZMod 2) 2

/-- The character is genuinely nontrivial, witnessed by the first crosscap
generator. -/
theorem n3ParityCharacter_generator_ne_one :
    n3ParityCharacter (FreeGroup.of (0 : Fin 3)) ≠ 1 := by
  simp [n3ParityCharacter, n3ParityGenerator]

/-- A nonidentity deck transformation of a connected covering has no fixed
point, by uniqueness of lifts against the identity map. -/
theorem deckTransformation_fixedPointFree
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] (p : E → B) (hp : IsCoveringMap p)
    (τ : E ≃ₜ E) (hdeck : p ∘ τ = p)
    (hne : τ ≠ Homeomorph.refl E) : ∀ x : E, τ x ≠ x := by
  intro x hx
  apply hne
  have hfun : (τ : E → E) = id :=
    hp.eq_of_comp_eq τ.continuous continuous_id (by simpa using hdeck) x
      (by simpa using hx)
  exact Homeomorph.ext (fun y ↦ by simpa using congrFun hfun y)

/-- The exact adapter from the planned `N₄ → N₃` deck data to the
fixed-point-free self-map required by the registered theorem. -/
theorem exists_fixedPointFree_selfMap_of_deckData
    [ConnectedSpace FourProjectivePlanesConnectedSum]
    (p : FourProjectivePlanesConnectedSum →
      ThreeProjectivePlanesConnectedSum)
    (τ : FourProjectivePlanesConnectedSum ≃ₜ
      FourProjectivePlanesConnectedSum)
    (hp : IsCoveringMap p) (hdeck : p ∘ τ = p)
    (hne : τ ≠ Homeomorph.refl FourProjectivePlanesConnectedSum) :
    ∃ f : C(FourProjectivePlanesConnectedSum,
        FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x :=
  ⟨τ, deckTransformation_fixedPointFree p hp τ hdeck hne⟩

#print axioms deckTransformation_fixedPointFree
#print axioms exists_fixedPointFree_selfMap_of_deckData
#print axioms n3ParityCharacter_crosscapRelator
#print axioms n3ParityCharacter_generator_ne_one

end ConstructionTargets.t99A03Closure

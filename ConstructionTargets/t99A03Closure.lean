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

/-- The standard one-relator presentation of the genus-three nonorientable
surface group. -/
abbrev N3PresentedGroup :=
  PresentedGroup ({n3CrosscapRelator} : Set (FreeGroup (Fin 3)))

/-- The parity character genuinely descends through the crosscap relator;
this is the index-two algebraic datum used by the future cover realization. -/
def n3PresentedParityCharacter :
    N3PresentedGroup →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (f := n3ParityGenerator) (by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    simpa [n3ParityCharacter] using n3ParityCharacter_crosscapRelator)

@[simp] theorem n3PresentedParityCharacter_generator (i : Fin 3) :
    n3PresentedParityCharacter (PresentedGroup.of i) = n3ParityGenerator i := by
  simp [n3PresentedParityCharacter]

/-- Descent has not collapsed the selected sheet-changing generator. -/
theorem n3PresentedParityCharacter_generator_ne_one :
    n3PresentedParityCharacter (PresentedGroup.of (0 : Fin 3)) ≠ 1 := by
  simp [n3ParityGenerator]

/-- The descended parity character reaches both sheets. -/
theorem n3PresentedParityCharacter_surjective :
    Function.Surjective n3PresentedParityCharacter := by
  intro y
  rcases y with ⟨y⟩
  interval_cases y
  · refine ⟨1, ?_⟩
    rfl
  · refine ⟨PresentedGroup.of (0 : Fin 3), ?_⟩
    rfl

/-- Hence the parity kernel is an index-two normal subgroup. -/
theorem n3PresentedParityCharacter_ker_index :
    n3PresentedParityCharacter.ker.index = 2 := by
  rw [Subgroup.index_ker]
  have hrange : n3PresentedParityCharacter.range = ⊤ :=
    MonoidHom.range_eq_top.mpr n3PresentedParityCharacter_surjective
  rw [hrange]
  norm_num [Nat.card_eq_fintype_card]

/-- The sheet quotient carried by the parity kernel is literally the
two-element deck group. -/
noncomputable def n3PresentedParityKernelQuotientEquiv :
    (N3PresentedGroup ⧸ n3PresentedParityCharacter.ker) ≃*
      Multiplicative (ZMod 2) :=
  QuotientGroup.quotientKerEquivOfSurjective
    n3PresentedParityCharacter n3PresentedParityCharacter_surjective

@[simp] theorem n3PresentedParityKernelQuotientEquiv_mk (g : N3PresentedGroup) :
    n3PresentedParityKernelQuotientEquiv
        (QuotientGroup.mk g) = n3PresentedParityCharacter g := by
  rfl

/-- The concrete two-sheet monodromy action obtained from the descended
parity character by left translation on the two-element sheet type. -/
def n3PresentedParitySheetAction :
    N3PresentedGroup →* Equiv.Perm (Multiplicative (ZMod 2)) :=
  (MulAction.toPermHom (Multiplicative (ZMod 2))
    (Multiplicative (ZMod 2))).comp n3PresentedParityCharacter

@[simp] theorem n3PresentedParitySheetAction_apply
    (g : N3PresentedGroup) (x : Multiplicative (ZMod 2)) :
    n3PresentedParitySheetAction g x = n3PresentedParityCharacter g * x :=
  rfl

/-- The first crosscap generator genuinely exchanges the two sheets. -/
theorem n3PresentedParitySheetAction_generator_moves_one :
    n3PresentedParitySheetAction (PresentedGroup.of (0 : Fin 3)) 1 ≠ 1 := by
  simpa using n3PresentedParityCharacter_generator_ne_one

/-- The parity monodromy is transitive on the actual two-element sheet
fiber, the algebraic connectedness criterion needed by cover realization. -/
theorem n3PresentedParitySheetAction_transitive
    (x y : Multiplicative (ZMod 2)) :
    ∃ g : N3PresentedGroup, n3PresentedParitySheetAction g x = y := by
  rcases n3PresentedParityCharacter_surjective (y * x⁻¹) with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  simp [hg]

/-- The sheet action has exactly the parity kernel, so the realized cover
will have the already-computed index two rather than a facade action. -/
theorem n3PresentedParitySheetAction_ker :
    n3PresentedParitySheetAction.ker = n3PresentedParityCharacter.ker := by
  ext g
  change MulAction.toPerm (n3PresentedParityCharacter g) = 1 ↔
    n3PresentedParityCharacter g = 1
  constructor
  · intro h
    exact (MulAction.toPerm_injective
      (α := Multiplicative (ZMod 2))
      (β := Multiplicative (ZMod 2))) (by
        calc
          MulAction.toPerm (n3PresentedParityCharacter g) = 1 := h
          _ = MulAction.toPerm (1 : Multiplicative (ZMod 2)) :=
            (MulAction.toPermHom (Multiplicative (ZMod 2))
              (Multiplicative (ZMod 2))).map_one.symm)
  · intro h
    rw [h]
    exact (MulAction.toPermHom (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 2))).map_one

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
#print axioms n3PresentedParityCharacter_generator_ne_one
#print axioms n3PresentedParitySheetAction_transitive
#print axioms n3PresentedParitySheetAction_ker

end ConstructionTargets.t99A03Closure

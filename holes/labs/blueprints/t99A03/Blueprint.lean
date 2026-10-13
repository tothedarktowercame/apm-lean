import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz

/-! # APM t99A03: fixed points on a wedge and a connected sum -/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.Surfaces
open ConstructionTargets.RationalLefschetz

noncomputable section

namespace T99A03

/-- The common point in the wedge of two projective planes. -/
def twoWedgePoint : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

/-- Four copies of `ℝP²`, joined at one point. -/
abbrev FourProjectivePlanesWedge := Wedge twoWedgePoint twoWedgePoint

/-- The connected sum of four copies of `ℝP²`. -/
abbrev FourProjectivePlanesConnectedSum := Surface false 4

/-- The connected sum of three copies of `ℝP²`, used as the base of the
double cover producing the fixed-point-free map. -/
abbrev ThreeProjectivePlanesConnectedSum := Surface false 3

end T99A03

/-- **LIBRARY.** Every self-map of the fourfold projective-plane wedge has
rational Lefschetz number one. -/
theorem t99A03_wedge_lefschetz_number :
    ∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), HasLefschetzNumber f 1 := by
  sorry

/-- **LIBRARY.** The Lefschetz fixed-point implication, specialized to the
finite projective-plane wedge.  Its homology calculation is supplied as a
hypothesis so this foundation can be developed in parallel with that
calculation. -/
theorem t99A03_wedge_fixed_point_of_lefschetz
    (hL : ∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), HasLefschetzNumber f 1) :
    ∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), ∃ x, f x = x := by
  sorry

/-- **LIBRARY.** The index-two normal subgroup of `π₁(N₃)` determined by one
crosscap is realized by a connected double cover with total space `N₄`; its
nontrivial deck involution is included in the output. -/
theorem t99A03_exists_N4_deck_involution :
    ∃ (_ : ConnectedSpace T99A03.FourProjectivePlanesConnectedSum)
      (p : T99A03.FourProjectivePlanesConnectedSum →
        T99A03.ThreeProjectivePlanesConnectedSum)
      (τ : T99A03.FourProjectivePlanesConnectedSum ≃ₜ
        T99A03.FourProjectivePlanesConnectedSum),
      IsCoveringMap p ∧ p ∘ τ = p ∧
        τ ≠ Homeomorph.refl T99A03.FourProjectivePlanesConnectedSum := by
  sorry

/-- A nonidentity deck transformation of a connected cover has no fixed
point.  This is the generic uniqueness-of-lifts step from the old stand-in. -/
theorem t99A03_deckTransformation_fixedPointFree
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

theorem apm_t99a03 :
    (∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), ∃ x, f x = x) ∧
    (∃ f : C(T99A03.FourProjectivePlanesConnectedSum,
        T99A03.FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x) := by
  constructor
  · exact t99A03_wedge_fixed_point_of_lefschetz
      t99A03_wedge_lefschetz_number
  · obtain ⟨hconn, p, τ, hp, hdeck, hne⟩ :=
      t99A03_exists_N4_deck_involution
    letI := hconn
    exact ⟨τ, t99A03_deckTransformation_fixedPointFree p hp τ hdeck hne⟩

#print axioms apm_t99a03

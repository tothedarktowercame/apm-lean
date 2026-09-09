import Mathlib
open Set
noncomputable section
namespace ConstructionTargets.EquivariantOrbitQuotient
variable {G H E F : Type*} [Group G] [Group H] [TopologicalSpace E]
  [TopologicalSpace F] [MulAction G E] [MulAction H F]
variable (a : G ≃* H) (h : E ≃ₜ F) (he : ∀ g x, h (g • x) = a g • h x)

include he in
theorem inverse_equivariant (g : H) (x : F) :
    h.symm (g • x) = a.symm g • h.symm x := by
  apply h.injective
  simp only [h.apply_symm_apply, he, a.apply_symm_apply]

include he in
theorem orbit_forward {x y : E} (hxy : MulAction.orbitRel G E x y) :
    MulAction.orbitRel H F (h x) (h y) := by
  rcases hxy with ⟨g, hg⟩
  exact ⟨a g, (he g y).symm.trans (congrArg h hg)⟩

def quotientHomeomorph : Quotient (MulAction.orbitRel G E) ≃ₜ
    Quotient (MulAction.orbitRel H F) where
  toFun := Quotient.map h (fun _ _ => orbit_forward a h he)
  invFun := Quotient.map h.symm (fun _ _ => orbit_forward a.symm h.symm
    (fun g x => inverse_equivariant a h he g x))
  left_inv := by intro q; induction q using Quotient.inductionOn with | h x => exact congrArg (Quotient.mk _) (h.symm_apply_apply x)
  right_inv := by intro q; induction q using Quotient.inductionOn with | h x => exact congrArg (Quotient.mk _) (h.apply_symm_apply x)
  continuous_toFun := continuous_quot_mk.comp h.continuous |>.quotient_lift _
  continuous_invFun := continuous_quot_mk.comp h.symm.continuous |>.quotient_lift _

@[simp] theorem quotientHomeomorph_mk (x : E) :
    quotientHomeomorph a h he (Quotient.mk _ x) = Quotient.mk _ (h x) := rfl

@[simp] theorem quotientHomeomorph_symm_mk (x : F) :
    (quotientHomeomorph a h he).symm (Quotient.mk _ x) = Quotient.mk _ (h.symm x) := rfl

def fiberHomeomorph (q : Quotient (MulAction.orbitRel G E)) :
    {x : E // Quotient.mk (MulAction.orbitRel G E) x = q} ≃ₜ
    {y : F // Quotient.mk (MulAction.orbitRel H F) y = quotientHomeomorph a h he q} where
  toFun x := ⟨h x.1, congrArg (quotientHomeomorph a h he) x.2⟩
  invFun y := ⟨h.symm y.1, by
    have hy := congrArg (quotientHomeomorph a h he).symm y.2
    simpa using hy⟩
  left_inv x := Subtype.ext (h.symm_apply_apply x.1)
  right_inv y := Subtype.ext (h.apply_symm_apply y.1)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem fiber_card (q : Quotient (MulAction.orbitRel G E)) :
    Nat.card {x : E // Quotient.mk (MulAction.orbitRel G E) x = q} =
    Nat.card {y : F // Quotient.mk (MulAction.orbitRel H F) y = quotientHomeomorph a h he q} :=
  Nat.card_congr (fiberHomeomorph a h he q).toEquiv

@[simp] theorem fiberHomeomorph_apply (q : Quotient (MulAction.orbitRel G E))
    (x : {x : E // Quotient.mk (MulAction.orbitRel G E) x = q}) :
    (fiberHomeomorph a h he q x).1 = h x.1 := rfl

#print axioms quotientHomeomorph_mk
#print axioms quotientHomeomorph_symm_mk
#print axioms fiberHomeomorph_apply
#print axioms inverse_equivariant
#print axioms orbit_forward
#print axioms quotientHomeomorph
#print axioms fiberHomeomorph
#print axioms fiber_card
end ConstructionTargets.EquivariantOrbitQuotient

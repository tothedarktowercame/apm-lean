import ConstructionTargets.EquivariantOrbitQuotient
open Set Topology
noncomputable section
namespace ConstructionTargets.EquivariantCoverTransport
open EquivariantOrbitQuotient
variable {G H E F : Type*} [Group G] [Group H] [TopologicalSpace E]
  [TopologicalSpace F] [MulAction G E] [MulAction H F]
variable (a : G ≃* H) (h : E ≃ₜ F) (he : ∀ g x, h (g • x) = a g • h x)
include he in
 theorem transport
    (hp : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G E)) G) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel H F)) H where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul g := by
    letI : ContinuousConstSMul G E := hp.toContinuousConstSMul
    have hc := h.continuous.comp ((continuous_const_smul (a.symm g)).comp h.symm.continuous)
    simpa only [Function.comp_def, he, a.apply_symm_apply, h.apply_symm_apply] using hc
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint x := by
    obtain ⟨U, hU, hd⟩ := hp.disjoint (h.symm x)
    refine ⟨h '' U, by simpa using h.isOpenMap.image_mem_nhds hU, ?_⟩
    intro g hg
    obtain ⟨z, ⟨w, ⟨u, hu, hwu⟩, hgz⟩, v, hv, hvz⟩ := hg
    have huv : a.symm g • u = v := by
      apply h.injective
      rw [he, a.apply_symm_apply, hwu]
      exact hgz.trans hvz.symm
    have hg1 := hd (a.symm g) ⟨v, ⟨u, hu, huv⟩, hv⟩
    exact a.symm.injective (hg1.trans (map_one a.symm).symm)

include he in
theorem covering
    (hp : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G E)) G) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel H F)) :=
  (transport a h he hp).isCoveringMap
def minusOne : Circle := ⟨-1, by simp [Submonoid.unitSphere]⟩
@[simp] theorem minusOne_mul : minusOne * minusOne = 1 := by
  apply Subtype.ext
  change (-1 : ℂ) * (-1) = 1
  ring
@[simp] theorem minusOne_inv : minusOne⁻¹ = minusOne := by
  apply inv_eq_of_mul_eq_one_right
  exact minusOne_mul

def signSubgroup : Subgroup Circle where
  carrier := {z | z = 1 ∨ z = minusOne}
  one_mem' := Or.inl rfl
  mul_mem' := by rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by rintro x (rfl | rfl) <;> simp

theorem sign_discrete : IsDiscrete (signSubgroup : Set Circle) := by
  have hfin : (signSubgroup : Set Circle).Finite := by
    exact (Set.finite_singleton 1).union (Set.finite_singleton minusOne)
  exact hfin.isDiscrete

theorem sign_quotient_cover : IsQuotientCoveringMap
    (Quotient.mk (MulAction.orbitRel signSubgroup Circle)) signSubgroup := by
  apply isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroup signSubgroup sign_discrete
  intro x y
  exact Quotient.eq''.trans QuotientGroup.rightRel_apply

def circleTranslation (c : Circle) : Circle ≃ₜ Circle := Homeomorph.mulLeft c

theorem circle_translation_equivariant (c : Circle) (g : signSubgroup) (x : Circle) :
    circleTranslation c (g • x) = g • circleTranslation c x := by
  change c * ((g : Circle) * x) = (g : Circle) * (c * x)
  ac_rfl

theorem translated_circle_cover (c : Circle) : IsQuotientCoveringMap
    (Quotient.mk (MulAction.orbitRel signSubgroup Circle)) signSubgroup :=
  transport (MulEquiv.refl signSubgroup) (circleTranslation c)
    (circle_translation_equivariant c) sign_quotient_cover

def translated_circle_quotient (c : Circle) :=
  quotientHomeomorph (MulEquiv.refl signSubgroup) (circleTranslation c)
    (circle_translation_equivariant c)

@[simp] theorem translated_circle_quotient_mk (c x : Circle) :
    translated_circle_quotient c (Quotient.mk _ x) = Quotient.mk _ (c * x) := rfl

#print axioms EquivariantOrbitQuotient.quotientHomeomorph
#print axioms EquivariantOrbitQuotient.quotientHomeomorph_mk
#print axioms EquivariantOrbitQuotient.fiberHomeomorph
#print axioms EquivariantOrbitQuotient.fiberHomeomorph_apply
#print axioms EquivariantOrbitQuotient.fiber_card
#print axioms translated_circle_quotient_mk
#print axioms sign_quotient_cover
#print axioms translated_circle_cover
#print axioms translated_circle_quotient
#print axioms transport
#print axioms covering
end ConstructionTargets.EquivariantCoverTransport

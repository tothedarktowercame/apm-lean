import Mathlib.Topology.Covering.Basic
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
open Set
namespace ConstructionTargets.LiteralCoveringPullback
variable {E B X : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
variable (p : E → B) (f : X → B)
abbrev Pullback := {z : X × E // f z.1 = p z.2}
def projection (z : Pullback p f) : X := z.1.1

def fiberEquiv (x : X) : (projection p f ⁻¹' {x}) ≃ (p ⁻¹' {f x}) where
  toFun z := ⟨z.1.1.2, by change p z.1.1.2 = f x; rw [← z.1.2, show z.1.1.1 = x from z.2]⟩
  invFun e := ⟨⟨(x, e.1), e.2.symm⟩, rfl⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext z.2.symm rfl
  right_inv e := rfl

omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X] in
@[simp] theorem fiberEquiv_apply_val (x : X) (z : projection p f ⁻¹' {x}) :
    (fiberEquiv p f x z).1 = z.1.1.2 := rfl
omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X] in
@[simp] theorem fiberEquiv_symm_apply_val (x : X) (e : p ⁻¹' {f x}) :
    ((fiberEquiv p f x).symm e).1.1 = (x, e.1) := rfl

omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X] in
theorem fiber_card (x : X) : Nat.card (projection p f ⁻¹' {x}) = Nat.card (p ⁻¹' {f x}) :=
  Nat.card_congr (fiberEquiv p f x)

variable {p f}
/-- Pull back an actual evenly covered neighborhood, including an empty sheet space. -/
def localHomeomorph {I : Type*} [TopologicalSpace I] {U : Set B}
    (H : p ⁻¹' U ≃ₜ U × I) (hH : ∀ e, (H e).1.1 = p e)
    (hf : Continuous f) :
    (projection p f ⁻¹' (f ⁻¹' U)) ≃ₜ (f ⁻¹' U) × I where
  toFun z := (⟨z.1.1.1, z.2⟩, (H ⟨z.1.1.2, by change p z.1.1.2 ∈ U; rw [← z.1.2]; exact z.2⟩).2)
  invFun xi := ⟨⟨(xi.1.1, (H.symm (⟨f xi.1.1, xi.1.2⟩, xi.2)).1), by
    have h := hH (H.symm (⟨f xi.1.1, xi.1.2⟩, xi.2))
    simpa using h⟩, xi.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    have h : (⟨f z.1.1.1, z.2⟩, (H ⟨z.1.1.2, by change p z.1.1.2 ∈ U; rw [← z.1.2]; exact z.2⟩).2) =
        H ⟨z.1.1.2, by change p z.1.1.2 ∈ U; rw [← z.1.2]; exact z.2⟩ := by
      apply Prod.ext
      · apply Subtype.ext
        exact z.1.2.trans (hH ⟨z.1.1.2, by change p z.1.1.2 ∈ U; rw [← z.1.2]; exact z.2⟩).symm
      · rfl
    simp only [h, Homeomorph.symm_apply_apply]
  right_inv xi := by
    refine Prod.ext ?_ ?_
    · rfl
    change (H (H.symm (⟨f xi.1.1, xi.1.2⟩, xi.2))).2 = xi.2
    exact congrArg Prod.snd (H.apply_symm_apply (⟨f xi.1.1, xi.1.2⟩, xi.2))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem localHomeomorph_fst {I : Type*} [TopologicalSpace I] {U : Set B}
    (H : p ⁻¹' U ≃ₜ U × I) (hH : ∀ e, (H e).1.1 = p e)
    (hf : Continuous f) (z : projection p f ⁻¹' (f ⁻¹' U)) :
    (localHomeomorph H hH hf z).1.1 = projection p f z := rfl

@[simp] theorem localHomeomorph_symm_val {I : Type*} [TopologicalSpace I] {U : Set B}
    (H : p ⁻¹' U ≃ₜ U × I) (hH : ∀ e, (H e).1.1 = p e)
    (hf : Continuous f) (xi : (f ⁻¹' U) × I) :
    ((localHomeomorph H hH hf).symm xi).1.1 =
      (xi.1.1, (H.symm (⟨f xi.1.1, xi.1.2⟩, xi.2)).1) := rfl

/-- Actual local product coordinates around each base point. -/
theorem exists_localHomeomorph (hp : IsCoveringMap p) (hf : Continuous f) (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
      ∃ H : (projection p f ⁻¹' U) ≃ₜ U × (p ⁻¹' {f x}),
        ∀ z, (H z).1.1 = projection p f z := by
  obtain ⟨_, U, hx, hU, _, H, hH⟩ := hp (f x)
  exact ⟨f ⁻¹' U, hx, hU.preimage hf, localHomeomorph H hH hf, fun _ => rfl⟩

theorem covering (hp : IsCoveringMap p) (hf : Continuous f) :
    IsCoveringMap (projection p f) := by
  intro x
  obtain ⟨hI, U, hx, hU, _, H, hH⟩ := hp (f x)
  haveI := hI
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := p ⁻¹' {f x})
  refine ⟨hI, f ⁻¹' U, hx, hU.preimage hf, ?_, localHomeomorph H hH hf, fun _ => rfl⟩
  exact (hU.preimage hf).preimage (continuous_fst.comp continuous_subtype_val)
end ConstructionTargets.LiteralCoveringPullback

#print axioms ConstructionTargets.LiteralCoveringPullback.fiberEquiv
#print axioms ConstructionTargets.LiteralCoveringPullback.fiberEquiv_apply_val
#print axioms ConstructionTargets.LiteralCoveringPullback.fiberEquiv_symm_apply_val
#print axioms ConstructionTargets.LiteralCoveringPullback.fiber_card
#print axioms ConstructionTargets.LiteralCoveringPullback.localHomeomorph
#print axioms ConstructionTargets.LiteralCoveringPullback.localHomeomorph_fst
#print axioms ConstructionTargets.LiteralCoveringPullback.localHomeomorph_symm_val
#print axioms ConstructionTargets.LiteralCoveringPullback.exists_localHomeomorph
#print axioms ConstructionTargets.LiteralCoveringPullback.covering

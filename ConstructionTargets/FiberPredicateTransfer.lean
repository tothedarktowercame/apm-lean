import ConstructionTargets.OpenPartialHomeomorphFiberTransfer
open Set
noncomputable section
namespace ConstructionTargets.FiberPredicateTransfer
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y) (P : X → Prop) (Q : Y → Prop)
  (V : Set Y) (hV : IsOpen V) (hVt : V ⊆ e.target)
  (heq : ∀ y ∈ V, Q y ↔ P (e.symm y))
  (x : {u // P u}) (hx : x.val ∈ e.source) (hxV : e x.val ∈ V)
private def predHomeo (P : X → Prop) : {u // P u} ≃ₜ {u // P u = True} :=
  Homeomorph.setCongr (by ext u; simp)

def transfer : OpenPartialHomeomorph {u // P u} {v // Q v} :=
  (predHomeo P).toOpenPartialHomeomorph.trans
    ((OpenPartialHomeomorphFiberTransfer.transfer e P Q True V hV hVt
      (fun y hy => propext (heq y hy)) ((predHomeo P) x) hx hxV).trans
      (predHomeo Q).symm.toOpenPartialHomeomorph)

theorem source_eq : (transfer e P Q V hV hVt heq x hx hxV).source =
    {u | u.val ∈ e.source ∧ e u.val ∈ V} := by
  ext u
  simp [transfer, predHomeo, OpenPartialHomeomorphFiberTransfer.source_eq]
  rfl
theorem target_eq : (transfer e P Q V hV hVt heq x hx hxV).target =
    Subtype.val ⁻¹' V := by
  ext v
  simp [transfer, predHomeo, OpenPartialHomeomorphFiberTransfer.target_eq]
  rfl
theorem center_mem : x ∈ (transfer e P Q V hV hVt heq x hx hxV).source := by
  rw [source_eq]
  exact ⟨hx,hxV⟩
theorem forward_eq (u : {u // P u})
    (hu : u ∈ (transfer e P Q V hV hVt heq x hx hxV).source) :
    ((transfer e P Q V hV hVt heq x hx hxV) u).val = e u.val := by
  rw [source_eq] at hu
  exact OpenPartialHomeomorphFiberTransfer.forward_eq e P Q True V hV hVt
    (fun y hy => propext (heq y hy)) ((predHomeo P) x) hx hxV ((predHomeo P) u) hu
theorem backward_eq (v : {v // Q v}) (hv : v.val ∈ V) :
    ((transfer e P Q V hV hVt heq x hx hxV).symm v).val = e.symm v.val := by
  exact OpenPartialHomeomorphFiberTransfer.backward_eq e P Q True V hV hVt
    (fun y hy => propext (heq y hy)) ((predHomeo P) x) hx hxV ((predHomeo Q) v) hv
#print axioms transfer
#print axioms source_eq
#print axioms target_eq
#print axioms center_mem
#print axioms forward_eq
#print axioms backward_eq
end ConstructionTargets.FiberPredicateTransfer

import Mathlib.Topology.OpenPartialHomeomorph.Constructions
open Set
noncomputable section
namespace ConstructionTargets.OpenPartialHomeomorphFiberTransfer
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
 (e : OpenPartialHomeomorph X Y) (f : X → Z) (g : Y → Z) (c : Z)
 (V : Set Y) (hV : IsOpen V) (hVt : V ⊆ e.target)
 (heq : ∀ y ∈ V, g y = f (e.symm y))
 (x : {x // f x = c}) (hx : x.val ∈ e.source) (hxV : e x.val ∈ V)
include heq in
private lemma forward_mem (u : {x // f x = c}) (hu : u.val ∈ e.source ∧ e u.val ∈ V) :
    g (e u.val) = c := by
  rw [heq _ hu.2, e.left_inv hu.1, u.property]
include heq in
private lemma backward_mem (v : {y // g y = c}) (hv : v.val ∈ V) : f (e.symm v.val) = c :=
  (heq _ hv).symm.trans v.property

def transfer : OpenPartialHomeomorph {x // f x = c} {y // g y = c} := by
  classical
  let y : {y // g y = c} := ⟨e x.val, forward_mem e f g c V heq x ⟨hx,hxV⟩⟩
  let S : Set {x // f x = c} := {u | u.val ∈ e.source ∧ e u.val ∈ V}
  let fw : {x // f x = c} → {y // g y = c} := fun u =>
    if h : u ∈ S then ⟨e u.val, forward_mem e f g c V heq u h⟩ else y
  let bw : {y // g y = c} → {x // f x = c} := fun v =>
    if h : v.val ∈ V then ⟨e.symm v.val, backward_mem e f g c V heq v h⟩ else x
  have hfw (u) (hu : u ∈ S) : (fw u).val = e u.val := by simp [fw,hu]
  have hbw (v) (hv : v.val ∈ V) : (bw v).val = e.symm v.val := by simp [bw,hv]
  refine {
    toFun := fw
    invFun := bw
    source := S
    target := (Subtype.val ⁻¹' V)
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := ?_
    open_target := hV.preimage continuous_subtype_val
    continuousOn_toFun := ?_
    continuousOn_invFun := ?_ }

  · intro u hu
    change (fw u).val ∈ V
    rw [hfw u hu]
    exact hu.2
  · intro v hv
    change (bw v).val ∈ e.source ∧ e (bw v).val ∈ V
    rw [hbw v hv]
    exact ⟨e.map_target (hVt hv), by simpa [e.right_inv (hVt hv)] using hv⟩
  · intro u hu
    apply Subtype.ext
    have hv : (fw u).val ∈ V := by rw [hfw u hu]; exact hu.2
    rw [hbw _ hv, hfw u hu, e.left_inv hu.1]
  · intro v hv
    apply Subtype.ext
    have hu : bw v ∈ S := by
      change (bw v).val ∈ e.source ∧ e (bw v).val ∈ V
      rw [hbw v hv]
      exact ⟨e.map_target (hVt hv), by simpa [e.right_inv (hVt hv)] using hv⟩
    rw [hfw _ hu, hbw v hv, e.right_inv (hVt hv)]
  · exact (e.isOpen_inter_preimage hV).preimage continuous_subtype_val
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply ((e.continuousOn.comp continuous_subtype_val.continuousOn
      (fun u hu => hu.1))).congr
    exact hfw
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply ((e.symm.continuousOn.comp continuous_subtype_val.continuousOn
      (fun v hv => hVt hv))).congr
    exact hbw

 theorem source_eq : (transfer e f g c V hV hVt heq x hx hxV).source =
    {u | u.val ∈ e.source ∧ e u.val ∈ V} := rfl
 theorem target_eq : (transfer e f g c V hV hVt heq x hx hxV).target = Subtype.val ⁻¹' V := rfl
 theorem center_mem : x ∈ (transfer e f g c V hV hVt heq x hx hxV).source := ⟨hx,hxV⟩
 theorem forward_eq (u : {x // f x = c}) (hu : u ∈ (transfer e f g c V hV hVt heq x hx hxV).source) :
    ((transfer e f g c V hV hVt heq x hx hxV) u).val = e u.val := by
  have hu' : u.val ∈ e.source ∧ e u.val ∈ V := hu
  simp [transfer, hu']
 theorem backward_eq (v : {y // g y = c}) (hv : v.val ∈ V) :
    ((transfer e f g c V hV hVt heq x hx hxV).symm v).val = e.symm v.val := by
  simp [transfer,hv]
#print axioms transfer
#print axioms source_eq
#print axioms target_eq
#print axioms center_mem
#print axioms forward_eq
#print axioms backward_eq
end ConstructionTargets.OpenPartialHomeomorphFiberTransfer

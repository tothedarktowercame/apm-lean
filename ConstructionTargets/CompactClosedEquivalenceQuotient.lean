import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Proper.Basic

open Set Topology

namespace ConstructionTargets

theorem exists_disjoint_open_saturated_of_isClosed_setoid
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2})
    {x y : X} (hxy : ¬s.r x y) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      Disjoint U V ∧
      (∀ a, a ∈ U → ∀ b, s.r a b → b ∈ U) ∧
      (∀ a, a ∈ V → ∀ b, s.r a b → b ∈ V) := by
  let R : Set (X × X) := {p | s.r p.1 p.2}
  let Cx : Set X := {z | s.r x z}
  let Cy : Set X := {z | s.r y z}
  have hCx : IsClosed Cx := by
    exact hs.preimage (continuous_const.prodMk continuous_id)
  have hCy : IsClosed Cy := by
    exact hs.preimage (continuous_const.prodMk continuous_id)
  have hclasses : Cx ×ˢ Cy ⊆ Rᶜ := by
    rintro ⟨a, b⟩ ⟨hxa, hyb⟩ hab
    exact hxy (s.trans hxa (s.trans hab (s.symm hyb)))
  obtain ⟨O, P, hO, hP, hCxO, hCyP, hOP⟩ :=
    generalized_tube_lemma hCx.isCompact hCy.isCompact
      (isOpen_compl_iff.mpr hs) hclasses
  let badO : Set X := Prod.fst '' (R ∩ (Set.univ ×ˢ Oᶜ))
  let badP : Set X := Prod.fst '' (R ∩ (Set.univ ×ˢ Pᶜ))
  have hbadO : IsClosed badO := by
    apply isClosedMap_fst_of_compactSpace
    exact hs.inter (isClosed_univ.prod (isClosed_compl_iff.mpr hO))
  have hbadP : IsClosed badP := by
    apply isClosedMap_fst_of_compactSpace
    exact hs.inter (isClosed_univ.prod (isClosed_compl_iff.mpr hP))
  refine ⟨badOᶜ, badPᶜ, hbadO.isOpen_compl, hbadP.isOpen_compl, ?_, ?_, ?_, ?_, ?_⟩
  · intro hx
    rcases hx with ⟨p, ⟨hpR, -, hpO⟩, hpx⟩
    subst hpx
    exact hpO (hCxO hpR)
  · intro hy
    rcases hy with ⟨p, ⟨hpR, -, hpP⟩, hpy⟩
    subst hpy
    exact hpP (hCyP hpR)
  · rw [Set.disjoint_left]
    intro z hzO hzP
    have hz_mem_O : z ∈ O := by
      by_contra hz
      exact hzO ⟨(z, z), ⟨s.refl z, Set.mem_univ z, hz⟩, rfl⟩
    have hz_mem_P : z ∈ P := by
      by_contra hz
      exact hzP ⟨(z, z), ⟨s.refl z, Set.mem_univ z, hz⟩, rfl⟩
    exact (hOP ⟨hz_mem_O, hz_mem_P⟩) (show (z, z) ∈ R from s.refl z)
  · intro a ha b hab hb
    rcases hb with ⟨p, ⟨hpc, -, hpO⟩, hpb⟩
    subst hpb
    exact ha ⟨(a, p.2), ⟨s.trans hab hpc, Set.mem_univ a, hpO⟩, rfl⟩
  · intro a ha b hab hb
    rcases hb with ⟨p, ⟨hpc, -, hpP⟩, hpb⟩
    subst hpb
    exact ha ⟨(a, p.2), ⟨s.trans hab hpc, Set.mem_univ a, hpP⟩, rfl⟩

theorem compact_closed_equivalence_quotient_t2
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Setoid X) (hs : IsClosed {p : X × X | s.r p.1 p.2}) :
    T2Space (Quotient s) := by
  rw [t2Space_iff]
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      have hxy : ¬ s.r x y := by
        intro h
        exact hqr (Quotient.sound h)
      obtain ⟨U, V, hU, hV, hx, hy, hUV, hUs, hVs⟩ :=
        exists_disjoint_open_saturated_of_isClosed_setoid s hs hxy
      refine ⟨Quotient.mk' '' U, Quotient.mk' '' V, ?_, ?_, ?_, ?_, ?_⟩
      · rw [isOpen_coinduced]
        have heq : Quotient.mk' ⁻¹' (Quotient.mk' '' U) = U := by
          ext z
          constructor
          · rintro ⟨a, ha, haz⟩
            exact hUs a ha z (Quotient.eq'.mp haz)
          · intro hz
            exact ⟨z, hz, rfl⟩
        rw [heq]
        exact hU
      · rw [isOpen_coinduced]
        have heq : Quotient.mk' ⁻¹' (Quotient.mk' '' V) = V := by
          ext z
          constructor
          · rintro ⟨a, ha, haz⟩
            exact hVs a ha z (Quotient.eq'.mp haz)
          · intro hz
            exact ⟨z, hz, rfl⟩
        rw [heq]
        exact hV
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, rfl⟩
      · rw [Set.disjoint_left]
        rintro q ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        have hr : s.r b a := Quotient.eq'.mp hab
        exact Set.disjoint_left.1 hUV ha (hVs b hb a hr)

#print axioms exists_disjoint_open_saturated_of_isClosed_setoid
#print axioms compact_closed_equivalence_quotient_t2

end ConstructionTargets

import Mathlib
import ConstructionTargets.CoveringDegree

/-! # t98J02: separation and lifts of simple closed curves -/

open Set ConstructionTargets.CoveringDegree
noncomputable section
namespace T98J02

structure ClosedSurface where
  carrier : Type
  topology : TopologicalSpace carrier
  charts : @ChartedSpace (EuclideanSpace ℝ (Fin 2)) _ carrier topology
  compact : @CompactSpace carrier topology
  hausdorff : @T2Space carrier topology
  secondCountable : @SecondCountableTopology carrier topology
  connected : @ConnectedSpace carrier topology

attribute [instance] ClosedSurface.topology ClosedSurface.charts
  ClosedSurface.compact ClosedSurface.hausdorff ClosedSurface.secondCountable
  ClosedSurface.connected

/-- A degree-one lift, expressed through parametrizations of both image circles. -/
def IsCurveLift {F E : Type} [TopologicalSpace F] [TopologicalSpace E]
    (p : E → F) (c : C(Circle, F)) (l : C(Circle, E)) : Prop :=
  Topology.IsEmbedding c ∧ Topology.IsEmbedding l ∧ ∀ z, p (l z) = c z

def Nonseparating {F : Type} [TopologicalSpace F] (c : C(Circle, F)) : Prop :=
  IsPreconnected (range c)ᶜ

/-- A concrete separation certificate for a subset: two disjoint relatively
open pieces cover it, and both pieces meet it. -/
def SeparatesSet {X : Type} [TopologicalSpace X]
    (s U V : Set X) : Prop :=
  IsOpen (s ∩ U) ∧ IsOpen (s ∩ V) ∧
    s ⊆ U ∪ V ∧ Disjoint (s ∩ U) (s ∩ V) ∧
    (s ∩ U).Nonempty ∧ (s ∩ V).Nonempty

end T98J02
open T98J02

/-- LIBRARY: explicit torus/trivial-double-cover model, including the elementary
open-set certificate which witnesses separation of the lifted complement. -/
-- BEGIN SEAT AREA
noncomputable def t98J02_disconnected_trivialCover_model_aux_charts :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (Circle × Circle) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
    (EuclideanSpace.finAddEquivProd (n := 1) (m := 1)).symm.toHomeomorph.isOpenEmbedding.singletonChartedSpace
  letI : ChartedSpace
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (Circle × Circle) :=
    prodChartedSpace _ Circle _ Circle
  exact ChartedSpace.comp _ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) _

noncomputable def t98J02_disconnected_trivialCover_model_aux_surface : ClosedSurface where
  carrier := Circle × Circle
  topology := inferInstance
  charts := t98J02_disconnected_trivialCover_model_aux_charts
  compact := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  connected := by
    letI : PathConnectedSpace Circle := isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (E := ℂ) (Complex.rank_real_complex ▸ by norm_num)
        0 (r := 1) (by norm_num))
    infer_instance

theorem t98J02_disconnected_trivialCover_model :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E))
      (U V : Set E),
      0 < n ∧ ¬ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      Nonseparating c ∧ SeparatesSet (range l)ᶜ U V := by
  let F := t98J02_disconnected_trivialCover_model_aux_surface
  let E := Bundle.TotalSpace (Fin 2) (Bundle.Trivial F.carrier (Fin 2))
  let p : E → F.carrier := Bundle.TotalSpace.proj
  let c : C(Circle, F.carrier) :=
    ⟨fun z ↦ (z, (1 : Circle)), continuous_id.prodMk continuous_const⟩
  let l : C(Circle, E) := ⟨fun z ↦ ⟨(z, (1 : Circle)), (0 : Fin 2)⟩, by
    exact (Bundle.Trivial.homeomorphProd F.carrier (Fin 2)).symm.continuous.comp
      ((continuous_id.prodMk continuous_const).prodMk continuous_const)⟩
  let U : Set E := {x | x.snd = (0 : Fin 2)}
  let V : Set E := {x | x.snd = (1 : Fin 2)}
  have hcover : IsKSheetedCover p 2 := by
    refine ⟨FiberBundle.isCoveringMap, ?_, ?_⟩
    · intro b
      exact Finite.of_injective (fun x : {e : E // p e = b} ↦ x.1.snd)
        (by rintro ⟨⟨b₁, i₁⟩, hb₁⟩ ⟨⟨b₂, i₂⟩, hb₂⟩ hi
            apply Subtype.ext
            apply Bundle.TotalSpace.ext
            · exact hb₁.trans hb₂.symm
            · exact heq_of_eq hi)
    · intro b
      let e : {x : E // p x = b} ≃ Fin 2 :=
        { toFun := fun x ↦ x.1.snd
          invFun := fun i ↦ ⟨⟨b, i⟩, rfl⟩
          left_inv := by
            rintro ⟨⟨b', i⟩, hb⟩
            apply Subtype.ext
            apply Bundle.TotalSpace.ext
            · simpa [p] using hb.symm
            · rfl
          right_inv := by intro i; rfl }
      rw [Nat.card_congr e]
      simp
  have hcemb : Topology.IsEmbedding c := by
    exact isEmbedding_prodMkLeft (1 : Circle)
  have hlemb : Topology.IsEmbedding l := by
    exact (Bundle.Trivial.homeomorphProd F.carrier (Fin 2)).symm.isEmbedding.comp
      ((isEmbedding_prodMkLeft (0 : Fin 2)).comp hcemb)
  have hcpre : Nonseparating c := by
    unfold Nonseparating
    have hcircle : IsPreconnected (Set.univ : Set Circle) := by
      letI : PathConnectedSpace Circle := isPathConnected_iff_pathConnectedSpace.mp
        (isPathConnected_sphere (E := ℂ) (Complex.rank_real_complex ▸ by norm_num)
          0 (r := 1) (by norm_num))
      exact isPreconnected_univ
    have hpunc : IsPreconnected ({(1 : Circle)}ᶜ : Set Circle) := by
      change IsPreconnected ({(⟨(1 : ℂ), by norm_num⟩ : Circle)}ᶜ : Set Circle)
      have h := isPreconnected_range
        (continuousOn_univ.mp (by simpa using
          (stereographic (v := (1 : ℂ)) (by norm_num)).continuousOn_symm))
      rw [range_stereographic_symm] at h
      exact h
    rw [show (range c)ᶜ = (Set.univ : Set Circle) ×ˢ ({(1 : Circle)}ᶜ) by
      ext x
      rcases x with ⟨x, y⟩
      simp only [mem_compl_iff, mem_range, c, ContinuousMap.coe_mk, mem_prod,
        mem_univ, true_and, mem_singleton_iff]
      change (¬ ∃ z : Circle, (z, (1 : Circle)) = (x, y)) ↔
        (True ∧ y ≠ 1)
      simp only [true_and]
      constructor
      · intro h hy
        exact h ⟨x, Prod.ext rfl hy.symm⟩
      · intro hy ⟨z, hz⟩
        exact hy (congrArg Prod.snd hz).symm]
    exact hcircle.prod hpunc
  have hopenU : IsOpen U := by
    change IsOpen ((fun x : E ↦ x.snd) ⁻¹' {(0 : Fin 2)})
    exact (Bundle.Trivial.homeomorphProd F.carrier (Fin 2)).continuous.snd.isOpen_preimage _
      (isOpen_discrete _)
  have hopenV : IsOpen V := by
    change IsOpen ((fun x : E ↦ x.snd) ⁻¹' {(1 : Fin 2)})
    exact (Bundle.Trivial.homeomorphProd F.carrier (Fin 2)).continuous.snd.isOpen_preimage _
      (isOpen_discrete _)
  have hclosedRange : IsClosed (range l) := by
    rw [show range l = {x : E | x.proj.2 = (1 : Circle) ∧ x.snd = (0 : Fin 2)} by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨hx, hi⟩
        refine ⟨x.proj.1, ?_⟩
        apply Bundle.TotalSpace.ext
        · exact Prod.ext rfl hx.symm
        · exact heq_of_eq hi.symm]
    exact (isClosed_singleton.preimage
      (Bundle.Trivial.homeomorphProd F.carrier (Fin 2)).continuous.fst.snd).inter
      (isClosed_singleton.preimage
        (Bundle.Trivial.homeomorphProd F.carrier (Fin 2)).continuous.snd)
  have hopenComp : IsOpen (range l)ᶜ := hclosedRange.isOpen_compl
  refine ⟨F, E, inferInstance, 2, p, c, l, U, V, by norm_num, ?_, hcover,
    ⟨hcemb, hlemb, by intro z; rfl⟩, hcpre, ?_⟩
  · intro h
    haveI := h
    have huv : IsPreconnected (Set.univ : Set E) := isPreconnected_univ
    have hu : (U : Set E).Nonempty := ⟨⟨((1 : Circle), (1 : Circle)), 0⟩, rfl⟩
    have hv : (V : Set E).Nonempty := ⟨⟨((1 : Circle), (1 : Circle)), 1⟩, rfl⟩
    obtain ⟨x, -, hxU, hxV⟩ := huv U V hopenU hopenV (by
      intro x
      have hi : x.snd = 0 ∨ x.snd = 1 := by
        generalize x.snd = i
        fin_cases i <;> simp
      simpa [U, V] using hi)
      (by simpa using hu) (by simpa using hv)
    exact Fin.zero_ne_one (hxU.symm.trans hxV)
  · refine ⟨hopenComp.inter hopenU, hopenComp.inter hopenV, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hi : x.snd = 0 ∨ x.snd = 1 := by
        generalize x.snd = i
        fin_cases i <;> simp
      simpa [U, V] using hi
    · exact Set.disjoint_left.2 (by
        intro x hxU hxV
        exact Fin.zero_ne_one (hxU.2.symm.trans hxV.2))
    · refine ⟨⟨((1 : Circle), (⟨-1, by
          simp [Submonoid.unitSphere, mem_sphere_zero_iff_norm]⟩ : Circle)), 0⟩, ?_, rfl⟩
      intro h
      rcases h with ⟨z, hz⟩
      have := congrArg (fun q : E ↦ q.proj.2) hz
      change (1 : Circle) = ⟨-1, _⟩ at this
      have hval := congrArg Subtype.val this
      norm_num at hval
    · refine ⟨⟨((1 : Circle), (1 : Circle)), 1⟩, ?_, rfl⟩
      intro h
      rcases h with ⟨z, hz⟩
      have := congrArg (fun q : E ↦ q.snd) hz
      change (0 : Fin 2) = 1 at this
      exact Fin.zero_ne_one this
-- END SEAT AREA

/-- A separation certificate rules out preconnectedness.  This is independent
of either surface construction. -/
theorem t98J02_separatesSet_not_preconnected
    {X : Type} [TopologicalSpace X] {s U V : Set X}
    (h : SeparatesSet s U V) : ¬ IsPreconnected s := by
  sorry

/-- LIBRARY: explicit connected double-cover model of a genus-two surface.
Path-connectedness of the lifted complement is recorded as the model's useful
point-set certificate. -/
theorem t98J02_connected_doubleCover_model :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      ¬ Nonseparating c ∧ IsPathConnected (range l)ᶜ := by
  sorry

/-- Path-connectedness of the complement implies the required
preconnectedness.  This is independent of either surface construction. -/
theorem t98J02_pathConnected_complement_nonseparating
    {E : Type} [TopologicalSpace E] (l : C(Circle, E))
    (h : IsPathConnected (range l)ᶜ) : Nonseparating l := by
  sorry

/-- LIBRARY: a degree-one lift of a nonseparating embedded circle through a
connected finite cover of closed surfaces remains nonseparating. -/
theorem t98J02_nonseparating_lift_connectedCover :
    ∀ (F : ClosedSurface) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      IsKSheetedCover p n → IsCurveLift p c l →
      Nonseparating c → Nonseparating l := by
  sorry

/-- LIBRARY: the trivial double cover of a torus supplies the counterexample
when disconnected covering spaces are allowed. -/
theorem t98J02_disconnected_trivialCover_counterexample :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ¬ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      Nonseparating c ∧ ¬ Nonseparating l := by
  obtain ⟨F, E, inst, n, p, c, l, U, V, hn, hE, hp, hl, hc, hsep⟩ :=
    t98J02_disconnected_trivialCover_model
  letI : TopologicalSpace E := inst
  exact ⟨F, E, inst, n, p, c, l, hn, hE, hp, hl, hc,
    t98J02_separatesSet_not_preconnected hsep⟩

/-- LIBRARY: a connected double cover of a genus-two surface can have a
nonseparating degree-one lift of a separating circle. -/
theorem t98J02_connected_doubleCover_counterexample :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      ¬ Nonseparating c ∧ Nonseparating l := by
  obtain ⟨F, E, inst, n, p, c, l, hn, hE, hp, hl, hc, hpath⟩ :=
    t98J02_connected_doubleCover_model
  letI : TopologicalSpace E := inst
  exact ⟨F, E, inst, n, p, c, l, hn, hE, hp, hl, hc,
    t98J02_pathConnected_complement_nonseparating l hpath⟩

theorem apm_t98j02 :
    (∀ (F : ClosedSurface) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      IsKSheetedCover p n → IsCurveLift p c l →
      Nonseparating c → Nonseparating l) ∧
    (∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ¬ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      Nonseparating c ∧ ¬ Nonseparating l) ∧
    (∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      ¬ Nonseparating c ∧ Nonseparating l) := by
  exact ⟨t98J02_nonseparating_lift_connectedCover,
    t98J02_disconnected_trivialCover_counterexample,
    t98J02_connected_doubleCover_counterexample⟩

#print axioms apm_t98j02

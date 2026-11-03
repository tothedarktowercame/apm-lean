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

/-- A separation certificate rules out preconnectedness.  This is independent
of either surface construction. -/
theorem t98J02_separatesSet_not_preconnected
    {X : Type} [TopologicalSpace X] {s U V : Set X}
    (h : SeparatesSet s U V) : ¬ IsPreconnected s := by
  rintro hs
  obtain ⟨hU, hV, hcover, hdisj, hU_ne, hV_ne⟩ := h
  have hcover' : s ⊆ (s ∩ U) ∪ (s ∩ V) := by
    intro x hxs
    rcases hcover hxs with hxU | hxV
    · exact Or.inl ⟨hxs, hxU⟩
    · exact Or.inr ⟨hxs, hxV⟩
  have hU_ne' : (s ∩ (s ∩ U)).Nonempty := by
    rcases hU_ne with ⟨x, hxs, hxU⟩
    exact ⟨x, hxs, hxs, hxU⟩
  have hV_ne' : (s ∩ (s ∩ V)).Nonempty := by
    rcases hV_ne with ⟨x, hxs, hxV⟩
    exact ⟨x, hxs, hxs, hxV⟩
  rcases hs (s ∩ U) (s ∩ V) hU hV hcover' hU_ne' hV_ne' with
    ⟨x, _, hxU, hxV⟩
  exact Set.disjoint_left.1 hdisj hxU hxV

open Topology Filter

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- A plane has no continuous injection to the line: the difference of antipodal values on a
circle changes sign, so it vanishes somewhere. -/
lemma t98J02_no_inj_plane (θ : E2 → ℝ) (a : E2) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn θ (Metric.sphere a r)) (hi : Set.InjOn θ (Metric.sphere a r)) : False := by
  let v : ℝ → E2 := fun t => !₂[Real.cos t, Real.sin t]
  have hv : Continuous v := by
    have h : v = fun t => (WithLp.toLp 2 ![Real.cos t, Real.sin t] : E2) := rfl
    rw [h]
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hvn : ∀ t, ‖v t‖ = 1 := by
    intro t
    simp [v, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hq : ∀ (s : ℝ) t, |s| = 1 → a + (s * r) • v t ∈ Metric.sphere a r := by
    intro s t hs
    simp [norm_smul, hvn, abs_of_pos hr, hs]
  let f : ℝ → ℝ := fun t => θ (a + ((1 : ℝ) * r) • v t)
  let g : ℝ → ℝ := fun t => θ (a + ((-1 : ℝ) * r) • v t)
  have hf : ContinuousOn f (Icc 0 Real.pi) :=
    hc.comp (by fun_prop) (fun t _ => hq 1 t (by simp))
  have hg : ContinuousOn g (Icc 0 Real.pi) :=
    hc.comp (by fun_prop) (fun t _ => hq (-1) t (by simp))
  have hv0 : v Real.pi = -v 0 := by
    ext i; fin_cases i <;> simp [v]
  have e1 : f Real.pi = g 0 := by simp [f, g, hv0]
  have e2 : g Real.pi = f 0 := by simp [f, g, hv0]
  have h0 : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hp : Real.pi ∈ Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
  have : ∃ t ∈ Icc 0 Real.pi, f t = g t := by
    rcases le_total (f 0) (g 0) with h | h
    · exact isPreconnected_Icc.intermediate_value₂ h0 hp hf hg h (by rw [e1, e2]; exact h)
    · obtain ⟨t, ht, e⟩ := isPreconnected_Icc.intermediate_value₂ h0 hp hg hf h
        (by rw [e1, e2]; exact h)
      exact ⟨t, ht, e.symm⟩
  obtain ⟨t, -, e⟩ := this
  have := hi (hq 1 t (by simp)) (hq (-1) t (by simp)) e
  have h2 : (2 * r) • v t = 0 := by
    have h3 : ((1 : ℝ) * r) • v t = ((-1 : ℝ) * r) • v t := add_left_cancel this
    have : (2 * r) • v t = ((1 : ℝ) * r) • v t - ((-1 : ℝ) * r) • v t := by
      rw [← sub_smul]; ring_nf
    rw [this, h3, sub_self]
  have h4 := congrArg norm h2
  simp [norm_smul, hvn, abs_of_pos hr] at h4
  exact hr.ne' h4

/-- An embedded circle in a surface has empty interior. -/
lemma t98J02_interior_range_eq_empty {F : Type} [TopologicalSpace F] [T2Space F]
    [ChartedSpace E2 F] (c : C(Circle, F)) (hc : IsEmbedding c) :
    interior (range c) = ∅ := by
  by_contra hne
  obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hne
  let φ := chartAt E2 b
  have hbs : b ∈ φ.source := mem_chart_source E2 b
  let a := φ b
  have hat : a ∈ φ.target := φ.map_source hbs
  have hsa : φ.symm a = b := φ.left_inv hbs
  let O : Set E2 := φ.target ∩ φ.symm ⁻¹' interior (range c)
  have hO : IsOpen O := φ.symm.isOpen_inter_preimage isOpen_interior
  have haO : a ∈ O := ⟨hat, by simpa [hsa] using hb⟩
  have hsub : ∀ x ∈ O, φ.symm x ∈ range c := fun x hx => interior_subset hx.2
  haveI : Nonempty Circle := ⟨1⟩
  let g : E2 → Circle := fun x => Function.invFun c (φ.symm x)
  have hcg : ∀ x ∈ O, c (g x) = φ.symm x := fun x hx => Function.invFun_eq (hsub x hx)
  have hgc : ContinuousOn g O := by
    rw [hc.isInducing.continuousOn_iff]
    exact (φ.symm.continuousOn.mono inter_subset_left).congr (fun x hx => hcg x hx)
  have hgi : Set.InjOn g O := by
    intro x hx y hy e
    apply φ.symm.injOn hx.1 hy.1
    rw [← hcg x hx, ← hcg y hy, e]
  let h : E2 → ℂ := fun x => (g x : ℂ) * ((g a)⁻¹ : Circle)
  have hh : ContinuousOn h O := by
    apply ContinuousOn.mul _ continuousOn_const
    exact (continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp_continuousOn hgc
  have hha : h a = 1 := by simp [h]
  have hnear : ∀ᶠ x in 𝓝 a, x ∈ O ∧ h x ∈ Complex.slitPlane := by
    have h1 : ∀ᶠ x in 𝓝 a, x ∈ O := hO.mem_nhds haO
    have h2 : ContinuousAt h a := hh.continuousAt (hO.mem_nhds haO)
    have h3 := h2.eventually_mem (Complex.isOpen_slitPlane.mem_nhds (by simp [hha]))
    exact h1.and h3
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hs : Metric.sphere a (r / 2) ⊆ Metric.ball a r :=
    Metric.sphere_subset_ball (by linarith)
  refine t98J02_no_inj_plane (fun x => Complex.arg (h x)) a (r / 2) (by linarith) ?_ ?_
  · intro x hx
    have hxb := hball x (hs hx)
    have hsub' : Metric.sphere a (r / 2) ⊆ O := fun y hy => (hball y (hs hy)).1
    exact (Complex.continuousAt_arg hxb.2).comp_continuousWithinAt (hh.mono hsub' x hx)
  · intro x hx y hy e
    have hxb := hball x (hs hx)
    have hyb := hball y (hs hy)
    have hnx : ‖h x‖ = 1 := by simp [h]
    have hny : ‖h y‖ = 1 := by simp [h]
    have heq : h x = h y := Complex.ext_norm_arg (by rw [hnx, hny]) e
    have : (g x : ℂ) = g y := by
      have := mul_right_cancel₀ (by simp) heq
      exact this
    exact hgi hxb.1 hyb.1 (Circle.ext this)

/-- The sheets of a finite cover over a neighbourhood of `b`. -/
structure T98Sheets {E F : Type} [TopologicalSpace E] [TopologicalSpace F] (p : E → F) (b : F) where
  I : Type
  fin : Finite I
  U : Set F
  hU : IsOpen U
  hb : b ∈ U
  s : I → F → E
  cont : ∀ i, ContinuousOn (s i) U
  proj : ∀ i, ∀ u ∈ U, p (s i u) = u
  inj : ∀ u ∈ U, Function.Injective (fun i => s i u)
  surj : ∀ u ∈ U, ∀ e, p e = u → ∃ i, s i u = e
  germ : ∀ i, ∀ᶠ e in 𝓝 (s i b), p e ∈ U ∧ s i (p e) = e

lemma t98J02_exists_sheets {E F : Type} [TopologicalSpace E] [TopologicalSpace F] {p : E → F}
    (hp : IsCoveringMap p) (hfin : ∀ b, Finite {e : E // p e = b}) (b : F) (e₀ : E)
    (he₀ : p e₀ = b) : Nonempty (T98Sheets p b) := by
  subst he₀
  haveI : Nonempty (p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  have hev := hp (p e₀)
  let t := hev.toTrivialization
  have hbU : p e₀ ∈ t.baseSet := hev.mem_toTrivialization_baseSet
  haveI : DiscreteTopology (p ⁻¹' {p e₀}) := hev.1
  have hsrc : ∀ u ∈ t.baseSet, ∀ i, (u, i) ∈ t.target := fun u hu i => by
    rw [t.target_eq]; exact ⟨hu, mem_univ _⟩
  have hsymm : ∀ e, e ∈ t.source → t.toOpenPartialHomeomorph.symm (p e, (t e).2) = e := by
    intro e he
    have h : (p e, (t e).2) = t e := t.mk_proj_snd he
    rw [h]
    exact t.toOpenPartialHomeomorph.left_inv he
  refine ⟨{ I := p ⁻¹' {p e₀}
            fin := hfin (p e₀)
            U := t.baseSet
            hU := t.open_baseSet
            hb := hbU
            s := fun i u => t.toOpenPartialHomeomorph.symm (u, i)
            cont := ?_
            proj := ?_
            inj := ?_
            surj := ?_
            germ := ?_ }⟩
  · intro i
    exact t.toOpenPartialHomeomorph.continuousOn_symm.comp (by fun_prop)
      (fun u hu => hsrc u hu i)
  · intro i u hu
    exact t.proj_symm_apply (hsrc u hu i)
  · intro u hu i j e
    have h := congrArg t e
    simp only at h
    have hi := t.toOpenPartialHomeomorph.right_inv (hsrc u hu i)
    have hj := t.toOpenPartialHomeomorph.right_inv (hsrc u hu j)
    have : (u, i) = (u, j) := by
      rw [← hi, ← hj]; exact congrArg t e
    exact (Prod.ext_iff.1 this).2
  · intro u hu e he
    have hes : e ∈ t.source := by rw [t.source_eq]; simpa [he] using hu
    refine ⟨(t e).2, ?_⟩
    have := hsymm e hes
    rw [he] at this
    exact this
  · intro i
    have hi := hsrc _ hbU i
    have hy : t.toOpenPartialHomeomorph.symm (p e₀, i) ∈ t.source :=
      t.toOpenPartialHomeomorph.map_target hi
    have hti : t (t.toOpenPartialHomeomorph.symm (p e₀, i)) = (p e₀, i) :=
      t.toOpenPartialHomeomorph.right_inv hi
    have hc : ContinuousAt t (t.toOpenPartialHomeomorph.symm (p e₀, i)) :=
      t.toOpenPartialHomeomorph.continuousAt hy
    have h1 : ∀ᶠ e in 𝓝 (t.toOpenPartialHomeomorph.symm (p e₀, i)), e ∈ t.source :=
      t.open_source.mem_nhds hy
    have h2 : ∀ᶠ e in 𝓝 (t.toOpenPartialHomeomorph.symm (p e₀, i)), (t e).2 = i := by
      have h3 : ContinuousAt (fun e => (t e).2) (t.toOpenPartialHomeomorph.symm (p e₀, i)) :=
        continuous_snd.continuousAt.comp hc
      have h4 := h3.eventually_mem ((isOpen_discrete ({i} : Set _)).mem_nhds (by simp [hti]))
      exact h4
    filter_upwards [h1, h2] with e he hei
    refine ⟨?_, ?_⟩
    · rw [← t.mem_source]; exact he
    · have := hsymm e he
      rw [hei] at this
      exact this

lemma t98J02_count {E F : Type} [TopologicalSpace E] [TopologicalSpace F] {p : E → F} {b : F}
    (S : T98Sheets p b) (P : Set E) {u : F} (hu : u ∈ S.U) :
    Set.ncard {e | p e = u ∧ e ∈ P} = Set.ncard {i | S.s i u ∈ P} := by
  have : {e | p e = u ∧ e ∈ P} = (fun i => S.s i u) '' {i | S.s i u ∈ P} := by
    ext e
    constructor
    · rintro ⟨he, hP⟩
      obtain ⟨i, rfl⟩ := S.surj u hu e he
      exact ⟨i, hP, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨S.proj i u hu, hi⟩
  rw [this, Set.ncard_image_of_injective _ (S.inj u hu)]

/-- The heart of the argument.  Suppose the lifted circle `L` splits its complement into open `P`,
`Q`.  The number of points of a fibre lying in `P` is locally constant off the base circle `C`,
hence constant.  A fibre over `C` has only one point on `L`, so crossing `C` near that point can
change the count by one unless the sheet through it stays on one side of `L`. -/
theorem t98J02_nonseparating_lift_connectedCover :
    ∀ (F : ClosedSurface) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      IsKSheetedCover p n → IsCurveLift p c l →
      Nonseparating c → Nonseparating l := by
  intro F E _ _ n p c l hcov hlift hsep
  obtain ⟨hc, hl, hpl⟩ := hlift
  have hp := hcov.isCoveringMap
  haveI : T2Space E := by
    refine ⟨fun x y hne => ?_⟩
    by_cases h : p x = p y
    · exact hp.isSeparatedMap x y h hne
    · obtain ⟨U, V, hU, hV, hx, hy, d⟩ := t2_separation h
      exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous, hx, hy,
        d.preimage p⟩
  have hLc : IsClosed (range l) := (isCompact_range l.continuous).isClosed
  have hn : 0 < n := by
    have h1 := hcov.card_fiber (p (l 1))
    haveI := hcov.finite_fiber (p (l 1))
    rw [← h1]
    haveI : Nonempty {e : E // p e = p (l 1)} := ⟨⟨l 1, rfl⟩⟩
    exact Nat.card_pos
  have hfib : ∀ b, ∃ e, p e = b := by
    intro b
    have h1 := hcov.card_fiber b
    haveI := hcov.finite_fiber b
    have : 0 < Nat.card {e : E // p e = b} := by omega
    obtain ⟨⟨e, he⟩⟩ := (Nat.card_pos_iff.1 this).1
    exact ⟨e, he⟩
  have hsheets : ∀ b, Nonempty (T98Sheets p b) := fun b => by
    obtain ⟨e, he⟩ := hfib b
    exact t98J02_exists_sheets hp hcov.finite_fiber b e he
  have hpL : ∀ e ∈ range l, p e ∈ range c := by
    rintro _ ⟨z, rfl⟩; exact ⟨z, (hpl z).symm⟩
  by_contra hnot
  unfold Nonseparating at hnot
  -- a separation of the complement of the lift
  obtain ⟨P₀, Q₀, hP₀, hQ₀, hcov', hP₁, hQ₁, hdisj⟩ : ∃ P Q : Set E, IsOpen P ∧ IsOpen Q ∧
      (range l)ᶜ ⊆ P ∪ Q ∧ ((range l)ᶜ ∩ P).Nonempty ∧ ((range l)ᶜ ∩ Q).Nonempty ∧
      ¬ ((range l)ᶜ ∩ (P ∩ Q)).Nonempty := by
    simpa [IsPreconnected] using hnot
  let P := (range l)ᶜ ∩ P₀
  let Q := (range l)ᶜ ∩ Q₀
  have hP : IsOpen P := hLc.isOpen_compl.inter hP₀
  have hQ : IsOpen Q := hLc.isOpen_compl.inter hQ₀
  have hPQ : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨-, h3⟩
    exact hdisj ⟨x, h1, h2, h3⟩
  have hU : ∀ x, x ∉ range l → x ∈ P ∨ x ∈ Q := by
    intro x hx
    rcases hcov' hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hPL : ∀ x ∈ P, x ∉ range l := fun x hx => hx.1
  have hQL : ∀ x ∈ Q, x ∉ range l := fun x hx => hx.1
  let a : F.carrier → ℕ := fun u => Set.ncard {e | p e = u ∧ e ∈ P}
  -- the count is locally constant off the base circle
  have hloc : ∀ b, b ∉ range c → ∀ᶠ u in 𝓝 b, a u = a b := by
    intro b hb
    obtain ⟨S⟩ := hsheets b
    haveI := S.fin
    have h1 : ∀ i, ∀ᶠ u in 𝓝 b, u ∈ S.U ∧ (S.s i u ∈ P ↔ S.s i b ∈ P) := by
      intro i
      have hUb : S.U ∈ 𝓝 b := S.hU.mem_nhds S.hb
      have hca : ContinuousAt (S.s i) b := (S.cont i).continuousAt hUb
      have hnl : S.s i b ∉ range l := fun h => hb (by
        have := hpL _ h; rwa [S.proj i b S.hb] at this)
      rcases hU _ hnl with h | h
      · filter_upwards [hUb, hca.eventually_mem (hP.mem_nhds h)] with u hu hu2
        exact ⟨hu, by simp [hu2, h]⟩
      · filter_upwards [hUb, hca.eventually_mem (hQ.mem_nhds h)] with u hu hu2
        refine ⟨hu, ?_⟩
        have n1 : S.s i u ∉ P := fun h' => Set.disjoint_left.1 hPQ h' hu2
        have n2 : S.s i b ∉ P := fun h' => Set.disjoint_left.1 hPQ h' h
        simp [n1, n2]
    filter_upwards [Filter.eventually_all.2 h1, S.hU.mem_nhds S.hb] with u hu huU
    change Set.ncard _ = Set.ncard _
    rw [t98J02_count S P huU, t98J02_count S P S.hb]
    congr 1
    ext i
    exact (hu i).2
  have hconst : ∀ u v, u ∉ range c → v ∉ range c → a u = a v := by
    intro u v hu hv
    have hcont : ContinuousOn a (range c)ᶜ := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      exact (continuousAt_const (y := a x)).congr (by
        filter_upwards [hloc x hx] with u hu using hu.symm)
    exact IsPreconnected.constant hsep hcont hu hv
  -- near a point of the lift, the complement of the lift lies on one side
  have hside : ∀ y ∈ range l, (∀ᶠ e in 𝓝 y, e ∉ range l → e ∈ P) ∨
      (∀ᶠ e in 𝓝 y, e ∉ range l → e ∈ Q) := by
    rintro y ⟨z₀, rfl⟩
    obtain ⟨S⟩ := hsheets (p (l z₀))
    set b := p (l z₀) with hb
    haveI : Finite S.I := S.fin
    obtain ⟨i₀, hi₀⟩ := S.surj b S.hb (l z₀) rfl
    have hother : ∀ i, i ≠ i₀ → S.s i b ∉ range l := by
      rintro i hi ⟨z, hz⟩
      have h1 : c z = c z₀ := by
        rw [← hpl z, ← hpl z₀, hz, S.proj i b S.hb]
      have h2 : z = z₀ := hc.injective h1
      apply hi
      apply S.inj b S.hb
      change S.s i b = S.s i₀ b
      rw [hi₀, ← hz, h2]
    have hW : ∀ᶠ u in 𝓝 b, u ∈ S.U ∧ ∀ i, i ≠ i₀ → S.s i u ∉ range l := by
      refine Filter.Eventually.and (S.hU.mem_nhds S.hb) ?_
      refine Filter.eventually_all.2 fun i => ?_
      by_cases hi : i = i₀
      · exact Filter.Eventually.of_forall fun _ h => absurd hi h
      · have hca : ContinuousAt (S.s i) b := (S.cont i).continuousAt (S.hU.mem_nhds S.hb)
        filter_upwards [hca.eventually_mem (hLc.isOpen_compl.mem_nhds (hother i hi))] with u hu _
        exact hu
    haveI : LocallyConnectedSpace F.carrier := ChartedSpace.locallyConnectedSpace E2 F.carrier
    obtain ⟨V, hVW, hVo, hbV, hVc⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 inferInstance b _ hW
    -- the other sheets stay on one side
    have hsame : ∀ i, i ≠ i₀ → ∀ u ∈ V, (S.s i u ∈ P ↔ S.s i b ∈ P) := by
      intro i hi u hu
      have hVU : V ⊆ S.U := fun x hx => (hVW hx).1
      have hT : IsPreconnected (S.s i '' V) := hVc.isPreconnected.image _ ((S.cont i).mono hVU)
      have hTs : S.s i '' V ⊆ P ∪ Q := by
        rintro _ ⟨x, hx, rfl⟩
        exact hU _ ((hVW hx).2 i hi)
      have hbi : S.s i b ∈ S.s i '' V := ⟨b, hbV, rfl⟩
      rcases hU _ (hother i hi) with h | h
      · have := hT.subset_left_of_subset_union hP hQ hPQ hTs ⟨_, hbi, h⟩
        simp [this ⟨u, hu, rfl⟩, h]
      · have := hT.subset_right_of_subset_union hP hQ hPQ hTs ⟨_, hbi, h⟩
        have n1 : S.s i u ∉ P := fun h' => Set.disjoint_left.1 hPQ h' (this ⟨u, hu, rfl⟩)
        have n2 : S.s i b ∉ P := fun h' => Set.disjoint_left.1 hPQ h' h
        simp [n1, n2]
    -- so the count forces the sheet through the lift to stay on one side
    have hkey : ∀ u ∈ V, ∀ v ∈ V, u ∉ range c → v ∉ range c → S.s i₀ u ∈ P → S.s i₀ v ∈ P := by
      intro u hu v hv huc hvc hup
      by_contra hvp
      have huU := (hVW hu).1
      have hvU := (hVW hv).1
      have h1 := hconst u v huc hvc
      change Set.ncard _ = Set.ncard _ at h1
      rw [t98J02_count S P huU, t98J02_count S P hvU] at h1
      have h2 : {i | S.s i v ∈ P} ⊂ {i | S.s i u ∈ P} := by
        refine ⟨?_, ?_⟩
        · intro i hi
          by_cases h : i = i₀
          · subst h; exact hup
          · exact (hsame i h u hu).2 ((hsame i h v hv).1 hi)
        · intro h
          exact hvp (h hup)
      exact (Set.ncard_lt_ncard h2 (Set.Finite.subset (Set.finite_univ) (Set.subset_univ _))).ne h1.symm
    have hgerm : ∀ᶠ e in 𝓝 (l z₀), p e ∈ V ∧ S.s i₀ (p e) = e := by
      have h1 := S.germ i₀
      rw [hi₀] at h1
      have h2 : ∀ᶠ e in 𝓝 (l z₀), p e ∈ V :=
        hp.continuous.continuousAt.eventually_mem (hVo.mem_nhds hbV)
      filter_upwards [h1, h2] with e he he2
      exact ⟨he2, he.2⟩
    have hoff : ∀ e, p e ∈ V → S.s i₀ (p e) = e → e ∉ range l → p e ∉ range c := by
      rintro e heV hes hne ⟨z, hz⟩
      obtain ⟨i, hi⟩ := S.surj (p e) (hVW heV).1 (l z) (by rw [hpl, hz])
      by_cases h : i = i₀
      · subst h
        exact hne ⟨z, by rw [← hes, ← hi]⟩
      · exact (hVW heV).2 i h ⟨z, hi.symm⟩
    by_cases hex : ∃ u ∈ V, u ∉ range c ∧ S.s i₀ u ∈ P
    · obtain ⟨u, hu, huc, hup⟩ := hex
      left
      filter_upwards [hgerm] with e he hne
      have := hkey u hu _ he.1 huc (hoff e he.1 he.2 hne) hup
      rwa [he.2] at this
    · right
      filter_upwards [hgerm] with e he hne
      rcases hU e hne with h | h
      · exact absurd ⟨p e, he.1, hoff e he.1 he.2 hne, by rw [he.2]; exact h⟩ hex
      · exact h
  have hIntC := t98J02_interior_range_eq_empty c hc
  have hIntL : interior (range l) = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
    have ho : IsOpen (p '' interior (range l)) := hp.isOpenMap _ isOpen_interior
    have hsub : p '' interior (range l) ⊆ range c := by
      rintro _ ⟨e, he, rfl⟩
      exact hpL e (interior_subset he)
    have : p y ∈ interior (range c) := interior_maximal hsub ho ⟨y, hy, rfl⟩
    rw [hIntC] at this
    exact this
  let WP : Set E := {y | ∀ᶠ e in 𝓝 y, e ∉ range l → e ∈ P}
  let WQ : Set E := {y | ∀ᶠ e in 𝓝 y, e ∉ range l → e ∈ Q}
  have hWP : IsOpen WP := isOpen_setOf_eventually_nhds
  have hWQ : IsOpen WQ := isOpen_setOf_eventually_nhds
  have hWdisj : ∀ y, y ∈ WP → y ∈ WQ → False := by
    intro y h1 h2
    have h3 : ∀ᶠ e in 𝓝 y, e ∈ range l := by
      filter_upwards [h1, h2] with e he1 he2
      by_contra hne
      exact Set.disjoint_left.1 hPQ (he1 hne) (he2 hne)
    have : y ∈ interior (range l) := mem_interior_iff_mem_nhds.2 h3
    rw [hIntL] at this
    exact this
  have hfinish : ∀ R T : Set E, IsOpen R → IsOpen T → Disjoint R T → (∀ x ∈ T, x ∉ range l) →
      (∀ x, x ∉ range l → x ∈ R ∨ x ∈ T) → T.Nonempty →
      (∀ y ∈ range l, ∀ᶠ e in 𝓝 y, e ∉ range l → e ∈ R) → False := by
    intro R T hR hT hd hTL hcv hne hall
    have hcl : IsClosed T := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      by_cases hxl : x ∈ range l
      · filter_upwards [hall x hxl] with e he heT
        exact Set.disjoint_left.1 hd (he (hTL e heT)) heT
      · rcases hcv x hxl with h | h
        · filter_upwards [hR.mem_nhds h] with e he heT
          exact Set.disjoint_left.1 hd he heT
        · exact absurd h hx
    have : T = univ := IsClopen.eq_univ ⟨hcl, hT⟩ hne
    exact hTL (l 1) (this ▸ mem_univ _) ⟨1, rfl⟩
  haveI : PreconnectedSpace Circle := by
    have : PathConnectedSpace Circle := isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (E := ℂ) (Complex.rank_real_complex ▸ by norm_num)
        0 (r := 1) (by norm_num))
    infer_instance
  have hA : IsClopen (l ⁻¹' WP) := by
    refine ⟨?_, hWP.preimage l.continuous⟩
    rw [← isOpen_compl_iff]
    have : (l ⁻¹' WP)ᶜ = l ⁻¹' WQ := by
      ext z
      constructor
      · intro hz
        exact (hside (l z) ⟨z, rfl⟩).resolve_left hz
      · intro hz hz'
        exact hWdisj _ hz' hz
    rw [this]
    exact hWQ.preimage l.continuous
  obtain ⟨xP, hxP⟩ := hP₁
  obtain ⟨xQ, hxQ⟩ := hQ₁
  rcases isClopen_iff.1 hA with h | h
  · refine hfinish Q P hQ hP hPQ.symm hPL (fun x hx => (hU x hx).symm) ⟨xP, hxP⟩ ?_
    rintro _ ⟨z, rfl⟩
    have : z ∉ l ⁻¹' WP := by rw [h]; simp
    exact (hside (l z) ⟨z, rfl⟩).resolve_left this
  · refine hfinish P Q hP hQ hPQ hQL hU ⟨xQ, hxQ⟩ ?_
    rintro _ ⟨z, rfl⟩
    have : z ∈ l ⁻¹' WP := by rw [h]; simp
    exact this


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


/-! ### The Klein bottle double cover

The base is the quotient of the torus by the free involution `(u, v) ↦ (-u, -v̄)`, which is a
Klein bottle.  The imaginary part of `v` descends to the quotient and vanishes exactly on the
image of the circle `v = 1`, so that image separates; upstairs the circle is a coordinate circle. -/

namespace T98Klein

abbrev Tor := Circle × Circle

def minusOne : Circle := ⟨-1, by simp [Submonoid.unitSphere, mem_sphere_zero_iff_norm]⟩

@[simp] lemma coe_m : ((minusOne : Circle) : ℂ) = -1 := rfl

lemma m_mul_m : minusOne * minusOne = 1 := by
  apply Circle.ext; simp

lemma m_ne_one : minusOne ≠ 1 := by
  intro h
  have := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at this

lemma m_inv : minusOne⁻¹ = minusOne := inv_eq_of_mul_eq_one_left m_mul_m

def tau (x : Tor) : Tor := (minusOne * x.1, minusOne * x.2⁻¹)

lemma tau_tau (x : Tor) : tau (tau x) = x := by
  apply Prod.ext
  · simp [tau, ← mul_assoc, m_mul_m]
  · change minusOne * (minusOne * x.2⁻¹)⁻¹ = x.2
    rw [mul_inv, inv_inv, m_inv, ← mul_assoc, m_mul_m, one_mul]

lemma tau_ne (x : Tor) : tau x ≠ x := by
  intro h
  have h1 : minusOne * x.1 = x.1 := congrArg Prod.fst h
  exact m_ne_one (by simpa using h1)

lemma continuous_tau : Continuous tau := by
  unfold tau
  fun_prop

instance act : MulAction ℤˣ Tor where
  smul g x := if g = 1 then x else tau x
  one_smul x := if_pos rfl
  mul_smul g h x := by
    change (if g * h = 1 then x else tau x) =
      (if g = 1 then (if h = 1 then x else tau x) else tau (if h = 1 then x else tau x))
    rcases Int.units_eq_one_or g with rfl | rfl <;> rcases Int.units_eq_one_or h with rfl | rfl <;>
      simp [tau_tau]

lemma one_act (x : Tor) : (1 : ℤˣ) • x = x := if_pos rfl
lemma neg_act (x : Tor) : (-1 : ℤˣ) • x = tau x := if_neg (by decide)

instance : ContinuousConstSMul ℤˣ Tor where
  continuous_const_smul g := by
    rcases Int.units_eq_one_or g with rfl | rfl
    · exact continuous_id.congr fun x => (one_act x).symm
    · exact continuous_tau.congr fun x => (neg_act x).symm

instance : IsCancelSMul ℤˣ Tor :=
  isCancelSMul_iff_eq_one_of_smul_eq.2 fun g x h => by
    rcases Int.units_eq_one_or g with rfl | rfl
    · rfl
    · rw [neg_act] at h
      exact absurd h (tau_ne x)

abbrev Bot := Quotient (MulAction.orbitRel ℤˣ Tor)

def kleinProj : Tor → Bot := Quotient.mk _

lemma cov : IsQuotientCoveringMap kleinProj ℤˣ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

lemma kleinProj_tau (x : Tor) : kleinProj (tau x) = kleinProj x := by
  apply cov.apply_eq_iff_mem_orbit.2
  exact ⟨-1, neg_act x⟩

lemma kleinProj_eq {x y : Tor} (h : kleinProj x = kleinProj y) : x = y ∨ x = tau y := by
  obtain ⟨g, hg⟩ := cov.apply_eq_iff_mem_orbit.1 h
  rcases Int.units_eq_one_or g with rfl | rfl
  · left
    exact hg.symm.trans (one_act y)
  · right
    exact hg.symm.trans (neg_act y)

lemma circle_connected : PathConnectedSpace Circle :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (E := ℂ) (Complex.rank_real_complex ▸ by norm_num)
      0 (r := 1) (by norm_num))

/-- Charts on the quotient: compose a local inverse of `kleinProj` with a torus chart. -/
noncomputable def kleinCharts : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Bot := by
  letI := t98J02_disconnected_trivialCover_model_aux_charts
  have hl := cov.isCoveringMap.isLocalHomeomorph
  choose f hf hfe using fun e : Tor => hl e
  have hs : Function.Surjective kleinProj := cov.surjective
  exact
    { atlas := range fun e : Tor => (f e).symm.trans (chartAt (EuclideanSpace ℝ (Fin 2)) e)
      chartAt := fun x => (f (Function.surjInv hs x)).symm.trans
        (chartAt (EuclideanSpace ℝ (Fin 2)) (Function.surjInv hs x))
      mem_chart_source := fun x => by
        have h1 : (f (Function.surjInv hs x)) (Function.surjInv hs x) = x := by
          rw [← hfe]; exact Function.surjInv_eq hs x
        have h2 : x ∈ (f (Function.surjInv hs x)).target := by
          have := (f (Function.surjInv hs x)).map_source (hf (Function.surjInv hs x))
          rwa [h1] at this
        have h3 : (f (Function.surjInv hs x)).symm x = Function.surjInv hs x := by
          have := (f (Function.surjInv hs x)).left_inv (hf (Function.surjInv hs x))
          rwa [h1] at this
        simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
          OpenPartialHomeomorph.symm_source]
        exact ⟨h2, by rw [h3]; exact mem_chart_source _ _⟩
      chart_mem_atlas := fun x => ⟨_, rfl⟩ }

def surface : ClosedSurface where
  carrier := Bot
  topology := inferInstance
  charts := kleinCharts
  compact := inferInstance
  hausdorff := inferInstance
  secondCountable := ContinuousConstSMul.secondCountableTopology
  connected := by
    haveI := circle_connected
    infer_instance

def height : Bot → ℝ :=
  Quotient.lift (fun x : Tor => ((x.2 : ℂ)).im) (by
    rintro x y ⟨g, hg⟩
    change g • y = x at hg
    change ((x.2 : ℂ)).im = ((y.2 : ℂ)).im
    rcases Int.units_eq_one_or g with rfl | rfl
    · rw [one_act] at hg
      rw [hg]
    · rw [neg_act] at hg
      rw [← hg]
      simp [tau, Circle.coe_inv_eq_conj])

lemma continuous_height : Continuous height :=
  Continuous.quotient_lift (by fun_prop) _

lemma im_zero_of_circle (v : Circle) (h : (v : ℂ).im = 0) : v = 1 ∨ v = minusOne := by
  have hn : ‖(v : ℂ)‖ = 1 := Circle.norm_coe v
  have hre : (v : ℂ).re = 1 ∨ (v : ℂ).re = -1 := by
    have h1 : (v : ℂ) = ((v : ℂ).re : ℂ) := by
      apply Complex.ext <;> simp [h]
    rw [h1, Complex.norm_real, Real.norm_eq_abs] at hn
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.1 hn with h2 | h2
    · left; exact h2
    · right; exact h2
  rcases hre with h1 | h1
  · left; apply Circle.ext; apply Complex.ext <;> simp [h, h1]
  · right; apply Circle.ext; apply Complex.ext <;> simp [h, h1]

end T98Klein
open T98Klein

theorem t98J02_connected_doubleCover_counterexample :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      ¬ Nonseparating c ∧ Nonseparating l := by
  let l : C(Circle, Tor) := ⟨fun z => (z, 1), continuous_id.prodMk continuous_const⟩
  let c : C(Circle, Bot) := ⟨fun z => kleinProj (l z), cov.continuous.comp l.continuous⟩
  have hcinj : Function.Injective c := by
    intro z w h
    rcases kleinProj_eq h with h1 | h1
    · exact congrArg Prod.fst h1
    · have h2 : (1 : Circle) = minusOne * (1 : Circle)⁻¹ := congrArg Prod.snd h1
      exact absurd (by simpa using h2.symm) m_ne_one
  have hcemb : Topology.IsEmbedding c :=
    (c.continuous.isClosedEmbedding hcinj).isEmbedding
  have hlemb : Topology.IsEmbedding l := isEmbedding_prodMkLeft (1 : Circle)
  have hcover : IsKSheetedCover kleinProj 2 := by
    have hbij : ∀ b, ∃ e, kleinProj e = b := fun b => cov.surjective b
    have hequiv : ∀ b, Nonempty (ℤˣ ≃ {e : Tor // kleinProj e = b}) := by
      intro b
      obtain ⟨e, rfl⟩ := hbij b
      refine ⟨Equiv.ofBijective (fun g => ⟨g • e, cov.apply_eq_iff_mem_orbit.2 ⟨g, rfl⟩⟩) ⟨?_, ?_⟩⟩
      · intro g g' h
        exact IsCancelSMul.right_cancel g g' e (congrArg Subtype.val h)
      · rintro ⟨e', he'⟩
        obtain ⟨g, hg⟩ := cov.apply_eq_iff_mem_orbit.1 he'
        exact ⟨g, Subtype.ext hg⟩
    refine ⟨cov.isCoveringMap, ?_, ?_⟩
    · intro b
      obtain ⟨φ⟩ := hequiv b
      exact Finite.of_equiv _ φ
    · intro b
      obtain ⟨φ⟩ := hequiv b
      rw [← Nat.card_congr φ, Nat.card_eq_fintype_card, Fintype.card_units_int]
  refine ⟨surface, Tor, inferInstance, 2, kleinProj, c, l, by norm_num, ?_, hcover,
    ⟨hcemb, hlemb, fun _ => rfl⟩, ?_, ?_⟩
  · haveI := circle_connected
    infer_instance
  · intro hsep
    unfold Nonseparating at hsep
    change IsPreconnected (range c)ᶜ at hsep
    have hrange0 : ∀ x ∈ range c, height x = 0 := by
      rintro _ ⟨z, rfl⟩
      change (((1 : Circle) : ℂ)).im = 0
      simp
    let w : Circle := Circle.exp (Real.pi / 2)
    have hw : (w : ℂ).im = 1 := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two]
    let x₁ : Bot := kleinProj (1, w)
    let x₂ : Bot := kleinProj (1, w⁻¹)
    have h₁ : height x₁ = 1 := hw
    have h₂ : height x₂ = -1 := by
      change ((w⁻¹ : Circle) : ℂ).im = -1
      rw [Circle.coe_inv_eq_conj]
      simp [hw]
    have hx₁ : x₁ ∈ (range c)ᶜ := fun h => by
      have := hrange0 _ h; rw [h₁] at this; norm_num at this
    have hx₂ : x₂ ∈ (range c)ᶜ := fun h => by
      have := hrange0 _ h; rw [h₂] at this; norm_num at this
    obtain ⟨x, hx, hx0⟩ := hsep.intermediate_value hx₂ hx₁ continuous_height.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (height x₂) (height x₁) by rw [h₁, h₂]; constructor <;> norm_num)
    obtain ⟨⟨u, v⟩, rfl⟩ := cov.surjective x
    apply hx
    rcases im_zero_of_circle v hx0 with rfl | rfl
    · exact ⟨u, rfl⟩
    · refine ⟨minusOne * u, ?_⟩
      change kleinProj (minusOne * u, 1) = kleinProj (u, minusOne)
      rw [← kleinProj_tau (u, minusOne)]
      congr 1
      apply Prod.ext
      · rfl
      · simp [tau, m_inv, m_mul_m]
  · unfold Nonseparating
    have hcircle : IsPreconnected (Set.univ : Set Circle) := by
      haveI := circle_connected
      exact isPreconnected_univ
    have hpunc : IsPreconnected ({(1 : Circle)}ᶜ : Set Circle) := by
      change IsPreconnected ({(⟨(1 : ℂ), by norm_num⟩ : Circle)}ᶜ : Set Circle)
      have h := isPreconnected_range
        (continuousOn_univ.mp (by simpa using
          (stereographic (v := (1 : ℂ)) (by norm_num)).continuousOn_symm))
      rw [range_stereographic_symm] at h
      exact h
    rw [show (range l)ᶜ = (Set.univ : Set Circle) ×ˢ ({(1 : Circle)}ᶜ) by
      ext ⟨x, y⟩
      constructor
      · intro h
        refine ⟨mem_univ _, fun hy => h ⟨x, Prod.ext rfl (Eq.symm hy)⟩⟩
      · rintro ⟨-, hy⟩ ⟨z, hz⟩
        exact hy (congrArg Prod.snd hz).symm]
    exact hcircle.prod hpunc

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


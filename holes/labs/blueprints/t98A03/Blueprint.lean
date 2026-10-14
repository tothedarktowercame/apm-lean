import Mathlib
import Mathlib.Topology.Constructions.SumProd
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.CoveringMonodromyCosets

/-! # APM t98A03 — blueprint

The four mathematical conclusions are isolated as library-scale contracts.
The final theorem is only their conjunction.
-/

open scoped LinearAlgebra.Projectivization
open scoped Manifold
open Set

noncomputable section

abbrev apm_t98a03_Torus := Circle × Circle
abbrev apm_t98a03_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t98a03_RP2 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℝ) inferInstance

inductive apm_t98a03_wedgeRel
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Sum apm_t98a03_Torus apm_t98a03_RP2 →
      Sum apm_t98a03_Torus apm_t98a03_RP2 → Prop
  | base : apm_t98a03_wedgeRel t₀ r₀ (.inl t₀) (.inr r₀)

def apm_t98a03_X (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :=
  Quotient (Relation.EqvGen.setoid (apm_t98a03_wedgeRel t₀ r₀))

noncomputable instance (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    TopologicalSpace (apm_t98a03_X t₀ r₀) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t98a03_Torus apm_t98a03_RP2 ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t98a03_wedgeRel t₀ r₀)) z)
    inferInstance

def apm_t98a03_basepoint
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_X t₀ r₀ :=
  Quotient.mk _ (.inl t₀)

lemma apm_t98a03_wedge_base_eq
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_basepoint t₀ r₀ = Quotient.mk _ (.inr r₀) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t98a03_wedgeRel.base (t₀ := t₀) (r₀ := r₀)))

abbrev apm_t98a03_expectedFundamentalGroup :=
  Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative (ZMod 2))

def apm_t98a03_IsTopologicalManifold
    (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty (T2Space X) ∧
    ∃ n : ℕ,
      ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
        let _ := charts
        IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0 X

structure apm_t98a03_Cover (X : Type*) [TopologicalSpace X] where
  total : Type
  topology : TopologicalSpace total
  projection : total → X

def apm_t98a03_IsConnectedThreeFoldCover
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) : Prop :=
  letI := C.topology
  IsCoveringMap C.projection ∧
    Nonempty (ConnectedSpace C.total) ∧
    ∀ x : X, Nat.card {e : C.total // C.projection e = x} = 3

def apm_t98a03_IsRegularCover
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) : Prop :=
  letI := C.topology
  IsCoveringMap C.projection ∧
    ∀ x y : C.total, C.projection x = C.projection y →
      ∃ h : C.total ≃ₜ C.total,
        (∀ z : C.total, C.projection (h z) = C.projection z) ∧ h x = y

lemma apm_t98a03_threeFoldCover_surjective
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X)
    (hC : apm_t98a03_IsConnectedThreeFoldCover C) :
    Function.Surjective C.projection := by
  letI := C.topology
  intro x
  by_contra hx
  push_neg at hx
  letI : IsEmpty {e : C.total // C.projection e = x} :=
    ⟨fun e ↦ hx e.1 e.2⟩
  have hcard := hC.2.2 x
  simp at hcard

lemma apm_t98a03_threeFoldCover_fiber_equiv_fin_three
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X)
    (hC : apm_t98a03_IsConnectedThreeFoldCover C) (x : X) :
    Nonempty ({e : C.total // C.projection e = x} ≃ Fin 3) := by
  letI := C.topology
  have hcard0 : Nat.card {e : C.total // C.projection e = x} ≠ 0 := by
    rw [hC.2.2 x]
    norm_num
  letI : Finite {e : C.total // C.projection e = x} :=
    Nat.finite_of_card_ne_zero hcard0
  letI := Fintype.ofFinite {e : C.total // C.projection e = x}
  exact ⟨Fintype.equivOfCardEq (by
    simpa [Nat.card_eq_fintype_card] using hC.2.2 x)⟩

def apm_t98a03_HasConnectedPuncturedNeighborhood
    {X : Type*} [TopologicalSpace X] (S : Set X) (p : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
    IsPreconnected ((U ∩ S) \ {p})

/-- LIBRARY: a point of an open subset of the real plane has a smaller open
neighborhood whose puncture is preconnected. -/
lemma apm_t98a03_plane_punctured_neighborhood
    (W : Set (EuclideanSpace ℝ (Fin 2))) (hW : IsOpen W) {x} (hx : x ∈ W) :
    ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ IsPreconnected (V \ {x}) := by
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x hx
  refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hrW, ?_⟩
  let A : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    Set.Ioo 0 r ×ˢ Metric.sphere 0 1
  let f : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun q => x + q.1 • q.2
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hA : IsPreconnected A := by
    exact (ordConnected_Ioo.isPreconnected.prod
      (isPathConnected_sphere hrank 0 (r := 1) (by norm_num)).isConnected.isPreconnected)
  have hf : Continuous f := by
    exact continuous_const.add (continuous_fst.smul continuous_snd)
  have himage : f '' A = Metric.ball x r \ {x} := by
    ext y
    constructor
    · rintro ⟨q, ⟨hq, hu⟩, rfl⟩
      have hq0 : 0 < q.1 := hq.1
      have hu_norm : ‖q.2‖ = 1 := by
        simpa [Metric.mem_sphere] using hu
      constructor
      · rw [Metric.mem_ball, dist_eq_norm]
        rw [add_sub_cancel_left, norm_smul, hu_norm, mul_one]
        simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq.2
      · simp only [mem_singleton_iff]
        intro heq
        have : q.1 • q.2 = 0 := by
          simpa [f] using congrArg (fun z => z - x) heq
        exact hq0.ne' (smul_eq_zero.mp this |>.resolve_right (by
          intro hz
          simpa [hz] using hu_norm))
    · rintro ⟨hyball, hyx⟩
      let ρ : ℝ := ‖y - x‖
      let u : EuclideanSpace ℝ (Fin 2) := ρ⁻¹ • (y - x)
      have hρ : 0 < ρ := by
        rw [show ρ = dist y x by simp [ρ, dist_eq_norm]]
        exact dist_pos.mpr (by simpa [mem_singleton_iff] using hyx)
      have hρr : ρ < r := by
        rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hyball
        simpa [ρ, norm_sub_rev] using hyball
      have hu : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        rw [show ‖u‖ = |ρ⁻¹| * ‖y - x‖ by simp [u, norm_smul]]
        rw [abs_of_pos (inv_pos.mpr hρ)]
        exact inv_mul_cancel₀ hρ.ne'
      refine ⟨(ρ, u), ⟨⟨hρ, hρr⟩, hu⟩, ?_⟩
      simp [f, u, hρ.ne']
  rw [← himage]
  exact hA.image _ hf.continuousOn

/-- LIBRARY: transport a connected punctured neighborhood through a local
chart.  The plane-side conclusion is an explicit hypothesis so this lemma is
independent of `apm_t98a03_plane_punctured_neighborhood`. -/
lemma apm_t98a03_chart_transport_punctured_neighborhood
    {X : Type*} [TopologicalSpace X] {S U : Set X} {p : X}
    {W : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (hpU : p ∈ U) (hpS : p ∈ S)
    (e : ↥(U ∩ S) ≃ₜ ↥W)
    (hplane : ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ (e ⟨p, hpU, hpS⟩ : EuclideanSpace ℝ (Fin 2)) ∈ V ∧
      V ⊆ W ∧ IsPreconnected (V \ {(e ⟨p, hpU, hpS⟩ :
        EuclideanSpace ℝ (Fin 2))})) :
    apm_t98a03_HasConnectedPuncturedNeighborhood S p := by
  obtain ⟨V, hVopen, hxV, hVW, hVconn⟩ := hplane
  let q : ↑(U ∩ S) := ⟨p, hpU, hpS⟩
  let A : Set (↑(U ∩ S)) :=
    e ⁻¹' ((↑) ⁻¹' V)
  have hAopen : IsOpen A := by
    exact (hVopen.preimage continuous_subtype_val).preimage e.continuous
  obtain ⟨O, hOopen, hOA⟩ := isOpen_induced_iff.mp hAopen
  refine ⟨O ∩ U, hOopen.inter hU, ?_, ?_⟩
  · constructor
    · have hqA : q ∈ A := by
        exact hxV
      have : p ∈ O := by
        have := congrArg (fun T : Set (↑(U ∩ S)) => q ∈ T) hOA
        exact this.mpr hqA
      exact this
    · exact hpU
  · let D : Set (↑V) := {y | (y : EuclideanSpace ℝ (Fin 2)) ≠ e q}
    let f : ↑V → X := fun y =>
      (e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ : ↑(U ∩ S))
    have hDconn : IsPreconnected D := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have hval : Subtype.val '' D =
          V \ {(e q : EuclideanSpace ℝ (Fin 2))} := by
        ext y
        simp [D, and_comm]
      rw [hval]
      exact hVconn
    have hfcont : Continuous f := by
      exact continuous_subtype_val.comp
        (e.symm.continuous.comp
          (Continuous.subtype_mk continuous_subtype_val (fun y => hVW y.2)))
    have himage : f '' D = (((O ∩ U) ∩ S) \ {p}) := by
      ext z
      constructor
      · rintro ⟨y, hyD, rfl⟩
        have hyA : e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ ∈ A := by
          simp [A]
        have hyO : (e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ :
            ↑(U ∩ S)).1 ∈ O := by
          have h := congrArg
            (fun T : Set (↑(U ∩ S)) =>
              e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ ∈ T) hOA
          exact h.mpr hyA
        refine ⟨⟨⟨hyO, (e.symm ⟨y, hVW y.2⟩).2.1⟩,
          (e.symm ⟨y, hVW y.2⟩).2.2⟩, ?_⟩
        intro hz
        have hzq : e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ = q := by
          apply Subtype.ext
          exact hz
        apply hyD
        change (y : EuclideanSpace ℝ (Fin 2)) = e q
        simpa using congrArg (fun r : ↑(U ∩ S) =>
          (e r : EuclideanSpace ℝ (Fin 2))) hzq
      · rintro ⟨⟨⟨hzO, hzU⟩, hzS⟩, hzp⟩
        let r : ↑(U ∩ S) := ⟨z, hzU, hzS⟩
        have hrA : r ∈ A := by
          have h := congrArg (fun T : Set (↑(U ∩ S)) => r ∈ T) hOA
          exact h.mp hzO
        have herV : (e r : EuclideanSpace ℝ (Fin 2)) ∈ V := hrA
        let y : ↑V := ⟨(e r : EuclideanSpace ℝ (Fin 2)), herV⟩
        refine ⟨y, ?_, ?_⟩
        · change (y : EuclideanSpace ℝ (Fin 2)) ≠ e q
          intro heq
          apply hzp
          have : r = q := e.injective (Subtype.ext heq)
          exact congrArg Subtype.val this
        · change (e.symm ⟨(y : EuclideanSpace ℝ (Fin 2)), hVW y.2⟩ :
            ↑(U ∩ S)).1 = z
          simp [y, r]
    rw [← himage]
    exact hDconn.image f hfcont.continuousOn

/-- Seat (general topology): if `A, B` are closed, meet at most in `p`, and an
open-set slice meets both away from `p`, then the punctured slice of `A ∪ B` is
not preconnected (`isPreconnected_iff_subset_of_disjoint_closed`). -/
lemma apm_t98a03_union_closed_punctured_not_preconnected {X : Type*}
    [TopologicalSpace X] {A B U : Set X} {p : X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∩ B ⊆ {p})
    (hUA : ((U ∩ A) \ {p}).Nonempty) (hUB : ((U ∩ B) \ {p}).Nonempty) :
    ¬ IsPreconnected ((U ∩ (A ∪ B)) \ {p}) := by
  intro hpre
  let S := (U ∩ (A ∪ B)) \ {p}
  have hcover : S ⊆ A ∪ B := by
    intro x hx
    exact hx.1.2
  have hdisj : S ∩ (A ∩ B) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hxS, hxAB⟩
    exact hxS.2 (hAB hxAB)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre
    A B hA hB hcover hdisj) with hsub | hsub
  · rcases hUB with ⟨x, ⟨⟨hxU, hxB⟩, hxp⟩⟩
    have hxS : x ∈ S := ⟨⟨hxU, Or.inr hxB⟩, hxp⟩
    have hxA := hsub hxS
    exact hxp (hAB ⟨hxA, hxB⟩)
  · rcases hUA with ⟨x, ⟨⟨hxU, hxA⟩, hxp⟩⟩
    have hxS : x ∈ S := ⟨⟨hxU, Or.inl hxA⟩, hxp⟩
    have hxB := hsub hxS
    exact hxp (hAB ⟨hxA, hxB⟩)

/-- The image of the torus summand in the point wedge. -/
def apm_t98a03_torusBranch
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Set (apm_t98a03_X t₀ r₀) :=
  Set.range (fun t => Quotient.mk _ (Sum.inl t))

/-- The image of the projective-plane summand in the point wedge. -/
def apm_t98a03_rp2Branch
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Set (apm_t98a03_X t₀ r₀) :=
  Set.range (fun r => Quotient.mk _ (Sum.inr r))

lemma apm_t98a03_wedge_branches_cover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_torusBranch t₀ r₀ ∪ apm_t98a03_rp2Branch t₀ r₀ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Quotient.inductionOn x ?_
  rintro (t | r)
  · exact Or.inl ⟨t, rfl⟩
  · exact Or.inr ⟨r, rfl⟩

/-- Seat: both compact summand images are closed. -/
def apm_t98a03_wedge_branches_closed_aux_torusPred
    (r₀ : apm_t98a03_RP2) :
    Sum apm_t98a03_Torus apm_t98a03_RP2 → Prop
  | .inl _ => True
  | .inr r => r = r₀

def apm_t98a03_wedge_branches_closed_aux_rp2Pred
    (t₀ : apm_t98a03_Torus) :
    Sum apm_t98a03_Torus apm_t98a03_RP2 → Prop
  | .inl t => t = t₀
  | .inr _ => True

lemma apm_t98a03_wedge_branches_closed_aux_torus_invariant
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    {a b : Sum apm_t98a03_Torus apm_t98a03_RP2}
    (h : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀) a b) :
    apm_t98a03_wedge_branches_closed_aux_torusPred r₀ a ↔
      apm_t98a03_wedge_branches_closed_aux_torusPred r₀ b := by
  induction h with
  | rel a b h => cases h; simp [apm_t98a03_wedge_branches_closed_aux_torusPred]
  | refl => exact Iff.rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

lemma apm_t98a03_wedge_branches_closed_aux_rp2_invariant
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    {a b : Sum apm_t98a03_Torus apm_t98a03_RP2}
    (h : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀) a b) :
    apm_t98a03_wedge_branches_closed_aux_rp2Pred t₀ a ↔
      apm_t98a03_wedge_branches_closed_aux_rp2Pred t₀ b := by
  induction h with
  | rel a b h => cases h; simp [apm_t98a03_wedge_branches_closed_aux_rp2Pred]
  | refl => exact Iff.rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

lemma apm_t98a03_wedge_branches_closed
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    IsClosed (apm_t98a03_torusBranch t₀ r₀) ∧
      IsClosed (apm_t98a03_rp2Branch t₀ r₀) := by
  have hr₀ : IsClosed ({r₀} : Set apm_t98a03_RP2) := by
    rw [isClosed_coinduced]
    have heq :
        (Projectivization.mk' ℝ) ⁻¹' ({r₀} : Set apm_t98a03_RP2) =
          Subtype.val ⁻¹' (Submodule.span ℝ {r₀.rep}) := by
      ext w
      simp only [mem_preimage, mem_singleton_iff]
      rw [Projectivization.mk'_eq_mk]
      conv_lhs => rw [← Projectivization.mk_rep r₀]
      rw [Projectivization.mk_eq_mk_iff']
      exact Submodule.mem_span_singleton.symm
    rw [heq]
    exact (Submodule.span ℝ {r₀.rep}).closed_of_finiteDimensional.preimage
      continuous_subtype_val
  rw [isClosed_coinduced, isClosed_coinduced]
  constructor
  · have heq :
        (fun z : Sum apm_t98a03_Torus apm_t98a03_RP2 ↦ Quotient.mk _ z) ⁻¹'
            apm_t98a03_torusBranch t₀ r₀ =
          Set.range Sum.inl ∪ {Sum.inr r₀} := by
      ext z
      constructor
      · rintro ⟨t, ht⟩
        have hrel : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀) z (.inl t) :=
          (Quotient.exact ht).symm
        have hi := (apm_t98a03_wedge_branches_closed_aux_torus_invariant
          t₀ r₀ hrel).2 trivial
        cases z with
        | inl s => exact Or.inl ⟨s, rfl⟩
        | inr r => exact Or.inr (by simpa using hi)
      · rintro (hz | hz)
        · rcases hz with ⟨t, rfl⟩
          exact ⟨t, rfl⟩
        · simp only [mem_singleton_iff] at hz
          subst hz
          exact ⟨t₀, by simpa [apm_t98a03_basepoint] using
            apm_t98a03_wedge_base_eq t₀ r₀⟩
    have hir : IsClosed ({Sum.inr r₀} : Set
        (Sum apm_t98a03_Torus apm_t98a03_RP2)) := by
      simpa using isClosedMap_inr _ hr₀
    exact heq.symm ▸ (isClosed_range_inl.union hir)
  · have heq :
        (fun z : Sum apm_t98a03_Torus apm_t98a03_RP2 ↦ Quotient.mk _ z) ⁻¹'
            apm_t98a03_rp2Branch t₀ r₀ =
          {Sum.inl t₀} ∪ Set.range Sum.inr := by
      ext z
      constructor
      · rintro ⟨r, hr⟩
        have hrel : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀) z (.inr r) :=
          (Quotient.exact hr).symm
        have hi := (apm_t98a03_wedge_branches_closed_aux_rp2_invariant
          t₀ r₀ hrel).2 trivial
        cases z with
        | inl t => exact Or.inl (by simpa using hi)
        | inr s => exact Or.inr ⟨s, rfl⟩
      · rintro (hz | hz)
        · simp only [mem_singleton_iff] at hz
          subst hz
          exact ⟨r₀, by simpa [apm_t98a03_basepoint] using
            (apm_t98a03_wedge_base_eq t₀ r₀).symm⟩
        · rcases hz with ⟨r, rfl⟩
          exact ⟨r, rfl⟩
    have ht₀ : IsClosed ({t₀} : Set apm_t98a03_Torus) := isClosed_singleton
    have hil : IsClosed ({Sum.inl t₀} : Set
        (Sum apm_t98a03_Torus apm_t98a03_RP2)) := by
      simpa using isClosedMap_inl _ ht₀
    exact heq.symm ▸ (hil.union isClosed_range_inr)

/-- Seat: the two summand images meet only at the wedge point. -/
def apm_t98a03_wedge_branches_intersection_aux_isBase
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Sum apm_t98a03_Torus apm_t98a03_RP2 → Prop
  | .inl t => t = t₀
  | .inr r => r = r₀

lemma apm_t98a03_wedge_branches_intersection_aux_eq_or_base
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    {x y : Sum apm_t98a03_Torus apm_t98a03_RP2}
    (h : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀) x y) :
    x = y ∨
      (apm_t98a03_wedge_branches_intersection_aux_isBase t₀ r₀ x ∧
       apm_t98a03_wedge_branches_intersection_aux_isBase t₀ r₀ y) := by
  induction h with
  | rel x y hxy =>
      cases hxy
      exact Or.inr ⟨rfl, rfl⟩
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
      rcases ih with hxy | ⟨hx, hy⟩
      · exact Or.inl hxy.symm
      · exact Or.inr ⟨hy, hx⟩
  | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with hxy | ⟨hx, hy⟩
      · subst y
        exact ih₂
      · rcases ih₂ with hyz | ⟨hy', hz⟩
        · subst z
          exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩

lemma apm_t98a03_wedge_branches_intersection
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_torusBranch t₀ r₀ ∩ apm_t98a03_rp2Branch t₀ r₀ ⊆
      {apm_t98a03_basepoint t₀ r₀} := by
  rintro x ⟨⟨t, rfl⟩, ⟨r, hr⟩⟩
  have heq : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀)
      (Sum.inl t) (Sum.inr r) := Quotient.exact hr.symm
  rcases apm_t98a03_wedge_branches_intersection_aux_eq_or_base
      t₀ r₀ heq with hbad | ⟨ht, hr₀⟩
  · cases hbad
  · change t = t₀ at ht
    subst t
    exact rfl

lemma apm_t98a03_wedge_branches_accumulate_aux_torus
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (U : Set (apm_t98a03_X t₀ r₀)) (hU : IsOpen U)
    (hpU : apm_t98a03_basepoint t₀ r₀ ∈ U) :
    ∃ t ≠ t₀, Quotient.mk _ (Sum.inl t) ∈ U := by
  let q : Sum apm_t98a03_Torus apm_t98a03_RP2 → apm_t98a03_X t₀ r₀ :=
    fun z ↦ Quotient.mk _ z
  let V : Set apm_t98a03_Torus := Sum.inl ⁻¹' (q ⁻¹' U)
  have hq : IsOpen (q ⁻¹' U) := by
    exact hU
  have hV : IsOpen V := hq.preimage continuous_inl
  have ht₀V : t₀ ∈ V := by
    exact hpU
  let f : ℝ → apm_t98a03_Torus :=
    fun s ↦ (t₀.1 * Circle.exp s, t₀.2)
  have hf : Continuous f := by
    exact (continuous_const.mul Circle.exp.continuous).prodMk continuous_const
  have hW : IsOpen (f ⁻¹' V) := hV.preimage hf
  have hzero : (0 : ℝ) ∈ f ⁻¹' V := by
    simpa [f] using ht₀V
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW 0 hzero
  let s : ℝ := min (ε / 2) (Real.pi / 2)
  have hspos : 0 < s := lt_min (half_pos hε) (half_pos Real.pi_pos)
  have hsε : s < ε :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hspi : s < Real.pi :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self Real.pi_pos)
  have hfsV : f s ∈ V := by
    apply hεW
    simpa [Real.dist_eq, abs_of_pos hspos] using hsε
  refine ⟨f s, ?_, hfsV⟩
  intro heq
  have heq₁ : t₀.1 * Circle.exp s = t₀.1 := congrArg Prod.fst heq
  have hexp : Circle.exp s = 1 := by
    apply mul_left_cancel (a := t₀.1)
    simpa using heq₁
  have him := congrArg (fun z : Circle ↦ (z : ℂ).im) hexp
  have hsin : Real.sin s = 0 := by
    simpa [Circle.coe_exp, Complex.exp_mul_I] using him
  exact (Real.sin_pos_of_pos_of_lt_pi hspos hspi).ne' hsin

lemma apm_t98a03_wedge_branches_accumulate_aux_rp2
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (U : Set (apm_t98a03_X t₀ r₀)) (hU : IsOpen U)
    (hpU : apm_t98a03_basepoint t₀ r₀ ∈ U) :
    ∃ r ≠ r₀, Quotient.mk _ (Sum.inr r) ∈ U := by
  let q : Sum apm_t98a03_Torus apm_t98a03_RP2 → apm_t98a03_X t₀ r₀ :=
    fun z => Quotient.mk _ z
  have hopen : IsOpen (q ⁻¹' U) := by
    exact hU
  have hrU : Sum.inr r₀ ∈ q ⁻¹' U := by
    change Quotient.mk _ (Sum.inr r₀) ∈ U
    rw [← apm_t98a03_wedge_base_eq t₀ r₀]
    exact hpU
  have hRopen : IsOpen (Sum.inr ⁻¹' (q ⁻¹' U)) :=
    hopen.preimage continuous_inr
  rw [isOpen_coinduced] at hRopen
  let v : Fin 3 → ℝ := r₀.rep
  have hv : v ≠ 0 := r₀.rep_nonzero
  have hvU : (⟨v, hv⟩ : {w : Fin 3 → ℝ // w ≠ 0}) ∈
      (Projectivization.mk' ℝ) ⁻¹' (Sum.inr ⁻¹' (q ⁻¹' U)) := by
    simpa [v, Projectivization.mk_rep] using hrU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hRopen _ hvU
  have hspan : Submodule.span ℝ ({v} : Set (Fin 3 → ℝ)) ≠ ⊤ := by
    intro htop
    have hfin : Module.finrank ℝ (Submodule.span ℝ ({v} : Set (Fin 3 → ℝ))) =
        Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)) := by rw [htop]
    rw [finrank_span_singleton hv] at hfin
    norm_num at hfin
  obtain ⟨w, -, hw⟩ :=
    SetLike.exists_of_lt (show Submodule.span ℝ ({v} : Set (Fin 3 → ℝ)) < ⊤ from
      lt_top_iff_ne_top.mpr hspan)
  let a : ℝ := ε / (2 * (‖w‖ + 1))
  have ha : 0 < a := div_pos hε (by positivity)
  have haw : ‖a • w‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    have hd : 0 < 2 * (‖w‖ + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith [norm_nonneg w]
  have hvaw : v + a • w ≠ 0 := by
    intro hz
    apply hw
    apply (Submodule.smul_mem_iff _ ha.ne').mp
    have : a • w = -v := by simpa using congrArg (fun z => z - v) hz
    rw [this]
    exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  let r : apm_t98a03_RP2 := Projectivization.mk ℝ (v + a • w) hvaw
  refine ⟨r, ?_, ?_⟩
  · intro heq
    have hm : Projectivization.mk ℝ (v + a • w) hvaw =
        Projectivization.mk ℝ v hv := by simpa [r, v, Projectivization.mk_rep] using heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp hm
    have hmem : v + a • w ∈ Submodule.span ℝ ({v} : Set (Fin 3 → ℝ)) := by
      rw [← hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    apply hw
    have ht := Submodule.sub_mem _ hmem (Submodule.subset_span (by simp) :
      v ∈ Submodule.span ℝ ({v} : Set (Fin 3 → ℝ)))
    have : a • w ∈ Submodule.span ℝ ({v} : Set (Fin 3 → ℝ)) := by
      simpa only [add_sub_cancel_left] using ht
    exact (Submodule.smul_mem_iff _ ha.ne').mp this
  · apply hball
    rw [Metric.mem_ball]
    change dist (⟨v + a • w, hvaw⟩ : {z : Fin 3 → ℝ // z ≠ 0}) ⟨v, hv⟩ < ε
    change ‖(v + a • w) - v‖ < ε
    simpa using haw

lemma apm_t98a03_wedge_branches_accumulate
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (U : Set (apm_t98a03_X t₀ r₀)) (hU : IsOpen U)
    (hpU : apm_t98a03_basepoint t₀ r₀ ∈ U) :
    ((U ∩ apm_t98a03_torusBranch t₀ r₀) \ {apm_t98a03_basepoint t₀ r₀}).Nonempty ∧
      ((U ∩ apm_t98a03_rp2Branch t₀ r₀) \ {apm_t98a03_basepoint t₀ r₀}).Nonempty := by
  obtain ⟨t, ht, htU⟩ :=
    apm_t98a03_wedge_branches_accumulate_aux_torus t₀ r₀ U hU hpU
  obtain ⟨r, hr, hrU⟩ :=
    apm_t98a03_wedge_branches_accumulate_aux_rp2 t₀ r₀ U hU hpU
  constructor
  · refine ⟨Quotient.mk _ (Sum.inl t), ⟨⟨htU, ⟨t, rfl⟩⟩, ?_⟩⟩
    intro heq
    have hrel : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀)
        (Sum.inl t) (Sum.inl t₀) := Quotient.exact heq
    rcases apm_t98a03_wedge_branches_intersection_aux_eq_or_base
        t₀ r₀ hrel with h | h
    · exact ht (Sum.inl.inj h)
    · exact ht h.1
  · refine ⟨Quotient.mk _ (Sum.inr r), ⟨⟨hrU, ⟨r, rfl⟩⟩, ?_⟩⟩
    intro heq
    have hrel : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀)
        (Sum.inr r) (Sum.inl t₀) := Quotient.exact heq
    rcases apm_t98a03_wedge_branches_intersection_aux_eq_or_base
        t₀ r₀ hrel with h | h
    · cases h
    · exact hr h.1

/-- Sorry-free assembly of the quotient-geometry facts. -/
lemma apm_t98a03_wedge_point_no_connected_punctured_neighborhood
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ¬ apm_t98a03_HasConnectedPuncturedNeighborhood
        (Set.univ : Set (apm_t98a03_X t₀ r₀))
        (apm_t98a03_basepoint t₀ r₀) := by
  rintro ⟨U, hU, hpU, hpre⟩
  have hc := apm_t98a03_wedge_branches_closed t₀ r₀
  have ha := apm_t98a03_wedge_branches_accumulate t₀ r₀ U hU hpU
  have hnot := apm_t98a03_union_closed_punctured_not_preconnected
    hc.1 hc.2 (apm_t98a03_wedge_branches_intersection t₀ r₀) ha.1 ha.2
  apply hnot
  rw [apm_t98a03_wedge_branches_cover]
  simpa using hpre

/-- Seat: Euclidean punctured balls are preconnected in every dimension but one. -/
lemma apm_t98a03_euclidean_punctured_neighborhood_of_dim_ne_one
    (n : ℕ) (hn : n ≠ 1) (W : Set (EuclideanSpace ℝ (Fin n)))
    (hW : IsOpen W) {x} (hx : x ∈ W) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ IsPreconnected (V \ {x}) := by
  rcases n with (_ | n)
  · refine ⟨W, hW, hx, Subset.rfl, ?_⟩
    have hdiff : W \ {x} = ∅ := by
      ext y
      constructor
      · rintro ⟨_, hy⟩
        exact (hy (Subsingleton.elim y x)).elim
      · simp
    rw [hdiff]
    exact isPreconnected_empty
  · have hnpos : 0 < n := by
      rcases n with (_ | n)
      · exact (hn rfl).elim
      · omega
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x hx
    refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hrW, ?_⟩
    let A : Set (ℝ × EuclideanSpace ℝ (Fin (n + 1))) :=
      Set.Ioo 0 r ×ˢ Metric.sphere 0 1
    let f : ℝ × EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1)) := fun q => x + q.1 • q.2
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
      rw [← Module.finrank_eq_rank]
      rw [finrank_euclideanSpace_fin]
      exact_mod_cast (show 1 < n + 1 by omega)
    have hA : IsPreconnected A :=
      ordConnected_Ioo.isPreconnected.prod
        (isPathConnected_sphere hrank 0 (r := 1) (by norm_num)).isConnected.isPreconnected
    have hf : Continuous f :=
      continuous_const.add (continuous_fst.smul continuous_snd)
    have himage : f '' A = Metric.ball x r \ {x} := by
      ext y
      constructor
      · rintro ⟨q, ⟨hq, hu⟩, rfl⟩
        have hq0 : 0 < q.1 := hq.1
        have hu_norm : ‖q.2‖ = 1 := by
          simpa [Metric.mem_sphere] using hu
        constructor
        · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            hu_norm, mul_one]
          simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq.2
        · simp only [mem_singleton_iff]
          intro heq
          have hz : q.1 • q.2 = 0 := by
            simpa [f] using congrArg (fun z => z - x) heq
          exact hq0.ne' (smul_eq_zero.mp hz |>.resolve_right (by
            intro hzero
            simpa [hzero] using hu_norm))
      · rintro ⟨hyball, hyx⟩
        let ρ : ℝ := ‖y - x‖
        let u : EuclideanSpace ℝ (Fin (n + 1)) := ρ⁻¹ • (y - x)
        have hρ : 0 < ρ := by
          rw [show ρ = dist y x by simp [ρ, dist_eq_norm]]
          exact dist_pos.mpr (by simpa [mem_singleton_iff] using hyx)
        have hρr : ρ < r := by
          rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hyball
          simpa [ρ, norm_sub_rev] using hyball
        have hu : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]
          rw [show ‖u‖ = |ρ⁻¹| * ‖y - x‖ by simp [u, norm_smul]]
          rw [abs_of_pos (inv_pos.mpr hρ)]
          exact inv_mul_cancel₀ hρ.ne'
        refine ⟨(ρ, u), ⟨⟨hρ, hρr⟩, hu⟩, ?_⟩
        simp [f, u, hρ.ne']
    rw [← himage]
    exact hA.image _ hf.continuousOn

/-- Seat: chart transport, with its Euclidean input explicit for parallel proof. -/
lemma apm_t98a03_manifold_punctured_neighborhood_of_dim_ne_one
    {X : Type*} [TopologicalSpace X] (n : ℕ)
    (charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) X)
    (hman : let _ := charts
      IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0 X)
    (hn : n ≠ 1)
    (heuclid : ∀ (W : Set (EuclideanSpace ℝ (Fin n))), IsOpen W →
      ∀ x ∈ W, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ IsPreconnected (V \ {x})) :
    ∀ p : X, apm_t98a03_HasConnectedPuncturedNeighborhood Set.univ p := by
  letI := charts
  haveI := hman
  intro p
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  obtain ⟨V, hVopen, hpV, hVtarget, hVconn⟩ :=
    heuclid e.target e.open_target (e p)
      (mem_chart_target (EuclideanSpace ℝ (Fin n)) p)
  refine ⟨e.source ∩ e ⁻¹' V, e.isOpen_inter_preimage hVopen,
    ⟨mem_chart_source _ _, hpV⟩, ?_⟩
  have hcont : ContinuousOn e.symm (V \ {e p}) :=
    e.continuousOn_symm.mono (fun y hy ↦ hVtarget hy.1)
  have himage : e.symm '' (V \ {e p}) =
      (((e.source ∩ e ⁻¹' V) ∩ Set.univ) \ {p}) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyV, hyp⟩, rfl⟩
      have hyT : y ∈ e.target := hVtarget hyV
      have hzS : e.symm y ∈ e.source := e.map_target hyT
      refine ⟨⟨⟨hzS, ?_⟩, trivial⟩, ?_⟩
      · simpa [e.right_inv hyT] using hyV
      · intro hz
        apply hyp
        have := congrArg e hz
        simpa only [mem_singleton_iff, e.right_inv hyT] using this
    · rintro ⟨⟨⟨hzS, hzV⟩, -⟩, hzp⟩
      refine ⟨e z, ⟨hzV, ?_⟩, ?_⟩
      · intro heq
        apply hzp
        simp only [mem_singleton_iff]
        calc
          z = e.symm (e z) := (e.left_inv hzS).symm
          _ = e.symm (e p) := congrArg e.symm heq
          _ = p := e.left_inv (mem_chart_source _ _)
      · exact e.left_inv hzS
  have h := hVconn.image e.symm hcont
  rw [himage] at h
  exact h

/-- A point has arbitrarily small preconnected punctured neighborhoods. -/
def apm_t98a03_HasPuncturedPreconnectedBasis
    {X : Type*} [TopologicalSpace X] (p : X) : Prop :=
  ∀ U : Set X, IsOpen U → p ∈ U →
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ IsPreconnected (V \ {p})

/-- Seat: a torus point away from the gluing point retains its plane property. -/
lemma apm_t98a03_wedge_has_plane_point_aux_prod_exp_local :
    IsLocalHomeomorph
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (Circle.exp (x 0), Circle.exp (x 1))) := by
  intro x
  obtain ⟨e₀, hx₀, he₀⟩ := isLocalHomeomorph_circleExp (x 0)
  obtain ⟨e₁, hx₁, he₁⟩ := isLocalHomeomorph_circleExp (x 1)
  let h : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow (X := ℝ))
  refine ⟨h.toOpenPartialHomeomorph.trans (e₀.prod e₁), ?_, ?_⟩
  · simp [h, hx₀, hx₁]
  · funext y
    simp [h, ← he₀, ← he₁]

lemma apm_t98a03_wedge_has_plane_point
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ p : apm_t98a03_X t₀ r₀,
      apm_t98a03_HasPuncturedPreconnectedBasis p := by
  classical
  let F : EuclideanSpace ℝ (Fin 2) → apm_t98a03_Torus := fun x =>
    (Circle.exp (x 0), Circle.exp (x 1))
  let t' : apm_t98a03_Torus := (1, 1)
  let t'' : apm_t98a03_Torus := (Circle.exp Real.pi, 1)
  have htt : t'' ≠ t' := by
    intro h
    exact Circle.exp_pi_ne_one (congrArg Prod.fst h)
  let t : apm_t98a03_Torus := if t' ≠ t₀ then t' else t''
  have ht : t ≠ t₀ := by
    simp only [t]
    split_ifs with h
    · exact h
    · intro heq
      exact htt (heq.trans (not_ne_iff.mp h).symm)
  let z : EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow (X := ℝ))).symm (Complex.arg t.1, Complex.arg t.2)
  have hFz : F z = t := by
    apply Prod.ext
    · exact Circle.exp_arg t.1
    · exact Circle.exp_arg t.2
  let q : Sum apm_t98a03_Torus apm_t98a03_RP2 → apm_t98a03_X t₀ r₀ :=
    fun s => Quotient.mk _ s
  refine ⟨q (.inl t), ?_⟩
  intro U hU hpU
  have hFlocal : IsLocalHomeomorph F := by
    simpa [F] using apm_t98a03_wedge_has_plane_point_aux_prod_exp_local
  obtain ⟨e, hze, he⟩ := hFlocal z
  let W : Set (EuclideanSpace ℝ (Fin 2)) :=
    e.source ∩ F ⁻¹' ((fun a => q (.inl a)) ⁻¹' U) ∩ F ⁻¹' ({t₀}ᶜ)
  have hFcont : Continuous F := by
    exact (Circle.exp.continuous.comp (EuclideanSpace.proj 0).continuous).prodMk
      (Circle.exp.continuous.comp (EuclideanSpace.proj 1).continuous)
  have hWopen : IsOpen W := by
    exact (e.open_source.inter
      (hU.preimage (continuous_coinduced_rng.comp
        (continuous_inl.comp hFcont)))).inter
      (isOpen_compl_singleton.preimage hFcont)
  have hzW : z ∈ W := by
    refine ⟨⟨hze, ?_⟩, ?_⟩
    · simpa [q, hFz] using hpU
    · simpa [hFz] using ht
  obtain ⟨V, hVopen, hzV, hVW, hVpre⟩ :=
    apm_t98a03_plane_punctured_neighborhood W hWopen hzW
  let A : Set apm_t98a03_Torus := F '' V
  let N : Set (apm_t98a03_X t₀ r₀) := q '' (Sum.inl '' A)
  have hFinj : Set.InjOn F V := by
    intro x hx y hy hxy
    have hxsrc : x ∈ e.source := (hVW hx).1.1
    have hysrc : y ∈ e.source := (hVW hy).1.1
    have : e x = e y := by simpa [he] using hxy
    exact e.injOn hxsrc hysrc this
  have hAt₀ : t₀ ∉ A := by
    rintro ⟨x, hx, hxt⟩
    exact (hVW hx).2 hxt
  have hAopen : IsOpen A := by
    rw [show A = e '' V by ext y; simp [A, he]]
    exact e.isOpen_image_of_subset_source hVopen (fun _ hx => (hVW hx).1.1)
  have hpreimage : q ⁻¹' N = Sum.inl '' A := by
    ext s
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hs⟩
      have hrel : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀) s (.inl a) :=
        (Quotient.exact hs).symm
      rcases apm_t98a03_wedge_branches_intersection_aux_eq_or_base
          t₀ r₀ hrel with hsa | ⟨hsbase, habase⟩
      · subst s
        exact ⟨a, ha, rfl⟩
      · change a = t₀ at habase
        subst a
        exact (hAt₀ ha).elim
    · rintro ⟨a, ha, rfl⟩
      exact ⟨.inl a, ⟨a, ha, rfl⟩, rfl⟩
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · rw [isOpen_coinduced, hpreimage]
    simpa using isOpenMap_inl _ hAopen
  · exact ⟨.inl t, ⟨t, ⟨z, hzV, hFz⟩, rfl⟩, rfl⟩
  · rintro y ⟨_, ⟨a, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    have hxU : q (.inl (F x)) ∈ U := (hVW hx).1.2
    exact hxU
  · have himage : (fun x => q (.inl (F x))) '' (V \ {z}) =
        N \ {q (.inl t)} := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxV, hxz⟩, rfl⟩
        refine ⟨⟨.inl (F x), ⟨F x, ⟨x, hxV, rfl⟩, rfl⟩, rfl⟩, ?_⟩
        intro heq
        have hrel : Relation.EqvGen (apm_t98a03_wedgeRel t₀ r₀)
            (.inl (F x)) (.inl t) := Quotient.exact heq
        rcases apm_t98a03_wedge_branches_intersection_aux_eq_or_base
            t₀ r₀ hrel with hsame | ⟨_, htbase⟩
        · apply hxz
          apply hFinj hxV hzV
          simpa [hFz] using Sum.inl.inj hsame
        · exact ht (by simpa using htbase)
      · rintro ⟨⟨_, ⟨a, ⟨x, hxV, hxa⟩, rfl⟩, rfl⟩, hyne⟩
        subst a
        refine ⟨x, ⟨hxV, ?_⟩, rfl⟩
        intro hxz
        subst x
        exact hyne (by simp [hFz])
    rw [← himage]
    exact hVpre.image _
      ((continuous_coinduced_rng.comp continuous_inl).comp hFcont).continuousOn

/-- Seat: a one-manifold has the opposite local puncture property. -/
lemma apm_t98a03_one_manifold_punctured_obstruction
    {X : Type*} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanSpace ℝ (Fin 1)) X)
    (hman : let _ := charts
      IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) 0 X) :
    ∀ p : X, ¬ apm_t98a03_HasPuncturedPreconnectedBasis p := by
  letI := charts
  intro p hp
  let e := extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) p
  have hp_source : p ∈ e.source := mem_extChartAt_source p
  obtain ⟨V, hVopen, hpV, hVsub, hVconn⟩ :=
    hp e.source (isOpen_extChartAt_source (I := 𝓘(ℝ,
      EuclideanSpace ℝ (Fin 1))) p) hp_source
  have hVsource : V ⊆ e.source := hVsub
  have himage_open : IsOpen (e '' V) := by
    rw [e.image_eq_target_inter_inv_preimage hVsource]
    exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ,
      EuclideanSpace ℝ (Fin 1))) p).isOpen_inter_preimage
        (isOpen_extChartAt_target (I := 𝓘(ℝ,
          EuclideanSpace ℝ (Fin 1))) p) hVopen
  have hep : e p ∈ e '' V := ⟨p, hpV, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 himage_open (e p) hep
  let v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  let a := e p - (ε / 2) • v
  let b := e p + (ε / 2) • v
  have ha_ball : a ∈ Metric.ball (e p) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp [a, v, norm_smul, abs_of_pos hε]
    linarith
  have hb_ball : b ∈ Metric.ball (e p) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp [b, v, norm_smul, abs_of_pos hε]
    linarith
  obtain ⟨xa, hxaV, hxa⟩ := hball ha_ball
  obtain ⟨xb, hxbV, hxb⟩ := hball hb_ball
  have hxa_ne : xa ≠ p := by
    intro h
    subst xa
    have h : a = e p := hxa.symm
    have h' := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) h
    simp [a, v, hε.ne'] at h'
  have hxb_ne : xb ≠ p := by
    intro h
    subst xb
    have h : b = e p := hxb.symm
    have h' := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) h
    simp [b, v, hε.ne'] at h'
  let f : X → ℝ := fun x => EuclideanSpace.proj 0 (e x)
  have hfcont : ContinuousOn f (V \ {p}) :=
    (EuclideanSpace.proj 0).continuous.continuousOn.comp
      ((continuousOn_extChartAt (I := 𝓘(ℝ,
        EuclideanSpace ℝ (Fin 1))) p).mono (diff_subset.trans hVsource))
      (fun _ _ => Set.mem_univ _)
  have himage_conn : IsPreconnected (f '' (V \ {p})) :=
    hVconn.image f hfcont
  have ha_mem : a 0 ∈ f '' (V \ {p}) :=
    ⟨xa, ⟨hxaV, by simpa using hxa_ne⟩, by simp [f, hxa]⟩
  have hb_mem : b 0 ∈ f '' (V \ {p}) :=
    ⟨xb, ⟨hxbV, by simpa using hxb_ne⟩, by simp [f, hxb]⟩
  have hbetween : e p 0 ∈ Set.Icc (a 0) (b 0) := by
    simp [a, b, v]
    exact (div_nonneg hε.le (by norm_num))
  have hep_image : e p 0 ∈ f '' (V \ {p}) :=
    himage_conn.Icc_subset ha_mem hb_mem hbetween
  rcases hep_image with ⟨x, ⟨hxV, hxp⟩, hxe⟩
  have hxsource : x ∈ e.source := hVsource hxV
  have hcoord : e x = e p := by
    ext i
    fin_cases i
    exact hxe
  have hx : x = p := e.injOn hxsource hp_source hcoord
  exact hxp (by simpa [hx])

/-- LIBRARY: the wedge point separates two punctured surface neighborhoods. -/
theorem apm_t98a03_wedge_not_manifold
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ¬apm_t98a03_IsTopologicalManifold (apm_t98a03_X t₀ r₀) := by
  rintro ⟨_, n, charts, hman⟩
  by_cases hn : n = 1
  · subst n
    obtain ⟨p, hp⟩ := apm_t98a03_wedge_has_plane_point t₀ r₀
    exact apm_t98a03_one_manifold_punctured_obstruction charts hman p hp
  · have heuclid := apm_t98a03_euclidean_punctured_neighborhood_of_dim_ne_one n hn
    have hlocal := apm_t98a03_manifold_punctured_neighborhood_of_dim_ne_one
      n charts hman hn (fun W hW x hx => heuclid W hW hx)
    exact apm_t98a03_wedge_point_no_connected_punctured_neighborhood t₀ r₀
      (hlocal (apm_t98a03_basepoint t₀ r₀))

/-- LIBRARY: van Kampen for this literal quotient, plus the torus and RP² computations. -/
theorem apm_t98a03_fundamentalGroup
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Nonempty
      (FundamentalGroup (apm_t98a03_X t₀ r₀) (apm_t98a03_basepoint t₀ r₀) ≃*
        apm_t98a03_expectedFundamentalGroup) := by
  sorry

/-- LIBRARY: realize the cyclic transitive action on `Fin 3` as a cover. -/
theorem apm_t98a03_regular_threeFoldCover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ C : apm_t98a03_Cover (apm_t98a03_X t₀ r₀),
      apm_t98a03_IsConnectedThreeFoldCover C ∧ apm_t98a03_IsRegularCover C := by
  sorry

/-- LIBRARY: realize the transitive `S₃` action with nonnormal point stabilizer. -/
theorem apm_t98a03_irregular_threeFoldCover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ C : apm_t98a03_Cover (apm_t98a03_X t₀ r₀),
      apm_t98a03_IsConnectedThreeFoldCover C ∧ ¬apm_t98a03_IsRegularCover C := by
  sorry

theorem apm_t98a03
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    let X := apm_t98a03_X t₀ r₀
    let x₀ := apm_t98a03_basepoint t₀ r₀
    (¬apm_t98a03_IsTopologicalManifold X) ∧
    Nonempty
      (FundamentalGroup X x₀ ≃* apm_t98a03_expectedFundamentalGroup) ∧
    (∃ C : apm_t98a03_Cover X,
      apm_t98a03_IsConnectedThreeFoldCover C ∧
        apm_t98a03_IsRegularCover C) ∧
    (∃ C : apm_t98a03_Cover X,
      apm_t98a03_IsConnectedThreeFoldCover C ∧
        ¬apm_t98a03_IsRegularCover C) := by
  exact ⟨apm_t98a03_wedge_not_manifold t₀ r₀,
    apm_t98a03_fundamentalGroup t₀ r₀,
    apm_t98a03_regular_threeFoldCover t₀ r₀,
    apm_t98a03_irregular_threeFoldCover t₀ r₀⟩

#print axioms apm_t98a03

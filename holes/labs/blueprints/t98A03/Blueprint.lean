import Mathlib
import Mathlib.Topology.Constructions.SumProd
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.ProjectiveQuotientDescent

/-! # APM t98A03 — blueprint

The four mathematical conclusions are assembled sorry-free over seat-sized leaves.
The final theorem is their conjunction.
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

/-! ## Part B: the fundamental group

Route: the literal quotient is homeomorphic to the library point wedge
`ConstructionTargets.PointWedgeQuotient.Wedge t₀ r₀`; apply
`genericPointWedgeNormalizedFundamentalGroupEquiv` with explicit open
contractible neighbourhoods of both basepoints, then the torus computation
(product of two circles) and the projective-plane computation (copied from the
closed problem t92J05).

The following block is copied verbatim (prefix renamed `apm_t92J05_` →
`apm_t98a03_t92_`) from the sorry-free `problems/t92J05/lean/Main.lean`. -/

abbrev apm_t98a03_t92_S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

def apm_t98a03_t92_fundamentalGroup_prod_equiv
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (b : B) :
    FundamentalGroup (A × B) (a, b) ≃*
      FundamentalGroup A a × FundamentalGroup B b where
  toFun p := (Path.Homotopic.projLeft p, Path.Homotopic.projRight p)
  invFun p := Path.Homotopic.prod p.1 p.2
  left_inv p := Path.Homotopic.prod_projLeft_projRight p
  right_inv p := by
    ext
    · exact Path.Homotopic.projLeft_prod p.1 p.2
    · exact Path.Homotopic.projRight_prod p.1 p.2
  map_mul' p q := by
    apply Prod.ext
    · simpa only [CategoryTheory.End.mul_def] using
        (FundamentalGroupoidFunctor.projLeft
          (TopCat.of A) (TopCat.of B)).map_comp q p
    · simpa only [CategoryTheory.End.mul_def] using
        (FundamentalGroupoidFunctor.projRight
          (TopCat.of A) (TopCat.of B)).map_comp q p


abbrev apm_t98a03_t92_antipodalGroup := Multiplicative (ZMod 2)

def apm_t98a03_t92_antipodalSMul
    (g : apm_t98a03_t92_antipodalGroup) (x : apm_t98a03_t92_S2) : apm_t98a03_t92_S2 :=
  if g.toAdd = 0 then x else -x

instance : MulAction apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 where
  smul := apm_t98a03_t92_antipodalSMul
  one_smul x := by
    change apm_t98a03_t92_antipodalSMul (.ofAdd 0) x = x
    simp [apm_t98a03_t92_antipodalSMul]
  mul_smul g h x := by
    change apm_t98a03_t92_antipodalSMul (g * h) x =
      apm_t98a03_t92_antipodalSMul g (apm_t98a03_t92_antipodalSMul h x)
    fin_cases g <;> fin_cases h
    · change apm_t98a03_t92_antipodalSMul (.ofAdd 0) x =
        apm_t98a03_t92_antipodalSMul (.ofAdd 0)
          (apm_t98a03_t92_antipodalSMul (.ofAdd 0) x)
      simp [apm_t98a03_t92_antipodalSMul]
    · change apm_t98a03_t92_antipodalSMul (.ofAdd 1) x =
        apm_t98a03_t92_antipodalSMul (.ofAdd 0)
          (apm_t98a03_t92_antipodalSMul (.ofAdd 1) x)
      simp [apm_t98a03_t92_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t98a03_t92_antipodalSMul (.ofAdd 1) x =
        apm_t98a03_t92_antipodalSMul (.ofAdd 1)
          (apm_t98a03_t92_antipodalSMul (.ofAdd 0) x)
      simp [apm_t98a03_t92_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t98a03_t92_antipodalSMul (.ofAdd 0) x =
        apm_t98a03_t92_antipodalSMul (.ofAdd 1)
          (apm_t98a03_t92_antipodalSMul (.ofAdd 1) x)
      simp [apm_t98a03_t92_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]

instance : ContinuousConstSMul apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 where
  continuous_const_smul g := by
    fin_cases g
    · simpa [apm_t98a03_t92_antipodalSMul] using
        (continuous_id : Continuous (id : apm_t98a03_t92_S2 → apm_t98a03_t92_S2))
    · exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- **LIBRARY.** The antipodal `ZMod 2` action on the unit two-sphere is free. -/
lemma apm_t98a03_t92_antipodalAction_free :
    ∀ g : apm_t98a03_t92_antipodalGroup, ∀ x : apm_t98a03_t92_S2,
      g • x = x → g = 1 := by
  intro g x hx
  fin_cases g
  · rfl
  · exfalso
    have hneg : -(x : EuclideanSpace ℝ (Fin 3)) = x := by
      exact congrArg Subtype.val hx
    have hx0 : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
        calc
          (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = x + x := by
            exact two_smul ℝ (x : EuclideanSpace ℝ (Fin 3))
          _ = -(x : EuclideanSpace ℝ (Fin 3)) + x :=
            congrArg (fun y => y + (x : EuclideanSpace ℝ (Fin 3))) hneg.symm
          _ = 0 := neg_add_cancel (x : EuclideanSpace ℝ (Fin 3))
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    rw [hx0, norm_zero] at hnorm
    norm_num at hnorm

/-- **LIBRARY.** The finite antipodal action is properly discontinuous. -/
lemma apm_t98a03_t92_antipodalAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 := by
  infer_instance

/-- **LIBRARY.** Real projective two-space is the orbit quotient of the unit
two-sphere by the antipodal action. -/
def apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP
    (x : apm_t98a03_t92_S2) : apm_t98a03_RP2 :=
  Projectivization.mk ℝ x.1.ofLp (by
    intro hx
    have := x.property
    have hx' : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      apply WithLp.ofLp_injective 2
      simpa using hx
    rw [Metric.mem_sphere, dist_zero_right, hx', norm_zero] at this
    norm_num at this)

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous :
    Continuous apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP := by
  apply continuous_quotient_mk'.comp
  exact Continuous.subtype_mk
    (EuclideanSpace.equiv (Fin 3) ℝ |>.continuous.comp continuous_subtype_val) _

def apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0
    (v : {v : Fin 3 → ℝ // v ≠ 0}) :
    MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 :=
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (v : Fin 3 → ℝ)
  Quotient.mk'' ⟨(‖w‖⁻¹ : ℝ) • w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (by
      change WithLp.toLp 2 (v : Fin 3 → ℝ) ≠ 0
      exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective.ne v.property)⟩

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_continuous :
    Continuous apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 := by
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  · let e : (Fin 3 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
    exact ((continuous_norm.comp (e.continuous.comp continuous_subtype_val)).inv₀
      (fun (v : {v : Fin 3 → ℝ // v ≠ 0}) hv => v.property (by
        have := congrArg WithLp.ofLp (norm_eq_zero.mp hv)
        simpa using this))).smul
        (e.continuous.comp continuous_subtype_val)

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_scale
    (a b : {v : Fin 3 → ℝ // v ≠ 0}) (t : ℝ)
    (h : (a : Fin 3 → ℝ) = t • b) :
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 a =
      apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 b := by
  have ht : t ≠ 0 := by
    intro ht
    apply a.property
    simpa [ht] using h
  apply Quotient.sound
  by_cases hpos : 0 < t
  · refine ⟨Multiplicative.ofAdd 0, ?_⟩
    apply Subtype.ext
    change (‖WithLp.toLp 2 (b : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (b : Fin 3 → ℝ) =
      (‖WithLp.toLp 2 (a : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (a : Fin 3 → ℝ)
    rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    rw [mul_inv_rev, smul_smul]
    congr 1
    field_simp
  · refine ⟨Multiplicative.ofAdd 1, ?_⟩
    apply Subtype.ext
    change -_ = _
    have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht
    change -((‖WithLp.toLp 2 (b : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (b : Fin 3 → ℝ)) =
      (‖WithLp.toLp 2 (a : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (a : Fin 3 → ℝ)
    rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_neg htneg]
    rw [mul_inv_rev]
    simp only [one_div, neg_smul, smul_smul]
    congr 1
    field_simp
    simp

def apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
    (p : apm_t98a03_RP2) :
    MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 :=
  Projectivization.lift
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_scale p

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous :
    Continuous apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ := by
  apply isQuotientMap_quot_mk.continuous_iff.mpr
  exact apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_continuous

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP_invariant
    (x y : apm_t98a03_t92_S2)
    (h : MulAction.orbitRel apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 x y) :
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP x =
      apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP y := by
  rcases h with ⟨g, rfl⟩
  fin_cases g
  · rfl
  · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨-1, ?_⟩
    change (-1 : ℝ) • y.1.ofLp =
      (apm_t98a03_t92_antipodalSMul (Multiplicative.ofAdd 1) y).1.ofLp
    ext i
    simp [apm_t98a03_t92_antipodalSMul]

def apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ :
    MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 →
      apm_t98a03_RP2 :=
  Quotient.lift
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP_invariant

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous :
    Continuous apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ := by
  apply isQuotientMap_quot_mk.continuous_iff.mpr
  exact apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_left
    (q : MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2) :
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
      (apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    apply Quotient.sound
    refine ⟨Multiplicative.ofAdd 0, ?_⟩
    apply Subtype.ext
    change (x : EuclideanSpace ℝ (Fin 3)) =
      (‖WithLp.toLp 2 x.1.ofLp‖⁻¹ : ℝ) • WithLp.toLp 2 x.1.ofLp
    have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa [Metric.mem_sphere] using x.property
    simp [hx]

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_right
    (p : apm_t98a03_RP2) :
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
      (apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨‖WithLp.toLp 2 v‖⁻¹, ?_⟩
    ext i
    rfl

lemma apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient :
    Nonempty
      (MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 ≃ₜ
        apm_t98a03_RP2) := by
  exact ⟨{
    toFun := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
    invFun := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
    left_inv := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_left
    right_inv := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_right
    continuous_toFun := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous
    continuous_invFun := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous }⟩

/-- **LIBRARY.** Specialization of the deck-group quotient theorem to the
antipodal action, with the two action obligations supplied explicitly. -/
lemma apm_t98a03_t92_antipodalQuotient_fundamentalGroup
    (hfree : ∀ g : apm_t98a03_t92_antipodalGroup, ∀ x : apm_t98a03_t92_S2,
      g • x = x → g = 1)
    (hproper : ProperlyDiscontinuousSMul
      apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2)
    (x : apm_t98a03_t92_S2) :
    Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2)
          (Quotient.mk _ x) ≃*
        apm_t98a03_t92_antipodalGroup) := by
  letI : ProperlyDiscontinuousSMul
      apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 := hproper
  letI : SimplyConnectedSpace apm_t98a03_t92_S2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
      2 (by norm_num)
  letI : LocPathConnectedSpace apm_t98a03_t92_S2 :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) apm_t98a03_t92_S2
  exact
    ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      hfree x

/-- **LIBRARY.** A quotient/projectivization homeomorphism transports the deck
calculation to at least one concrete projective-plane basepoint. -/
lemma apm_t98a03_t92_projectivePlane_fundamentalGroup_at_one_point
    (e : MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 ≃ₜ
      apm_t98a03_RP2)
    (hdeck : ∀ x : apm_t98a03_t92_S2,
      Nonempty
        (FundamentalGroup
            (MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2)
            (Quotient.mk _ x) ≃*
          apm_t98a03_t92_antipodalGroup)) :
    ∃ x : apm_t98a03_RP2,
      Nonempty (FundamentalGroup apm_t98a03_RP2 x ≃* Multiplicative (ZMod 2)) := by
  let x : apm_t98a03_t92_S2 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  refine ⟨e (Quotient.mk _ x), ?_⟩
  obtain ⟨d⟩ := hdeck x
  exact
    ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
        e (Quotient.mk _ x)).symm.trans d⟩

/-- **LIBRARY.** The concrete real projective plane is path connected. -/
lemma apm_t98a03_t92_projectivePlane_pathConnected :
    PathConnectedSpace apm_t98a03_RP2 := by
  let V := Fin 3 → ℝ
  have hrank : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank]
    norm_num [V]
  have hnonzero : IsPathConnected ({0}ᶜ : Set V) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  letI : PathConnectedSpace {v : V // v ≠ 0} := by
    change PathConnectedSpace {v : V // v ∈ ({0}ᶜ : Set V)}
    exact isPathConnected_iff_pathConnectedSpace.mp hnonzero
  exact (Quotient.mk'_surjective (s := projectivizationSetoid ℝ V)).pathConnectedSpace
    continuous_quotient_mk'

/-- **LIBRARY.** On a path-connected space, one computed fundamental group
determines it at every basepoint. -/
lemma apm_t98a03_t92_fundamentalGroup_all_basepoints
    {X G : Type} [TopologicalSpace X] [Group G]
    (hpath : PathConnectedSpace X)
    (hone : ∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* G)) :
    ∀ x : X, Nonempty (FundamentalGroup X x ≃* G) := by
  letI : PathConnectedSpace X := hpath
  obtain ⟨x₀, e⟩ := hone
  intro x
  exact
    ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀).trans e.some⟩

/-- The antipodal two-sphere cover computes the fundamental group of the
concrete real projective plane at every basepoint. -/
theorem apm_t98a03_t92_bridge_projectivePlane_fundamentalGroup :
    ∀ x : apm_t98a03_RP2,
      Nonempty
        (FundamentalGroup apm_t98a03_RP2 x ≃*
          Multiplicative (ZMod 2)) := by
  letI := apm_t98a03_t92_antipodalAction_properlyDiscontinuous
  have hdeck := apm_t98a03_t92_antipodalQuotient_fundamentalGroup
    apm_t98a03_t92_antipodalAction_free
    apm_t98a03_t92_antipodalAction_properlyDiscontinuous
  obtain ⟨e⟩ := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient
  exact apm_t98a03_t92_fundamentalGroup_all_basepoints
    apm_t98a03_t92_projectivePlane_pathConnected
    (apm_t98a03_t92_projectivePlane_fundamentalGroup_at_one_point e hdeck)

/-! End of the block copied from t92J05. -/

instance apm_t98a03_torus_pathConnected : PathConnectedSpace apm_t98a03_Torus where
  nonempty := ⟨((1 : Circle), (1 : Circle))⟩
  joined x y := ⟨(PathConnectedSpace.somePath x.1 y.1).prod (PathConnectedSpace.somePath x.2 y.2)⟩

/-- The torus fundamental group at any basepoint. -/
def apm_t98a03_torus_fundamentalGroup (t : apm_t98a03_Torus) :
    FundamentalGroup apm_t98a03_Torus t ≃* Multiplicative (ℤ × ℤ) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected t ((1 : Circle), (1 : Circle))).trans
    ((apm_t98a03_t92_fundamentalGroup_prod_equiv (1 : Circle) (1 : Circle)).trans
      ((MulEquiv.prodCongr
          ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
          ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt).trans
        (MulEquiv.prodMultiplicative ℤ ℤ).symm))

/-- The literal quotient is the library point wedge (same carrier, same
topology, pointwise-equivalent generating relations). -/
def apm_t98a03_X_homeomorph_wedge
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_X t₀ r₀ ≃ₜ ConstructionTargets.PointWedgeQuotient.Wedge t₀ r₀ :=
  ConstructionTargets.PointWedgeQuotient.quotientHomeomorphOfRelIff
    (apm_t98a03_wedgeRel t₀ r₀) (ConstructionTargets.PointWedgeQuotient.Rel t₀ r₀)
    (by
      intro a b
      constructor
      · rintro ⟨⟩
        exact ConstructionTargets.PointWedgeQuotient.Rel.base
      · rintro ⟨⟩
        exact apm_t98a03_wedgeRel.base)

/-- The open neighbourhood of `c` in the circle obtained by deleting `-c`. -/
def apm_t98a03_circleNbhd (c : Circle) : Set Circle :=
  {z | (z : ℂ) ≠ -(c : ℂ)}

lemma apm_t98a03_circleNbhd_isOpen (c : Circle) : IsOpen (apm_t98a03_circleNbhd c) :=
  isOpen_ne_fun continuous_subtype_val continuous_const

lemma apm_t98a03_circleNbhd_mem (c : Circle) : c ∈ apm_t98a03_circleNbhd c := by
  intro h
  exact Circle.coe_ne_zero c (self_eq_neg.mp h)

/-- Seat (generic): the punctured circle `{z | z ≠ -c}` contracts to `c`,
relative to `c`.

Route: the rotation `Homeomorph.mulLeft c⁻¹ : Circle ≃ₜ Circle` sends `c` to `1`
and `apm_t98a03_circleNbhd c` onto
`ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood` (`{z | z ≠ -1}`);
restrict it to the subtypes (`Homeomorph.subtype` or `Homeomorph.image`/`Set.image`
API) and pull back
`ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood_contraction`
with `ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm`.
Estimated 40–80 lines. -/
lemma apm_t98a03_circleNbhd_contraction (c : Circle) :
    Nonempty
      (ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
        (apm_t98a03_circleNbhd c) ⟨c, apm_t98a03_circleNbhd_mem c⟩) := by
  let e0 : Circle ≃ₜ Circle := Homeomorph.mulLeft c⁻¹
  have he_mem (z : Circle) :
      z ∈ apm_t98a03_circleNbhd c ↔
        e0 z ∈ ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood := by
    change (z : ℂ) ≠ -(c : ℂ) ↔ ((c⁻¹ * z : Circle) : ℂ) ≠ -1
    constructor
    · intro hz h
      apply hz
      have := congrArg (fun w : ℂ ↦ (c : ℂ) * w) h
      simpa using this
    · intro hz h
      apply hz
      change (((c⁻¹ : Circle) : ℂ) * (z : ℂ)) = -1
      rw [h]
      simp
  let e : apm_t98a03_circleNbhd c ≃ₜ
      ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood := {
    toFun z := ⟨e0 z.1, (he_mem z.1).1 z.2⟩
    invFun z := ⟨e0.symm z.1, (he_mem (e0.symm z.1)).2 (by simpa using z.2)⟩
    left_inv z := by
      apply Subtype.ext
      exact e0.symm_apply_apply z.1
    right_inv z := by
      apply Subtype.ext
      exact e0.apply_symm_apply z.1
    continuous_toFun := Continuous.subtype_mk
      (e0.continuous.comp continuous_subtype_val) _
    continuous_invFun := Continuous.subtype_mk
      (e0.symm.continuous.comp continuous_subtype_val) _ }
  have he_base : e ⟨c, apm_t98a03_circleNbhd_mem c⟩ =
      ⟨1, ConstructionTargets.PointWedgeVanKampen.circleBase_mem⟩ := by
    apply Subtype.ext
    simp [e, e0]
  refine ⟨?_⟩
  exact
    ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e
      (he_base.symm ▸
        ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood_contraction)

/-- Product neighbourhood of a torus point. -/
def apm_t98a03_torusNbhd (t₀ : apm_t98a03_Torus) : Set apm_t98a03_Torus :=
  apm_t98a03_circleNbhd t₀.1 ×ˢ apm_t98a03_circleNbhd t₀.2

lemma apm_t98a03_torusNbhd_isOpen (t₀ : apm_t98a03_Torus) :
    IsOpen (apm_t98a03_torusNbhd t₀) :=
  (apm_t98a03_circleNbhd_isOpen _).prod (apm_t98a03_circleNbhd_isOpen _)

lemma apm_t98a03_torusNbhd_mem (t₀ : apm_t98a03_Torus) :
    t₀ ∈ apm_t98a03_torusNbhd t₀ :=
  ⟨apm_t98a03_circleNbhd_mem _, apm_t98a03_circleNbhd_mem _⟩

/-- Assembly: product of the two circle contractions. -/
def apm_t98a03_torusNbhd_contraction (t₀ : apm_t98a03_Torus) :
    ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      (apm_t98a03_torusNbhd t₀) ⟨t₀, apm_t98a03_torusNbhd_mem t₀⟩ :=
  ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm
    (Homeomorph.Set.prod (apm_t98a03_circleNbhd t₀.1) (apm_t98a03_circleNbhd t₀.2))
    (ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction.prod
      (apm_t98a03_circleNbhd_contraction t₀.1).some
      (apm_t98a03_circleNbhd_contraction t₀.2).some)

/-- The affine chart of `RP²` around `r₀`: lines not orthogonal to `r₀`. -/
def apm_t98a03_rp2Nbhd (r₀ : apm_t98a03_RP2) : Set apm_t98a03_RP2 :=
  {r | dotProduct r.rep r₀.rep ≠ 0}

lemma apm_t98a03_rep_dot_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) (u : Fin 3 → ℝ)
    (h : dotProduct v u ≠ 0) :
    dotProduct (Projectivization.mk ℝ v hv).rep u ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  rw [← ha, Units.smul_def, smul_dotProduct, smul_eq_mul]
  exact mul_ne_zero a.ne_zero h

lemma apm_t98a03_rp2Nbhd_mem (r₀ : apm_t98a03_RP2) : r₀ ∈ apm_t98a03_rp2Nbhd r₀ := by
  intro h
  exact r₀.rep_nonzero (dotProduct_self_eq_zero.mp h)

/-- Seat (generic): the affine chart is open.

Route: `isOpen_coinduced`; the preimage under `Projectivization.mk' ℝ` is
`{v | dotProduct v.1 r₀.rep ≠ 0}` (use `Projectivization.exists_smul_eq_mk_rep`
and `Units.ne_zero`, as in `apm_t98a03_rep_dot_ne_zero`, in both directions),
which is open by continuity of `v ↦ dotProduct v r₀.rep`
(`Continuous.dotProduct` / `continuous_finset_sum`) and `isOpen_ne_fun`.
Estimated 25–50 lines. -/
lemma apm_t98a03_rp2Nbhd_isOpen (r₀ : apm_t98a03_RP2) :
    IsOpen (apm_t98a03_rp2Nbhd r₀) := by
  rw [isOpen_coinduced]
  have hpreimage :
      (Projectivization.mk' ℝ) ⁻¹' apm_t98a03_rp2Nbhd r₀ =
        {v : {v : Fin 3 → ℝ // v ≠ 0} | dotProduct v.1 r₀.rep ≠ 0} := by
    ext v
    constructor
    · intro hrep hv
      obtain ⟨a, ha⟩ :=
        Projectivization.exists_smul_eq_mk_rep ℝ v.1 v.2
      apply hrep
      change (Projectivization.mk ℝ v.1 v.2).rep ⬝ᵥ r₀.rep = 0
      rw [← ha, Units.smul_def, smul_dotProduct, smul_eq_mul, hv, mul_zero]
    · exact apm_t98a03_rep_dot_ne_zero v.2 r₀.rep
  rw [hpreimage]
  apply isOpen_ne_fun _ continuous_const
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/-- The homogeneous straight-line formula used to contract the chart. -/
def apm_t98a03_rp2ContractVec (u v : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  (1 - t) • v + (t * (dotProduct v u / dotProduct u u)) • u

lemma apm_t98a03_rp2ContractVec_dot (u v : Fin 3 → ℝ) (hu : dotProduct u u ≠ 0)
    (t : ℝ) :
    dotProduct (apm_t98a03_rp2ContractVec u v t) u = dotProduct v u := by
  simp only [apm_t98a03_rp2ContractVec, add_dotProduct, smul_dotProduct, smul_eq_mul]
  field_simp
  ring

lemma apm_t98a03_rp2ContractVec_ne_zero (u v : Fin 3 → ℝ) (hu : dotProduct u u ≠ 0)
    (hv : dotProduct v u ≠ 0) (t : ℝ) :
    apm_t98a03_rp2ContractVec u v t ≠ 0 := by
  intro h
  apply hv
  rw [← apm_t98a03_rp2ContractVec_dot u v hu t, h, zero_dotProduct]

lemma apm_t98a03_rep_self_dot_ne_zero (r : apm_t98a03_RP2) :
    dotProduct r.rep r.rep ≠ 0 := fun h => r.rep_nonzero (dotProduct_self_eq_zero.mp h)

/-- The contraction of the chart as an explicit map (not yet known continuous). -/
def apm_t98a03_rp2Contract (r₀ : apm_t98a03_RP2)
    (p : unitInterval × apm_t98a03_rp2Nbhd r₀) : apm_t98a03_rp2Nbhd r₀ :=
  ⟨Projectivization.mk ℝ (apm_t98a03_rp2ContractVec r₀.rep p.2.1.rep p.1)
      (apm_t98a03_rp2ContractVec_ne_zero _ _ (apm_t98a03_rep_self_dot_ne_zero r₀) p.2.2 _),
    apm_t98a03_rep_dot_ne_zero _ _ (by
      rw [apm_t98a03_rp2ContractVec_dot _ _ (apm_t98a03_rep_self_dot_ne_zero r₀)]
      exact p.2.2)⟩

/-- Seat (generic): the explicit chart contraction is continuous.

`apm_t98a03_rp2Contract r₀ (t, r) = [(1-t)·v + t·(v·u/u·u)·u]` with `v = r.rep`,
`u = r₀.rep`.  The formula is homogeneous of degree one in `v`, so the map is
`[F(t, v)]` for ANY representative `v` of `r` (`Projectivization.mk_eq_mk_iff'`).
Route: `Projectivization.mk'` is an open quotient map
(`ConstructionTargets.ProjectiveQuotientDescent.projectiveQuotientMap_isOpen`
with `K := ℝ, n := 2`; the instance on `ProjectiveSpaceTopology.Space ℝ 2` is
definitionally ours).  Restrict it to the open saturated preimage
`{v | dotProduct v.1 u ≠ 0}` (`IsOpenQuotientMap.restrictPreimage`), take the
product with `unitInterval` (`IsOpenQuotientMap.prodMap` with `.id`), and check
continuity upstairs, where the map is `(t, v) ↦ mk (F t v)` (continuous into the
subtype by `Continuous.subtype_mk`). Estimated 80–160 lines. -/
lemma apm_t98a03_rp2Contract_continuous_aux_iff (r₀ : apm_t98a03_RP2)
    (v : {v : Fin 3 → ℝ // v ≠ 0}) :
    Projectivization.mk' ℝ v ∈ apm_t98a03_rp2Nbhd r₀ ↔
      dotProduct v.1 r₀.rep ≠ 0 := by
  constructor
  · intro hrep hv
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1 v.2
    apply hrep
    change dotProduct (Projectivization.mk ℝ v.1 v.2).rep r₀.rep = 0
    rw [← ha, Units.smul_def, smul_dotProduct, smul_eq_mul, hv, mul_zero]
  · exact apm_t98a03_rep_dot_ne_zero v.2 _

lemma apm_t98a03_rp2Contract_continuous_aux_open (r₀ : apm_t98a03_RP2) :
    IsOpen (apm_t98a03_rp2Nbhd r₀) := by
  rw [isOpen_coinduced]
  have hc : Continuous (fun v : {v : Fin 3 → ℝ // v ≠ 0} ↦
      dotProduct v.1 r₀.rep) := by
    fun_prop
  have hopen : IsOpen {x : ℝ | x ≠ 0} := isClosed_singleton.isOpen_compl
  convert hopen.preimage hc using 1
  ext v
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  exact apm_t98a03_rp2Contract_continuous_aux_iff r₀ v

lemma apm_t98a03_rp2Contract_continuous (r₀ : apm_t98a03_RP2) :
    Continuous (apm_t98a03_rp2Contract r₀) := by
  let q : {v : Fin 3 → ℝ // v ≠ 0} → apm_t98a03_RP2 :=
    ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 2
  let S : Set apm_t98a03_RP2 := apm_t98a03_rp2Nbhd r₀
  let qS : q ⁻¹' S → S := S.restrictPreimage q
  have hq : IsOpenQuotientMap q := ⟨
    ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 2,
    ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 2,
    ConstructionTargets.ProjectiveQuotientDescent.projectiveQuotientMap_isOpen ℝ 2⟩
  have hqS : IsOpenQuotientMap qS :=
    IsOpenQuotientMap.of_isOpenMap_isQuotientMap
      (hq.isOpenMap.restrictPreimage S)
      (hq.isQuotientMap.restrictPreimage_isOpen
        (apm_t98a03_rp2Contract_continuous_aux_open r₀))
  have hprod : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) qS) :=
    IsOpenQuotientMap.id.prodMap hqS
  rw [← hprod.continuous_comp_iff]
  let F (p : unitInterval × (q ⁻¹' S)) : apm_t98a03_rp2Nbhd r₀ :=
    ⟨q ⟨apm_t98a03_rp2ContractVec r₀.rep p.2.1.1 p.1,
        apm_t98a03_rp2ContractVec_ne_zero _ _
          (apm_t98a03_rep_self_dot_ne_zero r₀)
          ((apm_t98a03_rp2Contract_continuous_aux_iff r₀ p.2.1).mp p.2.2) _⟩,
      apm_t98a03_rep_dot_ne_zero _ _ (by
        rw [apm_t98a03_rp2ContractVec_dot _ _
          (apm_t98a03_rep_self_dot_ne_zero r₀)]
        exact (apm_t98a03_rp2Contract_continuous_aux_iff r₀ p.2.1).mp p.2.2)⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    apply (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 2).comp
    apply Continuous.subtype_mk
    dsimp only [F, apm_t98a03_rp2ContractVec]
    fun_prop
  have heq : apm_t98a03_rp2Contract r₀ ∘
      Prod.map (id : unitInterval → unitInterval) qS = F := by
    funext p
    apply Subtype.ext
    dsimp only [Function.comp_apply, Prod.map_apply, id_eq, qS, S, F,
      apm_t98a03_rp2Contract]
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ p.2.1.1 p.2.1.2
    apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    refine ⟨a, ?_⟩
    change a • apm_t98a03_rp2ContractVec r₀.rep p.2.1.1 p.1 =
      apm_t98a03_rp2ContractVec r₀.rep
        (Projectivization.mk ℝ p.2.1.1 p.2.1.2).rep p.1
    simp only [apm_t98a03_rp2ContractVec]
    rw [← ha]
    simp only [Units.smul_def, smul_add, smul_smul, smul_dotProduct,
      smul_eq_mul]
    module
  rw [heq]
  exact hF

lemma apm_t98a03_rp2Contract_zero (r₀ : apm_t98a03_RP2) (r : apm_t98a03_rp2Nbhd r₀) :
    apm_t98a03_rp2Contract r₀ (0, r) = r := by
  apply Subtype.ext
  simp only [apm_t98a03_rp2Contract, apm_t98a03_rp2ContractVec, Set.Icc.coe_zero,
    sub_zero, one_smul, zero_mul, zero_smul, add_zero]
  exact Projectivization.mk_rep _

lemma apm_t98a03_rp2Contract_one (r₀ : apm_t98a03_RP2) (r : apm_t98a03_rp2Nbhd r₀) :
    apm_t98a03_rp2Contract r₀ (1, r) = ⟨r₀, apm_t98a03_rp2Nbhd_mem r₀⟩ := by
  apply Subtype.ext
  change Projectivization.mk ℝ _ _ = r₀
  conv_rhs => rw [← Projectivization.mk_rep r₀]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨dotProduct r.1.rep r₀.rep / dotProduct r₀.rep r₀.rep, ?_⟩
  simp [apm_t98a03_rp2ContractVec]

lemma apm_t98a03_rp2Contract_fixed (r₀ : apm_t98a03_RP2) (t : unitInterval) :
    apm_t98a03_rp2Contract r₀ (t, ⟨r₀, apm_t98a03_rp2Nbhd_mem r₀⟩) =
      ⟨r₀, apm_t98a03_rp2Nbhd_mem r₀⟩ := by
  apply Subtype.ext
  change Projectivization.mk ℝ _ _ = r₀
  conv_rhs => rw [← Projectivization.mk_rep r₀]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  have hu := apm_t98a03_rep_self_dot_ne_zero r₀
  simp only [apm_t98a03_rp2ContractVec, div_self hu, mul_one, one_smul]
  rw [← add_smul]
  simp

/-- Assembly: the chart contraction as a pointed contraction. -/
def apm_t98a03_rp2Nbhd_contraction (r₀ : apm_t98a03_RP2) :
    ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      (apm_t98a03_rp2Nbhd r₀) ⟨r₀, apm_t98a03_rp2Nbhd_mem r₀⟩ where
  homotopy :=
    { toFun := apm_t98a03_rp2Contract r₀
      continuous_toFun := apm_t98a03_rp2Contract_continuous r₀
      map_zero_left := apm_t98a03_rp2Contract_zero r₀
      map_one_left := apm_t98a03_rp2Contract_one r₀ }
  fixed := apm_t98a03_rp2Contract_fixed r₀

/-- Assembly: van Kampen for this literal quotient, plus the torus and RP²
computations. -/
theorem apm_t98a03_fundamentalGroup
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Nonempty
      (FundamentalGroup (apm_t98a03_X t₀ r₀) (apm_t98a03_basepoint t₀ r₀) ≃*
        apm_t98a03_expectedFundamentalGroup) := by
  letI : PathConnectedSpace apm_t98a03_RP2 := apm_t98a03_t92_projectivePlane_pathConnected
  obtain ⟨eRP⟩ := apm_t98a03_t92_bridge_projectivePlane_fundamentalGroup r₀
  exact ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
      (apm_t98a03_X_homeomorph_wedge t₀ r₀) (apm_t98a03_basepoint t₀ r₀)).trans
    ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeNormalizedFundamentalGroupEquiv
      t₀ r₀ (apm_t98a03_rp2Nbhd r₀) (apm_t98a03_torusNbhd t₀)
      (apm_t98a03_rp2Nbhd_isOpen r₀) (apm_t98a03_torusNbhd_isOpen t₀)
      (apm_t98a03_rp2Nbhd_mem r₀) (apm_t98a03_torusNbhd_mem t₀)
      (apm_t98a03_rp2Nbhd_contraction r₀) (apm_t98a03_torusNbhd_contraction t₀)).trans
      (MulEquiv.coprodCongr (apm_t98a03_torus_fundamentalGroup t₀) eRP))⟩

/-! ## Part C: the two three-sheeted covers

Both covers are written as explicit glued spaces.  Generic machinery first:
`apm_t98a03_Glue σ τ` glues `A ⊕ B` along `σ j ~ τ j` (`j : J`); the base wedge
is the case `J = Unit`.  Given local homeomorphisms `p : A' → A`, `q : B' → B`
whose basepoint fibres are exactly the glued points, the induced map of glued
spaces is a covering map (`apm_t98a03_glueMap_isCoveringMap`, assembled from
Mathlib's `IsCoveringMapOn.of_openPartialHomeomorph`: compact Hausdorff total
space, Hausdorff base, local homeomorphism).

* regular:   `T² ⊔ (Fin 3 × RP²)`, torus sheets `(ζᵏc, t₀.2)` glued to `(k, r₀)`;
  base map `(z,w) ↦ (z³,w)` and `snd`; deck group generated by
  `(z,w) ↦ (ζz,w)`, `(k,r) ↦ (k+1,r)`.
* irregular: `T² ⊔ (S² ⊔ RP²)`, torus sheets glued to `r₀ ∈ RP²`, `s`, `-s`
  (`s` the unit representative of `r₀`); base map on `S²` is the antipodal
  quotient.  The lift of the RP² generator closes up on the RP² sheet but not on
  the sphere sheet, so no deck transformation exchanges those sheets. -/

section Glue

inductive apm_t98a03_GlueRel {J A B : Type} (σ : J → A) (τ : J → B) :
    A ⊕ B → A ⊕ B → Prop
  | glue (j : J) : apm_t98a03_GlueRel σ τ (.inl (σ j)) (.inr (τ j))

/-- `A ⊕ B` with `σ j` identified with `τ j` for every `j`. -/
def apm_t98a03_Glue {J A B : Type} (σ : J → A) (τ : J → B) : Type :=
  Quotient (Relation.EqvGen.setoid (apm_t98a03_GlueRel σ τ))

noncomputable instance {J A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (σ : J → A) (τ : J → B) : TopologicalSpace (apm_t98a03_Glue σ τ) :=
  TopologicalSpace.coinduced
    (fun z : A ⊕ B =>
      (Quotient.mk (Relation.EqvGen.setoid (apm_t98a03_GlueRel σ τ)) z :
        apm_t98a03_Glue σ τ))
    inferInstance

def apm_t98a03_glueMk {J A B : Type} (σ : J → A) (τ : J → B) :
    A ⊕ B → apm_t98a03_Glue σ τ :=
  Quotient.mk _

lemma apm_t98a03_glueMk_continuous {J A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (σ : J → A) (τ : J → B) :
    Continuous (apm_t98a03_glueMk σ τ) :=
  continuous_coinduced_rng

lemma apm_t98a03_glueMk_surjective {J A B : Type} (σ : J → A) (τ : J → B) :
    Function.Surjective (apm_t98a03_glueMk σ τ) :=
  Quotient.mk_surjective

lemma apm_t98a03_glueMk_glue {J A B : Type} (σ : J → A) (τ : J → B) (j : J) :
    apm_t98a03_glueMk σ τ (.inl (σ j)) = apm_t98a03_glueMk σ τ (.inr (τ j)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (apm_t98a03_GlueRel.glue j))

/-- The explicit equivalence relation: equal, or a glued pair. -/
def apm_t98a03_GlueEq {J A B : Type} (σ : J → A) (τ : J → B) (x y : A ⊕ B) : Prop :=
  x = y ∨ ∃ j, (x = .inl (σ j) ∧ y = .inr (τ j)) ∨ (x = .inr (τ j) ∧ y = .inl (σ j))

/-- Seat (generic): with injective gluing maps the classes are the glued pairs
and singletons.

Route: `←` is `Quotient.sound` with `EqvGen.rel`/`symm`.  `→`: `Quotient.exact`
gives `Relation.EqvGen (apm_t98a03_GlueRel σ τ) x y`; induct on it, proving
that `apm_t98a03_GlueEq σ τ` is reflexive, symmetric and transitive
(transitivity: `inl (σ j) ~ inr (τ j) ~ inl (σ j')` forces `j = j'` by
injectivity of `τ`, and dually with `σ`; `Sum.inl.injEq`, `Sum.inr.injEq`,
`reduceCtorEq` close the mixed cases). Estimated 40–80 lines. -/
lemma apm_t98a03_glueMk_eq_iff {J A B : Type} {σ : J → A} {τ : J → B}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ) (x y : A ⊕ B) :
    apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔ apm_t98a03_GlueEq σ τ x y := by
  constructor
  · intro h
    have hxy : Relation.EqvGen (apm_t98a03_GlueRel σ τ) x y := Quotient.exact h
    clear h
    induction hxy with
    | rel x y hrel =>
        cases hrel with
        | glue j => exact Or.inr ⟨j, Or.inl ⟨rfl, rfl⟩⟩
    | refl x => exact Or.inl rfl
    | symm x y _ ih =>
        rcases ih with hxy | ⟨j, hxy | hxy⟩
        · exact Or.inl hxy.symm
        · exact Or.inr ⟨j, Or.inr ⟨hxy.2, hxy.1⟩⟩
        · exact Or.inr ⟨j, Or.inl ⟨hxy.2, hxy.1⟩⟩
    | trans x y z _ _ ihxy ihyz =>
        rcases ihxy with hxy | ⟨j, hxy | hxy⟩
        · subst y
          exact ihyz
        · rcases ihyz with hyz | ⟨k, hyz | hyz⟩
          · subst z
            exact Or.inr ⟨j, Or.inl hxy⟩
          · cases hxy.2.symm.trans hyz.1
          · have hjk : j = k := hτ (Sum.inr.inj (hxy.2.symm.trans hyz.1))
            subst k
            exact Or.inl (hxy.1.trans hyz.2.symm)
        · rcases ihyz with hyz | ⟨k, hyz | hyz⟩
          · subst z
            exact Or.inr ⟨j, Or.inr hxy⟩
          · have hjk : j = k := hσ (Sum.inl.inj (hxy.2.symm.trans hyz.1))
            subst k
            exact Or.inl (hxy.1.trans hyz.2.symm)
          · cases hxy.2.symm.trans hyz.1
  · intro h
    rcases h with rfl | ⟨j, h | h⟩
    · rfl
    · rcases h with ⟨rfl, rfl⟩
      exact apm_t98a03_glueMk_glue σ τ j
    · rcases h with ⟨rfl, rfl⟩
      exact (apm_t98a03_glueMk_glue σ τ j).symm

/-- Seat (generic): gluing two Hausdorff spaces along finitely many pairs of
points (injective gluing maps) gives a Hausdorff space.

Route: `t2Space_iff` / `t2_separation` on representatives using `hmk`.  A set
`W` of the glued space is open iff its preimages under `glueMk ∘ inl` and
`glueMk ∘ inr` are open (`isOpen_coinduced`, `isOpen_sum_iff`).  Finite sets
are closed (`Set.Finite.isClosed`, `Set.finite_range`), so: two unglued points
of `A` are separated inside `A` minus the glued points; an unglued point and a
glued class `j` are separated by `(U_A ∖ σ(other)) ⊔ (B ∖ τ(other))`-type
saturated opens; two glued classes `j ≠ j'` by separating `σ j, σ j'` in `A`
and `τ j, τ j'` in `B`.  Estimated 100–180 lines. -/
lemma apm_t98a03_glue_t2Space {J A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [T2Space A] [T2Space B] [Finite J] {σ : J → A} {τ : J → B}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hmk : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y) :
    T2Space (apm_t98a03_Glue σ τ) := by
  sorry

lemma apm_t98a03_glue_compactSpace {J A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] [CompactSpace A] [CompactSpace B] (σ : J → A) (τ : J → B) :
    CompactSpace (apm_t98a03_Glue σ τ) := by
  refine ⟨?_⟩
  rw [← (apm_t98a03_glueMk_surjective σ τ).range_eq]
  exact isCompact_range (apm_t98a03_glueMk_continuous σ τ)

/-- Seat (generic): the glued space of two connected pieces is connected; here
`B` need not be connected, only each point of `B` must be joined inside `B` by
a preconnected set to some glued point.

Route: the image of `A` (`isPreconnected_range`) meets each image
`glueMk '' (inr '' S_b)` in the glued class of `τ j = σ j`
(`apm_t98a03_glueMk_glue`); use `IsPreconnected.sUnion`/`isPreconnected_of_forall`
around a point of the image of `A`, plus surjectivity of `glueMk`;
`connectedSpace_iff_univ`.  Estimated 40–80 lines. -/
lemma apm_t98a03_glue_connectedSpace {J A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] [ConnectedSpace A] [Nonempty J] {σ : J → A} {τ : J → B}
    (hB : ∀ b : B, ∃ j : J, ∃ S : Set B, IsPreconnected S ∧ b ∈ S ∧ τ j ∈ S) :
    ConnectedSpace (apm_t98a03_Glue σ τ) := by
  let fA : A → apm_t98a03_Glue σ τ :=
    fun a => apm_t98a03_glueMk σ τ (.inl a)
  let fB : B → apm_t98a03_Glue σ τ :=
    fun b => apm_t98a03_glueMk σ τ (.inr b)
  have hfA : Continuous fA :=
    (apm_t98a03_glueMk_continuous σ τ).comp continuous_inl
  have hfB : Continuous fB :=
    (apm_t98a03_glueMk_continuous σ τ).comp continuous_inr
  let j₀ : J := Classical.choice inferInstance
  let x₀ : apm_t98a03_Glue σ τ := fA (σ j₀)
  rw [connectedSpace_iff_univ]
  refine ⟨⟨x₀, mem_univ x₀⟩, isPreconnected_of_forall x₀ ?_⟩
  intro y hy
  obtain ⟨z, rfl⟩ := apm_t98a03_glueMk_surjective σ τ y
  cases z with
  | inl a =>
      refine ⟨Set.range fA, subset_univ _, ?_, ?_, isPreconnected_range hfA⟩
      · exact ⟨σ j₀, rfl⟩
      · exact ⟨a, rfl⟩
  | inr b =>
      obtain ⟨j, S, hS, hbS, hjS⟩ := hB b
      let T : Set (apm_t98a03_Glue σ τ) := Set.range fA ∪ fB '' S
      have hSA : IsPreconnected (Set.range fA) := isPreconnected_range hfA
      have hSB : IsPreconnected (fB '' S) := hS.image fB hfB.continuousOn
      have hmeet : (Set.range fA ∩ fB '' S).Nonempty := by
        refine ⟨fA (σ j), ⟨⟨σ j, rfl⟩, τ j, hjS, ?_⟩⟩
        exact (apm_t98a03_glueMk_glue σ τ j).symm
      refine ⟨T, subset_univ _, ?_, ?_, hSA.union' hmeet hSB⟩
      · exact Or.inl ⟨σ j₀, rfl⟩
      · exact Or.inr ⟨b, hbS, rfl⟩

/-- Seat (generic): compatible self-homeomorphisms of the pieces descend.

Route: `Quotient.map'` of `Sum.map α β` (relation preserved: `glue j` goes to
`glue (π j)` by `hα, hβ`), and of `Sum.map α.symm β.symm` for the inverse
(`α.symm (σ (π j)) = σ j`); continuity by `Continuous.quotient_map'` and
`Continuous.sumMap`, as in `apm_t98a03_glueMap` below.  Estimated 40–70 lines. -/
lemma apm_t98a03_glue_homeomorph {J A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] {σ : J → A} {τ : J → B}
    (α : A ≃ₜ A) (β : B ≃ₜ B) (π : J ≃ J)
    (hα : ∀ j, α (σ j) = σ (π j)) (hβ : ∀ j, β (τ j) = τ (π j)) :
    ∃ h : apm_t98a03_Glue σ τ ≃ₜ apm_t98a03_Glue σ τ,
      ∀ x, h (apm_t98a03_glueMk σ τ x) = apm_t98a03_glueMk σ τ (Sum.map α β x) := by
  sorry

/-- The point wedge as a glued space. -/
abbrev apm_t98a03_Wedge {A B : Type} (a₀ : A) (b₀ : B) :=
  apm_t98a03_Glue (fun _ : Unit => a₀) (fun _ : Unit => b₀)

lemma apm_t98a03_wedge_mk_eq_iff {A B : Type} (a₀ : A) (b₀ : B) (x y : A ⊕ B) :
    apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y :=
  apm_t98a03_glueMk_eq_iff (Function.injective_of_subsingleton _)
    (Function.injective_of_subsingleton _) x y

lemma apm_t98a03_glueMap_respects {J A B A' B' : Type} {σ : J → A'} {τ : J → B'}
    {a₀ : A} {b₀ : B} (p : A' → A) (q : B' → B)
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀) {x y : A' ⊕ B'}
    (h : Relation.EqvGen (apm_t98a03_GlueRel σ τ) x y) :
    Relation.EqvGen (apm_t98a03_GlueRel (fun _ : Unit => a₀) (fun _ : Unit => b₀))
      (Sum.map p q x) (Sum.map p q y) := by
  induction h with
  | rel a b hab =>
    cases hab with
    | glue j =>
      simp only [Sum.map_inl, Sum.map_inr, hp, hq]
      exact Relation.EqvGen.rel _ _ (apm_t98a03_GlueRel.glue ())
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The map of glued spaces induced by `p ⊔ q`. -/
def apm_t98a03_glueMap {J A B A' B' : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B'] {σ : J → A'} {τ : J → B'}
    {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀) :
    C(apm_t98a03_Glue σ τ, apm_t98a03_Wedge a₀ b₀) where
  toFun := Quotient.map' (Sum.map p q)
    (fun _ _ h => apm_t98a03_glueMap_respects p q hp hq h)
  continuous_toFun := by
    apply Continuous.quotient_map'
    exact p.continuous.sumMap q.continuous

lemma apm_t98a03_glueMap_mk {J A B A' B' : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B'] {σ : J → A'} {τ : J → B'}
    {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀) (x : A' ⊕ B') :
    apm_t98a03_glueMap p q hp hq (apm_t98a03_glueMk σ τ x) =
      apm_t98a03_glueMk _ _ (Sum.map p q x) := rfl

/-- Seat (generic): the glued map is open.

Route: for open `O`, show `glueMk⁻¹' (f '' O) = Sum.map p q '' (glueMk⁻¹' O)`
(then open: `isOpen_coinduced`; `Sum.map` of open maps is open, e.g. via
`isOpenMap_inl/inr` and `IsOpenMap.comp`, or `isOpen_sum_iff`).  `⊇` is the
formula `apm_t98a03_glueMap_mk`.  `⊆`: if `glueMk x = f (glueMk e)` with
`e ∈ glueMk⁻¹' O`, then by `hmkX` either `x = Sum.map p q e`, or `x` is a
basepoint representative and so is `Sum.map p q e`; then `e` is a glued point
(`hpσ`/`hqτ`), its glued partner also lies in `glueMk⁻¹' O`
(`apm_t98a03_glueMk_glue`), and the partner maps to the other basepoint
representative.  Estimated 70–120 lines. -/
lemma apm_t98a03_glueMap_isOpenMap {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hpo : IsOpenMap p) (hqo : IsOpenMap q)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y) :
    IsOpenMap (apm_t98a03_glueMap p q hp hq) := by
  sorry

/-- Seat (generic): local injectivity at an unglued point of `A'`.

Route: from `hpl a'` get `φ` with `a' ∈ φ.source`, `p = φ` (injective on
`φ.source`, `OpenPartialHomeomorph.injOn`).  Let
`U := φ.source \ Set.range σ` (open: `Set.finite_range σ` is closed in the T2
space `A'`), `W := glueMk σ τ '' (Sum.inl '' U)`.  `W` is open: its
`glueMk`-preimage is `Sum.inl '' U` (no glued points; `hmkE`), open by
`isOpenMap_inl`.  On `W`, `f (glueMk (inl u)) = glueMk (inl (p u))` with
`p u ≠ a₀` (`hpσ`), so `hmkX` reduces equality of images to `p u = p u'`.
Estimated 50–90 lines. -/
lemma apm_t98a03_glueMap_locInj_inl {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B'] [T2Space A']
    [Finite J] {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B}
    (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hpl : IsLocalHomeomorph p)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hmkE : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y)
    (a' : A') (ha' : a' ∉ Set.range σ) :
    ∃ W : Set (apm_t98a03_Glue σ τ), IsOpen W ∧
      apm_t98a03_glueMk σ τ (.inl a') ∈ W ∧ Set.InjOn (apm_t98a03_glueMap p q hp hq) W := by
  sorry

/-- Seat (generic): local injectivity at an unglued point of `B'`; the mirror
image of `apm_t98a03_glueMap_locInj_inl` (same route with `inr`, `q`, `τ`).
Estimated 50–90 lines. -/
lemma apm_t98a03_glueMap_locInj_inr {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B'] [T2Space B']
    [Finite J] {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B}
    (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hql : IsLocalHomeomorph q)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ)
    (hmkE : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y)
    (b' : B') (hb' : b' ∉ Set.range τ) :
    ∃ W : Set (apm_t98a03_Glue σ τ), IsOpen W ∧
      apm_t98a03_glueMk σ τ (.inr b') ∈ W ∧ Set.InjOn (apm_t98a03_glueMap p q hp hq) W := by
  sorry

/-- Seat (generic): local injectivity at a glued point.

Route: take `φ` for `p` at `σ j` and `ψ` for `q` at `τ j`; let
`U := φ.source \ σ '' {j}ᶜ`, `V := ψ.source \ τ '' {j}ᶜ` (open: finite sets are
closed).  `W := glueMk σ τ '' (Sum.inl '' U ∪ Sum.inr '' V)` has exactly that
preimage (`hmkE`: the only glued pair meeting it is `σ j ~ τ j`, both inside),
hence is open.  Injectivity: by `hmkX`, `f`-images of two points of `W` agree iff
they are equal non-basepoint representatives (then `φ`/`ψ` injectivity), or both
are basepoint representatives — and the only points of `U`, `V` over `a₀`, `b₀`
are `σ j`, `τ j` (`hpσ`, `hqτ`), which are one class.  Estimated 80–140 lines. -/
lemma apm_t98a03_glueMap_locInj_glued {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B'] [T2Space A']
    [T2Space B'] [Finite J] {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B}
    (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hpl : IsLocalHomeomorph p) (hql : IsLocalHomeomorph q)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ)
    (hmkE : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y)
    (j : J) :
    ∃ W : Set (apm_t98a03_Glue σ τ), IsOpen W ∧
      apm_t98a03_glueMk σ τ (.inl (σ j)) ∈ W ∧
        Set.InjOn (apm_t98a03_glueMap p q hp hq) W := by
  sorry

/-- A continuous open locally injective map is a local homeomorphism. -/
lemma apm_t98a03_isLocalHomeomorph_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hc : Continuous f) (ho : IsOpenMap f)
    (hinj : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨U, hU, hxU, hinjU⟩ := hinj x
  exact ⟨U, hU.mem_nhds hxU,
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hc.comp continuous_subtype_val) hinjU.injective (ho.restrict hU)⟩

/-- Assembly: the glued map is a covering map. -/
theorem apm_t98a03_glueMap_isCoveringMap {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    [T2Space A] [T2Space B] [T2Space A'] [T2Space B'] [CompactSpace A']
    [CompactSpace B'] [Finite J] {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B}
    (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hpl : IsLocalHomeomorph p) (hql : IsLocalHomeomorph q)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ) :
    IsCoveringMap (apm_t98a03_glueMap p q hp hq) := by
  have hmkE := apm_t98a03_glueMk_eq_iff hσ hτ
  have hmkX := apm_t98a03_wedge_mk_eq_iff a₀ b₀
  haveI : T2Space (apm_t98a03_Glue σ τ) := apm_t98a03_glue_t2Space hσ hτ hmkE
  haveI : T2Space (apm_t98a03_Wedge a₀ b₀) :=
    apm_t98a03_glue_t2Space (Function.injective_of_subsingleton _)
      (Function.injective_of_subsingleton _) hmkX
  haveI : CompactSpace (apm_t98a03_Glue σ τ) := apm_t98a03_glue_compactSpace σ τ
  have hinj : ∀ e, ∃ W : Set (apm_t98a03_Glue σ τ), IsOpen W ∧ e ∈ W ∧
      Set.InjOn (apm_t98a03_glueMap p q hp hq) W := by
    intro e
    obtain ⟨x, rfl⟩ := apm_t98a03_glueMk_surjective σ τ e
    rcases x with a' | b'
    · by_cases ha : a' ∈ Set.range σ
      · obtain ⟨j, rfl⟩ := ha
        exact apm_t98a03_glueMap_locInj_glued p q hp hq hpl hql hσ hτ hpσ hqτ hmkE hmkX j
      · exact apm_t98a03_glueMap_locInj_inl p q hp hq hpl hpσ hmkE hmkX a' ha
    · by_cases hb : b' ∈ Set.range τ
      · obtain ⟨j, rfl⟩ := hb
        rw [← apm_t98a03_glueMk_glue]
        exact apm_t98a03_glueMap_locInj_glued p q hp hq hpl hql hσ hτ hpσ hqτ hmkE hmkX j
      · exact apm_t98a03_glueMap_locInj_inr p q hp hq hql hqτ hmkE hmkX b' hb
  have hloc : IsLocalHomeomorph (apm_t98a03_glueMap p q hp hq) :=
    apm_t98a03_isLocalHomeomorph_of_isOpenMap (map_continuous _)
      (apm_t98a03_glueMap_isOpenMap p q hp hq hpl.isOpenMap hql.isOpenMap hpσ hqτ hmkX)
      hinj
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact IsCoveringMapOn.of_openPartialHomeomorph (map_continuous _) (fun e _ => by
    obtain ⟨φ, h1, h2⟩ := hloc e
    exact ⟨φ, h1, h2.symm⟩)

/-- Seat (generic): fibre over an unglued point of `A`.

Route: `Nat.card_congr` with the equivalence
`{a' // p a' = a} ≃ {e // f e = glueMk (inl a)}`, `a' ↦ glueMk (inl a')`.
Well defined by `apm_t98a03_glueMap_mk`.  Injective: `p a' = a ≠ a₀`, so
`a' ∉ range σ` (`hpσ`) and `hmkE` forces equality.  Surjective: a representative
`inr b'` would give `glueMk (inr (q b')) = glueMk (inl a)`, impossible by `hmkX`
since `a ≠ a₀`; a representative `inl a'` has `p a' = a` by `hmkX`.
Estimated 40–80 lines. -/
lemma apm_t98a03_glueMap_fiber_inl {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hmkE : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y)
    (a : A) (ha : a ≠ a₀) :
    Nat.card {e // apm_t98a03_glueMap p q hp hq e =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) (.inl a)} =
      Nat.card {a' // p a' = a} := by
  sorry

/-- Seat (generic): fibre over an unglued point of `B`; mirror image of
`apm_t98a03_glueMap_fiber_inl`.  Estimated 40–80 lines. -/
lemma apm_t98a03_glueMap_fiber_inr {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ)
    (hmkE : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y)
    (b : B) (hb : b ≠ b₀) :
    Nat.card {e // apm_t98a03_glueMap p q hp hq e =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) (.inr b)} =
      Nat.card {b' // q b' = b} := by
  sorry

/-- Seat (generic): the fibre over the wedge point is the set of glued classes.

Route: `Nat.card_congr` with `J ≃ {e // f e = basepoint}`,
`j ↦ glueMk (inl (σ j))` (in the fibre by `hp`).  Injective by `hmkE` and `hσ`.
Surjective: a representative `inl a'` of a fibre point has `p a' = a₀` (`hmkX`),
so `a' = σ j` (`hpσ`); a representative `inr b'` has `b' = τ j` (`hqτ`) and
`glueMk (inr (τ j)) = glueMk (inl (σ j))` (`apm_t98a03_glueMk_glue`).
Estimated 40–80 lines. -/
lemma apm_t98a03_glueMap_fiber_base {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ)
    (hmkE : ∀ x y, apm_t98a03_glueMk σ τ x = apm_t98a03_glueMk σ τ y ↔
      apm_t98a03_GlueEq σ τ x y)
    (hmkX : ∀ x y, apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) x =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) y ↔
      apm_t98a03_GlueEq (fun _ : Unit => a₀) (fun _ : Unit => b₀) x y) :
    Nat.card {e // apm_t98a03_glueMap p q hp hq e =
        apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b₀) (.inl a₀)} =
      Nat.card J := by
  sorry

/-- Assembly: if every fibre of `p`, `q` away from the basepoints and the set of
glued classes all have `n` elements, every fibre of the glued map does. -/
theorem apm_t98a03_glueMap_fiber_card {J A B A' B' : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    {σ : J → A'} {τ : J → B'} {a₀ : A} {b₀ : B} (p : C(A', A)) (q : C(B', B))
    (hp : ∀ j, p (σ j) = a₀) (hq : ∀ j, q (τ j) = b₀)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hpσ : ∀ a', p a' = a₀ ↔ a' ∈ Set.range σ)
    (hqτ : ∀ b', q b' = b₀ ↔ b' ∈ Set.range τ) (n : ℕ)
    (hA : ∀ a, Nat.card {a' // p a' = a} = n) (hB : ∀ b, Nat.card {b' // q b' = b} = n)
    (hJ : Nat.card J = n) :
    ∀ x, Nat.card {e // apm_t98a03_glueMap p q hp hq e = x} = n := by
  have hmkE := apm_t98a03_glueMk_eq_iff hσ hτ
  have hmkX := apm_t98a03_wedge_mk_eq_iff a₀ b₀
  intro x
  obtain ⟨y, rfl⟩ := apm_t98a03_glueMk_surjective _ _ x
  rcases y with a | b
  · by_cases ha : a = a₀
    · subst ha
      rw [apm_t98a03_glueMap_fiber_base p q hp hq hσ hτ hpσ hqτ hmkE hmkX, hJ]
    · rw [apm_t98a03_glueMap_fiber_inl p q hp hq hpσ hmkE hmkX a ha, hA]
  · by_cases hb : b = b₀
    · subst hb
      have hbase : apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b) (.inr b) =
          apm_t98a03_glueMk (fun _ : Unit => a₀) (fun _ : Unit => b) (.inl a₀) :=
        (apm_t98a03_glueMk_glue (fun _ : Unit => a₀) (fun _ : Unit => b) ()).symm
      rw [hbase, apm_t98a03_glueMap_fiber_base p q hp hq hσ hτ hpσ hqτ hmkE hmkX, hJ]
    · rw [apm_t98a03_glueMap_fiber_inr p q hp hq hqτ hmkE hmkX b hb, hB]

/-- No deck transformation carries the start of a closed lift to the start of an
open lift of the same loop (uniqueness of lifts, `IsCoveringMap.eq_of_comp_eq`). -/
lemma apm_t98a03_no_deck_of_lift_mismatch {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {f : E → X} (hf : IsCoveringMap f)
    (γ₁ γ₂ : C(unitInterval, E)) (hγ : f ∘ γ₁ = f ∘ γ₂)
    (h₁ : γ₁ 0 = γ₁ 1) (h₂ : γ₂ 0 ≠ γ₂ 1) :
    ¬∃ h : E ≃ₜ E, (∀ z, f (h z) = f z) ∧ h (γ₁ 0) = γ₂ 0 := by
  rintro ⟨h, hdeck, h0⟩
  have hcomp : f ∘ (h ∘ γ₁) = f ∘ γ₂ := by
    funext t
    simpa [hdeck] using congrFun hγ t
  have heq := hf.eq_of_comp_eq (h.continuous.comp γ₁.continuous) γ₂.continuous hcomp 0
    (by simpa using h0)
  have h1 := congrFun heq 1
  apply h₂
  simp only [Function.comp_apply] at h1
  rw [← h1, ← h₁, h0]

lemma apm_t98a03_isLocalHomeomorph_prodMap {X Y X' Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → X'} {g : Y → Y'} (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph (Prod.map f g) := by
  intro x
  obtain ⟨φ, hφ, rfl⟩ := hf x.1
  obtain ⟨ψ, hψ, rfl⟩ := hg x.2
  exact ⟨φ.prod ψ, ⟨hφ, hψ⟩, rfl⟩

lemma apm_t98a03_isLocalHomeomorph_snd {F Y : Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace Y] :
    IsLocalHomeomorph (Prod.snd : F × Y → Y) :=
  apm_t98a03_isLocalHomeomorph_of_isOpenMap continuous_snd isOpenMap_snd
    (fun x => ⟨{x.1} ×ˢ Set.univ, (isOpen_discrete _).prod isOpen_univ, ⟨rfl, trivial⟩,
      fun a ha b hb hab => Prod.ext (ha.1.trans hb.1.symm) hab⟩)

/-- Seat (generic): `Sum.elim` of local homeomorphisms into a common space is a
local homeomorphism.

Route: `apm_t98a03_isLocalHomeomorph_of_isOpenMap`: continuity by
`continuous_sum_dom`; open map since an open `O ⊆ X ⊕ Y` has image
`f '' (inl⁻¹' O) ∪ g '' (inr⁻¹' O)` (`isOpen_sum_iff`,
`IsLocalHomeomorph.isOpenMap`); local injectivity on `inl '' φ.source` /
`inr '' ψ.source` (open by `isOpenMap_inl`/`isOpenMap_inr`).
Estimated 30–60 lines. -/
lemma apm_t98a03_isLocalHomeomorph_sumElim {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Z} {g : Y → Z}
    (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph (Sum.elim f g) := by
  sorry

end Glue

/-! ### Packaging a cover of the glued wedge as a cover of the literal quotient -/

def apm_t98a03_wedge_homeomorph_X (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_Wedge t₀ r₀ ≃ₜ apm_t98a03_X t₀ r₀ :=
  ConstructionTargets.PointWedgeQuotient.quotientHomeomorphOfRelIff
    (apm_t98a03_GlueRel (fun _ : Unit => t₀) (fun _ : Unit => r₀))
    (apm_t98a03_wedgeRel t₀ r₀)
    (by
      intro a b
      constructor
      · rintro ⟨⟩
        exact apm_t98a03_wedgeRel.base
      · rintro ⟨⟩
        exact apm_t98a03_GlueRel.glue ())

def apm_t98a03_coverOf {E : Type} [TopologicalSpace E] (t₀ : apm_t98a03_Torus)
    (r₀ : apm_t98a03_RP2) (f : E → apm_t98a03_Wedge t₀ r₀) :
    apm_t98a03_Cover (apm_t98a03_X t₀ r₀) :=
  ⟨E, inferInstance, apm_t98a03_wedge_homeomorph_X t₀ r₀ ∘ f⟩

lemma apm_t98a03_coverOf_threeFold {E : Type} [TopologicalSpace E]
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) (f : E → apm_t98a03_Wedge t₀ r₀)
    (hf : IsCoveringMap f) (hconn : ConnectedSpace E)
    (hcard : ∀ x, Nat.card {e // f e = x} = 3) :
    apm_t98a03_IsConnectedThreeFoldCover (apm_t98a03_coverOf t₀ r₀ f) := by
  refine ⟨hf.homeomorph_comp _, ⟨hconn⟩, fun x => ?_⟩
  change Nat.card {e : E // apm_t98a03_wedge_homeomorph_X t₀ r₀ (f e) = x} = 3
  rw [← hcard ((apm_t98a03_wedge_homeomorph_X t₀ r₀).symm x)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun e =>
    (apm_t98a03_wedge_homeomorph_X t₀ r₀).apply_eq_iff_eq_symm_apply)

lemma apm_t98a03_coverOf_regular_iff {E : Type} [TopologicalSpace E]
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) (f : E → apm_t98a03_Wedge t₀ r₀) :
    apm_t98a03_IsRegularCover (apm_t98a03_coverOf t₀ r₀ f) ↔
      IsCoveringMap f ∧ ∀ x y : E, f x = f y →
        ∃ h : E ≃ₜ E, (∀ z, f (h z) = f z) ∧ h x = y := by
  let e := apm_t98a03_wedge_homeomorph_X t₀ r₀
  change (IsCoveringMap (e ∘ f) ∧ ∀ x y : E, e (f x) = e (f y) →
      ∃ h : E ≃ₜ E, (∀ z, e (f (h z)) = e (f z)) ∧ h x = y) ↔ _
  simp only [EmbeddingLike.apply_eq_iff_eq, IsCoveringMap.homeomorph_comp_iff]

/-! ### The torus triple cover `(z, w) ↦ (z³, w)` -/

def apm_t98a03_zeta : Circle := Circle.exp (2 * Real.pi / 3)

lemma apm_t98a03_zeta_pow_three : apm_t98a03_zeta ^ 3 = 1 := by
  rw [apm_t98a03_zeta, ← Circle.exp_nsmul, nsmul_eq_mul]
  rw [show ((3 : ℕ) : ℝ) * (2 * Real.pi / 3) = 2 * Real.pi by push_cast; ring]
  exact Circle.exp_two_pi

/-- Seat: `1, ζ, ζ²` are distinct.

Route: `Circle.exp` is injective on `[0, 2π)` / `Circle.exp_eq_one`
(`Circle.exp x = 1 ↔ ∃ n : ℤ, x = n * (2π)`, or via `Complex.exp_eq_one_iff`);
`ζ^k = Circle.exp (k * 2π/3)` by `Circle.exp_nsmul`; compare `ζ^i = ζ^j` as
`ζ^(j-i) = 1` with `0 < j - i < 3`; `fin_cases`. Estimated 25–50 lines. -/
lemma apm_t98a03_zeta_pow_injective :
    Function.Injective (fun k : Fin 3 => apm_t98a03_zeta ^ (k : ℕ)) := by
  sorry

/-- Seat: the cube roots of `a = c³` in the circle are `c, ζc, ζ²c`.

Route: `←` from `apm_t98a03_zeta_pow_three` (`mul_pow`, `pow_right_comm`).
`→`: `w := z * c⁻¹` has `w ^ 3 = 1`; the polynomial `X³ - 1` has at most three
roots in the field `ℂ` (`Polynomial.card_roots'` / `Multiset.card_roots`), and
`1, ζ, ζ²` are three distinct roots (`apm_t98a03_zeta_pow_injective`, pass it
in as a hypothesis or reprove), so `w` is one of them; alternatively
`Complex.mem_rootsOfUnity` gives `w = exp(2πik/3)` directly.
Estimated 50–100 lines. -/
lemma apm_t98a03_circle_cube_roots (a c : Circle) (hc : c ^ 3 = a) (z : Circle) :
    z ^ 3 = a ↔ ∃ k : Fin 3, z = apm_t98a03_zeta ^ (k : ℕ) * c := by
  sorry

/-- A chosen cube root. -/
def apm_t98a03_cubeRoot (a : Circle) : Circle :=
  Classical.choose ((Circle.isQuotientCoveringMap_npow 3).surjective a)

lemma apm_t98a03_cubeRoot_pow (a : Circle) : apm_t98a03_cubeRoot a ^ 3 = a :=
  Classical.choose_spec ((Circle.isQuotientCoveringMap_npow 3).surjective a)

def apm_t98a03_torusCube : C(apm_t98a03_Torus, apm_t98a03_Torus) :=
  ⟨Prod.map (fun z : Circle => z ^ 3) id, (continuous_pow 3).prodMap continuous_id⟩

lemma apm_t98a03_torusCube_isLocalHomeomorph :
    IsLocalHomeomorph apm_t98a03_torusCube :=
  apm_t98a03_isLocalHomeomorph_prodMap
    ((Circle.isQuotientCoveringMap_npow 3).isCoveringMap.isLocalHomeomorph)
    (Homeomorph.refl Circle).isLocalHomeomorph

/-- The three torus points over `t₀`. -/
def apm_t98a03_sheetPt (t₀ : apm_t98a03_Torus) (k : Fin 3) : apm_t98a03_Torus :=
  (apm_t98a03_zeta ^ (k : ℕ) * apm_t98a03_cubeRoot t₀.1, t₀.2)

lemma apm_t98a03_torusCube_sheetPt (t₀ : apm_t98a03_Torus) (k : Fin 3) :
    apm_t98a03_torusCube (apm_t98a03_sheetPt t₀ k) = t₀ := by
  have h := (apm_t98a03_circle_cube_roots t₀.1 _ (apm_t98a03_cubeRoot_pow t₀.1)
    (apm_t98a03_zeta ^ (k : ℕ) * apm_t98a03_cubeRoot t₀.1)).2 ⟨k, rfl⟩
  exact Prod.ext h rfl

lemma apm_t98a03_sheetPt_injective (t₀ : apm_t98a03_Torus) :
    Function.Injective (apm_t98a03_sheetPt t₀) := by
  intro i j h
  have h1 := congrArg Prod.fst h
  exact apm_t98a03_zeta_pow_injective (mul_right_cancel h1)

lemma apm_t98a03_torusCube_eq_iff (t₀ e : apm_t98a03_Torus) :
    apm_t98a03_torusCube e = t₀ ↔ e ∈ Set.range (apm_t98a03_sheetPt t₀) := by
  constructor
  · intro h
    have h1 : e.1 ^ 3 = t₀.1 := congrArg Prod.fst h
    have h2 : e.2 = t₀.2 := by
      have := congrArg Prod.snd h
      exact this
    obtain ⟨k, hk⟩ := (apm_t98a03_circle_cube_roots t₀.1 _
      (apm_t98a03_cubeRoot_pow t₀.1) e.1).1 h1
    exact ⟨k, Prod.ext hk.symm h2.symm⟩
  · rintro ⟨k, rfl⟩
    exact apm_t98a03_torusCube_sheetPt t₀ k

/-- Every fibre of the torus triple cover has three points. -/
lemma apm_t98a03_torusCube_fiber_card (t : apm_t98a03_Torus) :
    Nat.card {e // apm_t98a03_torusCube e = t} = 3 := by
  have hbij : Function.Bijective (fun k : Fin 3 =>
      (⟨apm_t98a03_sheetPt t k, apm_t98a03_torusCube_sheetPt t k⟩ :
        {e // apm_t98a03_torusCube e = t})) := by
    refine ⟨fun i j h => apm_t98a03_sheetPt_injective t (congrArg Subtype.val h), ?_⟩
    rintro ⟨e, he⟩
    obtain ⟨k, hk⟩ := (apm_t98a03_torusCube_eq_iff t e).1 he
    exact ⟨k, Subtype.ext hk⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

instance : T2Space apm_t98a03_RP2 :=
  (apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient).some.t2Space

instance : CompactSpace apm_t98a03_RP2 :=
  (apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient).some.compactSpace

instance : PathConnectedSpace apm_t98a03_RP2 := apm_t98a03_t92_projectivePlane_pathConnected

/-! ### The regular cover -/

/-- Three projective planes, sheet `k` glued at `(k, r₀)`. -/
abbrev apm_t98a03_RegB := Fin 3 × apm_t98a03_RP2

def apm_t98a03_regTau (r₀ : apm_t98a03_RP2) (k : Fin 3) : apm_t98a03_RegB := (k, r₀)

def apm_t98a03_regQ : C(apm_t98a03_RegB, apm_t98a03_RP2) := ⟨Prod.snd, continuous_snd⟩

lemma apm_t98a03_regQ_tau (r₀ : apm_t98a03_RP2) (k : Fin 3) :
    apm_t98a03_regQ (apm_t98a03_regTau r₀ k) = r₀ := rfl

abbrev apm_t98a03_RegE (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :=
  apm_t98a03_Glue (apm_t98a03_sheetPt t₀) (apm_t98a03_regTau r₀)

def apm_t98a03_regMap (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    C(apm_t98a03_RegE t₀ r₀, apm_t98a03_Wedge t₀ r₀) :=
  apm_t98a03_glueMap apm_t98a03_torusCube apm_t98a03_regQ
    (apm_t98a03_torusCube_sheetPt t₀) (apm_t98a03_regQ_tau r₀)

lemma apm_t98a03_regTau_injective (r₀ : apm_t98a03_RP2) :
    Function.Injective (apm_t98a03_regTau r₀) :=
  fun _ _ h => congrArg Prod.fst h

lemma apm_t98a03_regQ_eq_iff (r₀ : apm_t98a03_RP2) (b : apm_t98a03_RegB) :
    apm_t98a03_regQ b = r₀ ↔ b ∈ Set.range (apm_t98a03_regTau r₀) := by
  constructor
  · intro h
    exact ⟨b.1, Prod.ext rfl h.symm⟩
  · rintro ⟨k, rfl⟩
    rfl

lemma apm_t98a03_regQ_fiber_card (r : apm_t98a03_RP2) :
    Nat.card {b // apm_t98a03_regQ b = r} = 3 := by
  have e : {b // apm_t98a03_regQ b = r} ≃ Fin 3 :=
    { toFun := fun b => b.1.1
      invFun := fun k => ⟨(k, r), rfl⟩
      left_inv := by
        rintro ⟨⟨k, r'⟩, h⟩
        change r' = r at h
        subst h
        rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma apm_t98a03_regMap_isCoveringMap (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    IsCoveringMap (apm_t98a03_regMap t₀ r₀) :=
  apm_t98a03_glueMap_isCoveringMap _ _ _ _ apm_t98a03_torusCube_isLocalHomeomorph
    apm_t98a03_isLocalHomeomorph_snd (apm_t98a03_sheetPt_injective t₀)
    (apm_t98a03_regTau_injective r₀) (apm_t98a03_torusCube_eq_iff t₀)
    (apm_t98a03_regQ_eq_iff r₀)

lemma apm_t98a03_regE_connected (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ConnectedSpace (apm_t98a03_RegE t₀ r₀) :=
  apm_t98a03_glue_connectedSpace (fun b =>
    ⟨b.1, {b.1} ×ˢ Set.univ, isPreconnected_singleton.prod isPreconnected_univ,
      ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩)

/-- The sheet rotation of the torus: `(z, w) ↦ (ζ z, w)`. -/
def apm_t98a03_torusRot : apm_t98a03_Torus ≃ₜ apm_t98a03_Torus :=
  (Homeomorph.mulLeft apm_t98a03_zeta).prodCongr (Homeomorph.refl Circle)

/-- The sheet rotation of the three planes: `(k, r) ↦ (k + 1, r)`. -/
def apm_t98a03_regRot : apm_t98a03_RegB ≃ₜ apm_t98a03_RegB :=
  (Homeomorph.mk (Equiv.addRight (1 : Fin 3)) continuous_of_discreteTopology
    continuous_of_discreteTopology).prodCongr (Homeomorph.refl apm_t98a03_RP2)

lemma apm_t98a03_zeta_mul_pow (k : Fin 3) :
    apm_t98a03_zeta * apm_t98a03_zeta ^ (k : ℕ) =
      apm_t98a03_zeta ^ ((k + 1 : Fin 3) : ℕ) := by
  fin_cases k
  · simp
  · simp [pow_succ]
  · show apm_t98a03_zeta * apm_t98a03_zeta ^ 2 = apm_t98a03_zeta ^ 0
    rw [pow_zero, ← pow_succ', apm_t98a03_zeta_pow_three]

lemma apm_t98a03_torusRot_sheetPt (t₀ : apm_t98a03_Torus) (k : Fin 3) :
    apm_t98a03_torusRot (apm_t98a03_sheetPt t₀ k) =
      apm_t98a03_sheetPt t₀ (Equiv.addRight (1 : Fin 3) k) := by
  change (apm_t98a03_zeta * (apm_t98a03_zeta ^ (k : ℕ) * apm_t98a03_cubeRoot t₀.1), t₀.2) =
    (apm_t98a03_zeta ^ ((k + 1 : Fin 3) : ℕ) * apm_t98a03_cubeRoot t₀.1, t₀.2)
  rw [← mul_assoc, apm_t98a03_zeta_mul_pow]

lemma apm_t98a03_regRot_tau (r₀ : apm_t98a03_RP2) (k : Fin 3) :
    apm_t98a03_regRot (apm_t98a03_regTau r₀ k) =
      apm_t98a03_regTau r₀ (Equiv.addRight (1 : Fin 3) k) := rfl

lemma apm_t98a03_regDeck_commutes (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (h : apm_t98a03_RegE t₀ r₀ ≃ₜ apm_t98a03_RegE t₀ r₀)
    (hh : ∀ x, h (apm_t98a03_glueMk _ _ x) =
      apm_t98a03_glueMk _ _ (Sum.map apm_t98a03_torusRot apm_t98a03_regRot x)) :
    ∀ z, apm_t98a03_regMap t₀ r₀ (h z) = apm_t98a03_regMap t₀ r₀ z := by
  intro z
  obtain ⟨x, rfl⟩ := apm_t98a03_glueMk_surjective _ _ z
  rw [hh x]
  rcases x with ⟨z1, w⟩ | ⟨k, r⟩
  · change apm_t98a03_glueMk _ _ (.inl ((apm_t98a03_zeta * z1) ^ 3, w)) =
      apm_t98a03_glueMk _ _ (.inl (z1 ^ 3, w))
    rw [mul_pow, apm_t98a03_zeta_pow_three, one_mul]
  · rfl

/-- Seat: every fibre of the regular cover is an orbit of the sheet rotation
`h` (`h` acts by `(z,w) ↦ (ζz,w)` on the torus and `(k,r) ↦ (k+1,r)` on the
planes, formula `hh`).

Route: write `x = glueMk a`, `y = glueMk b` (`apm_t98a03_glueMk_surjective`);
`hxy` and `apm_t98a03_glueMap_mk` give
`glueMk (Sum.map torusCube regQ a) = glueMk (Sum.map torusCube regQ b)` in the
wedge; decide it with `apm_t98a03_wedge_mk_eq_iff`.  Non-basepoint torus case:
`b.1 = ζ^k a.1` by `apm_t98a03_circle_cube_roots`, then `y = h^[k] x` by `hh`.
Non-basepoint plane case: `b = (a.1 + m, a.2)`.  Basepoint case: both are
glued classes `glueMk (inl (sheetPt t₀ k))` (`apm_t98a03_torusCube_eq_iff`,
`apm_t98a03_regQ_eq_iff`, `apm_t98a03_glueMk_glue`) and
`h (glueMk (inl (sheetPt t₀ k))) = glueMk (inl (sheetPt t₀ (k+1)))` by `hh` and
`apm_t98a03_torusRot_sheetPt`.  Finish with `fin_cases` on the differences.
Estimated 80–150 lines. -/
lemma apm_t98a03_regular_fiber_orbit (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (h : apm_t98a03_RegE t₀ r₀ ≃ₜ apm_t98a03_RegE t₀ r₀)
    (hh : ∀ x, h (apm_t98a03_glueMk _ _ x) =
      apm_t98a03_glueMk _ _ (Sum.map apm_t98a03_torusRot apm_t98a03_regRot x))
    (x y : apm_t98a03_RegE t₀ r₀)
    (hxy : apm_t98a03_regMap t₀ r₀ x = apm_t98a03_regMap t₀ r₀ y) :
    y = x ∨ y = h x ∨ y = h (h x) := by
  sorry

/-- Assembly: the regular cover. -/
theorem apm_t98a03_regular_threeFoldCover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ C : apm_t98a03_Cover (apm_t98a03_X t₀ r₀),
      apm_t98a03_IsConnectedThreeFoldCover C ∧ apm_t98a03_IsRegularCover C := by
  obtain ⟨h, hh⟩ := apm_t98a03_glue_homeomorph apm_t98a03_torusRot apm_t98a03_regRot
    (Equiv.addRight (1 : Fin 3)) (apm_t98a03_torusRot_sheetPt t₀) (apm_t98a03_regRot_tau r₀)
  have hcov := apm_t98a03_regMap_isCoveringMap t₀ r₀
  have hdeck := apm_t98a03_regDeck_commutes t₀ r₀ h hh
  refine ⟨apm_t98a03_coverOf t₀ r₀ (apm_t98a03_regMap t₀ r₀), ?_, ?_⟩
  · exact apm_t98a03_coverOf_threeFold t₀ r₀ _ hcov (apm_t98a03_regE_connected t₀ r₀)
      (apm_t98a03_glueMap_fiber_card apm_t98a03_torusCube apm_t98a03_regQ
        (apm_t98a03_torusCube_sheetPt t₀) (apm_t98a03_regQ_tau r₀)
        (apm_t98a03_sheetPt_injective t₀) (apm_t98a03_regTau_injective r₀)
        (apm_t98a03_torusCube_eq_iff t₀) (apm_t98a03_regQ_eq_iff r₀) 3
        apm_t98a03_torusCube_fiber_card apm_t98a03_regQ_fiber_card (by simp))
  · rw [apm_t98a03_coverOf_regular_iff]
    refine ⟨hcov, fun x y hxy => ?_⟩
    rcases apm_t98a03_regular_fiber_orbit t₀ r₀ h hh x y hxy with rfl | rfl | rfl
    · exact ⟨Homeomorph.refl _, fun _ => rfl, rfl⟩
    · exact ⟨h, hdeck, rfl⟩
    · exact ⟨h.trans h, fun z => by simp [hdeck], rfl⟩

/-! ### The irregular cover -/

/-- The sphere-to-plane projection (copied map `..._aux_toP`). -/
def apm_t98a03_sphereProj : apm_t98a03_t92_S2 → apm_t98a03_RP2 :=
  apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP

def apm_t98a03_antipodalHomeomorph :
    MulAction.orbitRel.Quotient apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 ≃ₜ
      apm_t98a03_RP2 where
  toFun := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
  invFun := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
  left_inv := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_left
  right_inv := apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_right
  continuous_toFun :=
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous
  continuous_invFun :=
    apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous

lemma apm_t98a03_sphereProj_isCoveringMap : IsCoveringMap apm_t98a03_sphereProj := by
  haveI : IsCancelSMul apm_t98a03_t92_antipodalGroup apm_t98a03_t92_S2 :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr apm_t98a03_t92_antipodalAction_free
  have h := (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (G := apm_t98a03_t92_antipodalGroup) (E := apm_t98a03_t92_S2)).isCoveringMap
  exact h.homeomorph_comp apm_t98a03_antipodalHomeomorph

instance : SimplyConnectedSpace apm_t98a03_t92_S2 :=
  ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 2
    (by norm_num)

/-- The unit representative of a projective point. -/
def apm_t98a03_unitRep (r : apm_t98a03_RP2) : apm_t98a03_t92_S2 :=
  ⟨(‖WithLp.toLp 2 r.rep‖⁻¹ : ℝ) • WithLp.toLp 2 r.rep, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (by
      change WithLp.toLp 2 r.rep ≠ 0
      exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective.ne r.rep_nonzero)⟩

lemma apm_t98a03_sphereProj_unitRep (r : apm_t98a03_RP2) :
    apm_t98a03_sphereProj (apm_t98a03_unitRep r) = r := by
  conv_rhs => rw [← Projectivization.mk_rep r]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨‖WithLp.toLp 2 r.rep‖⁻¹, ?_⟩
  ext i
  rfl

lemma apm_t98a03_sphereProj_neg (x : apm_t98a03_t92_S2) :
    apm_t98a03_sphereProj (-x) = apm_t98a03_sphereProj x := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨-1, ?_⟩
  ext i
  simp

/-- Seat: the fibres of `S² → RP²` are antipodal pairs.

Route: `apm_t98a03_sphereProj x = mk x` (as vectors); `Projectivization.mk_eq_mk_iff'`
gives `y = a • x` for a real `a`; taking norms (`norm_smul`, both unit) gives
`|a| = 1`, so `a = 1` or `a = -1` (`abs_eq`); `Subtype.ext`, `WithLp` coercions
as in the copied `..._aux_toQ0_scale`.  `←` by `apm_t98a03_sphereProj_neg`.
Estimated 30–60 lines. -/
lemma apm_t98a03_sphereProj_eq_iff (x y : apm_t98a03_t92_S2) :
    apm_t98a03_sphereProj y = apm_t98a03_sphereProj x ↔ y = x ∨ y = -x := by
  sorry

/-- No point of the sphere is its own antipode. -/
lemma apm_t98a03_sphere_ne_neg (x : apm_t98a03_t92_S2) : x ≠ -x := by
  intro h
  have h' : (x : EuclideanSpace ℝ (Fin 3)) = -(x : EuclideanSpace ℝ (Fin 3)) := by
    simpa using congrArg Subtype.val h
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by simp
  have h2 : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h']
    exact neg_add_cancel _
  have h0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [h0, norm_zero] at hx
  exact zero_ne_one hx

/-- Sphere sheet and one plane sheet. -/
abbrev apm_t98a03_IrrB := apm_t98a03_t92_S2 ⊕ apm_t98a03_RP2

/-- Glued points: `r₀` on the plane sheet, `±s` on the sphere sheet. -/
def apm_t98a03_irrTau (r₀ : apm_t98a03_RP2) : Fin 3 → apm_t98a03_IrrB :=
  ![.inr r₀, .inl (apm_t98a03_unitRep r₀), .inl (-apm_t98a03_unitRep r₀)]

def apm_t98a03_irrQ : C(apm_t98a03_IrrB, apm_t98a03_RP2) :=
  ⟨Sum.elim apm_t98a03_sphereProj id,
    continuous_sum_dom.2
      ⟨apm_t98a03_t92_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous,
        continuous_id⟩⟩

lemma apm_t98a03_irrQ_tau (r₀ : apm_t98a03_RP2) (k : Fin 3) :
    apm_t98a03_irrQ (apm_t98a03_irrTau r₀ k) = r₀ := by
  fin_cases k
  · rfl
  · exact apm_t98a03_sphereProj_unitRep r₀
  · change apm_t98a03_sphereProj (-apm_t98a03_unitRep r₀) = r₀
    rw [apm_t98a03_sphereProj_neg, apm_t98a03_sphereProj_unitRep]

/-- The three glued points of the irregular cover are distinct. -/
lemma apm_t98a03_irrTau_injective (r₀ : apm_t98a03_RP2)
    (hne : ∀ x : apm_t98a03_t92_S2, x ≠ -x) :
    Function.Injective (apm_t98a03_irrTau r₀) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [apm_t98a03_irrTau] at h ⊢ <;>
    first
    | rfl
    | exact hne _ h
    | exact hne _ h.symm

/-- Seat: the fibre of the irregular plane-side map over `r₀` is exactly the
glued points.  Route: `inr r` maps to `r`; `inl x` maps to `r₀` iff
`x = ±unitRep r₀` (`hproj` with `apm_t98a03_sphereProj_unitRep`); `fin_cases`
for `←`. Estimated 20–40 lines. -/
lemma apm_t98a03_irrQ_eq_iff (r₀ : apm_t98a03_RP2)
    (hproj : ∀ x y : apm_t98a03_t92_S2,
      apm_t98a03_sphereProj y = apm_t98a03_sphereProj x ↔ y = x ∨ y = -x)
    (b : apm_t98a03_IrrB) :
    apm_t98a03_irrQ b = r₀ ↔ b ∈ Set.range (apm_t98a03_irrTau r₀) := by
  sorry

/-- Seat: every fibre of the irregular plane-side map has three points:
`inl (unitRep r)`, `inl (-unitRep r)`, `inr r`.  Route: `Nat.card_congr` with an
explicit `Fin 3` equivalence, using `hproj`, `hne` and
`apm_t98a03_sphereProj_unitRep`. Estimated 30–60 lines. -/
lemma apm_t98a03_irrQ_fiber_card
    (hproj : ∀ x y : apm_t98a03_t92_S2,
      apm_t98a03_sphereProj y = apm_t98a03_sphereProj x ↔ y = x ∨ y = -x)
    (hne : ∀ x : apm_t98a03_t92_S2, x ≠ -x) (r : apm_t98a03_RP2) :
    Nat.card {b // apm_t98a03_irrQ b = r} = 3 := by
  sorry

abbrev apm_t98a03_IrrE (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :=
  apm_t98a03_Glue (apm_t98a03_sheetPt t₀) (apm_t98a03_irrTau r₀)

def apm_t98a03_irrMap (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    C(apm_t98a03_IrrE t₀ r₀, apm_t98a03_Wedge t₀ r₀) :=
  apm_t98a03_glueMap apm_t98a03_torusCube apm_t98a03_irrQ
    (apm_t98a03_torusCube_sheetPt t₀) (apm_t98a03_irrQ_tau r₀)

lemma apm_t98a03_irrMap_isCoveringMap (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    IsCoveringMap (apm_t98a03_irrMap t₀ r₀) :=
  apm_t98a03_glueMap_isCoveringMap _ _ _ _ apm_t98a03_torusCube_isLocalHomeomorph
    (apm_t98a03_isLocalHomeomorph_sumElim
      apm_t98a03_sphereProj_isCoveringMap.isLocalHomeomorph
      (Homeomorph.refl apm_t98a03_RP2).isLocalHomeomorph)
    (apm_t98a03_sheetPt_injective t₀)
    (apm_t98a03_irrTau_injective r₀ apm_t98a03_sphere_ne_neg)
    (apm_t98a03_torusCube_eq_iff t₀)
    (apm_t98a03_irrQ_eq_iff r₀ apm_t98a03_sphereProj_eq_iff)

lemma apm_t98a03_irrE_connected (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ConnectedSpace (apm_t98a03_IrrE t₀ r₀) := by
  refine apm_t98a03_glue_connectedSpace (fun b => ?_)
  rcases b with x | r
  · exact ⟨1, Set.range Sum.inl, isPreconnected_range continuous_inl, ⟨x, rfl⟩,
      ⟨apm_t98a03_unitRep r₀, rfl⟩⟩
  · exact ⟨0, Set.range Sum.inr, isPreconnected_range continuous_inr, ⟨r, rfl⟩,
      ⟨r₀, rfl⟩⟩

/-- Seat: a loop of the base with a closed lift and an open lift.

Route: let `s := apm_t98a03_unitRep r₀` and `γ : Path s (-s)` in the sphere
(`PathConnectedSpace.somePath`; the sphere is simply connected, hence path
connected, by the instance above).  Put
`γ₂ := glueMk ∘ inr ∘ inl ∘ γ` (sphere sheet, from `s` to `-s`) and
`γ₁ := glueMk ∘ inr ∘ inr ∘ sphereProj ∘ γ` (plane sheet; closed because
`sphereProj (-s) = sphereProj s`, `apm_t98a03_sphereProj_neg`).  Both project to
`glueMk (inr (sphereProj (γ t)))` (`apm_t98a03_glueMap_mk`, definitional).
`γ₂ 0 ≠ γ₂ 1`: by `hmkE` two `inr` representatives are identified only if equal,
and `s ≠ -s` (`hne`).  Continuity: `apm_t98a03_glueMk_continuous`,
`continuous_inr`, `continuous_inl`, the copied `..._aux_toP_continuous`.
Estimated 40–80 lines. -/
lemma apm_t98a03_irregular_paths (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (hne : ∀ x : apm_t98a03_t92_S2, x ≠ -x)
    (hmkE : ∀ x y, apm_t98a03_glueMk (apm_t98a03_sheetPt t₀) (apm_t98a03_irrTau r₀) x =
        apm_t98a03_glueMk (apm_t98a03_sheetPt t₀) (apm_t98a03_irrTau r₀) y ↔
      apm_t98a03_GlueEq (apm_t98a03_sheetPt t₀) (apm_t98a03_irrTau r₀) x y) :
    ∃ γ₁ γ₂ : C(unitInterval, apm_t98a03_IrrE t₀ r₀),
      apm_t98a03_irrMap t₀ r₀ ∘ γ₁ = apm_t98a03_irrMap t₀ r₀ ∘ γ₂ ∧
        γ₁ 0 = γ₁ 1 ∧ γ₂ 0 ≠ γ₂ 1 := by
  sorry

/-- Assembly: the irregular cover. -/
theorem apm_t98a03_irregular_threeFoldCover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ C : apm_t98a03_Cover (apm_t98a03_X t₀ r₀),
      apm_t98a03_IsConnectedThreeFoldCover C ∧ ¬apm_t98a03_IsRegularCover C := by
  have hcov := apm_t98a03_irrMap_isCoveringMap t₀ r₀
  have hinj := apm_t98a03_irrTau_injective r₀ apm_t98a03_sphere_ne_neg
  refine ⟨apm_t98a03_coverOf t₀ r₀ (apm_t98a03_irrMap t₀ r₀), ?_, ?_⟩
  · exact apm_t98a03_coverOf_threeFold t₀ r₀ _ hcov (apm_t98a03_irrE_connected t₀ r₀)
      (apm_t98a03_glueMap_fiber_card apm_t98a03_torusCube apm_t98a03_irrQ
        (apm_t98a03_torusCube_sheetPt t₀) (apm_t98a03_irrQ_tau r₀)
        (apm_t98a03_sheetPt_injective t₀) hinj
        (apm_t98a03_torusCube_eq_iff t₀)
        (apm_t98a03_irrQ_eq_iff r₀ apm_t98a03_sphereProj_eq_iff) 3
        apm_t98a03_torusCube_fiber_card
        (apm_t98a03_irrQ_fiber_card apm_t98a03_sphereProj_eq_iff apm_t98a03_sphere_ne_neg)
        (by simp))
  · rw [apm_t98a03_coverOf_regular_iff]
    rintro ⟨_, hreg⟩
    obtain ⟨γ₁, γ₂, hγ, h₁, h₂⟩ := apm_t98a03_irregular_paths t₀ r₀
      apm_t98a03_sphere_ne_neg
      (apm_t98a03_glueMk_eq_iff (apm_t98a03_sheetPt_injective t₀) hinj)
    exact apm_t98a03_no_deck_of_lift_mismatch hcov γ₁ γ₂ hγ h₁ h₂
      (hreg _ _ (congrFun hγ 0))

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

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
lemma apm_t98a03_wedge_branches_closed
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    IsClosed (apm_t98a03_torusBranch t₀ r₀) ∧
      IsClosed (apm_t98a03_rp2Branch t₀ r₀) := by
  sorry

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

/-- Seat: every open wedge-point neighborhood meets each branch away from it. -/
lemma apm_t98a03_wedge_branches_accumulate
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2)
    (U : Set (apm_t98a03_X t₀ r₀)) (hU : IsOpen U)
    (hpU : apm_t98a03_basepoint t₀ r₀ ∈ U) :
    ((U ∩ apm_t98a03_torusBranch t₀ r₀) \ {apm_t98a03_basepoint t₀ r₀}).Nonempty ∧
      ((U ∩ apm_t98a03_rp2Branch t₀ r₀) \ {apm_t98a03_basepoint t₀ r₀}).Nonempty := by
  sorry

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
  sorry

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
  sorry

/-- A point has arbitrarily small preconnected punctured neighborhoods. -/
def apm_t98a03_HasPuncturedPreconnectedBasis
    {X : Type*} [TopologicalSpace X] (p : X) : Prop :=
  ∀ U : Set X, IsOpen U → p ∈ U →
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ IsPreconnected (V \ {p})

/-- Seat: a torus point away from the gluing point retains its plane property. -/
lemma apm_t98a03_wedge_has_plane_point
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ p : apm_t98a03_X t₀ r₀,
      apm_t98a03_HasPuncturedPreconnectedBasis p := by
  sorry

/-- Seat: a one-manifold has the opposite local puncture property. -/
lemma apm_t98a03_one_manifold_punctured_obstruction
    {X : Type*} [TopologicalSpace X]
    (charts : ChartedSpace (EuclideanSpace ℝ (Fin 1)) X)
    (hman : let _ := charts
      IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) 0 X) :
    ∀ p : X, ¬ apm_t98a03_HasPuncturedPreconnectedBasis p := by
  sorry

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

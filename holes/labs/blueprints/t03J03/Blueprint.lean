import Mathlib
import ConstructionTargets.Surfaces

/-! # Blueprint for APM t03J03 -/

open Set
open ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t03J03_N3 := Surface false 3
abbrev apm_t03J03_Sigma2 := Surface true 2
abbrev apm_t03J03_N4 := Surface false 4

def apm_t03J03_IsOrientableSurface (Y : Type)
    (tY : TopologicalSpace Y) : Prop :=
  ∃ g : ℕ, Nonempty
    (@Homeomorph Y (Surface true g) tY (inferInstance : TopologicalSpace (Surface true g)))

def apm_t03J03_isTwoFoldCover {E X : Type}
    (tE : TopologicalSpace E) (tX : TopologicalSpace X)
    (p : E → X) : Prop :=
  @IsCoveringMap E X tE tX p ∧
  ∀ x : X, Nat.card {e : E // p e = x} = 2

structure apm_t03J03_connectedDoubleCover
    (X : Type) (tX : TopologicalSpace X) where
  E : Type
  topology : TopologicalSpace E
  p : E → X
  covering : apm_t03J03_isTwoFoldCover topology tX p
  connected : @IsConnected E topology (Set.univ : Set E)

def apm_t03J03_coverEquivalent
    {X : Type} {tX : TopologicalSpace X}
    (c d : apm_t03J03_connectedDoubleCover X tX) : Prop :=
  let _ := c.topology
  let _ := d.topology
  ∃ h : c.E ≃ₜ d.E, ∀ e : c.E, d.p (h e) = c.p e

abbrev apm_t03J03_character :=
  {phi : Fin 3 → ZMod 2 // phi ≠ 0}

def apm_t03J03_orientationCharacter : Fin 3 → ZMod 2 :=
  fun _ ↦ 1

abbrev apm_t03J03_Cylinder := Circle × Set.Icc (0 : ℝ) 1

def apm_t03J03_trivialCoverMap {X : Type} : X ⊕ X → X :=
  Sum.elim id id

def apm_t03J03_generalCoverEquivalent
    {E F X : Type}
    (tE : TopologicalSpace E) (tF : TopologicalSpace F)
    (p : E → X) (q : F → X) : Prop :=
  let _ := tE
  let _ := tF
  ∃ h : E ≃ₜ F, ∀ e : E, q (h e) = p e

lemma apm_t03J03_euler_N3 : eulerCharacteristic false 3 = -1 := by
  rfl

lemma apm_t03J03_euler_Sigma2 : eulerCharacteristic true 2 = -2 := by
  rfl

lemma apm_t03J03_euler_N4 : eulerCharacteristic false 4 = -2 := by
  rfl

lemma apm_t03J03_character_card : Nat.card apm_t03J03_character = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide

lemma apm_t03J03_orientationCharacter_ne_zero :
    apm_t03J03_orientationCharacter ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [apm_t03J03_orientationCharacter] at h0

def apm_t03J03_orientationCharacterAsCharacter : apm_t03J03_character :=
  ⟨apm_t03J03_orientationCharacter, apm_t03J03_orientationCharacter_ne_zero⟩

/-- The final lift follows from Mathlib's fundamental-group lifting criterion
once a point above the basepoint and the induced range inclusion are given. -/
lemma apm_t03J03_exists_cylinderLift_of_range_le
    [PathConnectedSpace apm_t03J03_Cylinder]
    [LocPathConnectedSpace apm_t03J03_Cylinder]
    (Y : Type) (tY : TopologicalSpace Y) (p : Y → apm_t03J03_N3)
    (hp : apm_t03J03_isTwoFoldCover tY inferInstance p)
    (f : apm_t03J03_Cylinder → apm_t03J03_N3)
    (hf : @Topology.IsEmbedding apm_t03J03_Cylinder apm_t03J03_N3
      inferInstance inferInstance f)
    (z₀ : apm_t03J03_Cylinder) (y₀ : Y)
    (hy₀ : p y₀ = f z₀)
    (hle : (FundamentalGroup.map ⟨f, hf.continuous⟩ z₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.1.continuous⟩ hy₀).range) :
    ∃ lift : apm_t03J03_Cylinder → Y,
      @Continuous apm_t03J03_Cylinder Y inferInstance tY lift ∧
      ∀ z, p (lift z) = f z := by
  letI : TopologicalSpace Y := tY
  let fc : C(apm_t03J03_Cylinder, apm_t03J03_N3) := ⟨f, hf.continuous⟩
  obtain ⟨F, hF, _⟩ :=
    hp.1.existsUnique_continuousMap_lifts_of_range_le hy₀ hle
  refine ⟨F, F.continuous, ?_⟩
  intro z
  exact congrFun hF.2 z

/-- **LIBRARY: polygon double-cover classification and surface normal forms.** -/
theorem apm_t03J03_connected_double_cover_classification :
    ∃ reps : apm_t03J03_character →
        apm_t03J03_connectedDoubleCover apm_t03J03_N3 inferInstance,
      (∀ c : apm_t03J03_connectedDoubleCover apm_t03J03_N3 inferInstance,
        ∃! phi : apm_t03J03_character,
          apm_t03J03_coverEquivalent c (reps phi)) ∧
      (∀ phi : apm_t03J03_character,
        if (phi : Fin 3 → ZMod 2) = apm_t03J03_orientationCharacter then
          Nonempty (@Homeomorph (reps phi).E apm_t03J03_Sigma2
            (reps phi).topology inferInstance)
        else
          Nonempty (@Homeomorph (reps phi).E apm_t03J03_N4
            (reps phi).topology inferInstance)) := by
  sorry

lemma apm_t03J03_disconnected_double_cover_trivial_aux_base_pathConnected :
    IsPathConnected (Set.univ : Set apm_t03J03_N3) := by
  letI : PathConnectedSpace Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (E := ℂ) zero_le_one)
  rw [← Set.range_eq_univ.mpr (surjective_surfaceQuotient false 3)]
  simpa only [Set.image_univ] using
    (pathConnectedSpace_iff_univ.mp (inferInstance : PathConnectedSpace Disk)).image
      (continuous_surfaceQuotient false 3)

/-- Seat: `N₃` is locally connected (a quotient of the closed disc, which is
locally connected; quotient maps preserve local connectedness). -/
theorem apm_t03J03_N3_locallyConnected : LocallyConnectedSpace apm_t03J03_N3 := by
  letI : LocPathConnectedSpace Disk :=
    (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace
  have hq : Topology.IsQuotientMap (surfaceQuotient false 3) :=
    Topology.IsQuotientMap.mk (surjective_surfaceQuotient false 3) rfl
  letI : LocPathConnectedSpace apm_t03J03_N3 := hq.locPathConnectedSpace
  infer_instance

lemma apm_t03J03_disconnected_two_sheeted_split_aux_clopen
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [ConnectedSpace X] (p : E → X)
    (h2 : ∀ x : X, Nat.card {e : E // p e = x} = 2)
    (hE : ¬ IsConnected (Set.univ : Set E)) :
    ∃ U : Set E, IsClopen U ∧ U.Nonempty ∧ Uᶜ.Nonempty := by
  haveI : Nonempty E := by
    let x : X := Classical.arbitrary X
    have hc : Nat.card {e : E // p e = x} = 2 := h2 x
    have hs : Nonempty {e : E // p e = x} := by
      by_contra hn
      haveI : IsEmpty {e : E // p e = x} := not_nonempty_iff.mp hn
      simpa using hc
    exact ⟨hs.some.1⟩
  have hncs : ¬ ConnectedSpace E := fun h ↦ hE (connectedSpace_iff_univ.mp h)
  rw [connectedSpace_iff_clopen] at hncs
  push_neg at hncs
  obtain ⟨U, hU, hne, hnu⟩ := hncs this
  refine ⟨U, hU, hne, ?_⟩
  simpa only [Set.nonempty_compl] using hnu

lemma apm_t03J03_disconnected_two_sheeted_split_aux_unique_of_both
    {E X : Type} (p : E → X) (U : Set E)
    (h2 : ∀ x : X, Nat.card {e : E // p e = x} = 2)
    (hboth : ∀ x, (∃ e, e ∈ U ∧ p e = x) ∧ (∃ e, e ∉ U ∧ p e = x)) :
    (∀ x, ∃! e, e ∈ U ∧ p e = x) ∧
      (∀ x, ∃! e, e ∉ U ∧ p e = x) := by
  have one_side (x : X) (V : Set E)
      (ha : ∃ e, e ∈ V ∧ p e = x) (hb : ∃ e, e ∉ V ∧ p e = x) :
      ∃! e, e ∈ V ∧ p e = x := by
    obtain ⟨a, haV, hap⟩ := ha
    obtain ⟨b, hbV, hbp⟩ := hb
    refine ⟨a, ⟨haV, hap⟩, ?_⟩
    intro c hc
    have hab : (⟨a, hap⟩ : {e : E // p e = x}) ≠ ⟨b, hbp⟩ := by
      intro heq
      have : a = b := congrArg Subtype.val heq
      exact hbV (this ▸ haV)
    obtain ⟨u, v, huv, huv_univ⟩ := Nat.card_eq_two_iff.mp (h2 x)
    have hall : ∀ z : {e : E // p e = x}, z = ⟨a, hap⟩ ∨ z = ⟨b, hbp⟩ := by
      intro z
      have hz : z = u ∨ z = v := by
        have : z ∈ ({u, v} : Set {e : E // p e = x}) := by rw [huv_univ]; trivial
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      have ha_pair : (⟨a, hap⟩ : {e : E // p e = x}) = u ∨ ⟨a, hap⟩ = v := by
        have : (⟨a, hap⟩ : {e : E // p e = x}) ∈ ({u, v} : Set _) := by rw [huv_univ]; trivial
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      have hb_pair : (⟨b, hbp⟩ : {e : E // p e = x}) = u ∨ ⟨b, hbp⟩ = v := by
        have : (⟨b, hbp⟩ : {e : E // p e = x}) ∈ ({u, v} : Set _) := by rw [huv_univ]; trivial
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      rcases hz with rfl | rfl <;> rcases ha_pair with ha | ha <;>
        rcases hb_pair with hb | hb <;> simp_all
    rcases hall ⟨c, hc.2⟩ with hca | hcb
    · exact congrArg Subtype.val hca
    · exfalso
      have hcb' : c = b := congrArg Subtype.val hcb
      exact hbV (hcb' ▸ hc.1)
  constructor
  · intro x
    exact one_side x U (hboth x).1 (hboth x).2
  · intro x
    apply one_side x Uᶜ (hboth x).2
    simpa only [Set.mem_compl_iff, not_not] using (hboth x).1

/-- Seat (generic): over a connected, locally connected base, the image of a
nonempty clopen subset of a covering space is everything (it is open since
covering maps are open; its complement is open: over a connected evenly covered
neighbourhood each sheet is connected, so it lies inside or outside the clopen
set). -/
theorem apm_t03J03_clopen_image_univ {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p)
    (U : Set E) (hU : IsClopen U) (hne : U.Nonempty) : p '' U = Set.univ := by
  apply IsClopen.eq_univ
  · refine ⟨?_, hp.isOpenMap U hU.isOpen⟩
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : x ∉ p '' U := by simpa using hx
    obtain ⟨_, V, hxV, hV, hpV, H, hH⟩ := hp x
    obtain ⟨W, hWV, hWopen, hxW, hWconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x V
        (hV.mem_nhds hxV)
    refine Filter.mem_of_superset (hWopen.mem_nhds hxW) ?_
    intro y hyW hy_image
    obtain ⟨e, heU, rfl⟩ := hy_image
    have hpeV : p e ∈ V := hWV hyW
    let i := (H ⟨e, hpeV⟩).2
    let g : W → E := fun z ↦ H.symm (⟨z.1, hWV z.2⟩, i)
    have hg_cont : Continuous g := by
      dsimp [g]
      fun_prop
    have hge : g ⟨p e, hyW⟩ = e := by
      change ↑(H.symm (⟨⟨p e, hWV hyW⟩, i⟩)) = e
      have hpair : (⟨⟨p e, hWV hyW⟩, i⟩ : V × (p ⁻¹' {x})) = H ⟨e, hpeV⟩ := by
        ext
        · exact (hH ⟨e, hpeV⟩).symm
        · rfl
      rw [hpair]
      exact congrArg Subtype.val (H.symm_apply_apply ⟨e, hpeV⟩)
    have hgx_p : p (g ⟨x, hxW⟩) = x := by
      simpa [g] using (hH (H.symm (⟨⟨x, hWV hxW⟩, i⟩))).symm
    have hgx_not : g ⟨x, hxW⟩ ∉ U := by
      intro hgxU
      exact hx' ⟨g ⟨x, hxW⟩, hgxU, hgx_p⟩
    letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWconn
    have himage_pre : IsPreconnected (g '' Set.univ) :=
      ((connectedSpace_iff_univ.mp inferInstance).image g hg_cont.continuousOn).isPreconnected
    have hge_mem : g ⟨p e, hyW⟩ ∈ g '' Set.univ :=
      ⟨⟨p e, hyW⟩, Set.mem_univ _, rfl⟩
    have himage_sub : g '' Set.univ ⊆ U :=
      himage_pre.subset_isClopen hU ⟨g ⟨p e, hyW⟩, hge_mem, hge.symm ▸ heU⟩
    have hgx_mem : g ⟨x, hxW⟩ ∈ g '' Set.univ :=
      ⟨⟨x, hxW⟩, Set.mem_univ _, rfl⟩
    exact hgx_not (himage_sub hgx_mem)
  · exact hne.image p

theorem apm_t03J03_disconnected_two_sheeted_split {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p)
    (h2 : ∀ x : X, Nat.card {e : E // p e = x} = 2) (hE : ¬ IsConnected (Set.univ : Set E))
    (himage : ∀ U : Set E, IsClopen U → U.Nonempty → p '' U = Set.univ) :
    ∃ U : Set E, IsClopen U ∧ (∀ x, ∃! e, e ∈ U ∧ p e = x) ∧
      (∀ x, ∃! e, e ∉ U ∧ p e = x) := by
  obtain ⟨U, hU, hUne, hUcne⟩ :=
    apm_t03J03_disconnected_two_sheeted_split_aux_clopen p h2 hE
  have hU_image : p '' U = Set.univ := himage U hU hUne
  have hUc_image : p '' Uᶜ = Set.univ := himage Uᶜ hU.compl hUcne
  have hboth :
      ∀ x, (∃ e, e ∈ U ∧ p e = x) ∧ (∃ e, e ∉ U ∧ p e = x) := by
    intro x
    constructor
    · have hx : x ∈ p '' U := by rw [hU_image]; trivial
      obtain ⟨e, heU, hep⟩ := hx
      exact ⟨e, heU, hep⟩
    · have hx : x ∈ p '' Uᶜ := by rw [hUc_image]; trivial
      obtain ⟨e, heUc, hep⟩ := hx
      exact ⟨e, heUc, hep⟩
  obtain ⟨hU_unique, hUc_unique⟩ :=
    apm_t03J03_disconnected_two_sheeted_split_aux_unique_of_both p U h2 hboth
  exact ⟨U, hU, hU_unique, hUc_unique⟩

/-- Seat (generic): a split as above makes `p` equivalent to the trivial cover
`X ⊕ X → X` (each clopen piece maps homeomorphically: a bijective covering map
is a homeomorphism, being a continuous open bijection). -/
theorem apm_t03J03_trivial_of_split {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : E → X) (hp : IsCoveringMap p)
    (U : Set E) (hU : IsClopen U) (h1 : ∀ x, ∃! e, e ∈ U ∧ p e = x)
    (h1' : ∀ x, ∃! e, e ∉ U ∧ p e = x) :
    apm_t03J03_generalCoverEquivalent inferInstance inferInstance p
      (apm_t03J03_trivialCoverMap (X := X)) := by
  classical
  let f : E → X ⊕ X := fun e ↦ if e ∈ U then Sum.inl (p e) else Sum.inr (p e)
  have hf_cont : Continuous f := by
    apply Continuous.piecewise
    · intro e he
      rw [hU.frontier_eq] at he
      exact he.elim
    · exact continuous_inl.comp hp.continuous
    · exact continuous_inr.comp hp.continuous
  have hf_inj : Function.Injective f := by
    intro e e' heq
    by_cases he : e ∈ U
    · have he' : e' ∈ U := by
        by_contra hn
        simp [f, he, hn] at heq
      have hp_eq : p e = p e' := by simpa [f, he, he'] using heq
      exact (h1 (p e)).unique (⟨he, rfl⟩) (⟨he', hp_eq.symm⟩)
    · have he' : e' ∉ U := by
        intro he'
        simp [f, he, he'] at heq
      have hp_eq : p e = p e' := by simpa [f, he, he'] using heq
      exact (h1' (p e)).unique (⟨he, rfl⟩) (⟨he', hp_eq.symm⟩)
  have hf_surj : Function.Surjective f := by
    intro z
    cases z with
    | inl x =>
        obtain ⟨e, he, hpe⟩ := (h1 x).exists
        exact ⟨e, by simp [f, he, hpe]⟩
    | inr x =>
        obtain ⟨e, he, hpe⟩ := (h1' x).exists
        exact ⟨e, by simp [f, he, hpe]⟩
  have hf_open : IsOpenMap f := by
    intro V hV
    rw [isOpen_sum_iff]
    constructor
    · have himage : Sum.inl ⁻¹' (f '' V) = p '' (V ∩ U) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff]
        constructor
        · rintro ⟨e, heV, heq⟩
          by_cases heU : e ∈ U
          · exact ⟨e, ⟨heV, heU⟩, by simpa [f, heU] using heq⟩
          · simp [f, heU] at heq
        · rintro ⟨e, ⟨heV, heU⟩, rfl⟩
          exact ⟨e, heV, by simp [f, heU]⟩
      rw [himage]
      exact hp.isOpenMap _ (hV.inter hU.isOpen)
    · have himage : Sum.inr ⁻¹' (f '' V) = p '' (V ∩ Uᶜ) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff, Set.mem_compl_iff]
        constructor
        · rintro ⟨e, heV, heq⟩
          by_cases heU : e ∈ U
          · simp [f, heU] at heq
          · exact ⟨e, ⟨heV, heU⟩, by simpa [f, heU] using heq⟩
        · rintro ⟨e, ⟨heV, heU⟩, rfl⟩
          exact ⟨e, heV, by simp [f, heU]⟩
      rw [himage]
      exact hp.isOpenMap _ (hV.inter hU.isClosed.isOpen_compl)
  refine ⟨(Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).toHomeomorphOfContinuousOpen
      hf_cont hf_open, ?_⟩
  intro e
  by_cases he : e ∈ U <;> simp [apm_t03J03_trivialCoverMap, f, he]

/-- **LIBRARY: classification of disconnected two-sheeted covers.** -/
theorem apm_t03J03_disconnected_double_cover_trivial :
    ∀ (E : Type) (tE : TopologicalSpace E) (p : E → apm_t03J03_N3),
      apm_t03J03_isTwoFoldCover tE inferInstance p →
      ¬ @IsConnected E tE (Set.univ : Set E) →
      apm_t03J03_generalCoverEquivalent tE inferInstance
        p apm_t03J03_trivialCoverMap := by
  intro E tE p hcov hE
  haveI := apm_t03J03_N3_locallyConnected
  haveI : PathConnectedSpace apm_t03J03_N3 :=
    (pathConnectedSpace_iff_univ.mpr apm_t03J03_disconnected_double_cover_trivial_aux_base_pathConnected)
  obtain ⟨U, hU, h1, h1'⟩ :=
    @apm_t03J03_disconnected_two_sheeted_split E _ tE _ inferInstance _ p hcov.1 hcov.2 hE
      (fun U hU hne => @apm_t03J03_clopen_image_univ E _ tE _ inferInstance _ p hcov.1 U hU hne)
  exact @apm_t03J03_trivial_of_split E _ tE _ p hcov.1 U hU h1 h1'

/-- **LIBRARY: the two-sided annulus core has trivial orientation monodromy.** -/
theorem apm_t03J03_orientable_double_cover_annulus_lift :
    (∃ reps : apm_t03J03_character →
        apm_t03J03_connectedDoubleCover apm_t03J03_N3 inferInstance,
      (∀ c : apm_t03J03_connectedDoubleCover apm_t03J03_N3 inferInstance,
        ∃! phi : apm_t03J03_character,
          apm_t03J03_coverEquivalent c (reps phi)) ∧
      (∀ phi : apm_t03J03_character,
        if (phi : Fin 3 → ZMod 2) = apm_t03J03_orientationCharacter then
          Nonempty (@Homeomorph (reps phi).E apm_t03J03_Sigma2
            (reps phi).topology inferInstance)
        else
          Nonempty (@Homeomorph (reps phi).E apm_t03J03_N4
            (reps phi).topology inferInstance))) →
    ∀ (Y : Type) (tY : TopologicalSpace Y) (p : Y → apm_t03J03_N3),
      apm_t03J03_isTwoFoldCover tY inferInstance p →
      apm_t03J03_IsOrientableSurface Y tY →
      ∀ f : apm_t03J03_Cylinder → apm_t03J03_N3,
        @Topology.IsEmbedding apm_t03J03_Cylinder apm_t03J03_N3
          inferInstance inferInstance f →
        ∃ lift : apm_t03J03_Cylinder → Y,
          @Continuous apm_t03J03_Cylinder Y inferInstance tY lift ∧
          ∀ z, p (lift z) = f z := by
  sorry

theorem apm_t03j03
    :
    eulerCharacteristic false 3 = -1 ∧
    eulerCharacteristic true 2 = -2 ∧
    eulerCharacteristic false 4 = -2 ∧
    Nat.card apm_t03J03_character = 7 ∧
    (∃ reps : apm_t03J03_character →
        apm_t03J03_connectedDoubleCover apm_t03J03_N3 inferInstance,
      (∀ c : apm_t03J03_connectedDoubleCover apm_t03J03_N3 inferInstance,
        ∃! phi : apm_t03J03_character,
          apm_t03J03_coverEquivalent c (reps phi)) ∧
      (∀ phi : apm_t03J03_character,
        if (phi : Fin 3 → ZMod 2) = apm_t03J03_orientationCharacter then
          Nonempty (@Homeomorph (reps phi).E apm_t03J03_Sigma2
            (reps phi).topology inferInstance)
        else
          Nonempty (@Homeomorph (reps phi).E apm_t03J03_N4
            (reps phi).topology inferInstance))) ∧
    (∀ (E : Type) (tE : TopologicalSpace E) (p : E → apm_t03J03_N3),
      apm_t03J03_isTwoFoldCover tE inferInstance p →
      ¬ @IsConnected E tE (Set.univ : Set E) →
      apm_t03J03_generalCoverEquivalent tE inferInstance
        p apm_t03J03_trivialCoverMap) ∧
    (∀ (Y : Type) (tY : TopologicalSpace Y) (p : Y → apm_t03J03_N3),
      apm_t03J03_isTwoFoldCover tY inferInstance p →
      apm_t03J03_IsOrientableSurface Y tY →
      ∀ f : apm_t03J03_Cylinder → apm_t03J03_N3,
        @Topology.IsEmbedding apm_t03J03_Cylinder apm_t03J03_N3
          inferInstance inferInstance f →
        ∃ lift : apm_t03J03_Cylinder → Y,
          @Continuous apm_t03J03_Cylinder Y inferInstance tY lift ∧
          ∀ z, p (lift z) = f z) := by
  exact ⟨apm_t03J03_euler_N3, apm_t03J03_euler_Sigma2,
    apm_t03J03_euler_N4, apm_t03J03_character_card,
    apm_t03J03_connected_double_cover_classification,
    apm_t03J03_disconnected_double_cover_trivial,
    apm_t03J03_orientable_double_cover_annulus_lift
      apm_t03J03_connected_double_cover_classification⟩

#print axioms apm_t03j03

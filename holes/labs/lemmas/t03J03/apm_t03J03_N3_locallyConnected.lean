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
-- BEGIN SEAT AREA
theorem apm_t03J03_N3_locallyConnected : LocallyConnectedSpace apm_t03J03_N3 := by
  sorry
-- END SEAT AREA

/-- Seat (generic): a disconnected two-sheeted covering of a connected, locally
connected space splits into a clopen set and its complement, each meeting every
fibre exactly once (the sheet count of a clopen set is locally constant over
connected evenly covered neighbourhoods; it is 0, 1 or 2, and 0/2 force `U`
empty/everything). -/
theorem apm_t03J03_disconnected_two_sheeted_split {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p)
    (h2 : ∀ x : X, Nat.card {e : E // p e = x} = 2) (hE : ¬ IsConnected (Set.univ : Set E)) :
    ∃ U : Set E, IsClopen U ∧ (∀ x, ∃! e, e ∈ U ∧ p e = x) ∧
      (∀ x, ∃! e, e ∉ U ∧ p e = x) := by
  sorry

/-- Seat (generic): a split as above makes `p` equivalent to the trivial cover
`X ⊕ X → X` (each clopen piece maps homeomorphically: a bijective covering map
is a homeomorphism, being a continuous open bijection). -/
theorem apm_t03J03_trivial_of_split {E X : Type}
    [TopologicalSpace E] [TopologicalSpace X] (p : E → X) (hp : IsCoveringMap p)
    (U : Set E) (hU : IsClopen U) (h1 : ∀ x, ∃! e, e ∈ U ∧ p e = x)
    (h1' : ∀ x, ∃! e, e ∉ U ∧ p e = x) :
    apm_t03J03_generalCoverEquivalent inferInstance inferInstance p
      (apm_t03J03_trivialCoverMap (X := X)) := by
  sorry

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

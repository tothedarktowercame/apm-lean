import Mathlib
import ConstructionTargets.Surfaces

/-!
# APM t03J03: double covers of the three-crosscap surface

## Statement repairs

None.

## Encoding questions

The classified surfaces are the concrete polygon quotients from
`ConstructionTargets.Surfaces`. Covering spaces, their maps and equivalences,
the seven connected-cover representatives, the embedded cylinder, and its
lift are represented by their actual objects.
-/

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

/-- The final cylinder-lifting conclusion follows directly from Mathlib's
fundamental-group lifting criterion once its range inclusion is supplied. -/
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
  obtain ⟨F, hF, _⟩ := hp.1.existsUnique_continuousMap_lifts_of_range_le hy₀ hle
  refine ⟨F, F.continuous, ?_⟩
  intro z
  exact congrFun hF.2 z

/-- Why this unblocks `apm_t03j03`: this is the missing classification of
connected double covers by nonzero `ZMod 2` characters, including the
orientation-character test that distinguishes `Sigma₂` from `N₄`. -/
theorem apm_t03J03_bridge_1 :
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

/-- Why this unblocks `apm_t03j03`: this is the complementary classification
theorem for disconnected two-sheeted covers of the connected three-crosscap
surface; it identifies every such cover with the trivial double cover. -/
theorem apm_t03J03_bridge_2 :
    ∀ (E : Type) (tE : TopologicalSpace E) (p : E → apm_t03J03_N3),
      apm_t03J03_isTwoFoldCover tE inferInstance p →
      ¬ @IsConnected E tE (Set.univ : Set E) →
      apm_t03J03_generalCoverEquivalent tE inferInstance
        p apm_t03J03_trivialCoverMap := by
  sorry

/-- Why this unblocks `apm_t03j03`: this is the orientation-character range
consequence in its geometric form.  It states that every embedded cylinder
lifts continuously to every orientable two-sheeted cover, exactly the final
conjunct required after the general lifting criterion above. -/
theorem apm_t03J03_bridge_3 :
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
  refine ⟨apm_t03J03_euler_N3, apm_t03J03_euler_Sigma2,
    apm_t03J03_euler_N4, apm_t03J03_character_card, ?_⟩
  /-
  Boundary (closer hop 3): hop 2 closed four frozen numerical conjuncts.
  The three Euler-characteristic identities reduce directly to
  `ConstructionTargets.Surfaces.eulerCharacteristic`, and
  `apm_t03J03_character_card` computes the cardinality of the nonzero
  functions `Fin 3 → ZMod 2` as seven. The orientation character is also
  bundled explicitly as `apm_t03J03_orientationCharacterAsCharacter`.

  The remaining existential requires constructing seven actual connected
  covering spaces of the polygon quotient, proving every connected double
  cover equivalent to exactly one of them, and identifying their total spaces
  as `Sigma₂` or `N₄`. `ConstructionTargets.Surfaces` supplies only the
  quotient presentations and elementary Euler arithmetic; it has no covering
  maps, connectedness proofs, surface classification, or fundamental-group
  computation. The disconnected clause likewise requires the theorem that a
  disconnected two-sheeted cover of this connected base is the trivial cover.

  Going beyond that boundary, hop 3 packages Mathlib's covering lifting
  criterion as `apm_t03J03_exists_cylinderLift_of_range_le`. Given the
  standard path-connected/local-path-connected instances for the cylinder, a
  chosen point in the fiber, and the induced fundamental-group range
  inclusion, it constructs exactly the continuous lift and commuting equation
  required by the frozen final conjunct. Thus no additional lifting or
  topology-instance bookkeeping remains after those inputs are available.

  The range inclusion normally follows from the missing orientation-character
  classification. Renewed searches of `LEMMA-INDEX.md`, all
  `ConstructionTargets/`, Mathlib's covering, monodromy, fundamental-group,
  quotient-surface, and surface-classification sources, related covering
  siblings, and git history found no compiled classification bridge. The
  frozen statement is unchanged.
  -/
  sorry

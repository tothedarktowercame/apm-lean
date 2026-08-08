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
  native_decide

lemma apm_t03J03_orientationCharacter_ne_zero :
    apm_t03J03_orientationCharacter ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [apm_t03J03_orientationCharacter] at h0

def apm_t03J03_orientationCharacterAsCharacter : apm_t03J03_character :=
  ⟨apm_t03J03_orientationCharacter, apm_t03J03_orientationCharacter_ne_zero⟩

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
  Boundary (closer hop 2): four frozen numerical conjuncts are now closed.
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

  I additionally investigated Mathlib's covering lifting criterion
  `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`. It can produce
  the final cylinder lift only after proving the relevant fundamental-group
  range inclusion (normally from orientation-character classification), which
  is exactly the missing global input. Searches of `LEMMA-INDEX.md`, all
  `ConstructionTargets/`, Mathlib's covering, monodromy, fundamental-group,
  quotient-surface, and surface-classification sources, related covering
  siblings, and git history found no compiled classification bridge. The
  frozen statement is unchanged.
  -/
  sorry

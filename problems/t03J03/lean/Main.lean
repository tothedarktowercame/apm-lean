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

theorem apm_t03j03
    :
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
  sorry

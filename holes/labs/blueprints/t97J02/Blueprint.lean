import Mathlib

open Set
open scoped Manifold ContDiff

noncomputable section

abbrev apm_t97J02_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t97J02_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t97J02_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t97J02_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_t97J02_SurfaceRel (orientable : Bool) (genus : ℕ)
    (x y : apm_t97J02_Disk) : Prop :=
  if orientable then
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      let tr : Set.Icc (0 : ℝ) 1 :=
        ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      (x = apm_t97J02_edgePoint (4 * genus) (4 * j) t ∧
          y = apm_t97J02_edgePoint (4 * genus) (4 * j + 2) tr) ∨
        (x = apm_t97J02_edgePoint (4 * genus) (4 * j + 1) t ∧
          y = apm_t97J02_edgePoint (4 * genus) (4 * j + 3) tr)
  else
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      x = apm_t97J02_edgePoint (2 * genus) (2 * j) t ∧
      y = apm_t97J02_edgePoint (2 * genus) (2 * j + 1) t

def apm_t97J02_Surface (orientable : Bool) (genus : ℕ) :=
  Quotient (Relation.EqvGen.setoid
    (apm_t97J02_SurfaceRel orientable genus))

noncomputable instance (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (apm_t97J02_Surface orientable genus) :=
  TopologicalSpace.coinduced
    (fun x : apm_t97J02_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t97J02_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    apm_t97J02_Disk → apm_t97J02_Surface orientable genus :=
  fun x => Quotient.mk _ x

lemma apm_t97J02_continuous_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Continuous (apm_t97J02_surfaceQuotient orientable genus) := by
  exact continuous_coinduced_rng

lemma apm_t97J02_surjective_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Function.Surjective (apm_t97J02_surfaceQuotient orientable genus) := by
  exact Quotient.mk_surjective

def apm_t97J02_eulerCharacteristic (orientable : Bool) (genus : ℕ) : ℤ :=
  if orientable then 2 - 2 * (genus : ℤ) else 2 - (genus : ℤ)

@[simp] lemma apm_t97J02_eulerCharacteristic_orientable (genus : ℕ) :
    apm_t97J02_eulerCharacteristic true genus = 2 - 2 * (genus : ℤ) := rfl

@[simp] lemma apm_t97J02_eulerCharacteristic_nonorientable (genus : ℕ) :
    apm_t97J02_eulerCharacteristic false genus = 2 - (genus : ℤ) := rfl

lemma apm_t97J02_candidate_eulerCharacteristics :
    apm_t97J02_eulerCharacteristic false 4 = -2 ∧
    apm_t97J02_eulerCharacteristic false 12 =
      5 * apm_t97J02_eulerCharacteristic false 4 ∧
    apm_t97J02_eulerCharacteristic true 7 =
      6 * apm_t97J02_eulerCharacteristic false 4 ∧
    apm_t97J02_eulerCharacteristic false 14 =
      6 * apm_t97J02_eulerCharacteristic false 4 := by
  norm_num

lemma apm_t97J02_nonorientable_genus_of_euler_eq
    (n genus : ℕ)
    (h : apm_t97J02_eulerCharacteristic false genus =
      (n : ℤ) * apm_t97J02_eulerCharacteristic false 4) :
    genus = 2 * n + 2 := by
  simp only [apm_t97J02_eulerCharacteristic_nonorientable] at h
  omega

lemma apm_t97J02_orientable_genus_of_euler_eq
    (n genus : ℕ)
    (h : apm_t97J02_eulerCharacteristic true genus =
      (n : ℤ) * apm_t97J02_eulerCharacteristic false 4) :
    genus = n + 1 := by
  simp only [apm_t97J02_eulerCharacteristic_orientable,
    apm_t97J02_eulerCharacteristic_nonorientable] at h
  omega

abbrev apm_t97J02_X := apm_t97J02_Surface false 4

def apm_t97J02_IsNfoldCover
    {E : Type} [TopologicalSpace E] (n : ℕ) (p : E → apm_t97J02_X) : Prop :=
  IsCoveringMap p ∧
    ∀ x : apm_t97J02_X, Nat.card {e : E // p e = x} = n

structure apm_t97J02_CoverWitness (orientable : Bool) (genus n : ℕ) where
  p : apm_t97J02_Surface orientable genus → apm_t97J02_X
  covering : apm_t97J02_IsNfoldCover n p

/-- LIBRARY: polygon/permutation-cover construction for the cyclic five-cover. -/
theorem apm_t97J02_exists_nonorientable_five_cover :
    Nonempty (apm_t97J02_CoverWitness false 12 5) := by
  sorry

/-- LIBRARY: orientation-double-cover followed by the cyclic three-cover. -/
theorem apm_t97J02_exists_orientable_six_cover :
    Nonempty (apm_t97J02_CoverWitness true 7 6) := by
  sorry

/-- LIBRARY: polygon/permutation-cover construction for the cyclic six-cover. -/
theorem apm_t97J02_exists_nonorientable_six_cover :
    Nonempty (apm_t97J02_CoverWitness false 14 6) := by
  sorry

/-- LIBRARY: finite-cover Euler multiplicativity, orientation parity, and
closed-surface classification, specialized to degree five. -/
theorem apm_t97J02_classify_five_cover :
    ∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) (⊤ : ℕ∞) E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 5 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface false 12) := by
  sorry

/-- LIBRARY: finite-cover Euler multiplicativity and closed-surface
classification, specialized to degree six. -/
theorem apm_t97J02_classify_six_cover :
    ∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) (⊤ : ℕ∞) E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 6 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface true 7) ∨
        Nonempty (E ≃ₜ apm_t97J02_Surface false 14) := by
  sorry

theorem apm_t97j02 :
    Nonempty (apm_t97J02_CoverWitness false 12 5) ∧
    (∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) (⊤ : ℕ∞) E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 5 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface false 12)) ∧
    Nonempty (apm_t97J02_CoverWitness true 7 6) ∧
    Nonempty (apm_t97J02_CoverWitness false 14 6) ∧
    ∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) (⊤ : ℕ∞) E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 6 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface true 7) ∨
        Nonempty (E ≃ₜ apm_t97J02_Surface false 14) := by
  exact ⟨apm_t97J02_exists_nonorientable_five_cover,
    apm_t97J02_classify_five_cover,
    apm_t97J02_exists_orientable_six_cover,
    apm_t97J02_exists_nonorientable_six_cover,
    apm_t97J02_classify_six_cover⟩

#print axioms apm_t97j02

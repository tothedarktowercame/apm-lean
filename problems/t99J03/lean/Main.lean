import Mathlib

/-!
# APM t99J03 — classification of compact connected surfaces

## Statement repairs

The spelling `Breifly` is corrected to `Briefly`. No mathematical content is
changed.

## Encoding questions

Mathlib has no packaged surface-classification theorem or geometric
realization of abstract triangulations. The two normal-form families are
therefore encoded concretely as polygon quotients of the closed disk: products
of commutators for orientable genus and paired equal-direction edges for
nonorientable genus. The theorem concerns actual compact connected smooth
2-manifolds and actual homeomorphisms to those quotients. The polygon
construction records the cut-to-a-polygon/normal-form proof outline requested
in part (b).
-/

open Set
open scoped Manifold

noncomputable section

abbrev apm_t99J03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t99J03_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t99J03_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t99J03_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_t99J03_SurfaceRel (orientable : Bool) (genus : ℕ)
    (x y : apm_t99J03_Disk) : Prop :=
  if orientable then
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      let tr : Set.Icc (0 : ℝ) 1 :=
        ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      (x = apm_t99J03_edgePoint (4 * genus) (4 * j) t ∧
          y = apm_t99J03_edgePoint (4 * genus) (4 * j + 2) tr) ∨
        (x = apm_t99J03_edgePoint (4 * genus) (4 * j + 1) t ∧
          y = apm_t99J03_edgePoint (4 * genus) (4 * j + 3) tr)
  else
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      x = apm_t99J03_edgePoint (2 * genus) (2 * j) t ∧
      y = apm_t99J03_edgePoint (2 * genus) (2 * j + 1) t

def apm_t99J03_Surface (orientable : Bool) (genus : ℕ) :=
  Quotient (Relation.EqvGen.setoid (apm_t99J03_SurfaceRel orientable genus))

noncomputable instance (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (apm_t99J03_Surface orientable genus) :=
  TopologicalSpace.coinduced
    (fun x : apm_t99J03_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t99J03_eulerCharacteristic (orientable : Bool) (genus : ℕ) : ℤ :=
  if orientable then 2 - 2 * genus else 2 - genus

@[simp] lemma apm_t99J03_eulerCharacteristic_orientable (genus : ℕ) :
    apm_t99J03_eulerCharacteristic true genus = 2 - 2 * genus := rfl

@[simp] lemma apm_t99J03_eulerCharacteristic_nonorientable (genus : ℕ) :
    apm_t99J03_eulerCharacteristic false genus = 2 - genus := rfl

/-- Euler characteristic determines the genus inside the orientable family. -/
lemma apm_t99J03_orientable_genus_eq_of_eulerCharacteristic_eq
    {g h : ℕ}
    (heq : apm_t99J03_eulerCharacteristic true g =
      apm_t99J03_eulerCharacteristic true h) :
    g = h := by
  simp only [apm_t99J03_eulerCharacteristic_orientable] at heq
  omega

/-- Euler characteristic determines the crosscap number inside the
nonorientable family. -/
lemma apm_t99J03_nonorientable_genus_eq_of_eulerCharacteristic_eq
    {g h : ℕ}
    (heq : apm_t99J03_eulerCharacteristic false g =
      apm_t99J03_eulerCharacteristic false h) :
    g = h := by
  simp only [apm_t99J03_eulerCharacteristic_nonorientable] at heq
  omega

/-- Once existence and homeomorphism invariance of the encoded Euler
characteristic are supplied, uniqueness of the genus parameters is purely
arithmetic. -/
lemma apm_t99J03_unique_classification_of_exists_of_euler_invariant
    (X : Type) [TopologicalSpace X]
    (hex : (∃ g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g)) ∨
      (∃ k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k)))
    (hχo : ∀ g h : ℕ,
      Nonempty (X ≃ₜ apm_t99J03_Surface true g) →
      Nonempty (X ≃ₜ apm_t99J03_Surface true h) →
      apm_t99J03_eulerCharacteristic true g =
        apm_t99J03_eulerCharacteristic true h)
    (hχn : ∀ g h : ℕ,
      Nonempty (X ≃ₜ apm_t99J03_Surface false g) →
      Nonempty (X ≃ₜ apm_t99J03_Surface false h) →
      apm_t99J03_eulerCharacteristic false g =
        apm_t99J03_eulerCharacteristic false h) :
    (∃! g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g)) ∨
      (∃! k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k)) := by
  rcases hex with ⟨g, hg⟩ | ⟨k, hk, hXk⟩
  · left
    refine ⟨g, hg, ?_⟩
    intro h hh
    exact apm_t99J03_orientable_genus_eq_of_eulerCharacteristic_eq
      (hχo h g hh hg)
  · right
    refine ⟨k, ⟨hk, hXk⟩, ?_⟩
    intro h hh
    exact apm_t99J03_nonorientable_genus_eq_of_eulerCharacteristic_eq
      (hχn h k hh.2 hXk)

theorem apm_t99j03 :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ConnectedSpace X] [ChartedSpace apm_t99J03_E2 X]
      [IsManifold (𝓘(ℝ, apm_t99J03_E2)) ⊤ X],
      (∃! g : ℕ,
        Nonempty (X ≃ₜ apm_t99J03_Surface true g) ∧
        apm_t99J03_eulerCharacteristic true g = 2 - 2 * g) ∨
      (∃! k : ℕ,
        0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k) ∧
        apm_t99J03_eulerCharacteristic false k = 2 - k) := by
  intro X _ _ _ _ _ _
  have hclassification :
      (∃! g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g)) ∨
      (∃! k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k)) := by
    /-
    CLOSER HOP 2 boundary. The two Euler-characteristic equations are
    compiled definitional lemmas, and the final `simpa` below removes them
    from both existence and uniqueness predicates. Thus the remaining bridge
    is exactly the classification dichotomy with uniqueness of genus/crosscap
    number for the concrete polygon quotients.

    Going beyond hop 1, the two lemmas
    `apm_t99J03_orientable_genus_eq_of_eulerCharacteristic_eq` and
    `apm_t99J03_nonorientable_genus_eq_of_eulerCharacteristic_eq` prove that
    Euler characteristic is injective in the genus parameter within each
    normal-form family. Thus once homeomorphism invariance of the genuine
    Euler characteristic is connected to this encoding, the numerical part of
    uniqueness is complete; only the topological invariance and orientability
    dichotomy remain.

    A proof must triangulate an arbitrary compact connected smooth surface,
    cut it to a fundamental polygon, normalize the paired-edge word into
    handle or crosscap form, construct the resulting homeomorphism to
    `apm_t99J03_Surface`, and prove uniqueness (for example via orientability
    and integral/mod-two homology). Searches of `LEMMA-INDEX.md`, all
    `ConstructionTargets/`, classification and polygon-quotient siblings,
    Mathlib's surface, triangulation, CW-complex, manifold, homology, and
    quotient APIs, and git history found no packaged surface-classification
    theorem or polygon-normal-form development. `ConstructionTargets.Surfaces`
    provides another concrete quotient family and the same definitional Euler
    formulas, but no theorem classifying arbitrary manifolds into it.
    The frozen statement is unchanged.

    CLOSER HOP 3 (2026-08-08): uniqueness is now separated completely from
    polygon normalization and homology by
    `apm_t99J03_unique_classification_of_exists_of_euler_invariant`. Given
    only the existence dichotomy and homeomorphism invariance of the encoded
    Euler characteristic within each family, the hop-2 injectivity lemmas
    produce both `∃!` conclusions. Therefore integral/mod-two homology is not
    needed for within-branch genus uniqueness; it is needed only if used to
    establish orientability or Euler invariance. Searches of Mathlib's Euler
    characteristic APIs found definitions for finite complexes and categories
    but no invariant attached to these arbitrary manifolds or polygon
    quotients. The live bridge is now existence of a normal form, the
    orientable/nonorientable dichotomy, and homeomorphism invariance of a
    compatible Euler characteristic. The frozen statement is unchanged.
    -/
    sorry
  simpa using hclassification

import Mathlib

/-!
# APM t97J02

## Statement repairs

None.

## Encoding questions

Closed classified surfaces are concrete polygon quotients of the unit disk.
For nonorientable genus `g` the edge word is `a₁a₁⋯a_ga_g`; for orientable
genus `g` it is the standard product of `g` commutators. Thus the base `N₄`
and all three candidate covering surfaces are actual topological spaces.
Coverings use Mathlib's `IsCoveringMap` and exact fiber cardinality.
-/

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

/-- The standard polygon edge relation for a classified closed surface. -/
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

/-- The connected sum of four real projective planes, `N₄`. -/
abbrev apm_t97J02_X := apm_t97J02_Surface false 4

/-- An exact `n`-sheeted covering of `N₄`. -/
def apm_t97J02_IsNfoldCover
    {E : Type} [TopologicalSpace E] (n : ℕ) (p : E → apm_t97J02_X) : Prop :=
  IsCoveringMap p ∧
    ∀ x : apm_t97J02_X, Nat.card {e : E // p e = x} = n

/-- A covering carried by one of the concrete polygon surfaces. -/
structure apm_t97J02_CoverWitness (orientable : Bool) (genus n : ℕ) where
  p : apm_t97J02_Surface orientable genus → apm_t97J02_X
  covering : apm_t97J02_IsNfoldCover n p

theorem apm_t97j02 :
    Nonempty (apm_t97J02_CoverWitness false 12 5) ∧
    (∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 5 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface false 12)) ∧
    Nonempty (apm_t97J02_CoverWitness true 7 6) ∧
    Nonempty (apm_t97J02_CoverWitness false 14 6) ∧
    ∀ (E : Type) [TopologicalSpace E] [T2Space E] [CompactSpace E]
        [ConnectedSpace E] [ChartedSpace apm_t97J02_E2 E]
        [IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]
        (p : E → apm_t97J02_X),
      apm_t97J02_IsNfoldCover 6 p →
        Nonempty (E ≃ₜ apm_t97J02_Surface true 7) ∨
        Nonempty (E ≃ₜ apm_t97J02_Surface false 14) := by
  sorry

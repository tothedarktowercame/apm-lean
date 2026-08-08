import Mathlib

/-!
# Polygon presentations of classified closed surfaces

This module exposes the concrete quotient presentations used by `t97J02`,
together with their elementary Euler-characteristic classification data.
-/

open Set

noncomputable section

namespace ConstructionTargets.Surfaces

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev Disk := Metric.closedBall (0 : ℂ) 1

def edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) : Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

/-- The standard polygon edge relation for a classified closed surface. -/
def SurfaceRel (orientable : Bool) (genus : ℕ) (x y : Disk) : Prop :=
  if orientable then
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      let tr : Set.Icc (0 : ℝ) 1 :=
        ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
      (x = edgePoint (4 * genus) (4 * j) t ∧
          y = edgePoint (4 * genus) (4 * j + 2) tr) ∨
        (x = edgePoint (4 * genus) (4 * j + 1) t ∧
          y = edgePoint (4 * genus) (4 * j + 3) tr)
  else
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      x = edgePoint (2 * genus) (2 * j) t ∧
      y = edgePoint (2 * genus) (2 * j + 1) t

def Surface (orientable : Bool) (genus : ℕ) :=
  Quotient (Relation.EqvGen.setoid (SurfaceRel orientable genus))

noncomputable instance (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (Surface orientable genus) :=
  TopologicalSpace.coinduced
    (fun x : Disk ↦ Quotient.mk _ x) inferInstance

def surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Disk → Surface orientable genus :=
  fun x => Quotient.mk _ x

lemma continuous_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Continuous (surfaceQuotient orientable genus) := by
  exact continuous_coinduced_rng

lemma surjective_surfaceQuotient (orientable : Bool) (genus : ℕ) :
    Function.Surjective (surfaceQuotient orientable genus) := by
  exact Quotient.mk_surjective

/-- Euler characteristic of the classified surface data. -/
def eulerCharacteristic (orientable : Bool) (genus : ℕ) : ℤ :=
  if orientable then 2 - 2 * (genus : ℤ) else 2 - (genus : ℤ)

@[simp] lemma eulerCharacteristic_orientable (genus : ℕ) :
    eulerCharacteristic true genus = 2 - 2 * (genus : ℤ) := rfl

@[simp] lemma eulerCharacteristic_nonorientable (genus : ℕ) :
    eulerCharacteristic false genus = 2 - (genus : ℤ) := rfl

/-- The connected sum of four real projective planes, `N₄`. -/
abbrev X := Surface false 4

/-- An exact `n`-sheeted covering of `N₄`. -/
def IsNfoldCover {E : Type} [TopologicalSpace E] (n : ℕ) (p : E → X) : Prop :=
  IsCoveringMap p ∧ ∀ x : X, Nat.card {e : E // p e = x} = n

/-- Classification data for a connected sum. Orientable genera add. If one
summand is nonorientable, every orientable handle contributes two crosscaps;
if both are nonorientable, their crosscap counts add. -/
def connectedSum (o1 : Bool) (g1 : ℕ) (o2 : Bool) (g2 : ℕ) : Bool × ℕ :=
  if o1 then
    if o2 then (true, g1 + g2) else (false, 2 * g1 + g2)
  else
    if o2 then (false, g1 + 2 * g2) else (false, g1 + g2)

/-- Euler characteristic is additive under connected sum, minus two. -/
lemma eulerCharacteristic_connectedSum
    (o1 : Bool) (g1 : ℕ) (o2 : Bool) (g2 : ℕ) :
    eulerCharacteristic (connectedSum o1 g1 o2 g2).1
        (connectedSum o1 g1 o2 g2).2 =
      eulerCharacteristic o1 g1 + eulerCharacteristic o2 g2 - 2 := by
  cases o1 <;> cases o2 <;> simp [connectedSum, eulerCharacteristic] <;> omega

end ConstructionTargets.Surfaces

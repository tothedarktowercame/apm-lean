import Mathlib
import ConstructionTargets.ManifoldFormTargets

/-! Intersection numbers from actual manifold derivatives. Nontransverse maps
are handled by a smooth homotopic transverse representative, not by imposing
transversality on the source problem. Realization and homotopy-invariance of
this relation are construction theorems still to prove. -/
open scoped Manifold ContDiff
noncomputable section
namespace ConstructionTargets.ManifoldIntersectionTargets
open ManifoldFormTargets
abbrev E (n : ℕ) := Fin n → ℝ
variable {a b : ℕ} {A B X : Type*}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
  [ChartedSpace (E a) A] [ChartedSpace (E b) B] [ChartedSpace (E (a+b)) X]

def Coincidence (f : A → X) (g : B → X) := {p : A × B // f p.1 = g p.2}

def Transverse (f : A → X) (g : B → X) : Prop :=
  ∀ p : Coincidence f g,
    LinearMap.range (mfderiv 𝓘(ℝ,E a) 𝓘(ℝ,E (a+b)) f p.val.1).toLinearMap ⊔
    LinearMap.range (mfderiv 𝓘(ℝ,E b) 𝓘(ℝ,E (a+b)) g p.val.2).toLinearMap = ⊤

/-- Concatenate the images of the standard bases, in left-then-right order. -/
def tangentFrame (f : A → X) (g : B → X) (p : Coincidence f g) :
    Fin (a+b) → E (a+b) :=
  Fin.append
    (fun i => mfderiv 𝓘(ℝ,E a) 𝓘(ℝ,E (a+b)) f p.val.1 (Pi.single i 1))
    (fun j => mfderiv 𝓘(ℝ,E b) 𝓘(ℝ,E (a+b)) g p.val.2 (Pi.single j 1))

/-- Dividing by the source volume evaluations corrects for both source
orientations; the numerator uses the ambient orientation at the intersection. -/
def localSign (volA : Form (E a) A a) (volB : Form (E b) B b)
    (volX : Form (E (a+b)) X (a+b)) (f : A → X) (g : B → X)
    (p : Coincidence f g) : ℤ :=
  let r := volX (f p.val.1) (tangentFrame f g p) /
    (volA p.val.1 (fun i => Pi.single i 1) * volB p.val.2 (fun j => Pi.single j 1))
  if 0 < r then 1 else if r < 0 then -1 else 0

/-- A finite signed count on a transverse representative of the right map.
The exact enumeration prevents dropped or duplicated intersections. -/
def HasIntersectionNumber (volA : Form (E a) A a) (volB : Form (E b) B b)
    (volX : Form (E (a+b)) X (a+b)) (f : ContinuousMap A X)
    (g : ContinuousMap B X) (value : ℤ) : Prop :=
  ∃ g' : ContinuousMap B X,
    ContMDiff 𝓘(ℝ,E b) 𝓘(ℝ,E (a+b)) ∞ g' ∧
    ContinuousMap.Homotopic g g' ∧ Transverse (a := a) (b := b) f g' ∧
    ∃ r : ℕ, ∃ enumerate : Fin r ≃ Coincidence f g',
      (∑ i : Fin r, localSign volA volB volX f g' (enumerate i)) = value

end ConstructionTargets.ManifoldIntersectionTargets

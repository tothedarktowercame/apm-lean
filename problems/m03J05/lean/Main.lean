import Mathlib

/-! # APM m03J05: linear and semilinear mixed boundary-value problems

## Statement repairs

The source writes `x \in R` in the antiderivative hypothesis; this is read as
the evident `x \in ℝ`.

## Encoding note

Mathlib does not currently bundle the Sobolev space `H¹(0,1)`.  In one
dimension it is canonically represented by a pair consisting of the value at
zero and an `L²(0,1)` weak derivative; `m03J05H1Value` reconstructs its absolutely
continuous representative.  Thus the central Sobolev object is retained rather
than replaced by a scalar surrogate.
-/

open MeasureTheory Set

noncomputable section

def m03J05UnitMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

abbrev m03J05H1 := ℝ × Lp ℝ 2 m03J05UnitMeasure

def m03J05H1Value (u : m03J05H1) (x : ℝ) : ℝ :=
  u.1 + ∫ t in (0 : ℝ)..x, u.2 t

def m03J05MixedEigenvalue (n : ℕ) : ℝ :=
  (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) ^ 2

def m03J05MixedEigenfunction (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)

def m03J05LinearWeakSolution
    (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure) (u : m03J05H1) : Prop :=
  u.1 = 0 ∧ ∀ v : m03J05H1, v.1 = 0 →
    (∫ x in (0 : ℝ)..1, u.2 x * v.2 x) +
      c * ∫ x in (0 : ℝ)..1, m03J05H1Value u x * m03J05H1Value v x =
        ∫ x in (0 : ℝ)..1, F x * m03J05H1Value v x

def m03J05Energy
    (F : Lp ℝ 2 m03J05UnitMeasure) (g : ℝ → ℝ) (u : m03J05H1) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, (u.2 x) ^ 2 +
    ∫ x in (0 : ℝ)..1, g (m03J05H1Value u x) -
      ∫ x in (0 : ℝ)..1, F x * m03J05H1Value u x

def m03J05NonlinearWeakSolution
    (F : Lp ℝ 2 m03J05UnitMeasure) (G : ℝ → ℝ) (u : m03J05H1) : Prop :=
  u.1 = 0 ∧ ∀ v : m03J05H1, v.1 = 0 →
    (∫ x in (0 : ℝ)..1, u.2 x * v.2 x) +
      ∫ x in (0 : ℝ)..1, G (m03J05H1Value u x) * m03J05H1Value v x =
        ∫ x in (0 : ℝ)..1, F x * m03J05H1Value v x

theorem apm_m03j05 (c : ℝ) (F : Lp ℝ 2 m03J05UnitMeasure) :
    ((¬ ∃ n : ℕ, c = -m03J05MixedEigenvalue n) →
      ∃! u : m03J05H1, m03J05LinearWeakSolution c F u) ∧
    (∀ n : ℕ, c = -m03J05MixedEigenvalue n →
      ((∃ u : m03J05H1, m03J05LinearWeakSolution c F u) ↔
        ∫ x in (0 : ℝ)..1, F x * m03J05MixedEigenfunction n x = 0) ∧
      ∀ u : m03J05H1, m03J05LinearWeakSolution c F u →
        ∀ v : m03J05H1,
          m03J05LinearWeakSolution c F v ↔
            ∃ a : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
              m03J05H1Value v x =
                m03J05H1Value u x + a * m03J05MixedEigenfunction n x) ∧
    (∀ (G g : ℝ → ℝ) (L : NNReal), LipschitzWith L G → Monotone G →
      (∀ x : ℝ, HasDerivAt g (G x) x) → g 0 = 0 →
        Differentiable ℝ (m03J05Energy F g)) ∧
    (∀ (G : ℝ → ℝ) (L : NNReal), LipschitzWith L G → Monotone G →
      ∃! u : m03J05H1, m03J05NonlinearWeakSolution F G u) := by
  sorry

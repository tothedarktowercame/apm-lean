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

/-- The explicit mixed eigenfunctions satisfy the Dirichlet condition at the
left endpoint. -/
lemma m03J05MixedEigenfunction_zero (n : ℕ) :
    m03J05MixedEigenfunction n 0 = 0 := by
  simp [m03J05MixedEigenfunction]

/-- The frequency in the explicit mixed spectrum is strictly positive. -/
lemma m03J05MixedFrequency_pos (n : ℕ) :
    0 < ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 := by
  positivity

/-- Consequently every displayed mixed eigenvalue is strictly positive. -/
lemma m03J05MixedEigenvalue_pos (n : ℕ) :
    0 < m03J05MixedEigenvalue n := by
  unfold m03J05MixedEigenvalue
  positivity

/-- The first derivative of each displayed mixed eigenfunction. -/
lemma m03J05MixedEigenfunction_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (m03J05MixedEigenfunction n)
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)) x := by
  unfold m03J05MixedEigenfunction
  convert (((hasDerivAt_id x).const_mul
    (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)).sin) using 1 <;>
      simp only [id_eq] <;> ring

/-- The explicit eigenfunctions satisfy the right Neumann boundary condition. -/
lemma m03J05MixedEigenfunction_deriv_one (n : ℕ) :
    deriv (m03J05MixedEigenfunction n) 1 = 0 := by
  rw [(m03J05MixedEigenfunction_hasDerivAt n 1).deriv]
  suffices Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)) = 0 by
    simpa using congrArg
      (fun z : ℝ => (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * z) this
  rw [Real.cos_eq_zero_iff]
  refine ⟨(n : ℤ), ?_⟩
  push_cast
  ring

/-- The displayed functions solve the expected constant-coefficient
eigenvalue equation pointwise. -/
lemma m03J05MixedEigenfunction_neg_deriv_deriv (n : ℕ) (x : ℝ) :
    -deriv (deriv (m03J05MixedEigenfunction n)) x =
      m03J05MixedEigenvalue n * m03J05MixedEigenfunction n x := by
  have hfirst : deriv (m03J05MixedEigenfunction n) = fun y : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * y) := by
    funext y
    exact (m03J05MixedEigenfunction_hasDerivAt n y).deriv
  rw [hfirst]
  have hsecond := (((hasDerivAt_id x).const_mul
    (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)).cos).const_mul
      (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)
  have hsecond' : deriv (fun y : ℝ =>
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * y)) x =
      ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 *
        (-Real.sin ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x) *
          (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)) := by
    simpa only [id_eq, mul_one] using hsecond.deriv
  rw [hsecond']
  simp only [m03J05MixedEigenvalue, m03J05MixedEigenfunction]
  ring

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
  /-
  SKIPPED (mixed Sturm–Liouville/Sobolev operator boundary). Searches found
  Mathlib's abstract Fredholm alternative for compact operators, but no
  compiled construction identifying the compact mixed-boundary resolvent on
  this `ℝ × Lp` realization, no classification of its spectrum as
  `m03J05MixedEigenvalue`, and no Fourier-sine completeness theorem from which
  the solvability and one-dimensional-kernel assertions follow.

  Closer hop 1 verifies the elementary spectral endpoint data:
  `m03J05MixedEigenfunction_zero`, `m03J05MixedFrequency_pos`, and
  `m03J05MixedEigenvalue_pos` prove the left Dirichlet condition and positivity
  of every displayed frequency/eigenvalue. A renewed search of Mathlib's
  Fredholm, compact-operator, Fourier, and interval-integral APIs found no
  theorem identifying the spectrum of the required mixed-boundary resolvent;
  `LEMMA-INDEX.md` and `ConstructionTargets/` likewise contain no mixed
  Fourier-sine completeness result.

  The nonlinear clauses additionally require proving that
  `u ↦ m03J05H1Value u` is a bounded Sobolev embedding, differentiating the
  integral Nemytskii functional from `LipschitzWith L G`, and applying a
  coercive/strictly monotone existence theorem on the zero-trace subspace.
  Related artifacts `m96A06`, `m95A03`, and `m01J06` were inspected; each
  retains an unresolved Sturm–Liouville or variational bridge. `m94A04` and
  `m98A03` also stop at Nemytskii differentiability/packaging boundaries.
  Thus no compiled sibling closes either remaining operator-theoretic chain.

  Closer hop 2 goes beyond the endpoint-positivity checks by compiling the
  local differential operator calculation. `m03J05MixedEigenfunction_hasDerivAt`
  gives the exact first derivative,
  `m03J05MixedEigenfunction_deriv_one` proves the right Neumann condition,
  and `m03J05MixedEigenfunction_neg_deriv_deriv` proves pointwise that
  `-u'' = λₙu`. Mathlib's `Real.cos_eq_zero_iff` supplies the only
  non-algebraic endpoint step. Searches additionally covered the derivative,
  trigonometric periodicity, orthogonal-family, eigenvector, compact-resolvent,
  and variational APIs. They provide these local identities but no theorem
  upgrading them to completeness of the half-integer sine family in `L²`, nor
  an isomorphism between the custom pair encoding and a standard Sobolev
  space. Consequently the Fredholm and nonlinear operator bridges remain
  open; the frozen statement is unchanged.
  -/
  sorry

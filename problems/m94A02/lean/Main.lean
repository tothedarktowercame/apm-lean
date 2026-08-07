import Mathlib

/-!
# APM m94A02

## Statement repairs

None.

## Encoding notes

The dimension is written as `n + 1` so that the largest and smallest entries
of the ordered spectrum have canonical indices `0` and `Fin.last n`.  Complex
eigenvalues of the real matrix are defined using its scalar extension to `ℂ`.
-/

open Matrix Polynomial
open scoped BigOperators

noncomputable def apm_m94a02_symmetricPart {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (A + A.transpose)

/-- A skew-symmetric matrix has zero symmetric part. -/
lemma apm_m94a02_symmetricPart_eq_zero_of_transpose_eq_neg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) :
    apm_m94a02_symmetricPart A = 0 := by
  simp [apm_m94a02_symmetricPart, hA]

def apm_m94a02_IsEigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧
    Matrix.mulVec (A.map (algebraMap ℝ ℂ)) v = lam • v

def apm_m94a02_IsOrderedSpectrum {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i ≤ j → σ j ≤ σ i) ∧
  Matrix.charpoly B = ∏ i : Fin n, (Polynomial.X - Polynomial.C (σ i))

theorem apm_m94a02
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (σ : Fin (n + 1) → ℝ)
    (hσ : apm_m94a02_IsOrderedSpectrum (apm_m94a02_symmetricPart A) σ) :
    (∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam →
      σ (Fin.last n) ≤ lam.re ∧ lam.re ≤ σ 0) ∧
    (A.transpose = -A →
      ∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam → lam.re = 0) := by
  /-
  Boundary: the intended proof tests the complex eigenvalue equation against
  its eigenvector, rewrites `lam.re` as the Hermitian Rayleigh quotient of
  `(A + Aᵀ) / 2`, and bounds that quotient by the extreme eigenvalues.

  I found Mathlib's Hermitian spectrum and Rayleigh infrastructure in
  `Mathlib.Analysis.Matrix.Spectrum` and
  `Mathlib.Analysis.InnerProductSpace.Rayleigh`, including canonical ordered
  eigenvalues and quadratic-form formulas. The statement, however, supplies
  an arbitrary ordered family `σ` characterized only by
  `Matrix.charpoly B = ∏ i, (X - C (σ i))`. I did not complete the
  polynomial-root multiplicity argument identifying this family with
  Mathlib's canonical Hermitian eigenvalue ordering, nor the conversion of
  the explicit `Matrix.mulVec` complex eigenvector equation to the library's
  continuous-linear-map Rayleigh quotient. The skew-symmetric conclusion can
  then follow either from the same calculation or by showing the symmetric
  part is zero, but depends on those bridges in this encoding.

  Closer hop 1 proves
  `apm_m94a02_symmetricPart_eq_zero_of_transpose_eq_neg`, closing the
  matrix-algebra reduction for the skew-symmetric case. A deeper source pass
  finds the exact canonical-spectrum comparison API in
  `Analysis/Matrix/Spectrum.lean`:
  `Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀` reconstructs the
  ordered eigenvalue list from the real parts of the characteristic roots,
  while `roots_charpoly_eq_eigenvalues` and `charpoly_eq` preserve
  multiplicity. These results provide a route to identify the arbitrary
  antitone `σ`, but applying them still requires proving the symmetric part is
  Hermitian and normalizing the supplied real-factor product into Mathlib's
  complex-root multiset.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling matrix
  artifacts, and git history found no already-compiled normalization bridge.
  The remaining second step is still the dot-product/Rayleigh identity for the
  explicitly encoded `mulVec` eigenvector. The frozen statement was unchanged.
  -/
  sorry

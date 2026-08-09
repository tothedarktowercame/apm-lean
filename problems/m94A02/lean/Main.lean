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

/-- The explicitly defined symmetric part is fixed by transpose. -/
lemma apm_m94a02_symmetricPart_transpose {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (apm_m94a02_symmetricPart A).transpose =
      apm_m94a02_symmetricPart A := by
  simp [apm_m94a02_symmetricPart, add_comm]

/-- Over the reals, transpose symmetry is precisely Hermitian symmetry. -/
lemma apm_m94a02_symmetricPart_isHermitian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (apm_m94a02_symmetricPart A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    apm_m94a02_symmetricPart_transpose]

/-- Scalar extension of the symmetric part to `ℂ` remains Hermitian, which is
the exact input expected by Mathlib's canonical spectrum API. -/
lemma apm_m94a02_symmetricPart_map_isHermitian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ((apm_m94a02_symmetricPart A).map (algebraMap ℝ ℂ)).IsHermitian := by
  apply (apm_m94a02_symmetricPart_isHermitian A).map
  intro x
  simp

/-- A real skew-symmetric matrix becomes skew-Hermitian after scalar
extension to `ℂ`. -/
lemma apm_m94a02_map_conjTranspose_eq_neg_of_transpose_eq_neg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) :
    (A.map (algebraMap ℝ ℂ))ᴴ = -(A.map (algebraMap ℝ ℂ)) := by
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j) hA
  simpa [Matrix.conjTranspose_apply] using congrArg (algebraMap ℝ ℂ) hij

/-- Multiplication by `I` converts the skew-Hermitian scalar extension into a
Hermitian matrix, allowing use of Mathlib's self-adjoint spectrum API. -/
lemma apm_m94a02_I_smul_map_isHermitian_of_transpose_eq_neg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) :
    (Complex.I • A.map (algebraMap ℝ ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j) hA
  have hijc : ((A j i : ℝ) : ℂ) = -((A i j : ℝ) : ℂ) := by
    simpa using congrArg (algebraMap ℝ ℂ) hij
  simp only [Matrix.conjTranspose_apply]
  simp [hijc]

def apm_m94a02_IsEigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧
    Matrix.mulVec (A.map (algebraMap ℝ ℂ)) v = lam • v

def apm_m94a02_IsOrderedSpectrum {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i ≤ j → σ j ≤ σ i) ∧
  Matrix.charpoly B = ∏ i : Fin n, (Polynomial.X - Polynomial.C (σ i))

/-- Eigenvalues of the complex scalar extension of a real skew-symmetric
matrix lie on the imaginary axis. Multiplication by `I` converts the matrix
to a Hermitian one, and the self-adjoint eigenvalue-reality theorem then
applies to the eigenvalue `I * lam`. -/
lemma apm_m94a02_eigenvalue_re_eq_zero_of_transpose_eq_neg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.transpose = -A) {lam : ℂ}
    (hlam : apm_m94a02_IsEigenvalue A lam) :
    lam.re = 0 := by
  rcases hlam with ⟨v, hv, heig⟩
  let M : Matrix (Fin n) (Fin n) ℂ := A.map (algebraMap ℝ ℂ)
  let B : Matrix (Fin n) (Fin n) ℂ := Complex.I • M
  have hB : B.IsHermitian := by
    simpa [B, M] using
      apm_m94a02_I_smul_map_isHermitian_of_transpose_eq_neg hA
  have heigB : B *ᵥ v = (Complex.I * lam) • v := by
    simp only [B, Matrix.smul_mulVec]
    rw [show M *ᵥ v = lam • v from heig]
    simp [smul_smul]
  have hvLp : WithLp.toLp 2 v ≠ (0 : EuclideanSpace ℂ (Fin n)) := by
    intro h
    apply hv
    have h' := congrArg WithLp.ofLp h
    simpa using h'
  have hvec : Module.End.HasEigenvector B.toEuclideanLin
      (Complex.I * lam) (WithLp.toLp 2 v) := by
    refine ⟨?_, hvLp⟩
    simpa [Matrix.toEuclideanLin_apply_piLp_toLp, heigB]
  have hreal :=
    (Matrix.isHermitian_iff_isSymmetric.mp hB).conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector hvec)
  have him := congrArg Complex.im hreal
  simp [map_mul, Complex.conj_I, Complex.mul_im] at him
  linarith

theorem apm_m94a02
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (σ : Fin (n + 1) → ℝ)
    (hσ : apm_m94a02_IsOrderedSpectrum (apm_m94a02_symmetricPart A) σ) :
    (∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam →
      σ (Fin.last n) ≤ lam.re ∧ lam.re ≤ σ 0) ∧
    (A.transpose = -A →
      ∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam → lam.re = 0) := by
  constructor
  ·
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

  CLOSER HOP 2 (partial). The Hermitian prerequisite is now fully compiled.
  `apm_m94a02_symmetricPart_transpose` proves the explicit average is fixed by
  transpose; `apm_m94a02_symmetricPart_isHermitian` transports this through
  the trivial real star operation; and
  `apm_m94a02_symmetricPart_map_isHermitian` proves that its scalar extension
  along `algebraMap ℝ ℂ` is Hermitian. The last lemma uses
  `Matrix.IsHermitian.map` and is exactly the input required by the canonical
  spectrum API identified in hop 1.

  A further inspection of `Analysis/Matrix/Hermitian.lean`,
  `Analysis/Matrix/Spectrum.lean`, `LinearAlgebra/Matrix/PosDef.lean`, and the
  dot-product/mulVec lemmas confirms that the quadratic-form representation is
  available once the explicit eigenvector equation is tested against
  `star v`. No theorem directly normalizes the frozen real-factor product to
  the complex root multiset or identifies an arbitrary antitone enumeration
  with `IsHermitian.eigenvalues`. Those polynomial-multiplicity and Rayleigh
  assembly steps remain open. The frozen statement is unchanged.

  Closer hop 3 routes around the ordered-spectrum obstruction for the second
  conjunct by compiling
  `apm_m94a02_map_conjTranspose_eq_neg_of_transpose_eq_neg`: complex scalar
  extension carries real skew-symmetry to skew-Hermitian symmetry. It also
  proves `apm_m94a02_I_smul_map_isHermitian_of_transpose_eq_neg`, packaging
  the corresponding self-adjoint matrix. A renewed
  search of the skew-adjoint, eigenspace, and inner-product spectrum APIs found
  the self-adjoint eigenvalue reality theorem, but no packaged corresponding
  imaginary-axis theorem for skew-adjoint eigenvalues. The remaining local
  step is to apply that theorem to `I • A` (or test the eigenvector equation
  against `star v`); the first conjunct still needs the arbitrary-`σ`
  multiplicity normalization. No unproved assertion was introduced.
  -/
    sorry
  · intro hA lam hlam
    exact apm_m94a02_eigenvalue_re_eq_zero_of_transpose_eq_neg hA hlam

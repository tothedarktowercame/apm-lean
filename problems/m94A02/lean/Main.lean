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

/-! ## Student attempt 1 (f25-student) — closing the first conjunct

Method (from memory `e-0b15c2c9` and `e-53fe93b7`):
1. Rayleigh identity: testing the eigenvector equation against the
   eigenvector gives `Re lam · ‖v‖²` as the Hermitian quadratic form of
   the scalar-extended symmetric part `Bc`.
2. Expand that quadratic form in the unitary eigenbasis of `Bc` as a
   convex combination of `eigenvalues₀`, then bound by the endpoints.
3. Normalize the arbitrary antitone family `σ` against `eigenvalues₀` by
   sortedness (`mergeSort`), never by pointwise algebra. -/

private lemma apm_m94a02_star_dot_conj {m : Type*} [Fintype m]
    (M : Matrix m m ℂ) (v : m → ℂ) :
    star v ⬝ᵥ (Mᴴ *ᵥ v) = star (star v ⬝ᵥ (M *ᵥ v)) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
    star_sum, StarMul.star_mul, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => by ring

private lemma apm_m94a02_unitary_quadratic {m : Type*} [Fintype m] [DecidableEq m]
    {U : Matrix m m ℂ} (hU : Uᴴ * U = 1) (w z : m → ℂ) :
    star (U *ᵥ w) ⬝ᵥ (U *ᵥ z) = star w ⬝ᵥ z := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
    Matrix.vecMul_one]

theorem apm_m94a02
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (σ : Fin (n + 1) → ℝ)
    (hσ : apm_m94a02_IsOrderedSpectrum (apm_m94a02_symmetricPart A) σ) :
    (∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam →
      σ (Fin.last n) ≤ lam.re ∧ lam.re ≤ σ 0) ∧
    (A.transpose = -A →
      ∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam → lam.re = 0) := by
  constructor
  · intro lam hlam
    obtain ⟨v, hv, heig⟩ := hlam
    set M := A.map (algebraMap ℝ ℂ) with hMdef
    set Bc := (apm_m94a02_symmetricPart A).map (algebraMap ℝ ℂ) with hBcdef
    have hB : Bc.IsHermitian := apm_m94a02_symmetricPart_map_isHermitian A
    have hBceq : Bc = (2 : ℂ)⁻¹ • (M + Mᴴ) := by
      ext i j
      simp only [hBcdef, hMdef, apm_m94a02_symmetricPart, Matrix.map_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
        star_apply]
      simp [Complex.conj_ofReal, Complex.ofReal_inv, Complex.ofReal_add,
        Complex.ofReal_mul]
    have hS : star v ⬝ᵥ (M *ᵥ v) = lam * (star v ⬝ᵥ v) := by
      rw [heig, dotProduct_smul, smul_eq_mul]
    have hq : (2 : ℂ) * (star v ⬝ᵥ (Bc *ᵥ v)) =
        lam * (star v ⬝ᵥ v) + star (lam * (star v ⬝ᵥ v)) := by
      rw [hBceq, Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec,
        dotProduct_add, apm_m94a02_star_dot_conj, hS, smul_eq_mul]
      field_simp
    have hc : star v ⬝ᵥ v = ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) := by
      simp [dotProduct, Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul]
    have hSv : 0 < ∑ i, Complex.normSq (v i) := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hcon; push_neg at hcon; exact hv (funext hcon)
      exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
        ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
    have hcre : (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
      rw [hc]; simp
    have hqre : (star v ⬝ᵥ (Bc *ᵥ v)).re = lam.re * (∑ i, Complex.normSq (v i)) := by
      have hvi : (star v ⬝ᵥ v).im = 0 := by
        rw [hc]; simp
      have hmulre : (lam * (star v ⬝ᵥ v)).re = lam.re * (star v ⬝ᵥ v).re := by
        rw [Complex.mul_re, hvi, mul_zero, sub_zero]
      have hsr : ∀ z : ℂ, (star z).re = z.re := by
        intro z; rw [← starRingEnd_apply]; exact Complex.conj_re z
      have h1 := congrArg Complex.re hq
      rw [Complex.mul_re, Complex.add_re, hsr, hmulre, hcre] at h1
      norm_num at h1
      linarith
    set U := (hB.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hUdef
    have hUstar : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
    set w := Uᴴ *ᵥ v with hwdef
    have hvw : U *ᵥ w = v := by
      rw [hwdef, Matrix.mulVec_mulVec]
      have h3 : U * Uᴴ = 1 := (Matrix.mul_eq_one_comm).mp hUstar
      rw [h3, Matrix.one_mulVec]
    set D := Matrix.diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) with hDdef
    have hspec : Bc = U * D * Uᴴ := by
      simpa [hUdef, hDdef] using hB.spectral_theorem
    have hBvec : Bc *ᵥ v = U *ᵥ (D *ᵥ w) := by
      rw [hspec, hwdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hexp : star v ⬝ᵥ (Bc *ᵥ v) =
        ∑ i, ((hB.eigenvalues i : ℝ) : ℂ) * ((Complex.normSq (w i) : ℝ) : ℂ) := by
      rw [hBvec, ← hvw, apm_m94a02_unitary_quadratic hUstar w (D *ᵥ w), hDdef]
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Finset.sum_ite_eq',
        Matrix.mulVec_diagonal, Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hwnorm : ∑ i, Complex.normSq (w i) = ∑ i, Complex.normSq (v i) := by
      have hww : star w ⬝ᵥ w = star v ⬝ᵥ v := by
        rw [← hvw, apm_m94a02_unitary_quadratic hUstar w w]
      have h2 : star w ⬝ᵥ w = ∑ i, ((Complex.normSq (w i) : ℝ) : ℂ) := by
        simp [dotProduct, Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul]
      rw [h2, hc] at hww
      have h1 := congrArg Complex.re hww
      simpa [Complex.re_sum] using h1
    have hanti : Antitone σ := fun a b hab => hσ.1 a b hab
    have hcp : Bc.charpoly.roots =
        Multiset.map (RCLike.ofReal ∘ σ) Finset.univ.val := by
      have hmap : Bc.charpoly =
          ∏ i : Fin (n + 1), (Polynomial.X - Polynomial.C (((σ i : ℝ) : ℂ))) := by
        rw [hBcdef, Matrix.charpoly_map, hσ.2, Polynomial.map_prod]
        simp [Polynomial.map_X, Polynomial.map_C]
      rw [hmap]
      have hne : (∏ i : Fin (n + 1),
          (Polynomial.X - Polynomial.C (((σ i : ℝ) : ℂ)))) ≠ 0 := by
        simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
      rw [Polynomial.roots_prod _ _ hne]
      simp [Function.comp_def]
    have hsort : (Bc.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn σ := by
      simp_rw [hcp, ← Multiset.map_map, Fin.univ_val_map, Multiset.map_coe,
        List.map_ofFn, Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
      apply List.mergeSort_of_pairwise
      simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
      exact hanti.sortedGE_ofFn
    have hnorm : List.ofFn hB.eigenvalues₀ = List.ofFn σ :=
      (hB.sort_roots_charpoly_eq_eigenvalues₀).symm.trans hsort
    have hcard : Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin _
    have hmem : ∀ i : Fin (n + 1), ∃ j : Fin (n + 1),
        hB.eigenvalues i = σ j := by
      intro i
      have hi : hB.eigenvalues i = hB.eigenvalues₀
          ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := rfl
      set c : Fin (Fintype.card (Fin (n + 1))) :=
        (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i with hcdef
      have h9' : c.val < n + 1 := by omega
      refine ⟨Fin.cast hcard c, ?_⟩
      rw [hi]
      have h2 : (List.ofFn hB.eigenvalues₀)[c.val] = (List.ofFn σ)[c.val] := by
        simp only [hnorm]
      have ha : hB.eigenvalues₀ c = (List.ofFn hB.eigenvalues₀)[c.val] := by
        have hlen : (List.ofFn hB.eigenvalues₀).length =
            Fintype.card (Fin (n + 1)) := List.length_ofFn
        rw [List.getElem_ofFn (by rw [hlen]; exact c.isLt)]
      have hb : σ (Fin.cast hcard c) = (List.ofFn σ)[c.val] := by
        have hlen : (List.ofFn σ).length = n + 1 := List.length_ofFn
        have hlt : c.val < n + 1 :=
          Nat.lt_of_lt_of_le c.isLt (Nat.le_of_eq hcard)
        rw [List.getElem_ofFn (by rw [hlen]; exact hlt)]
        simp [Fin.cast, hcard]
      rw [ha, hb]
      exact h2
    have hmax : ∀ i, hB.eigenvalues i ≤ σ 0 := fun i => by
      obtain ⟨j, hj⟩ := hmem i
      rw [hj]; exact hσ.1 0 j (Fin.zero_le j)
    have hmin : ∀ i, σ (Fin.last n) ≤ hB.eigenvalues i := fun i => by
      obtain ⟨j, hj⟩ := hmem i
      rw [hj]; exact hσ.1 j (Fin.last n) (Fin.le_last j)
    have hqexp : (star v ⬝ᵥ (Bc *ᵥ v)).re =
        ∑ i, hB.eigenvalues i * Complex.normSq (w i) := by
      rw [hexp]
      simp only [Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.ofReal_im, mul_zero, sub_zero]
    constructor
    · have hsum : ∑ i, σ (Fin.last n) * Complex.normSq (w i) ≤
          ∑ i, hB.eigenvalues i * Complex.normSq (w i) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hmin i) (Complex.normSq_nonneg _)
      rw [← Finset.mul_sum, ← hqexp, hqre, hwnorm] at hsum
      exact (mul_le_mul_iff_of_pos_right hSv).mp hsum
    · have hsum : ∑ i, hB.eigenvalues i * Complex.normSq (w i) ≤
          ∑ i, σ 0 * Complex.normSq (w i) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hmax i) (Complex.normSq_nonneg _)
      rw [← Finset.mul_sum, ← hqexp, hqre, hwnorm] at hsum
      exact (mul_le_mul_iff_of_pos_right hSv).mp hsum
  · intro hA lam hlam
    exact apm_m94a02_eigenvalue_re_eq_zero_of_transpose_eq_neg hA hlam

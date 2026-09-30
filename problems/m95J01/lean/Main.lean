import Mathlib

/-!
# APM m95J01: decaying polynomials and the second derivative

## Statement repairs

None.

## Encoding questions

The function space is represented by an abstract inner-product space together
with an exact linear equivalence to polynomials of degree at most `n` and an
exact realization map `f(x)=e⁻ˣP(x)`. The integral identity pins its inner
product to the one printed in the problem, so this is not a coefficient-space
surrogate with the wrong geometry.
-/

noncomputable section

open MeasureTheory Set


/-- The polynomial model fixes the dimension before any integral or
Gram--Schmidt calculation is needed. -/
lemma apm_m95J01_finrank_of_equiv
    {n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) :
    Module.finrank ℝ H = n + 1 := by
  rw [← Polynomial.degreeLT_succ_eq_degreeLE] at P
  rw [LinearEquiv.finrank_eq P,
    LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1))]
  simp

/-- Completeness transports from the finite-dimensional polynomial model.
This closes the first frozen conjunct independently of the operator and
Gram--Schmidt constructions. -/
lemma apm_m95J01_complete_of_equiv
    {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) : Nonempty (CompleteSpace H) := by
  letI : FiniteDimensional ℝ (Polynomial.degreeLE ℝ n) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  letI : FiniteDimensional ℝ H := P.symm.finiteDimensional
  exact ⟨FiniteDimensional.complete ℝ H⟩

lemma apm_m95J01_monomial_linearIndependent
    {n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n)
    (monomial : Fin (n + 1) → H)
    (hmonomial : ∀ k : Fin (n + 1),
      (P (monomial k) : Polynomial ℝ) = Polynomial.X ^ (k : ℕ)) :
    LinearIndependent ℝ monomial := by
  apply LinearIndependent.of_comp P.toLinearMap
  apply LinearIndependent.of_comp (Polynomial.degreeLE ℝ n).subtype
  have hli := (Polynomial.basisMonomials ℝ).linearIndependent.comp
    (fun k : Fin (n + 1) ↦ (k : ℕ)) Fin.val_injective
  simp only [Polynomial.coe_basisMonomials,
    Polynomial.monomial_one_right_eq_X_pow] at hli
  convert hli using 1
  funext k
  exact hmonomial k

/-- The differential part `P'' - 2P'` strictly lowers degree, hence has zero
coefficient in the top slot of `degreeLE n`. -/
lemma apm_m95J01_top_coeff_derivative_sub
    {n : ℕ} (p : Polynomial.degreeLE ℝ n) :
    (Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
      2 • Polynomial.derivative (p : Polynomial ℝ)).coeff n = 0 := by
  have hpdeg : (p : Polynomial ℝ).degree ≤ (n : WithBot ℕ) :=
    Polynomial.mem_degreeLE.mp p.property
  have hcoeff1 : (p : Polynomial ℝ).coeff (n + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (hpdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self n))
  have hcoeff2 : (p : Polynomial ℝ).coeff (n + 2) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (hpdeg.trans_lt (by exact_mod_cast (by omega : n < n + 2)))
  simp [Polynomial.coeff_derivative, hcoeff1, hcoeff2]

/-- Coefficient recurrence for the strictly degree-lowering operator
`P ↦ P'' - 2P'`. -/
lemma apm_m95J01_coeff_derivative_sub (p : Polynomial ℝ) (k : ℕ) :
    (Polynomial.derivative (Polynomial.derivative p) -
      2 • Polynomial.derivative p).coeff k =
      ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * p.coeff (k + 2) -
        2 * ((k + 1 : ℕ) : ℝ) * p.coeff (k + 1) := by
  simp [Polynomial.coeff_derivative]
  ring

lemma apm_m95J01_derivative_sub_two_eq_zero {p : Polynomial ℝ}
    (h : Polynomial.derivative p - 2 • p = 0) : p = 0 := by
  by_contra hp
  have hnext : p.coeff (p.natDegree + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  have hc := congrArg (fun q : Polynomial ℝ ↦ q.coeff p.natDegree) h
  simp only [Polynomial.coeff_sub, Polynomial.coeff_derivative,
    Polynomial.coeff_smul, Polynomial.coeff_zero] at hc
  rw [hnext] at hc
  simp only [zero_mul, zero_sub] at hc
  simp only [two_nsmul] at hc
  have hlc : p.coeff p.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  exact hlc (by linarith)

lemma apm_m95J01_derivative_sub_two_injective :
    Function.Injective
      (fun p : Polynomial ℝ ↦ Polynomial.derivative p - 2 • p) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply apm_m95J01_derivative_sub_two_eq_zero
  rw [Polynomial.derivative_sub, smul_sub, sub_sub_sub_comm]
  exact sub_eq_zero.mpr hpq

lemma apm_m95J01_second_derivative_sub_two_derivative_eq_zero
    {p : Polynomial ℝ}
    (h : Polynomial.derivative (Polynomial.derivative p) -
      2 • Polynomial.derivative p = 0) :
    Polynomial.derivative p = 0 := by
  exact apm_m95J01_derivative_sub_two_eq_zero h

lemma apm_m95J01_kernel_polynomials_are_constant
    {p : Polynomial ℝ}
    (h : Polynomial.derivative (Polynomial.derivative p) -
      2 • Polynomial.derivative p = 0) :
    p = Polynomial.C (p.coeff 0) := by
  exact Polynomial.eq_C_of_derivative_eq_zero
    (apm_m95J01_second_derivative_sub_two_derivative_eq_zero h)

lemma apm_m95J01_derivative_sub_mem_degreeLE
    {n : ℕ} (p : Polynomial.degreeLE ℝ n) :
    Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
        2 • Polynomial.derivative (p : Polynomial ℝ) ∈
      Polynomial.degreeLE ℝ n := by
  rw [Polynomial.mem_degreeLE]
  apply (Polynomial.degree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.degree_derivative_le.trans
      (Polynomial.degree_derivative_le.trans
        (Polynomial.mem_degreeLE.mp p.property))
  · exact (Polynomial.degree_smul_le _ _).trans
      (Polynomial.degree_derivative_le.trans
        (Polynomial.mem_degreeLE.mp p.property))

def apm_m95J01_differentialEndomorphism (n : ℕ) :
    Polynomial.degreeLE ℝ n →ₗ[ℝ] Polynomial.degreeLE ℝ n :=
  LinearMap.codRestrict (Polynomial.degreeLE ℝ n)
    (((Polynomial.derivative.comp Polynomial.derivative :
        Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) -
      (2 : ℝ) • Polynomial.derivative).comp
        (Polynomial.degreeLE ℝ n).subtype)
    (by
      intro p
      simpa [two_smul ℝ, two_mul] using
        (apm_m95J01_derivative_sub_mem_degreeLE p))

lemma apm_m95J01_differentialEndomorphism_apply
    {n : ℕ} (p : Polynomial.degreeLE ℝ n) :
    (apm_m95J01_differentialEndomorphism n p : Polynomial ℝ) =
      Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
        2 • Polynomial.derivative (p : Polynomial ℝ) := by
  simp [apm_m95J01_differentialEndomorphism, two_smul ℝ, two_mul]

def apm_m95J01_constantOne (n : ℕ) : Polynomial.degreeLE ℝ n :=
  ⟨1, by simp [Polynomial.mem_degreeLE]⟩

lemma apm_m95J01_differentialEndomorphism_ker (n : ℕ) :
    (apm_m95J01_differentialEndomorphism n).ker =
      ℝ ∙ apm_m95J01_constantOne n := by
  apply le_antisymm
  · intro p hp
    have hp0 :
        Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
          2 • Polynomial.derivative (p : Polynomial ℝ) = 0 := by
      have h := congrArg
        (fun q : Polynomial.degreeLE ℝ n ↦ (q : Polynomial ℝ)) hp
      simpa [apm_m95J01_differentialEndomorphism_apply] using h
    have hc := apm_m95J01_kernel_polynomials_are_constant hp0
    rw [Submodule.mem_span_singleton]
    refine ⟨p.1.coeff 0, ?_⟩
    apply Subtype.ext
    simpa [apm_m95J01_constantOne, Algebra.smul_def] using hc.symm
  · intro p hp
    rw [Submodule.mem_span_singleton] at hp
    rcases hp with ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [apm_m95J01_differentialEndomorphism_apply,
      apm_m95J01_constantOne]

lemma apm_m95J01_differentialEndomorphism_ker_finrank (n : ℕ) :
    Module.finrank ℝ (apm_m95J01_differentialEndomorphism n).ker = 1 := by
  rw [apm_m95J01_differentialEndomorphism_ker]
  apply finrank_span_singleton
  intro h
  have := congrArg (fun p : Polynomial.degreeLE ℝ n ↦
    (p : Polynomial ℝ).coeff 0) h
  simpa [apm_m95J01_constantOne] using this

lemma apm_m95J01_differentialEndomorphism_range_finrank (n : ℕ) :
    Module.finrank ℝ (apm_m95J01_differentialEndomorphism n).range = n := by
  letI : FiniteDimensional ℝ (Polynomial.degreeLE ℝ n) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  have h := (apm_m95J01_differentialEndomorphism n).finrank_range_add_finrank_ker
  rw [apm_m95J01_differentialEndomorphism_ker_finrank] at h
  have hdim : Module.finrank ℝ (Polynomial.degreeLE ℝ n) = n + 1 := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE,
      LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1))]
    simp
  rw [hdim] at h
  omega

def apm_m95J01_topCoeff (n : ℕ) :
    Polynomial.degreeLE ℝ n →ₗ[ℝ] ℝ :=
  (Polynomial.lcoeff ℝ n).comp (Polynomial.degreeLE ℝ n).subtype

lemma apm_m95J01_topCoeff_ne_zero (n : ℕ) :
    apm_m95J01_topCoeff n ≠ 0 := by
  intro h
  let xn : Polynomial.degreeLE ℝ n :=
    ⟨Polynomial.X ^ n, by simp [Polynomial.mem_degreeLE]⟩
  have he := LinearMap.congr_fun h xn
  simp [apm_m95J01_topCoeff, xn] at he

lemma apm_m95J01_topCoeff_ker_finrank (n : ℕ) :
    Module.finrank ℝ (apm_m95J01_topCoeff n).ker = n := by
  letI : FiniteDimensional ℝ (Polynomial.degreeLE ℝ n) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (apm_m95J01_topCoeff_ne_zero n)
  have hdim : Module.finrank ℝ (Polynomial.degreeLE ℝ n) = n + 1 := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE,
      LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1))]
    simp
  rw [hdim] at h
  omega

lemma apm_m95J01_differentialEndomorphism_range_eq_topCoeff_ker (n : ℕ) :
    (apm_m95J01_differentialEndomorphism n).range =
      (apm_m95J01_topCoeff n).ker := by
  letI : FiniteDimensional ℝ (Polynomial.degreeLE ℝ n) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro q ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [apm_m95J01_topCoeff, LinearMap.comp_apply,
      Polynomial.lcoeff_apply]
    change ((apm_m95J01_differentialEndomorphism n p :
      Polynomial.degreeLE ℝ n) : Polynomial ℝ).coeff n = 0
    rw [apm_m95J01_differentialEndomorphism_apply]
    change
      (Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
        2 • Polynomial.derivative (p : Polynomial ℝ)).coeff n = 0
    exact apm_m95J01_top_coeff_derivative_sub p
  · rw [apm_m95J01_differentialEndomorphism_range_finrank,
      apm_m95J01_topCoeff_ker_finrank]

/-- The top-coefficient condition in the frozen range characterization is
necessary: it follows directly from the encoded formula for `T`. -/
lemma apm_m95J01_range_top_coeff_zero
    {n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) (T : H →ₗ[ℝ] H)
    (hT : ∀ f : H,
      (P (T f) : Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) -
          2 • Polynomial.derivative (P f : Polynomial ℝ) +
          (P f : Polynomial ℝ))
    {f g : H} (hfg : T f - f = g) :
    (P g : Polynomial ℝ).coeff n = 0 := by
  have hp : P (T f - f) = P g := congrArg P hfg
  rw [map_sub] at hp
  have hpoly := congrArg
    (fun q : Polynomial.degreeLE ℝ n ↦ (q : Polynomial ℝ)) hp
  change (P (T f) : Polynomial ℝ) - (P f : Polynomial ℝ) =
    (P g : Polynomial ℝ) at hpoly
  rw [hT f] at hpoly
  have hdiff :
      (P g : Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) -
          2 • Polynomial.derivative (P f : Polynomial ℝ) := by
    rw [← hpoly]
    abel
  rw [hdiff]
  exact apm_m95J01_top_coeff_derivative_sub (P f)

theorem apm_m95j01
    (n : ℕ) (hn : 0 < n)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n)
    (realize : H → ℝ → ℝ)
    (hrealize : ∀ (f : H) (x : ℝ),
      realize f x = Real.exp (-x) * (P f : Polynomial ℝ).eval x)
    (hinner : ∀ f g : H,
      inner ℝ f g = ∫ x in Set.Ioi (0 : ℝ), realize f x * realize g x)
    (monomial : Fin (n + 1) → H)
    (hmonomial : ∀ k : Fin (n + 1),
      (P (monomial k) : Polynomial ℝ) = Polynomial.X ^ (k : ℕ))
    (T : H →ₗ[ℝ] H)
    (hT : ∀ f : H,
      (P (T f) : Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) -
          2 • Polynomial.derivative (P f : Polynomial ℝ) +
          (P f : Polynomial ℝ)) :
    Nonempty (CompleteSpace H) ∧
    Module.finrank ℝ H = n + 1 ∧
    (∀ g : H,
      (∃ f : H, T f - f = g) ↔ (P g : Polynomial ℝ).coeff n = 0) ∧
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ H,
      ∀ k : Fin (n + 1),
        b k ∈ Submodule.span ℝ (monomial '' Set.Iic k) := by
  refine ⟨apm_m95J01_complete_of_equiv P,
    apm_m95J01_finrank_of_equiv P, ?_, ?_⟩
  · intro g
    constructor
    · rintro ⟨f, hfg⟩
      exact apm_m95J01_range_top_coeff_zero P T hT hfg
    · intro htop
      have hgker : P g ∈ (apm_m95J01_topCoeff n).ker := by
        rw [LinearMap.mem_ker]
        simpa [apm_m95J01_topCoeff] using htop
      rw [← apm_m95J01_differentialEndomorphism_range_eq_topCoeff_ker n] at hgker
      rcases hgker with ⟨p, hp⟩
      refine ⟨P.symm p, ?_⟩
      apply P.injective
      rw [map_sub]
      apply Subtype.ext
      simp only [Submodule.coe_sub, LinearEquiv.apply_symm_apply]
      rw [hT]
      simp only [LinearEquiv.apply_symm_apply]
      have hp' := congrArg
        (fun q : Polynomial.degreeLE ℝ n ↦ (q : Polynomial ℝ)) hp
      change ((apm_m95J01_differentialEndomorphism n p :
        Polynomial.degreeLE ℝ n) : Polynomial ℝ) =
          (P g : Polynomial ℝ) at hp'
      rw [apm_m95J01_differentialEndomorphism_apply] at hp'
      change Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) -
        2 • Polynomial.derivative (p : Polynomial ℝ) =
          (P g : Polynomial ℝ) at hp'
      rw [← hp']
      abel
  · letI : FiniteDimensional ℝ (Polynomial.degreeLE ℝ n) := by
      rw [← Polynomial.degreeLT_succ_eq_degreeLE]
      infer_instance
    letI : FiniteDimensional ℝ H := P.symm.finiteDimensional
    have hdim : Module.finrank ℝ H = Fintype.card (Fin (n + 1)) := by
      simpa using apm_m95J01_finrank_of_equiv P
    have hli := apm_m95J01_monomial_linearIndependent P monomial hmonomial
    let b : OrthonormalBasis (Fin (n + 1)) ℝ H :=
      InnerProductSpace.gramSchmidtOrthonormalBasis hdim monomial
    refine ⟨b, ?_⟩
    intro k
    have hk : InnerProductSpace.gramSchmidtNormed ℝ monomial k ≠ 0 := by
      intro hz
      have hnorm := InnerProductSpace.gramSchmidtNormed_unit_length k hli
      rw [hz, norm_zero] at hnorm
      norm_num at hnorm
    rw [show b k = InnerProductSpace.gramSchmidtNormed ℝ monomial k by
      exact InnerProductSpace.gramSchmidtOrthonormalBasis_apply hdim hk]
    unfold InnerProductSpace.gramSchmidtNormed
    exact Submodule.smul_mem _ _
      (InnerProductSpace.gramSchmidt_mem_span ℝ monomial (le_refl k))

#print axioms apm_m95j01

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

theorem apm_m95j01_abstract
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

#print axioms apm_m95j01_abstract

/-!
## Concrete construction (statement repair)

The graded gap: the abstract theorem above *assumed* an inner product space
whose inner product is the printed integral, and *assumed* a linear
endomorphism with the desired polynomial action.  Below we build the concrete
space `apm_m95J01_H n = {x ↦ e^{-x} p(x) | deg p ≤ n}` as a submodule of
`ℝ → ℝ`, equip it with the printed integral pairing (proving symmetry,
positive-definiteness and genuine integrability), define `T` as the second
derivative, and state its matrix in the monomial-exponential basis.
-/

/-- Realization map: a polynomial of degree at most `n` viewed as the function
`x ↦ e^{-x} p(x)`. -/
def apm_m95J01_realizeLM (n : ℕ) : Polynomial.degreeLE ℝ n →ₗ[ℝ] (ℝ → ℝ) where
  toFun p := fun x => Real.exp (-x) * (p : Polynomial ℝ).eval x
  map_add' p q := by funext x; simp [Polynomial.eval_add, mul_add]
  map_smul' c p := by funext x; simp [Polynomial.eval_smul]; ring

/-- The realization map is injective: a polynomial vanishing everywhere is
zero (infinitely many roots). -/
lemma apm_m95J01_realizeLM_injective (n : ℕ) :
    Function.Injective (apm_m95J01_realizeLM n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  apply Subtype.ext
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_univ.mono
  intro x _
  have h : Real.exp (-x) * (p : Polynomial ℝ).eval x = 0 := congrFun hp x
  exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)

/-- The concrete function space `H = {e^{-x} p(x) : deg p ≤ n}` as a submodule
of `ℝ → ℝ`. -/
def apm_m95J01_H (n : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  LinearMap.range (apm_m95J01_realizeLM n)

/-- Polynomial coordinates on `H`: the inverse of the realization map. -/
noncomputable def apm_m95J01_P (n : ℕ) :
    ↥(apm_m95J01_H n) ≃ₗ[ℝ] Polynomial.degreeLE ℝ n :=
  (LinearEquiv.ofInjective (apm_m95J01_realizeLM n)
    (apm_m95J01_realizeLM_injective n)).symm

/-- Every element of `H` really is the function `x ↦ e^{-x} p(x)` for its
coordinate polynomial. -/
lemma apm_m95J01_realize (n : ℕ) (f : ↥(apm_m95J01_H n)) (x : ℝ) :
    (f : ℝ → ℝ) x =
      Real.exp (-x) * ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) :
        Polynomial ℝ).eval x := by
  have h := LinearEquiv.apply_symm_apply
    (LinearEquiv.ofInjective (apm_m95J01_realizeLM n)
      (apm_m95J01_realizeLM_injective n)) f
  have h2 := congrFun (congrArg Subtype.val h) x
  simpa [apm_m95J01_P, apm_m95J01_realizeLM] using h2.symm

/-- Exponentially damped polynomials vanish at infinity. -/
lemma apm_m95J01_tendsto_exp_mul_eval (p : Polynomial ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.exp (-x) * p.eval x)
      Filter.atTop (nhds 0) := by
  rw [show (fun x : ℝ => Real.exp (-x) * p.eval x) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
        Real.exp (-x) * (p.coeff i * x ^ i) from
    funext fun x => by rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]]
  have hsum := tendsto_finset_sum (Finset.range (p.natDegree + 1))
    (fun (i : ℕ) (_ : i ∈ Finset.range (p.natDegree + 1)) => by
      have h0 : Filter.Tendsto (fun x : ℝ => (x : ℝ) ^ i * Real.exp (-x))
          Filter.atTop (nhds 0) := by
        apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (i : ℝ) 1
          one_pos).congr'
        exact Filter.Eventually.of_forall fun x => by
          show (x : ℝ) ^ (i : ℝ) * Real.exp (-1 * x) = x ^ i * Real.exp (-x)
          rw [Real.rpow_natCast]
          congr 2
          ring
      have h3 := h0.const_mul (p.coeff i)
      rw [mul_zero] at h3
      have h4 : Filter.Tendsto
          (fun x : ℝ => Real.exp (-x) * (p.coeff i * x ^ i))
          Filter.atTop (nhds 0) := by
        apply h3.congr'
        exact Filter.Eventually.of_forall fun x => by ring
      exact h4)
  rw [show (0 : ℝ) = ∑ _i ∈ Finset.range (p.natDegree + 1), (0 : ℝ) by simp]
  exact hsum

/-- The printed pairing integral is genuine: the integrand is integrable on
`(0, ∞)`. -/
lemma apm_m95J01_integrableOn (n : ℕ) (f g : ↥(apm_m95J01_H n)) :
    IntegrableOn (fun x => (f : ℝ → ℝ) x * (g : ℝ → ℝ) x) (Set.Ioi 0)
      volume := by
  rcases f.property with ⟨p, hp⟩
  rcases g.property with ⟨q, hq⟩
  have heq : (fun x => (f : ℝ → ℝ) x * (g : ℝ → ℝ) x) =
      fun x => Real.exp (-x) *
        (Real.exp (-x) *
          ((p : Polynomial ℝ).eval x * (q : Polynomial ℝ).eval x)) := by
    funext x
    have hfx : (f : ℝ → ℝ) x = Real.exp (-x) * (p : Polynomial ℝ).eval x :=
      (congrFun hp x).symm
    have hgx : (g : ℝ → ℝ) x = Real.exp (-x) * (q : Polynomial ℝ).eval x :=
      (congrFun hq x).symm
    rw [hfx, hgx]
    ring
  rw [heq]
  apply integrable_of_isBigO_exp_neg one_pos
  · apply Continuous.continuousOn
    apply Continuous.mul (Real.continuous_exp.comp continuous_neg)
    apply Continuous.mul (Real.continuous_exp.comp continuous_neg)
    exact (Polynomial.continuous _).mul (Polynomial.continuous _)
  · have h1 : (fun x : ℝ => Real.exp (-x)) =O[Filter.atTop]
        (fun x => Real.exp (-1 * x)) :=
      (Asymptotics.isBigO_refl _ _).congr' Filter.EventuallyEq.rfl
        (Filter.Eventually.of_forall fun x => congrArg Real.exp (by ring))
    have h2 := ((apm_m95J01_tendsto_exp_mul_eval
      ((p : Polynomial ℝ) * (q : Polynomial ℝ))).isBigO_one ℝ).congr'
      (Filter.Eventually.of_forall fun x => by
        show Real.exp (-x) * ((p : Polynomial ℝ) * (q : Polynomial ℝ)).eval x =
          Real.exp (-x) *
            ((p : Polynomial ℝ).eval x * (q : Polynomial ℝ).eval x)
        rw [Polynomial.eval_mul])
      Filter.EventuallyEq.rfl
    have hmul := h1.mul h2
    simp only [mul_one] at hmul
    exact hmul

/-- Positive-definiteness of the printed pairing: if `∫ f² = 0` then
`f = 0`. -/
lemma apm_m95J01_inner_definite (n : ℕ) (f : ↥(apm_m95J01_H n))
    (hf : ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℝ) x * (f : ℝ → ℝ) x = 0) :
    f = 0 := by
  by_contra hne
  -- the coordinate polynomial is nonzero
  have hP : (apm_m95J01_P n f : Polynomial.degreeLE ℝ n) ≠ 0 := by
    intro h
    exact hne ((apm_m95J01_P n).injective (by rw [h, map_zero]))
  set p := ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ)
      with hp_def
  have hp : p ≠ 0 := by
    intro h
    exact hP (Subtype.ext h)
  -- hence `p` is nonzero at some positive point
  obtain ⟨x₀, hx₀, hpx₀⟩ : ∃ x₀ ∈ Set.Ioi (0 : ℝ), p.eval x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Ioi_infinite 0).mono (fun x hx => h x hx)
  have hfx₀ : (f : ℝ → ℝ) x₀ ≠ 0 := by
    rw [apm_m95J01_realize n f x₀]
    exact mul_ne_zero (Real.exp_ne_zero _) hpx₀
  -- positivity of the integral
  set φ : ℝ → ℝ := fun x => (f : ℝ → ℝ) x * (f : ℝ → ℝ) x with hφ_def
  have hφ : Continuous φ := by
    rw [show φ = fun x => Real.exp (-x) * p.eval x * (Real.exp (-x) * p.eval x)
        from funext fun x => by
          show (f : ℝ → ℝ) x * (f : ℝ → ℝ) x = _
          rw [apm_m95J01_realize n f x]]
    exact ((Real.continuous_exp.comp continuous_neg).mul
      (Polynomial.continuous _)).mul
      ((Real.continuous_exp.comp continuous_neg).mul (Polynomial.continuous _))
  set c := φ x₀ / 2 with hc_def
  have hc : 0 < c := half_pos (mul_self_pos.mpr hfx₀)
  have hS : IsOpen ({x : ℝ | c < φ x} ∩ Set.Ioi 0) :=
    (isOpen_lt continuous_const hφ).inter isOpen_Ioi
  have hx₀S : x₀ ∈ {x : ℝ | c < φ x} ∩ Set.Ioi 0 :=
    ⟨half_lt_self (mul_self_pos.mpr hfx₀), hx₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x₀ hx₀S
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  have hmem : ∀ x ∈ Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2),
      x ∈ {x : ℝ | c < φ x} ∩ Set.Ioi 0 := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hsub : Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2) ⊆ Set.Ioi (0 : ℝ) :=
    fun x hx => (hmem x hx).2
  -- the integral is strictly positive
  have hint : IntegrableOn φ (Set.Ioi 0) volume := apm_m95J01_integrableOn n f f
  have h1 : (∫ x in Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2), φ x) ≤
      ∫ x in Set.Ioi (0 : ℝ), φ x := by
    apply MeasureTheory.setIntegral_mono_set hint
    · exact Filter.Eventually.of_forall fun x => mul_self_nonneg _
    · exact Filter.Eventually.of_forall fun x hx => hsub hx
  have h2 : c * ε ≤ ∫ x in Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2), φ x := by
    have hmono : (∫ _ in Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2), c) ≤
        ∫ x in Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2), φ x := by
      apply MeasureTheory.setIntegral_mono_on
      · exact integrableOn_const (hs := by simp [Real.volume_Ioo])
      · exact hint.mono_set hsub
      · exact measurableSet_Ioo
      · intro x hx
        exact (hmem x hx).1.le
    rw [integral_const, smul_eq_mul] at hmono
    have hvol : (volume.restrict (Set.Ioo (x₀ - ε / 2) (x₀ + ε / 2))).real
        Set.univ = ε := by
      have hnn : (0 : ℝ) ≤ x₀ + ε / 2 - (x₀ - ε / 2) := by linarith
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.toReal_ofReal hnn]
      linarith
    rw [hvol] at hmono
    linarith
  have hpos : 0 < ∫ x in Set.Ioi (0 : ℝ), φ x :=
    lt_of_lt_of_le (mul_pos hc hε) (h2.trans h1)
  rw [hf] at hpos
  exact lt_irrefl _ hpos

/-- The inner-product core on `H` given by the printed integral pairing. -/
@[reducible] noncomputable def apm_m95J01_core (n : ℕ) :
    InnerProductSpace.Core ℝ ↥(apm_m95J01_H n) where
  inner f g := ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℝ) x * (g : ℝ → ℝ) x
  conj_inner_symm f g := by
    simp only [starRingEnd_apply, star_trivial]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x _ => mul_comm _ _)
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun x _ => mul_self_nonneg _)
  add_left f g h := by
    have hfh := apm_m95J01_integrableOn n f h
    have hgh := apm_m95J01_integrableOn n g h
    rw [show (fun x => ((f + g : ↥(apm_m95J01_H n)) : ℝ → ℝ) x *
          (h : ℝ → ℝ) x) =
        fun x => (f : ℝ → ℝ) x * (h : ℝ → ℝ) x +
          (g : ℝ → ℝ) x * (h : ℝ → ℝ) x from
      funext fun x => by
        show ((f : ℝ → ℝ) + (g : ℝ → ℝ)) x * (h : ℝ → ℝ) x = _
        rw [Pi.add_apply, add_mul]]
    exact integral_add hfh hgh
  smul_left f g r := by
    simp only [starRingEnd_apply, star_trivial]
    rw [show (fun x => ((r • f : ↥(apm_m95J01_H n)) : ℝ → ℝ) x *
          (g : ℝ → ℝ) x) =
        fun x => r * ((f : ℝ → ℝ) x * (g : ℝ → ℝ) x) from
      funext fun x => by
        show (r • (f : ℝ → ℝ)) x * (g : ℝ → ℝ) x = _
        rw [Pi.smul_apply, smul_eq_mul]
        ring]
    rw [← integral_const_mul]
  definite f hf := apm_m95J01_inner_definite n f hf

noncomputable instance (n : ℕ) : NormedAddCommGroup ↥(apm_m95J01_H n) :=
  (apm_m95J01_core n).toNormedAddCommGroup

noncomputable instance (n : ℕ) : InnerProductSpace ℝ ↥(apm_m95J01_H n) :=
  InnerProductSpace.ofCore _

/-- Make the uniformity induced by the inner-product norm the canonical one
on `H` (rather than the pointwise uniformity inherited from `ℝ → ℝ`). -/
noncomputable instance (n : ℕ) : UniformSpace ↥(apm_m95J01_H n) :=
  PseudoMetricSpace.toUniformSpace

/-- The printed inner product is exactly the integral pairing. -/
lemma apm_m95J01_inner_eq (n : ℕ) (f g : ↥(apm_m95J01_H n)) :
    inner ℝ f g = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℝ) x * (g : ℝ → ℝ) x :=
  rfl

/-- The printed second derivative `T = (d/dx)²` as a linear endomorphism of
`H`: on coordinates, `(e^{-x} p)'' = e^{-x} (p'' - 2p' + p)`. -/
noncomputable def apm_m95J01_T (n : ℕ) :
    ↥(apm_m95J01_H n) →ₗ[ℝ] ↥(apm_m95J01_H n) :=
  (apm_m95J01_P n).symm.toLinearMap ∘ₗ
    ((apm_m95J01_differentialEndomorphism n + LinearMap.id) ∘ₗ
      (apm_m95J01_P n).toLinearMap)

lemma apm_m95J01_T_apply (n : ℕ) (f : ↥(apm_m95J01_H n)) :
    (apm_m95J01_P n (apm_m95J01_T n f) : Polynomial.degreeLE ℝ n) =
      (apm_m95J01_differentialEndomorphism n (apm_m95J01_P n f) +
        apm_m95J01_P n f) := by
  simp [apm_m95J01_T]

/-- The monomial-exponential basis `e_k(x) = e^{-x} x^k`. -/
noncomputable def apm_m95J01_e (n : ℕ) (k : Fin (n + 1)) :
    ↥(apm_m95J01_H n) :=
  (apm_m95J01_P n).symm ⟨Polynomial.X ^ (k : ℕ), by
    rw [Polynomial.mem_degreeLE]
    exact (Polynomial.degree_X_pow_le _).trans (by exact_mod_cast k.is_le)⟩

lemma apm_m95J01_P_e (n : ℕ) (k : Fin (n + 1)) :
    ((apm_m95J01_P n (apm_m95J01_e n k) : Polynomial.degreeLE ℝ n) :
      Polynomial ℝ) = Polynomial.X ^ (k : ℕ) := by
  unfold apm_m95J01_e
  rw [LinearEquiv.apply_symm_apply]

/-- Basis elements indexed by a natural number, extended by `0` above `n`. -/
noncomputable def apm_m95J01_e' (n : ℕ) (m : ℕ) : ↥(apm_m95J01_H n) :=
  if h : m ≤ n then apm_m95J01_e n ⟨m, Nat.lt_succ_of_le h⟩ else 0

/-- The matrix of `T` in the monomial-exponential basis:
`T e_k = e_k - 2k e_{k-1} + k(k-1) e_{k-2}`
(terms with negative index carry coefficient `0`). -/
lemma apm_m95J01_T_matrix (n : ℕ) (k : Fin (n + 1)) :
    apm_m95J01_T n (apm_m95J01_e n k) =
      apm_m95J01_e n k - (2 * (k : ℝ)) • apm_m95J01_e' n ((k : ℕ) - 1) +
        ((k : ℝ) * ((k : ℝ) - 1)) • apm_m95J01_e' n ((k : ℕ) - 2) := by
  have he' : ∀ m : ℕ, m ≤ n →
      ((apm_m95J01_P n (apm_m95J01_e' n m) : Polynomial.degreeLE ℝ n) :
        Polynomial ℝ) = Polynomial.X ^ m := by
    intro m hm
    rw [apm_m95J01_e', dif_pos hm]
    exact apm_m95J01_P_e n ⟨m, Nat.lt_succ_of_le hm⟩
  apply (apm_m95J01_P n).injective
  apply Subtype.ext
  simp only [apm_m95J01_T_apply, map_add, map_sub, map_smul, Submodule.coe_add,
    Submodule.coe_sub, Submodule.coe_smul, apm_m95J01_differentialEndomorphism_apply,
    apm_m95J01_P_e, he' _ (by omega : (k : ℕ) - 1 ≤ n),
    he' _ (by omega : (k : ℕ) - 2 ≤ n)]
  by_cases hk0 : (k : ℕ) = 0
  · simp [hk0]
  · have hk1 : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
    have e1 : Polynomial.derivative (Polynomial.X ^ (k : ℕ) : Polynomial ℝ) =
        ((k : ℕ) : ℝ) • Polynomial.X ^ ((k : ℕ) - 1) := by
      rw [Polynomial.derivative_X_pow, Polynomial.smul_eq_C_mul]
    have e2 : Polynomial.derivative (Polynomial.derivative
        (Polynomial.X ^ (k : ℕ) : Polynomial ℝ)) =
        (((k : ℕ) : ℝ) * (((k : ℕ) : ℝ) - 1)) • Polynomial.X ^ ((k : ℕ) - 2) := by
      rw [Polynomial.derivative_X_pow, Polynomial.derivative_C_mul,
        Polynomial.derivative_X_pow, Polynomial.smul_eq_C_mul, ← mul_assoc,
        ← Polynomial.C_mul, show (k : ℕ) - 1 - 1 = (k : ℕ) - 2 by omega,
        Nat.cast_sub hk1, Nat.cast_one]
    rw [e2, e1]
    module

/-- `T` really is the second derivative: as functions on `ℝ`,
`(T f)(x) = (d²/dx² f)(x)`. For `f(x) = e^{-x} p(x)` the product rule gives
`f' = e^{-x}(p' - p)` and hence `f'' = e^{-x}(p'' - 2p' + p)`, which is
exactly the polynomial action defining `T`. -/
lemma apm_m95J01_T_is_second_derivative (n : ℕ) (f : ↥(apm_m95J01_H n)) :
    ((apm_m95J01_T n f : ↥(apm_m95J01_H n)) : ℝ → ℝ) =
      deriv (deriv (f : ℝ → ℝ)) := by
  set p : Polynomial ℝ :=
    ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ) with hp
  have hd : ∀ q : Polynomial ℝ, ∀ x : ℝ,
      HasDerivAt (fun x => Real.exp (-x) * q.eval x)
        (Real.exp (-x) * (q.derivative.eval x - q.eval x)) x := by
    intro q x
    have hexp : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg' x)
      simpa using h
    have hmul := hexp.mul (Polynomial.hasDerivAt q x)
    convert hmul using 1
    ring
  have hf1 : deriv (f : ℝ → ℝ) =
      fun x => Real.exp (-x) * (p.derivative - p).eval x := by
    funext x
    rw [show (f : ℝ → ℝ) = fun x => Real.exp (-x) * p.eval x from
      funext (apm_m95J01_realize n f)]
    rw [(hd p x).deriv, Polynomial.eval_sub]
  have hf2 : deriv (deriv (f : ℝ → ℝ)) =
      fun x => Real.exp (-x) *
        ((p.derivative - p).derivative - (p.derivative - p)).eval x := by
    rw [hf1]
    funext x
    rw [(hd (p.derivative - p) x).deriv]
    simp only [Polynomial.eval_sub]
  have hcoord :
      ((apm_m95J01_P n (apm_m95J01_T n f) : Polynomial.degreeLE ℝ n) :
          Polynomial ℝ) =
        (p.derivative - p).derivative - (p.derivative - p) := by
    have h1 := congrArg Subtype.val (apm_m95J01_T_apply n f)
    rw [Submodule.coe_add, apm_m95J01_differentialEndomorphism_apply] at h1
    rw [h1, map_sub]
    module
  funext x
  rw [apm_m95J01_realize n (apm_m95J01_T n f) x, congrFun hf2 x, hcoord]

/-- The full repaired statement, over the concrete space. -/
theorem apm_m95j01 (n : ℕ) (hn : 0 < n) :
    -- (a) the printed integral pairing is a genuine, symmetric,
    -- positive-definite inner product, and `H` is a Hilbert space of
    -- dimension `n + 1`
    (∀ f g : ↥(apm_m95J01_H n),
      inner ℝ f g = ∫ x in Set.Ioi (0 : ℝ), (f : ℝ → ℝ) x * (g : ℝ → ℝ) x) ∧
    (∀ f g : ↥(apm_m95J01_H n),
      IntegrableOn (fun x => (f : ℝ → ℝ) x * (g : ℝ → ℝ) x) (Set.Ioi 0)
        volume) ∧
    (∀ f g : ↥(apm_m95J01_H n), inner ℝ f g = inner ℝ g f) ∧
    (∀ f : ↥(apm_m95J01_H n),
      0 ≤ inner ℝ f f ∧ (inner ℝ f f = 0 → f = 0)) ∧
    Nonempty (CompleteSpace ↥(apm_m95J01_H n)) ∧
    Module.finrank ℝ ↥(apm_m95J01_H n) = n + 1 ∧
    -- (b) `T = (d/dx)²` is the linear endomorphism of `H` with polynomial
    -- action `p ↦ p'' - 2p' + p`, and its matrix in the basis
    -- `e_k(x) = e^{-x} x^k` is `T e_k = e_k - 2k e_{k-1} + k(k-1) e_{k-2}`
    (∀ f : ↥(apm_m95J01_H n),
      ((apm_m95J01_P n (apm_m95J01_T n f) : Polynomial.degreeLE ℝ n) :
          Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative
            ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ)) -
          2 • Polynomial.derivative
            ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ) +
          ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ)) ∧
    -- (b′) `T` is literally the second derivative of the underlying function
    (∀ f : ↥(apm_m95J01_H n),
      ((apm_m95J01_T n f : ↥(apm_m95J01_H n)) : ℝ → ℝ) =
        deriv (deriv (f : ℝ → ℝ))) ∧
    (∀ k : Fin (n + 1),
      ((apm_m95J01_P n (apm_m95J01_e n k) : Polynomial.degreeLE ℝ n) :
        Polynomial ℝ) = Polynomial.X ^ (k : ℕ)) ∧
    (∀ k : Fin (n + 1),
      apm_m95J01_T n (apm_m95J01_e n k) =
        apm_m95J01_e n k - (2 * (k : ℝ)) • apm_m95J01_e' n ((k : ℕ) - 1) +
          ((k : ℝ) * ((k : ℝ) - 1)) • apm_m95J01_e' n ((k : ℕ) - 2)) ∧
    -- (c) `(T - I) f = g` is solvable iff the top coefficient of `g` vanishes
    (∀ g : ↥(apm_m95J01_H n),
      (∃ f : ↥(apm_m95J01_H n), apm_m95J01_T n f - f = g) ↔
        ((apm_m95J01_P n g : Polynomial.degreeLE ℝ n) :
          Polynomial ℝ).coeff n = 0) ∧
    -- (d) Gram–Schmidt applied to the monomial-exponential basis yields an
    -- orthonormal basis, flag-compatible with that basis
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ ↥(apm_m95J01_H n),
      ∀ k : Fin (n + 1),
        b k ∈ Submodule.span ℝ ((apm_m95J01_e n) '' Set.Iic k) := by
  have hTpoly : ∀ f : ↥(apm_m95J01_H n),
      ((apm_m95J01_P n (apm_m95J01_T n f) : Polynomial.degreeLE ℝ n) :
          Polynomial ℝ) =
        Polynomial.derivative (Polynomial.derivative
            ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ)) -
          2 • Polynomial.derivative
            ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ) +
          ((apm_m95J01_P n f : Polynomial.degreeLE ℝ n) : Polynomial ℝ) := by
    intro f
    rw [apm_m95J01_T_apply, Submodule.coe_add,
      apm_m95J01_differentialEndomorphism_apply]
  obtain ⟨hcomplete, hfinrank, hrange, hgram⟩ :=
    apm_m95j01_abstract n hn ↥(apm_m95J01_H n) (apm_m95J01_P n)
      (fun f x => (f : ℝ → ℝ) x)
      (fun f x => apm_m95J01_realize n f x)
      (fun f g => apm_m95J01_inner_eq n f g)
      (apm_m95J01_e n) (fun k => apm_m95J01_P_e n k)
      (apm_m95J01_T n) hTpoly
  exact ⟨apm_m95J01_inner_eq n, apm_m95J01_integrableOn n,
    fun f g => (real_inner_comm f g).symm,
    fun f => ⟨real_inner_self_nonneg, fun h => (inner_self_eq_zero (𝕜 := ℝ)).mp h⟩,
    hcomplete, hfinrank, hTpoly, apm_m95J01_T_is_second_derivative n,
    apm_m95J01_P_e n, apm_m95J01_T_matrix n, hrange, hgram⟩

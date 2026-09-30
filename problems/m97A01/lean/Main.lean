import Mathlib

/-!
# APM m97A01: Polar decomposition and compact adjoints

## Statement repairs

None. Although the source says "positive definite", it explicitly defines the
term using the non-strict inequality `⟨Bx,x⟩ ≥ 0`; this is Mathlib's
`ContinuousLinearMap.IsPositive` predicate.

## Encoding questions

The scalar field of the Hilbert space is not printed. We use the standard
complex Hilbert-space formulation. The modulus and adjoint are genuine
continuous linear operators; `Y` is the topological closure of the actual
range of the modulus, and `U : Y → X` is stated with its inclusion map,
factorization, uniqueness, and isometry property.
-/

noncomputable section

def apm_m97A01_modulusRange {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (B : X →L[ℂ] X) : Submodule ℂ X :=
  (LinearMap.range B.toLinearMap).topologicalClosure

def apm_m97A01_isModulus {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A B : X →L[ℂ] X) : Prop :=
  B.IsPositive ∧
  B.comp B = (ContinuousLinearMap.adjoint A).comp A ∧
  (∀ C : X →L[ℂ] X,
    C.IsPositive →
    C.comp C = (ContinuousLinearMap.adjoint A).comp A → C = B) ∧
  ∀ x : X, ‖B x‖ = ‖A x‖

def apm_m97A01_hasPolarFactor {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (A B : X →L[ℂ] X) : Prop :=
  ∃ inclusion : X →L[ℂ] apm_m97A01_modulusRange B,
    (∀ x : X, (inclusion x).1 = B x) ∧
    ∃ U : apm_m97A01_modulusRange B →L[ℂ] X,
      (∀ x : X, U (inclusion x) = A x) ∧
      (∀ y : apm_m97A01_modulusRange B, ‖U y‖ = ‖y‖) ∧
      ∀ V : apm_m97A01_modulusRange B →L[ℂ] X,
        (∀ x : X, V (inclusion x) = A x) → V = U

/-- The continuous functional calculus supplies the unique positive square
root of `A†A`. -/
lemma apm_m97A01_modulus_core
    (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) :
    ∃ B : X →L[ℂ] X,
      B.IsPositive ∧
      B.comp B = (ContinuousLinearMap.adjoint A).comp A ∧
      ∀ C : X →L[ℂ] X,
        C.IsPositive →
        C.comp C = (ContinuousLinearMap.adjoint A).comp A → C = B := by
  let P : X →L[ℂ] X := (ContinuousLinearMap.adjoint A).comp A
  let B : X →L[ℂ] X := CFC.sqrt P
  have hP : 0 ≤ P := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive P).mpr
    simpa [P] using ContinuousLinearMap.isPositive_adjoint_comp_self A
  refine ⟨B, (ContinuousLinearMap.nonneg_iff_isPositive B).mp
    (CFC.sqrt_nonneg P), ?_, ?_⟩
  · simpa [B, P] using CFC.sqrt_mul_sqrt_self P hP
  · intro C hC hC2
    have hCn : 0 ≤ C :=
      (ContinuousLinearMap.nonneg_iff_isPositive C).mpr hC
    exact (CFC.sqrt_unique (a := P) (b := C)
      (by simpa [P] using hC2) hCn).symm

/-- Positivity and the square identity determine the pointwise norm of the
modulus. -/
lemma apm_m97A01_modulus_norm
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A B : X →L[ℂ] X) (hB : B.IsPositive)
    (hB2 : B.comp B = (ContinuousLinearMap.adjoint A).comp A)
    (x : X) : ‖B x‖ = ‖A x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (B x)) (norm_nonneg (A x))]
  rw [B.apply_norm_sq_eq_inner_adjoint_left,
    A.apply_norm_sq_eq_inner_adjoint_left]
  rw [hB.isSelfAdjoint.adjoint_eq, hB2]

/-- The polar factor on the algebraic range of the modulus. Mathlib's
`LinearMap.compLeftInverse` performs the quotient-by-kernel construction. -/
noncomputable def apm_m97A01_polarOnRange
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (A B : X →L[ℂ] X) (hnorm : ∀ x : X, ‖B x‖ = ‖A x‖) :
    LinearMap.range B.toLinearMap →L[ℂ] X :=
  A.toLinearMap.compLeftInverse B.toLinearMap

lemma apm_m97A01_polarOnRange_apply
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (A B : X →L[ℂ] X) (hnorm : ∀ x : X, ‖B x‖ = ‖A x‖) (x : X) :
    apm_m97A01_polarOnRange A B hnorm ⟨B x, LinearMap.mem_range_self _ x⟩ = A x := by
  apply LinearMap.compLeftInverse_apply_of_bdd
  · exact ⟨1, fun z ↦ by simpa [hnorm z]⟩
  · rfl

/-- The algebraic-range polar factor is genuinely isometric. -/
lemma apm_m97A01_polarOnRange_norm
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (A B : X →L[ℂ] X) (hnorm : ∀ x : X, ‖B x‖ = ‖A x‖)
    (y : LinearMap.range B.toLinearMap) :
    ‖apm_m97A01_polarOnRange A B hnorm y‖ = ‖y‖ := by
  obtain ⟨x, hx⟩ := y.2
  rw [show y = ⟨B x, LinearMap.mem_range_self _ x⟩ from Subtype.ext hx.symm]
  rw [apm_m97A01_polarOnRange_apply]
  simpa using (hnorm x).symm

/-- The canonical inclusion appearing in the frozen polar-factor predicate:
`B` with codomain restricted to the closure of its algebraic range. -/
def apm_m97A01_modulusInclusion
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (B : X →L[ℂ] X) : X →L[ℂ] apm_m97A01_modulusRange B :=
  B.codRestrict (apm_m97A01_modulusRange B) fun x =>
    subset_closure (LinearMap.mem_range_self B.toLinearMap x)

lemma apm_m97A01_modulusInclusion_apply
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (B : X →L[ℂ] X) (x : X) :
    (apm_m97A01_modulusInclusion B x).1 = B x := by
  rfl

/-- Why this unblocks `apm_m97a01`: the polar isometry is already defined on
the algebraic range of `B`; this dense-range statement is the exact hypothesis
needed to extend it uniquely and continuously to `apm_m97A01_modulusRange B`,
the closure of that range. -/
theorem apm_m97A01_modulusInclusion_denseRange
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (B : X →L[ℂ] X) :
    DenseRange (apm_m97A01_modulusInclusion B) := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  change y ∈ closure
    ((fun z : apm_m97A01_modulusRange B ↦ z.1) ''
      Set.range (apm_m97A01_modulusInclusion B))
  have hrange :
      ((fun z : apm_m97A01_modulusRange B ↦ z.1) ''
        Set.range (apm_m97A01_modulusInclusion B)) =
          LinearMap.range B.toLinearMap := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      exact LinearMap.mem_range_self B.toLinearMap x
    · rintro ⟨x, rfl⟩
      exact ⟨apm_m97A01_modulusInclusion B x, ⟨x, rfl⟩, rfl⟩
  rw [hrange]
  exact hy

theorem apm_m97A01_hasPolarFactor_of_norm
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A B : X →L[ℂ] X) (hnorm : ∀ x : X, ‖B x‖ = ‖A x‖) :
    apm_m97A01_hasPolarFactor A B := by
  let e := (apm_m97A01_modulusInclusion B).toLinearMap
  let U : apm_m97A01_modulusRange B →L[ℂ] X :=
    A.toLinearMap.extendOfNorm e
  have hd : DenseRange e := apm_m97A01_modulusInclusion_denseRange B
  have hb : ∀ x : X, ‖A x‖ ≤ 1 * ‖e x‖ := by
    intro x
    rw [one_mul]
    change ‖A x‖ ≤ ‖B x‖
    exact (hnorm x).ge
  have hU (x : X) : U (apm_m97A01_modulusInclusion B x) = A x := by
    exact LinearMap.extendOfNorm_eq hd ⟨1, hb⟩ x
  refine ⟨apm_m97A01_modulusInclusion B,
    apm_m97A01_modulusInclusion_apply B, U, hU, ?_, ?_⟩
  · have heq : (fun y : apm_m97A01_modulusRange B ↦ ‖U y‖) = fun y ↦ ‖y‖ := by
      apply hd.equalizer (U.continuous.norm) continuous_norm
      funext x
      simp only [Function.comp_apply]
      change ‖A.toLinearMap.extendOfNorm e (e x)‖ = ‖e x‖
      rw [LinearMap.extendOfNorm_eq hd ⟨1, hb⟩ x]
      change ‖A x‖ = ‖B x‖
      exact (hnorm x).symm
    exact congrFun heq
  · intro V hV
    have heq : (V : apm_m97A01_modulusRange B → X) = U := by
      apply hd.equalizer V.continuous U.continuous
      funext x
      change V (apm_m97A01_modulusInclusion B x) =
        U (apm_m97A01_modulusInclusion B x)
      rw [hV x, hU x]
    ext y
    exact congrFun heq y

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem apm_m97A01_compact_sqrt
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (P : X →L[ℂ] X) (hP : P.IsPositive) (hPc : IsCompactOperator P) :
    IsCompactOperator (CFC.sqrt P : X →L[ℂ] X) := by
  let S : NonUnitalStarSubalgebra ℝ (X →L[ℂ] X) :=
    { carrier := {T | IsCompactOperator T ∧
          IsCompactOperator (ContinuousLinearMap.adjoint T)}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero]
        exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
      add_mem' := by
        rintro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
        exact ⟨hA.add hB, by simpa using hA'.add hB'⟩
      mul_mem' := by
        rintro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
        constructor
        · rw [ContinuousLinearMap.mul_def]
          simpa only [ContinuousLinearMap.coe_comp'] using hA.comp_clm B
        · rw [ContinuousLinearMap.mul_def,
            ContinuousLinearMap.adjoint_comp]
          simpa only [ContinuousLinearMap.coe_comp'] using
            hB'.comp_clm (ContinuousLinearMap.adjoint A)
      smul_mem' := by
        intro c A hA
        constructor
        · exact hA.1.smul c
        · have hadj : ContinuousLinearMap.adjoint (c • A) =
              c • ContinuousLinearMap.adjoint A := by
            ext x
            apply ext_inner_right ℂ
            intro y
            rw [ContinuousLinearMap.adjoint_inner_left]
            change inner ℂ x ((c : ℂ) • A y) =
              inner ℂ ((c : ℂ) • ContinuousLinearMap.adjoint A x) y
            rw [inner_smul_right, inner_smul_left,
              ContinuousLinearMap.adjoint_inner_left]
            simp
          rw [hadj]
          exact hA.2.smul c
      star_mem' := by
        rintro A ⟨hA, hA'⟩
        refine ⟨hA', ?_⟩
        rw [show star A = ContinuousLinearMap.adjoint A from rfl,
          ContinuousLinearMap.adjoint_adjoint]
        exact hA }
  letI : IsClosed ((S : NonUnitalStarSubalgebra ℝ (X →L[ℂ] X)) :
      Set (X →L[ℂ] X)) := by
    change IsClosed ({T : X →L[ℂ] X | IsCompactOperator T} ∩
      (fun T : X →L[ℂ] X => ContinuousLinearMap.adjoint T) ⁻¹'
        {T : X →L[ℂ] X | IsCompactOperator T})
    exact isClosed_setOf_isCompactOperator.inter
      (isClosed_setOf_isCompactOperator.preimage
        ContinuousLinearMap.adjoint.continuous)
  have hPmem : P ∈ S :=
    ⟨hPc, by
      rw [show ContinuousLinearMap.adjoint P = P from hP.isSelfAdjoint]
      exact hPc⟩
  rw [CFC.sqrt_eq_real_sqrt P
    ((ContinuousLinearMap.nonneg_iff_isPositive P).mpr hP)]
  exact (cfcₙ_mem (A := X →L[ℂ] X)
    (S := NonUnitalStarSubalgebra ℝ (X →L[ℂ] X)) Real.sqrt hPmem).1

theorem apm_m97A01_compact_adjoint
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    IsCompactOperator (ContinuousLinearMap.adjoint A) := by
  let C := ContinuousLinearMap.adjoint A
  let P := (ContinuousLinearMap.adjoint C).comp C
  have hCadj : ContinuousLinearMap.adjoint C = A := by
    simp [C]
  have hP : P = A.comp C := by simp [P, hCadj]
  have hPpos : P.IsPositive := by
    exact ContinuousLinearMap.isPositive_adjoint_comp_self C
  have hPc : IsCompactOperator P := by
    rw [hP]
    exact hA.comp_clm C
  let B : X →L[ℂ] X := CFC.sqrt P
  have hBc : IsCompactOperator B :=
    apm_m97A01_compact_sqrt P hPpos hPc
  have hBsq : B.comp B = P := by
    have hpnonneg : 0 ≤ P :=
      (ContinuousLinearMap.nonneg_iff_isPositive P).mpr hPpos
    exact CFC.sqrt_mul_sqrt_self P hpnonneg
  have hBpos : B.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive B).mp (CFC.sqrt_nonneg P)
  have hnorm : ∀ x : X, ‖B x‖ = ‖C x‖ := by
    intro x
    exact apm_m97A01_modulus_norm C B hBpos hBsq x
  obtain ⟨incl, hincl, U, hU, _, _⟩ :=
    apm_m97A01_hasPolarFactor_of_norm C B hnorm
  have hincl_eq : incl = apm_m97A01_modulusInclusion B := by
    ext x
    exact hincl x
  have hinclc : IsCompactOperator incl := by
    rw [hincl_eq]
    apply hBc.codRestrict
    exact (LinearMap.range B.toLinearMap).isClosed_topologicalClosure
  have hcomp : IsCompactOperator (U.comp incl) := hinclc.clm_comp U
  have heq : U.comp incl = C := by
    ext x
    exact hU x
  rw [heq] at hcomp
  exact hcomp

/-- The two positive products needed by a polar proof of compact-adjoint
compactness are compact without using compactness of the adjoint itself. -/
lemma apm_m97A01_compact_adjoint_comp_self
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    IsCompactOperator ((ContinuousLinearMap.adjoint A).comp A) := by
  exact hA.clm_comp (ContinuousLinearMap.adjoint A)

lemma apm_m97A01_compact_self_comp_adjoint
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    IsCompactOperator (A.comp (ContinuousLinearMap.adjoint A)) := by
  exact hA.comp_clm (ContinuousLinearMap.adjoint A)

/-- Adjoint compactness passes to an operator-norm limit once it is known for
the approximants.  The adjoint operation is an isometry, and compact
operators form a closed subset of the continuous-linear-map space. -/
lemma apm_m97A01_compact_adjoint_of_tendsto
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : X →L[ℂ] X) (F : ι → X →L[ℂ] X)
    (hF : Filter.Tendsto F l (nhds A))
    (hcompact : ∀ᶠ i in l,
      IsCompactOperator (ContinuousLinearMap.adjoint (F i))) :
    IsCompactOperator (ContinuousLinearMap.adjoint A) := by
  apply isCompactOperator_of_tendsto
    ((ContinuousLinearMap.adjoint.continuous.tendsto A).comp hF)
    hcompact

theorem apm_m97a01
    (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    (∃ absA : X →L[ℂ] X,
      apm_m97A01_isModulus A absA ∧
      apm_m97A01_hasPolarFactor A absA) ∧
    IsCompactOperator (ContinuousLinearMap.adjoint A) := by
  obtain ⟨B, hBpos, hBsq, hBuniq⟩ := apm_m97A01_modulus_core X A
  have hnorm : ∀ x : X, ‖B x‖ = ‖A x‖ :=
    apm_m97A01_modulus_norm A B hBpos hBsq
  constructor
  · exact ⟨B, ⟨hBpos, hBsq, hBuniq, hnorm⟩,
      apm_m97A01_hasPolarFactor_of_norm A B hnorm⟩
  · exact apm_m97A01_compact_adjoint A hA

import Mathlib

/-!
# APM m98J03 — orthogonal projections on a Hilbert space

## Statement repairs

None.

All six parts are included: the spectrum and its two degenerate cases,
compactness, the concrete orthogonal complement and its closedness, invariant
subspaces for commuting operators, and the adjoint.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

def apm_m98J03_perp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (V : ClosedSubmodule ℝ H) : Submodule ℝ H :=
  (V : Submodule ℝ H)ᗮ

lemma apm_m98J03_compact_starProjection_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (V : ClosedSubmodule ℝ H) :
    IsCompactOperator V.starProjection ↔
      FiniteDimensional ℝ (↥(V : Submodule ℝ H)) := by
  letI : CompleteSpace (↥(V : Submodule ℝ H)) :=
    IsComplete.completeSpace_coe V.isClosed'.isComplete
  constructor
  · intro hP
    have hres : IsCompactOperator
        (V.starProjection.toLinearMap.restrict fun x hx => V.starProjection_apply_mem x) :=
      hP.restrict' (fun x _ => V.starProjection_apply_mem x)
    have heq : V.starProjection.toLinearMap.restrict
        (fun x hx => V.starProjection_apply_mem x) = LinearMap.id := by
      ext x
      exact V.starProjection_eq_self_iff.mpr x.property
    rw [heq] at hres
    exact FiniteDimensional.of_isCompactOperator_id hres
  · intro hfin
    letI : FiniteDimensional ℝ (↥(V : Submodule ℝ H)) := hfin
    letI := FiniteDimensional.proper ℝ (↥(V : Submodule ℝ H))
    let Q : H →L[ℝ] (↥(V : Submodule ℝ H)) := V.starProjection.codRestrict V
      (fun x => V.starProjection_apply_mem x)
    have hQ : IsCompactOperator Q := isCompactOperator_of_locallyCompactSpace_dom Q
    have hcomp := hQ.clm_comp V.subtypeL
    simpa [Q, Function.comp_def] using hcomp

lemma apm_m98J03_spectrum_eq_zero_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Nontrivial H] (V : ClosedSubmodule ℝ H) :
    spectrum ℝ V.starProjection = ({0} : Set ℝ) ↔ V = ⊥ := by
  let P := V.starProjection
  have hPid : IsIdempotentElem P := V.isIdempotentElem_starProjection
  constructor
  · intro hs
    have hone_not : (1 : ℝ) ∉ spectrum ℝ P := by rw [hs]; simp
    have hunit : IsUnit (1 - P) := by
      simpa using (spectrum.notMem_iff.mp hone_not)
    have hcompid : IsIdempotentElem (1 - P) := hPid.one_sub
    have hPzero : P = 0 := by
      have h := (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hcompid
      have := congrArg (fun Q : H →L[ℝ] H => Q - 1) h
      simpa using this
    have hPzero' : V.starProjection = 0 := by simpa [P] using hPzero
    apply ClosedSubmodule.toSubmodule_injective
    rw [← V.range_starProjection, hPzero']
    ext x
    simp
  · intro hV
    subst V
    change spectrum ℝ ((⊥ : Submodule ℝ H).starProjection) = {0}
    rw [Submodule.starProjection_bot]
    ext r
    simp

lemma apm_m98J03_spectrum_eq_one_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [Nontrivial H] (V : ClosedSubmodule ℝ H) :
    spectrum ℝ V.starProjection = ({1} : Set ℝ) ↔ V = ⊤ := by
  let P := V.starProjection
  have hPid : IsIdempotentElem P := V.isIdempotentElem_starProjection
  constructor
  · intro hs
    have hzero_not : (0 : ℝ) ∉ spectrum ℝ P := by rw [hs]; simp
    have hunit : IsUnit P := spectrum.isUnit_of_zero_notMem ℝ hzero_not
    have hPone : P = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp hPid
    have hPone' : V.starProjection = 1 := by simpa [P] using hPone
    apply ClosedSubmodule.toSubmodule_injective
    rw [← V.range_starProjection, hPone']
    ext x
    simp
  · intro hV
    subst V
    change spectrum ℝ ((⊤ : Submodule ℝ H).starProjection) = {1}
    rw [Submodule.starProjection_top']
    ext r
    simp

lemma apm_m98J03_commute_preserves
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (V : ClosedSubmodule ℝ H) :
    ∀ A : H →L[ℝ] H, A.comp V.starProjection = V.starProjection.comp A →
      (∀ x ∈ (V : Set H), A x ∈ (V : Set H)) ∧
      (∀ x ∈ (apm_m98J03_perp V : Set H),
        A x ∈ (apm_m98J03_perp V : Set H)) := by
  intro A hcomm
  constructor
  · intro x hx
    change A x ∈ (V : Submodule ℝ H)
    rw [← V.starProjection_eq_self_iff]
    rw [← ContinuousLinearMap.comp_apply, ← hcomm,
      ContinuousLinearMap.comp_apply, V.starProjection_eq_self_iff.mpr hx]
  · intro x hx
    have hxzero : V.starProjection x = 0 := by
      change x ∈ V.starProjection.ker
      simpa [apm_m98J03_perp] using hx
    have hAxzero : V.starProjection (A x) = 0 := by
      rw [← ContinuousLinearMap.comp_apply, ← hcomm,
        ContinuousLinearMap.comp_apply, hxzero, map_zero]
    change A x ∈ (V : Submodule ℝ H)ᗮ
    rw [← V.ker_starProjection]
    exact hAxzero

lemma apm_m98J03_perp_isClosed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (V : ClosedSubmodule ℝ H) :
    IsClosed (apm_m98J03_perp V : Set H) :=
  (V : Submodule ℝ H).isClosed_orthogonal

lemma apm_m98J03_adjoint_starProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (V : ClosedSubmodule ℝ H) :
    V.starProjection.adjoint = V.starProjection :=
  (isSelfAdjoint_starProjection (V : Submodule ℝ H)).adjoint_eq

theorem apm_m98j03 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (V : ClosedSubmodule ℝ H) :
    let P := V.starProjection
    let Vperp := apm_m98J03_perp V
    spectrum ℝ P ⊆ ({0, 1} : Set ℝ) ∧
    (spectrum ℝ P = ({0} : Set ℝ) ↔ V = ⊥) ∧
    (spectrum ℝ P = ({1} : Set ℝ) ↔ V = ⊤) ∧
    (IsCompactOperator P ↔
      FiniteDimensional ℝ (↥(V : Submodule ℝ H))) ∧
    IsClosed (Vperp : Set H) ∧
    (∀ A : H →L[ℝ] H, A.comp P = P.comp A →
      (∀ x ∈ (V : Set H), A x ∈ (V : Set H)) ∧
      (∀ x ∈ (Vperp : Set H), A x ∈ (Vperp : Set H))) ∧
    P.adjoint = P := by
  dsimp only
  exact ⟨V.isIdempotentElem_starProjection.spectrum_subset ℝ,
    apm_m98J03_spectrum_eq_zero_iff V,
    apm_m98J03_spectrum_eq_one_iff V,
    apm_m98J03_compact_starProjection_iff V,
    apm_m98J03_perp_isClosed V,
    apm_m98J03_commute_preserves V,
    apm_m98J03_adjoint_starProjection V⟩

import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.CoveringMap

/-! # APM t96A05: extending a null-homotopic map to the punctured plane

## Statement repairs

This file encodes the final extension assertion.  The intermediate neighborhood
extension and tube question are proof-guiding subproblems and are not separate
theorem statements here.  The source separately assumes normality of `X × I`;
that assumption is retained explicitly.

## Encoding questions

The punctured plane is the concrete subtype of `ℝ × ℝ` excluding `(0,0)`.
Maps and the null homotopy are Mathlib continuous maps and `Nullhomotopic`.
-/

abbrev APMT96A05.PuncturedPlane := {p : ℝ × ℝ // p ≠ (0, 0)}

noncomputable section

/-- Regard a nonzero real pair as a nonzero complex number. -/
def APMT96A05.toComplex
    (p : APMT96A05.PuncturedPlane) : {z : ℂ // z ≠ 0} :=
  ⟨Complex.equivRealProdCLM.symm p.1, by
    intro h
    apply p.2
    simpa using congrArg Complex.equivRealProdCLM h⟩

/-- Return a nonzero complex number to real-pair coordinates. -/
def APMT96A05.ofComplex
    (z : {z : ℂ // z ≠ 0}) : APMT96A05.PuncturedPlane :=
  ⟨Complex.equivRealProdCLM z.1, by
    intro h
    apply z.2
    apply Complex.equivRealProdCLM.injective
    simpa using h⟩

lemma APMT96A05.ofComplex_toComplex
    (p : APMT96A05.PuncturedPlane) :
    APMT96A05.ofComplex (APMT96A05.toComplex p) = p := by
  apply Subtype.ext
  simp [APMT96A05.ofComplex, APMT96A05.toComplex]

/-- A nullhomotopic punctured-plane map has a continuous logarithm. -/
theorem apm_t96A05_exists_complex_logarithm
    {X : Type*} [TopologicalSpace X]
    (A : Set X)
    (f : C(A, APMT96A05.PuncturedPlane)) (hf : f.Nullhomotopic) :
    ∃ u : C(A, ℂ), ∀ a : A,
      Complex.exp (u a) = (APMT96A05.toComplex (f a)).1 := by
  sorry

/-- Tietze-extend a supplied logarithm and exponentiate it.  The logarithm
hypothesis is explicit so this lemma is independent of the covering lift. -/
theorem apm_t96A05_extend_from_complex_logarithm
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (A : Set X) (hA : IsClosed A)
    (f : C(A, APMT96A05.PuncturedPlane))
    (hlift : ∃ u : C(A, ℂ), ∀ a : A,
      Complex.exp (u a) = (APMT96A05.toComplex (f a)).1) :
    ∃ F : C(X, APMT96A05.PuncturedPlane), ∀ a : A, F a = f a := by
  sorry

theorem apm_t96a05
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    [NormalSpace (X × Set.Icc (0 : ℝ) 1)]
    (A : Set X) (hA : IsClosed A)
    (f : C(A, APMT96A05.PuncturedPlane)) (hf : f.Nullhomotopic) :
    ∃ F : C(X, APMT96A05.PuncturedPlane), ∀ a : A, F a = f a := by
  apply apm_t96A05_extend_from_complex_logarithm A hA f
  exact apm_t96A05_exists_complex_logarithm A f hf

#print axioms apm_t96a05

import Mathlib.Topology.Homotopy.Contractible

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

theorem apm_t96a05
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    [NormalSpace (X × Set.Icc (0 : ℝ) 1)]
    (A : Set X) (hA : IsClosed A)
    (f : C(A, APMT96A05.PuncturedPlane)) (hf : f.Nullhomotopic) :
    ∃ F : C(X, APMT96A05.PuncturedPlane), ∀ a : A, F a = f a := by
  sorry

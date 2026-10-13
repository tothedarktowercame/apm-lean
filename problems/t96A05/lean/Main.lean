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
  let c : C(APMT96A05.PuncturedPlane, {z : ℂ // z ≠ 0}) :=
    ⟨APMT96A05.toComplex, by
      apply Continuous.subtype_mk
      exact Complex.equivRealProdCLM.symm.continuous.comp continuous_subtype_val⟩
  obtain ⟨z₀, hz₀⟩ := hf.comp_right c
  obtain ⟨H⟩ := hz₀
  let Hr := H.symm
  let g : C(A, ℂ) := ContinuousMap.const A (Complex.log z₀.1)
  have hg : ∀ a : A, Hr (0, a) =
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) (g a) := by
    intro a
    rw [ContinuousMap.Homotopy.apply_zero]
    apply Subtype.ext
    change z₀.1 = Complex.exp (Complex.log z₀.1)
    exact (Complex.exp_log z₀.2).symm
  let L : C(unitInterval × A, ℂ) :=
    Complex.isCoveringMap_exp.liftHomotopy Hr g hg
  let atOne : C(A, unitInterval × A) :=
    (ContinuousMap.const A (1 : unitInterval)).prodMk (ContinuousMap.id A)
  let u : C(A, ℂ) := L.comp atOne
  refine ⟨u, ?_⟩
  intro a
  have hl := congr_fun
    (Complex.isCoveringMap_exp.liftHomotopy_lifts Hr g hg) ((1 : unitInterval), a)
  have hOne : Hr ((1 : unitInterval), a) = c (f a) := by
    exact ContinuousMap.Homotopy.apply_one Hr a
  have := congrArg Subtype.val hl
  simpa [u, atOne, L, hOne, c] using this

/-- Tietze-extend a supplied logarithm and exponentiate it.  The logarithm
hypothesis is explicit so this lemma is independent of the covering lift. -/
theorem apm_t96A05_extend_from_complex_logarithm
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (A : Set X) (hA : IsClosed A)
    (f : C(A, APMT96A05.PuncturedPlane))
    (hlift : ∃ u : C(A, ℂ), ∀ a : A,
      Complex.exp (u a) = (APMT96A05.toComplex (f a)).1) :
    ∃ F : C(X, APMT96A05.PuncturedPlane), ∀ a : A, F a = f a := by
  obtain ⟨u, hu⟩ := hlift
  let up : C(A, ℝ × ℝ) :=
    ⟨fun a ↦ Complex.equivRealProdCLM (u a),
      Complex.equivRealProdCLM.continuous.comp u.continuous⟩
  obtain ⟨U, hU⟩ := up.exists_extension hA.isClosedEmbedding_subtypeVal
  let z : C(X, ℂ) :=
    ⟨fun x ↦ Complex.equivRealProdCLM.symm (U x),
      Complex.equivRealProdCLM.symm.continuous.comp U.continuous⟩
  let ez : C(X, {z : ℂ // z ≠ 0}) :=
    ⟨fun x ↦ ⟨Complex.exp (z x), Complex.exp_ne_zero _⟩,
      Continuous.subtype_mk (Complex.continuous_exp.comp z.continuous) _⟩
  let F : C(X, APMT96A05.PuncturedPlane) :=
    ⟨fun x ↦ APMT96A05.ofComplex (ez x), by
      apply Continuous.subtype_mk
      exact Complex.equivRealProdCLM.continuous.comp
        (continuous_subtype_val.comp ez.continuous)⟩
  refine ⟨F, ?_⟩
  intro a
  apply Subtype.ext
  have hUa : U a = up a := congrArg (fun k : C(A, ℝ × ℝ) ↦ k a) hU
  have he : (ez a).1 = (APMT96A05.toComplex (f a)).1 := by
    dsimp [ez, z]
    rw [hUa]
    simpa [up] using hu a
  change Complex.equivRealProdCLM (ez a).1 = (f a).1
  rw [he]
  exact congrArg Subtype.val (APMT96A05.ofComplex_toComplex (f a))

theorem apm_t96a05
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    [NormalSpace (X × Set.Icc (0 : ℝ) 1)]
    (A : Set X) (hA : IsClosed A)
    (f : C(A, APMT96A05.PuncturedPlane)) (hf : f.Nullhomotopic) :
    ∃ F : C(X, APMT96A05.PuncturedPlane), ∀ a : A, F a = f a := by
  apply apm_t96A05_extend_from_complex_logarithm A hA f
  exact apm_t96A05_exists_complex_logarithm A f hf

#print axioms apm_t96a05

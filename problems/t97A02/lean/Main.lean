import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t97A02 — maps from a finite-complex-type space to the torus

The target is the genuine torus `Circle × Circle`, and `H₁` is Mathlib's
integral singular homology.  The topological hypotheses retain the properties
of finite simplicial realizations used by the argument.

## Statement repairs

Mathlib currently has abstract simplicial complexes but no general topological
geometric-realization construction.  The opaque “finite simplicial complex”
predicate is therefore replaced by its proof-relevant consequences: compact
Hausdorff, locally connected, and locally contractible.  This is the natural
scope in which the homological classification of maps to circles applies.

The opaque finiteness predicate is replaced by a genuine `Finite` instance on
the integral first singular-homology group.

## Encoding questions

None.
-/

open CategoryTheory

noncomputable section

abbrev apm_t97A02_Torus := Circle × Circle

abbrev apm_t97A02_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t97A02_firstProjection {X : Type} [TopologicalSpace X]
    (f : C(X, apm_t97A02_Torus)) : C(X, Circle) :=
  ContinuousMap.fst.comp f

def apm_t97A02_secondProjection {X : Type} [TopologicalSpace X]
    (f : C(X, apm_t97A02_Torus)) : C(X, Circle) :=
  ContinuousMap.snd.comp f

/-- Null-homotopies of the two circle coordinates recombine into a
null-homotopy of the torus-valued map. This isolates the remaining theorem to
the classification of maps into one circle. -/
lemma apm_t97A02_homotopic_const_of_projection_homotopies
    {X : Type} [TopologicalSpace X] (f : C(X, apm_t97A02_Torus))
    (p : apm_t97A02_Torus)
    (h₁ : ContinuousMap.Homotopic (apm_t97A02_firstProjection f)
      (ContinuousMap.const X p.1))
    (h₂ : ContinuousMap.Homotopic (apm_t97A02_secondProjection f)
      (ContinuousMap.const X p.2)) :
    ContinuousMap.Homotopic f (ContinuousMap.const X p) := by
  simpa [apm_t97A02_firstProjection, apm_t97A02_secondProjection] using
    h₁.prodMk h₂

theorem apm_t97a02
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [LocallyConnectedSpace X]
    (hX : LocallyContractibleSpace X)
    [Finite (apm_t97A02_H1 X)]
    (f : C(X, apm_t97A02_Torus)) :
    ∃ p : apm_t97A02_Torus,
      ContinuousMap.Homotopic f (ContinuousMap.const X p) := by
  /-
  PARTIAL boundary (closer hop 3).

  New compiled progress isolates the product target completely.
  `apm_t97A02_firstProjection` and `apm_t97A02_secondProjection` bundle the
  two circle coordinates, and
  `apm_t97A02_homotopic_const_of_projection_homotopies` reassembles any two
  coordinate null-homotopies with Mathlib's `ContinuousMap.Homotopic.prodMk`.
  Thus it suffices to prove the corresponding theorem for a single map
  `X → Circle`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, circle/torus siblings,
  Mathlib's singular-homology, cohomology, covering, and `AddCircle` sources,
  and git history found no theorem identifying homotopy classes `[X,S¹]`
  with integral `H¹(X)`, no universal lifting criterion stated from finite
  `H₁(X)`, and no computation of circle homology sufficient to assemble that
  route locally. Related artifacts `t03J01`, `t01A03`, and `t97J06` likewise
  record missing circle invariant or representability steps. The remaining
  bridge is therefore the one-circle null-homotopy theorem from finite
  integral first homology; the frozen statement is unchanged.
  -/
  sorry

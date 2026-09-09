import Mathlib
import ConstructionTargets.CircleHurewiczIsomorphism
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.ComponentRealLiftAssembly
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


namespace T97A02Closure
open CategoryTheory
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.CircleHurewiczIsomorphism
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.IntegralSingularHomologyComparison
noncomputable section
set_option autoImplicit false
abbrev FrozenH1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))
theorem finiteIntegralH1 (X : Type) [TopologicalSpace X] [Finite (FrozenH1 X)] :
    Finite (IntegralH1 X) :=
  Finite.of_surjective (singularHomologyComparison (TopCat.of X) 1).hom
    (fun z => ⟨(singularHomologyComparison (TopCat.of X) 1).inv z,
      (singularHomologyComparison (TopCat.of X) 1).inv_hom_id_apply z⟩)


theorem finite_to_int_zero {A : Type} [AddCommGroup A] [Finite A] (f : A →+ ℤ) (a : A) : f a = 0 := by
  have hp := (isOfFinAddOrder_of_finite a).addOrderOf_pos
  have h := congrArg f (addOrderOf_nsmul_eq_zero a)
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hp.ne')

theorem circle_H1_map_zero {X : Type} [TopologicalSpace X] [Finite (FrozenH1 X)]
    (f : C(X, Circle)) (z : IntegralH1 X) :
    HomologicalComplex.homologyMap (singularPostcomposition f) 1 z = 0 := by
  letI : Finite (IntegralH1 X) := finiteIntegralH1 X
  apply circleH1AddEquivInt.injective
  simpa using finite_to_int_zero
    (show IntegralH1 X →+ ℤ from circleH1AddEquivInt.toAddMonoidHom.comp
      (HomologicalComplex.homologyMap (singularPostcomposition f) 1).hom) z


theorem circle_hurewicz_injective_at_one :
    Function.Injective (fundamentalGroupH1Hom (1 : Circle)) := by
  intro p q hpq
  have hab : Abelianization.of p = Abelianization.of q :=
    circleAbelianizedFundamentalGroupH1MulEquiv.injective hpq
  apply ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.injective
  exact congrArg
    (Abelianization.lift
      ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.toMonoidHom) hab

theorem induced_loop_trivial_at_one {X : Type} [TopologicalSpace X]
    [Finite (FrozenH1 X)] (f : C(X, Circle)) (x : X) (hx : f x = 1)
    (p : FundamentalGroup X x) : FundamentalGroup.map f x p = 1 := by
  have hi : Function.Injective (fundamentalGroupH1Hom (f x)) := by
    rw [hx]
    exact circle_hurewicz_injective_at_one
  apply hi
  rw [map_one, ← fundamentalGroupH1Hom_naturality]
  exact congrArg Multiplicative.ofAdd (circle_H1_map_zero f _)


open ConstructionTargets.ComponentRealLiftAssembly
open ConstructionTargets.ClassicalLocalPathConnectivity
open ConstructionTargets.CircleUniversalCover

theorem component_lifts {X : Type} [TopologicalSpace X]
    (hX : LocallyContractibleSpace X) [Finite (FrozenH1 X)] (f : C(X,Circle))
    (c : ConnectedComponents X) :
    ∃ F : C(componentFiber c, ℝ), ∀ y, Circle.exp (F y) = f y.val := by
  letI := locPathConnected_of_classical hX
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let c : ConnectedComponents X := x
  let b : componentFiber c := ⟨x,rfl⟩
  letI : PathConnectedSpace (componentFiber c) := componentFiber_pathConnected hX c
  letI : LocPathConnectedSpace (componentFiber c) :=
    ((isOpen_discrete ({c} : Set (ConnectedComponents X))).preimage
      ConnectedComponents.continuous_coe).locPathConnectedSpace
  let g : C(X,Circle) := ⟨fun y => (f x)⁻¹ * f y, by fun_prop⟩
  have hg : g x = 1 := by simp [g]
  have he : circleCover 0 = (g.comp (componentInclusion c)) b := by
    simpa [circleCover, b, componentInclusion] using hg.symm
  obtain ⟨G, hG, _⟩ := circleCover_isCoveringMap.existsUnique_continuousMap_lifts_of_range_le he (by
    rintro z ⟨p,rfl⟩
    rw [component_loop_trivial g c b (induced_loop_trivial_at_one g x hg) p]
    exact Subgroup.one_mem _)
  refine ⟨⟨fun y => Complex.arg (f x : ℂ) + G y, by fun_prop⟩, ?_⟩
  intro y
  have hy := congrFun hG.2 y
  change Circle.exp (G y) = (f x)⁻¹ * f y.val at hy
  change Circle.exp (Complex.arg (f x : ℂ) + G y) = f y.val
  rw [Circle.exp_add, hy]
  have hxarg : Circle.exp (Complex.arg (f x : ℂ)) = f x := by
    apply Subtype.ext
    simp
  rw [hxarg]
  simp
end
end T97A02Closure

/-- Why this unblocks `apm_t97a02`: this is the missing one-circle
classification/lifting theorem.  The identification `[X,S¹] ≅ H¹(X;ℤ)` and
the universal-coefficient theorem make every class vanish when integral
`H₁(X)` is finite; compact local connectedness handles the finitely many
connected components and permits a single constant target point. -/
theorem apm_t97A02_bridge_1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [LocallyConnectedSpace X]
    (hX : LocallyContractibleSpace X)
    [Finite (apm_t97A02_H1 X)]
    (f : C(X, Circle)) :
    ∃ p : Circle,
      ContinuousMap.Homotopic f (ContinuousMap.const X p) := by
  refine ⟨1, ?_⟩
  exact ConstructionTargets.ComponentRealLiftAssembly.classical_component_lifts_nullhomotopic hX f
    (T97A02Closure.component_lifts hX f)

theorem apm_t97a02
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [LocallyConnectedSpace X]
    (hX : LocallyContractibleSpace X)
    [Finite (apm_t97A02_H1 X)]
    (f : C(X, apm_t97A02_Torus)) :
    ∃ p : apm_t97A02_Torus,
      ContinuousMap.Homotopic f (ContinuousMap.const X p) := by
  obtain ⟨p, hp⟩ := apm_t97A02_bridge_1 X hX (apm_t97A02_firstProjection f)
  obtain ⟨q, hq⟩ := apm_t97A02_bridge_1 X hX (apm_t97A02_secondProjection f)
  exact ⟨(p,q), apm_t97A02_homotopic_const_of_projection_homotopies f (p,q) hp hq⟩
#print axioms apm_t97A02_bridge_1
#print axioms apm_t97a02

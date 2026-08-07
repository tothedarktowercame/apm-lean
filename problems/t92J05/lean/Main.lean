import Mathlib
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t92J05

## Statement repairs

None.

## Encoding questions

`RP²`, `S²`, and `S¹` are encoded as their actual projectivization and metric
spheres. A closed oriented genus-two surface is an actual compact connected
2-manifold with integral homology `H₀ = ℤ`, `H₁ = ℤ⁴`, `H₂ = ℤ`, and zero
higher homology. Its asserted fundamental group is the actual presented group
on four generators with relator `[a₁,b₁][a₂,b₂]`.
-/

open CategoryTheory Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t92J05_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t92J05_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t92J05_S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
abbrev apm_t92J05_S1 := Metric.sphere (0 : ℂ) 1
abbrev apm_t92J05_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t92J05_Model := 𝓘(ℝ, apm_t92J05_E2)

abbrev apm_t92J05_H (k : ℕ) (S : Type) [TopologicalSpace S] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S))

def apm_t92J05_HasGenusTwoHomology
    (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (apm_t92J05_H 0 S ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t92J05_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t92J05_H 2 S ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t92J05_H k S)

/-- The commutator word on two generators of `FreeGroup (Fin 4)`. -/
def apm_t92J05_commutator (a b : Fin 4) : FreeGroup (Fin 4) :=
  FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹ * (FreeGroup.of b)⁻¹

@[simp] lemma apm_t92J05_commutator_self (a : Fin 4) :
    apm_t92J05_commutator a a = 1 := by
  simp [apm_t92J05_commutator]

/-- The genus-two surface relator `[a₁,b₁][a₂,b₂]`. -/
def apm_t92J05_genusTwoRelator : FreeGroup (Fin 4) :=
  apm_t92J05_commutator 0 1 * apm_t92J05_commutator 2 3

abbrev apm_t92J05_genusTwoGroup :=
  PresentedGroup ({apm_t92J05_genusTwoRelator} : Set (FreeGroup (Fin 4)))

theorem apm_t92j05 :
    (∀ x : apm_t92J05_RP2,
      Nonempty
        (FundamentalGroup apm_t92J05_RP2 x ≃* Multiplicative (ZMod 2))) ∧
    (∀ x : apm_t92J05_S2 × apm_t92J05_S1,
      Nonempty
        (FundamentalGroup (apm_t92J05_S2 × apm_t92J05_S1) x ≃*
          Multiplicative ℤ)) ∧
    ∀ (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        [PathConnectedSpace S] [ChartedSpace apm_t92J05_E2 S]
        [IsManifold apm_t92J05_Model ∞ S]
        (hS : apm_t92J05_HasGenusTwoHomology S) (x : S),
      Nonempty
        (FundamentalGroup S x ≃* apm_t92J05_genusTwoGroup) := by
  /-
  CLOSER HOP 1 boundary. The elementary presentation normalization
  `apm_t92J05_commutator_self` is compiled above as a sanity check on the
  frozen relator encoding.

  Mathlib's `AlgebraicTopology.FundamentalGroupoid.Product` proves that the
  fundamental groupoid functor preserves products. Thus the middle clause can
  in principle be reduced to the fundamental groups of the metric two-sphere
  and complex unit circle. Searches found no packaged theorem that the former
  is trivial or that the latter is `ℤ`; the available `Circle`/`AddCircle`
  topology does not include the required fundamental-group computation.

  The first clause needs the antipodal universal cover of the projectivization
  and its deck group, or an independent CW computation of `π₁(RP²)`. Mathlib's
  projectivization is algebraic/topological, but no covering-map theorem links
  the unit sphere quotient to it and no projective-space fundamental-group
  theorem is present.

  The final clause is not determined by homology alone for arbitrary spaces;
  the manifold hypotheses invoke the classification of compact oriented
  surfaces, after which a cell decomposition and Seifert--van Kampen yield the
  displayed presentation. Mathlib provides neither surface classification nor
  a topological Seifert--van Kampen theorem. The homology record does not by
  itself construct an equivalence or presentation of `FundamentalGroup S x`.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, related
  artifacts (`t01A01`, `t01A04`, `t01J03`, `t03J01`, `t98J03`), Mathlib's
  fundamental-groupoid product, sphere, circle/AddCircle, projectivization,
  covering-map, presented-group, manifold, and singular-homology sources, and
  git history. Product preservation was found, but none of the factor/group or
  classification computations needed to apply it.
  -/
  sorry

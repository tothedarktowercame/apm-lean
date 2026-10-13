import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Blueprint for APM t91J03

The only unproved boundary is the geometric universal-cover theorem saying
that winding twice forces a collision.  The remaining two lemmas and the
frozen theorem are elementary wiring and are proved here.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t91J03_Annulus := Circle × Set.Icc (0 : ℝ) 1

def apm_t91J03_firstProjection : C(apm_t91J03_Annulus, Circle) :=
  ⟨Prod.fst, continuous_fst⟩

def apm_t91J03_circleMap
    (gamma : C(Circle, apm_t91J03_Annulus)) : C(Circle, Circle) :=
  apm_t91J03_firstProjection.comp gamma

abbrev apm_t91J03_H1Circle :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle))

def apm_t91J03_H1Map
    (gamma : C(Circle, apm_t91J03_Annulus)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (apm_t91J03_circleMap gamma))

def apm_t91J03_HasWindingNumber
    (gamma : C(Circle, apm_t91J03_Annulus)) (n : ℤ) : Prop :=
  ∃ orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ,
    ∀ a : apm_t91J03_H1Circle,
      orientation.hom (apm_t91J03_H1Map gamma a) =
        n * orientation.hom a

def apm_t91J03_height
    (gamma : C(Circle, apm_t91J03_Annulus)) (z : Circle) : ℝ :=
  (gamma z).2.1

/-- Distinct points of an embedded annular circle with equal circle coordinate
have unequal height. -/
lemma apm_t91J03_height_ne_of_circleMap_eq
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    {z w : Circle} (hzw : z ≠ w)
    (hprojection : apm_t91J03_circleMap gamma z =
      apm_t91J03_circleMap gamma w) :
    apm_t91J03_height gamma z ≠ apm_t91J03_height gamma w := by
  intro hheight
  apply hzw
  apply hgamma.injective
  apply Prod.ext
  · exact hprojection
  · exact Subtype.ext hheight

/-- **LIBRARY: annular winding-two collision.**

An embedded circle in the closed annulus whose first projection has homological
degree of absolute value two would contain two distinct parameter points with
the same annular coordinates.  Its intended proof lifts to `ℝ × I`; the two
components of the lifted curve are cyclically permuted by deck translation,
while planar separation orders them and forces that translation to fix them.
-/
theorem apm_t91J03_winding_two_forces_annulus_collision
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (n : ℤ) (hn : apm_t91J03_HasWindingNumber gamma n)
    (habs : n.natAbs = 2) :
    ∃ z w : Circle, z ≠ w ∧
      apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w ∧
      apm_t91J03_height gamma z = apm_t91J03_height gamma w := by
  sorry

/-- The final contradiction, once the geometric collision is available. -/
lemma apm_t91J03_no_two_of_forced_fiber_collision
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (hcollision : ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n →
      n.natAbs = 2 →
      ∃ z w : Circle, z ≠ w ∧
        apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w ∧
        apm_t91J03_height gamma z = apm_t91J03_height gamma w) :
    ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2 := by
  intro n hn habs
  obtain ⟨z, w, hzw, hprojection, hheight⟩ := hcollision n hn habs
  exact (apm_t91J03_height_ne_of_circleMap_eq gamma hgamma hzw hprojection)
    hheight

theorem apm_t91j03
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus)) :
    ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2 := by
  apply apm_t91J03_no_two_of_forced_fiber_collision gamma hgamma
  intro n hn habs
  exact apm_t91J03_winding_two_forces_annulus_collision gamma hgamma n hn habs

#print axioms apm_t91j03

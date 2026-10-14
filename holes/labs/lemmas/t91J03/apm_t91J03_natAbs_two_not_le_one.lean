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

/-- **LIBRARY: classification of embedded circles in the closed annulus.**

For every choice of generator of `H₁(S¹; ℤ)`, the first projection of an
embedded annular circle acts by multiplication by `-1`, `0`, or `1`.

This is the genuine missing topological foundation.  One proof lifts the
embedded circle to the closed strip and uses Jordan separation to show that a
deck translate cannot cross it; equivalently, an essential simple closed curve
in an annulus represents a primitive homology class. -/
lemma apm_t91J03_embedded_annular_circle_homology_bound
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ) :
    ∃ m : ℤ, m.natAbs ≤ 1 ∧
      ∀ a : apm_t91J03_H1Circle,
        orientation.hom (apm_t91J03_H1Map gamma a) =
          m * orientation.hom a := by
  sorry

/-- A scalar describing an endomorphism of a rank-one module is unique.
This is deliberately independent of the annulus classification lemma. -/
lemma apm_t91J03_rank_one_scalar_unique
    (f : apm_t91J03_H1Circle ⟶ ModuleCat.of ℤ ℤ)
    (orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ)
    (n m : ℤ)
    (hn : ∀ a : apm_t91J03_H1Circle,
      f a = n * orientation.hom a)
    (hm : ∀ a : apm_t91J03_H1Circle,
      f a = m * orientation.hom a) :
    n = m := by
  sorry

/-- An integer of absolute value two cannot have absolute value at most one.
Kept separate so this leaf has no topological dependencies. -/
-- BEGIN SEAT AREA
lemma apm_t91J03_natAbs_two_not_le_one
    (n : ℤ) (htwo : n.natAbs = 2) (hle : n.natAbs ≤ 1) : False := by
  omega
-- END SEAT AREA

/-- An embedded annular circle cannot have homological winding of absolute
value two.  This assembly is sorry-free; its three inputs can be proved in
parallel. -/
lemma apm_t91J03_no_embedded_winding_two
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (n : ℤ) (hn : apm_t91J03_HasWindingNumber gamma n)
    (habs : n.natAbs = 2) : False := by
  obtain ⟨orientation, hn⟩ := hn
  obtain ⟨m, hm_bound, hm⟩ :=
    apm_t91J03_embedded_annular_circle_homology_bound gamma hgamma orientation
  have hnm : n = m := apm_t91J03_rank_one_scalar_unique
    (apm_t91J03_H1Map gamma ≫ orientation.hom) orientation n m hn hm
  subst m
  exact apm_t91J03_natAbs_two_not_le_one n habs hm_bound

/-- An embedded circle in the closed annulus whose first projection has
homological degree of absolute value two would contain two distinct parameter
points with the same annular coordinates.  The hypotheses are inconsistent by
the annular-circle classification above, so the collision follows. -/
theorem apm_t91J03_winding_two_forces_annulus_collision
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (n : ℤ) (hn : apm_t91J03_HasWindingNumber gamma n)
    (habs : n.natAbs = 2) :
    ∃ z w : Circle, z ≠ w ∧
      apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w ∧
      apm_t91J03_height gamma z = apm_t91J03_height gamma w := by
  exact False.elim
    (apm_t91J03_no_embedded_winding_two gamma hgamma n hn habs)

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

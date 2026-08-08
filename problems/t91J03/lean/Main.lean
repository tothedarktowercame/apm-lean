import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t91J03 — an embedded circle cannot wrap twice around an annulus

The annulus is the concrete product `Circle × [0,1]`.  Winding is encoded as
the action on integral first singular homology of the curve followed by the
first-coordinate projection to `Circle`.

## Statement repairs

The former uninterpreted opaque winding-number constant is replaced by the
actual induced map on `H₁(Circle; ℤ)`.  An orientation isomorphism with `ℤ`
identifies that map with multiplication by the winding number.  The conclusion
uses `Int.natAbs`, so reversing the chosen orientation has no effect.

## Encoding questions

None.
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

/-- For an embedded annular circle, two distinct parameter points in the same
circle fiber must have different heights. This is the exact elementary
contradiction consumed after the universal-cover argument produces a forced
collision. -/
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

/-- A precise interface for the remaining geometric theorem: winding
absolute value two must force two distinct points with the same annular
coordinates. Once that universal-cover/Jordan separation result is supplied,
the frozen conclusion follows with no further homology or embedding
bookkeeping. -/
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
  /-
  CLOSER HOP 3 boundary. The exact final contradiction is now compiled in
  `apm_t91J03_height_ne_of_circleMap_eq`: injectivity of the frozen embedding
  says distinct parameter points with equal circle projection must have
  unequal interval coordinates. The wrapper
  `apm_t91J03_no_two_of_forced_fiber_collision` reduces the theorem to the
  single geometric assertion that winding absolute value two forces such an
  equal-projection/equal-height pair.

  The harvested proof obtains that collision indirectly in the universal
  cover `ℝ × I`: the preimage consists of two disjoint properly embedded
  lines cyclically permuted by deck translation, while Jordan separation
  orders those lines from bottom to top and forces the translation to fix
  them. Mathlib has circle-power covering maps and general lifting APIs, but
  no universal-cover classification by winding number, proper-line Jordan
  separation for the strip, or theorem that embedded annular circles have
  degree only `0`, `1`, or `-1`. Searches covered `LEMMA-INDEX.md`, every
  `ConstructionTargets/` module, Mathlib's circle, covering, lift,
  fundamental-group, singular-homology, Jordan-curve, and separation sources,
  related winding/annulus artifacts, and git history. None supplies that
  geometric bridge. The frozen statement is unchanged; no axiom or opaque
  placeholder was introduced.
  -/
  sorry

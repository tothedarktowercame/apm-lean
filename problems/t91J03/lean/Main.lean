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

theorem apm_t91j03
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus)) :
    ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2 := by
  sorry

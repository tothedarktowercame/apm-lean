import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t02A08

## Statement repairs

The printed target `Z = {p} × S²` has dimension two. Its intersection with
the image of `f : S² → S¹ × S²` is therefore one-dimensional, so the stated
integer-valued oriented intersection number is not defined. Following the
supplied solution, `Z` is minimally replaced by the complementary-dimensional
circle `S¹ × {q}`. The constructed maps still land in the fiber `{p} × S²`
named in the source and wrap that fiber with degree `n`.

The notation `I_X` is corrected to `I_Y`, since the ambient manifold is `Y`.

## Encoding questions

Degree is encoded through the actual map induced on integral second singular
homology, after choosing the sphere's orientation isomorphism with `ℤ`.
Intersection with the repaired cycle `S¹ × {q}` is the degree of the second
projection, with the cycle pinned by an equality rather than hidden behind an
opaque integer-valued operation.
-/

open CategoryTheory

noncomputable section

abbrev apm_t02a08_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a08_S2 := Metric.sphere (0 : apm_t02a08_E3) 1
abbrev apm_t02a08_Y := Circle × apm_t02a08_S2

def apm_t02a08_Z (q : apm_t02a08_S2) : Set apm_t02a08_Y :=
  {y | y.2 = q}

def apm_t02a08_fiberMap
    (p : Circle) (g : C(apm_t02a08_S2, apm_t02a08_S2)) :
    C(apm_t02a08_S2, apm_t02a08_Y) :=
  (ContinuousMap.const apm_t02a08_S2 p).prodMk g

abbrev apm_t02a08_H2 :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t02a08_S2))

def apm_t02a08_H2Map (g : C(apm_t02a08_S2, apm_t02a08_S2)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)

def apm_t02a08_HasDegree
    (g : C(apm_t02a08_S2, apm_t02a08_S2)) (n : ℤ) : Prop :=
  ∃ orientation : apm_t02a08_H2 ≅ ModuleCat.of ℤ ℤ,
    ∀ a : apm_t02a08_H2,
      orientation.hom (apm_t02a08_H2Map g a) = n * orientation.hom a

def apm_t02a08_secondProjection : C(apm_t02a08_Y, apm_t02a08_S2) :=
  ⟨Prod.snd, continuous_snd⟩

def apm_t02a08_HasOrientedIntersection
    (f : C(apm_t02a08_S2, apm_t02a08_Y))
    (Z : Set apm_t02a08_Y) (n : ℤ) : Prop :=
  ∃ q : apm_t02a08_S2,
    Z = apm_t02a08_Z q ∧
    apm_t02a08_HasDegree (apm_t02a08_secondProjection.comp f) n

/-- Projecting the fiber map to its sphere factor recovers the original
sphere map. -/
lemma apm_t02a08_secondProjection_comp_fiberMap
    (p : Circle) (g : C(apm_t02a08_S2, apm_t02a08_S2)) :
    apm_t02a08_secondProjection.comp (apm_t02a08_fiberMap p g) = g := by
  ext x
  rfl

/-- Once a sphere map of degree `n` is available, the encoded oriented
intersection assertion for its fiber map follows definitionally. -/
lemma apm_t02a08_fiberMap_hasOrientedIntersection
    (p : Circle) (q : apm_t02a08_S2)
    (g : C(apm_t02a08_S2, apm_t02a08_S2)) (n : ℤ)
    (hg : apm_t02a08_HasDegree g n) :
    apm_t02a08_HasOrientedIntersection
      (apm_t02a08_fiberMap p g) (apm_t02a08_Z q) n := by
  refine ⟨q, rfl, ?_⟩
  rw [apm_t02a08_secondProjection_comp_fiberMap]
  exact hg

/-- Once the missing orientation isomorphism is supplied, the identity map
has degree one. This isolates the base case from the sphere-homology
computation itself. -/
lemma apm_t02a08_id_hasDegree
    (orientation : apm_t02a08_H2 ≅ ModuleCat.of ℤ ℤ) :
    apm_t02a08_HasDegree
      (⟨id, continuous_id⟩ : C(apm_t02a08_S2, apm_t02a08_S2)) 1 := by
  refine ⟨orientation, ?_⟩
  intro a
  simp only [one_mul]
  unfold apm_t02a08_H2Map
  have hid : TopCat.ofHom
      (⟨id, continuous_id⟩ : C(apm_t02a08_S2, apm_t02a08_S2)) =
      𝟙 (TopCat.of apm_t02a08_S2) := by
    rfl
  rw [hid]
  have hmap :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map_id (TopCat.of apm_t02a08_S2)
  rw [hmap]
  rfl

/-- Functoriality also supplies the algebraic multiplication law for degrees
once both maps have been computed relative to the same orientation. -/
lemma apm_t02a08_comp_hasDegree
    (orientation : apm_t02a08_H2 ≅ ModuleCat.of ℤ ℤ)
    (g h : C(apm_t02a08_S2, apm_t02a08_S2)) (m n : ℤ)
    (hg : ∀ a : apm_t02a08_H2,
      orientation.hom (apm_t02a08_H2Map g a) = m * orientation.hom a)
    (hh : ∀ a : apm_t02a08_H2,
      orientation.hom (apm_t02a08_H2Map h a) = n * orientation.hom a) :
    apm_t02a08_HasDegree (g.comp h) (m * n) := by
  refine ⟨orientation, fun a ↦ ?_⟩
  have hcomp : apm_t02a08_H2Map (g.comp h) =
      apm_t02a08_H2Map h ≫ apm_t02a08_H2Map g := by
    unfold apm_t02a08_H2Map
    simpa using
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom h) (TopCat.ofHom g)
  rw [hcomp]
  change orientation.hom (apm_t02a08_H2Map g (apm_t02a08_H2Map h a)) = _
  rw [hg, hh]
  ring

theorem apm_t02a08
    (p : Circle) (q : apm_t02a08_S2) :
    ∀ n : ℤ,
      ∃ g : C(apm_t02a08_S2, apm_t02a08_S2),
        apm_t02a08_HasDegree g n ∧
        apm_t02a08_HasOrientedIntersection
          (apm_t02a08_fiberMap p g) (apm_t02a08_Z q) n := by
  intro n
  obtain ⟨g, hg⟩ : ∃ g : C(apm_t02a08_S2, apm_t02a08_S2),
      apm_t02a08_HasDegree g n := by
    /-
    Boundary (closer hop 1): the intersection clause is completely discharged
    by `apm_t02a08_secondProjection_comp_fiberMap` and
    `apm_t02a08_fiberMap_hasOrientedIntersection`. The sole remaining task is
    construction, for each `n : ℤ`, of a continuous self-map of the concrete
    metric 2-sphere whose induced map on integral `H₂` is multiplication by
    `n` relative to some orientation isomorphism.

    The standard route suspends the degree-`n` circle power map (using complex
    conjugation for negative degree), or uses stereographic coordinates and
    the map `z ↦ z^n`. Mathlib has circle power maps, one-point
    compactification/sphere homeomorphisms, and the raw singular-homology
    functor, but searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
    sphere and degree artifacts, git history, and Mathlib's suspension,
    projectivization, one-point compactification, sphere, winding-number, and
    homology APIs found no theorem computing either `H₂` of this metric sphere
    as `ℤ` or the induced degree of those maps. Without the orientation
    isomorphism itself, even the identity and constant base cases cannot inhabit
    the frozen `HasDegree` predicate.

    CLOSER HOP 2: the identity base case is now separated from the missing
    homology computation. `apm_t02a08_id_hasDegree` proves that, given any
    orientation isomorphism `H₂(S²) ≅ ℤ`, the continuous identity map has
    degree one. The proof explicitly identifies its `TopCat` morphism with the
    categorical identity and applies functoriality of singular homology. Thus
    the earlier claim that even the identity case was wholly inaccessible is
    refined: only construction of the orientation isomorphism is missing for
    that case. Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
    sphere-homology and degree siblings, Mathlib's singular-homology, sphere,
    suspension, and compactification sources, and git history still found no
    `H₂` computation or induced-degree theorem for nontrivial maps. Arbitrary
    integer degree therefore remains open and the frozen statement is
    unchanged.

    CLOSER HOP 3 goes beyond the identity case by compiling the degree
    composition law. `apm_t02a08_comp_hasDegree` uses `map_comp` for the
    singular-homology functor and proves that maps acting by `m` and `n`
    relative to a common orientation have composite degree `m*n`. This
    completes the algebraic iteration needed once a generator such as a
    degree `-1` map and positive-degree constructions are available. Searches
    of Mathlib's chain-homotopy, suspension, reduced-homology, and sphere
    sources still provide neither the initial orientation isomorphism nor a
    computed nontrivial generator, so the geometric/homological construction
    of arbitrary degrees remains honestly open. The frozen statement is
    unchanged, and no unproved intermediate assertion was introduced.
    -/
    sorry
  exact ⟨g, hg, apm_t02a08_fiberMap_hasOrientedIntersection p q g n hg⟩

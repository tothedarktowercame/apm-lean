import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01A02

## Statement repairs

The former part (a) used an opaque `H₂` type and an axiom to install its group
structure. It is replaced by Mathlib's integral singular homology functor and
the actual morphism induced by `f`. No source claim is changed.

## Encoding questions

The torus and the four-sheeted map are concrete: `Circle × Circle` and
`(z,w) ↦ (z²,w²)`. The covering group is characterized by a free,
fiber-transitive `(Z/2)²` action.
-/

open CategoryTheory

abbrev apm_t01A02_Torus := Circle × Circle
abbrev apm_t01A02_Deck := ZMod 2 × ZMod 2

noncomputable section

/-- The double-in-each-coordinate torus covering. -/
def apm_t01A02_cover (x : apm_t01A02_Torus) : apm_t01A02_Torus :=
  (x.1 ^ 2, x.2 ^ 2)

/-- A regular covering whose deck group is `G`. -/
def apm_t01A02_hasCoveringGroup
    {S T G : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [AddGroup G] (p : S → T) : Prop :=
  IsCoveringMap p ∧
  ∃ act : G → S → S,
    (∀ x, act 0 x = x) ∧
    (∀ g h x, act (g + h) x = act g (act h x)) ∧
    (∀ g, Continuous (act g)) ∧
    (∀ g x, p (act g x) = p x) ∧
    (∀ g x, act g x = x → g = 0) ∧
    (∀ x y, p x = p y ↔ ∃ g, act g x = y)

abbrev apm_t01A02_H2 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The map induced on integral second homology. -/
def apm_t01A02_H2map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

lemma apm_t01A02_cover_continuous : Continuous apm_t01A02_cover := by
  unfold apm_t01A02_cover
  fun_prop

lemma apm_t01A02_cover_eq_prod_pow_two (x : apm_t01A02_Torus) :
    apm_t01A02_cover x = (x.1 ^ 2, x.2 ^ 2) := rfl

/-- Mathlib's quotient-covering theorem for powers on `Circle` directly gives
the double cover needed in each coordinate. -/
lemma apm_t01A02_isCoveringMap_circle_pow_two :
    IsCoveringMap (fun z : Circle ↦ z ^ 2) := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  exact (Circle.isQuotientCoveringMap_npow 2).isCoveringMap

/-- Coordinatewise squaring is surjective on the torus. -/
lemma apm_t01A02_cover_surjective : Function.Surjective apm_t01A02_cover := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hsurj : Function.Surjective (fun z : Circle ↦ z ^ 2) :=
    (Circle.isQuotientCoveringMap_npow 2).surjective
  rintro ⟨z, w⟩
  rcases hsurj z with ⟨z', hz'⟩
  rcases hsurj w with ⟨w', hw'⟩
  exact ⟨(z', w'), by simp [apm_t01A02_cover, hz', hw']⟩

/-- The antipodal point on the circle. -/
def apm_t01A02_antipode (z : Circle) : Circle :=
  ⟨-(z : ℂ), by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using z.property⟩

/-- The only points of the circle with the same square are antipodal points.
This is the algebraic kernel calculation needed for the four deck
transformations of the product cover. -/
lemma apm_t01A02_circle_sq_eq_sq_iff (z w : Circle) :
    z ^ 2 = w ^ 2 ↔ z = w ∨ z = apm_t01A02_antipode w := by
  constructor
  · intro h
    have hc : (z : ℂ) ^ 2 = (w : ℂ) ^ 2 := by
      exact_mod_cast h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hzw | hzw
    · exact Or.inl (Subtype.ext hzw)
    · right
      apply Subtype.ext
      exact hzw
  · rintro (rfl | rfl)
    · rfl
    · ext
      simp [apm_t01A02_antipode]

/-- Equality in a fiber of the torus squaring map is independently equality
or antipodality in the two circle coordinates. -/
lemma apm_t01A02_cover_eq_iff (x y : apm_t01A02_Torus) :
    apm_t01A02_cover x = apm_t01A02_cover y ↔
      (x.1 = y.1 ∨ x.1 = apm_t01A02_antipode y.1) ∧
      (x.2 = y.2 ∨ x.2 = apm_t01A02_antipode y.2) := by
  simp only [apm_t01A02_cover, Prod.mk.injEq]
  exact and_congr (apm_t01A02_circle_sq_eq_sq_iff x.1 y.1)
    (apm_t01A02_circle_sq_eq_sq_iff x.2 y.2)

theorem apm_t01a02 :
    ∀ f : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ¬Function.Surjective f →
      apm_t01A02_H2map f = 0 ∧
      apm_t01A02_hasCoveringGroup
        (G := apm_t01A02_Deck) apm_t01A02_cover ∧
      ((∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
          ∀ x, f x = apm_t01A02_cover (g x)) →
        ∃ x, f x = x) := by
  /-
  CLOSER HOP 1 boundary. The concrete map's continuity is now compiled as
  `apm_t01A02_cover_continuous`. Desk research found the nearby Mathlib theorem
  `isCoveringMap_npow 2` in `Analysis.Complex.CoveringMap`, proving squaring is
  a covering of the punctured complex plane. To obtain the frozen torus cover
  one must restrict this map to `Circle`, prove the preimage of `Circle` is
  exactly `Circle`, transport across the subtype homeomorphism, and construct
  the product of the two resulting covering maps. No product theorem for
  `IsCoveringMap` or packaged circle-power covering was found.

  The deck action can then be defined by coordinatewise multiplication by
  `±1`, indexed by `(ZMod 2)²`; freeness and fiber transitivity require the
  classification `z² = w² ↔ z = w ∨ z = -w` inside `Circle`. Searches of
  `LEMMA-INDEX.md`, all construction modules, closed circle/covering artifacts,
  and git history found no assembled declaration for that action.

  The first and last conjuncts are deeper: Mathlib does not compute integral
  `H₂` of `Circle × Circle`, does not expose degree/nonsurjectivity for this
  singular-homology morphism, and has no torus Lefschetz fixed-point theorem.
  The intended fixed-point route uses that a lift through the four-sheeted
  cover makes the induced degree divisible by four, while nonsurjectivity
  forces degree zero, giving nonzero Lefschetz number. Neither bridge is
  packaged in the closed corpus. Thus continuity is closed, while the
  restriction/product covering, deck action, homology degree, and fixed-point
  assemblies remain open.

  CLOSER HOP 2: the prior restriction claim is obsolete in the current
  Mathlib.  `Circle.isQuotientCoveringMap_npow 2` directly proves the circle
  squaring quotient cover.  The helpers
  `apm_t01A02_isCoveringMap_circle_pow_two` and
  `apm_t01A02_cover_surjective` now compile the coordinate covering and
  surjectivity of the concrete torus map.  Mathlib's
  `IsOpenQuotientMap.prodMap` combines the underlying open quotient maps, but
  no product constructor for `IsCoveringMap` or evenly-covered neighborhoods
  was found.  Finishing the middle conjunct still requires assembling those
  product trivializations and identifying the product of the two power-map
  kernels with `(ZMod 2)²`.  Searches of the newer Circle quotient-cover API
  did not uncover any torus `H₂` computation or Lefschetz theorem, so the first
  and last conjuncts retain the deeper hop-1 boundary.

  CLOSER HOP 3: the kernel classification is now compiled rather than merely
  proposed. `apm_t01A02_antipode` bundles complex negation on `Circle`,
  `apm_t01A02_circle_sq_eq_sq_iff` proves that equal squares are exactly equal
  or antipodal points, and `apm_t01A02_cover_eq_iff` applies this independently
  to both torus coordinates. This identifies every fiber set-theoretically
  with its four sign choices and discharges the algebraic ingredient needed
  for fiber transitivity. A renewed search of the covering sources, lemma
  index, construction modules, all problem artifacts, and git history still
  found no product-cover constructor; directly building one requires pairing
  the two local trivializations and reconciling their fiber index types.
  Neither the singular-homology corpus nor prior torus artifacts supplies the
  independent `H₂` degree or Lefschetz bridges. Thus the four-point fiber
  classification is closed, but the product trivialization/deck action and
  the two global algebraic-topology conjuncts remain open.
  -/
  sorry

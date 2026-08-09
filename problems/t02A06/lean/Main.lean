import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t02A06

## Statement repairs

For part (a), the two great circles are required to be distinct; otherwise
their oriented intersection number is not defined by transverse point-counting.
In part (c), “a degree map” is read as “a map of nonzero degree”. Without
“nonzero”, every continuous map between the stated oriented manifolds has a
degree and the assertion would be vacuous rather than the intended question.

## Encoding questions

The intersection is the actual subtype of the two great circles, with local
sign determined by the cross product of their oriented normals. Part (b) is
strengthened to the nonexistence of a homeomorphism. In part (c), degree zero
is expressed without a placeholder as vanishing of the actual induced map on
integral third singular homology.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t02a06_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev apm_t02a06_S1 := apm_t02a06_Sphere 1
abbrev apm_t02a06_S2 := apm_t02a06_Sphere 2
abbrev apm_t02a06_S3 := apm_t02a06_Sphere 3
abbrev apm_t02a06_S4 := apm_t02a06_Sphere 4
abbrev apm_t02a06_T3 := apm_t02a06_S1 × apm_t02a06_S1 × apm_t02a06_S1

def apm_t02a06_greatCircle (normal : apm_t02a06_S2) : Set apm_t02a06_S2 :=
  {x | inner ℝ (x : EuclideanSpace ℝ (Fin 3)) normal = 0}

abbrev apm_t02a06_intersection (normal₁ normal₂ : apm_t02a06_S2) :=
  {x : apm_t02a06_S2 //
    x ∈ apm_t02a06_greatCircle normal₁ ∩ apm_t02a06_greatCircle normal₂}

def apm_t02a06_localSign {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) : ℤ :=
  if 0 < dotProduct
      (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))
      (x.1 : Fin 3 → ℝ) then 1 else -1

def apm_t02a06_signedIntersection {normal₁ normal₂ : apm_t02a06_S2}
    (e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂) : ℤ :=
  ∑ i : Fin 2, apm_t02a06_localSign (e i)

lemma apm_t02a06_localSign_eq_one_or_neg_one
    {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) :
    apm_t02a06_localSign x = 1 ∨ apm_t02a06_localSign x = -1 := by
  unfold apm_t02a06_localSign
  split_ifs <;> simp

/-- Reuses the two-term cancellation pattern proved in sibling `t01A07`. -/
lemma apm_t02a06_signedIntersection_eq_zero_of_opposite
    {normal₁ normal₂ : apm_t02a06_S2}
    (e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂)
    (h : apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1)) :
    apm_t02a06_signedIntersection e = 0 := by
  rw [apm_t02a06_signedIntersection, Fin.sum_univ_two, h]
  omega

/-- Antipodal negation preserves the common intersection of two great
circles. -/
def apm_t02a06_intersectionAntipodal
    {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) :
    apm_t02a06_intersection normal₁ normal₂ := by
  refine ⟨⟨-(x.1 : EuclideanSpace ℝ (Fin 3)), ?_⟩, ?_⟩
  · simpa [mem_sphere_zero_iff_norm] using x.1.property
  · rcases x.2 with ⟨hx₁, hx₂⟩
    constructor <;> simp only [apm_t02a06_greatCircle, Set.mem_setOf_eq] at hx₁ hx₂ ⊢
    · simpa using congrArg Neg.neg hx₁
    · simpa using congrArg Neg.neg hx₂

@[simp] lemma apm_t02a06_intersectionAntipodal_coe
    {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) :
    ((apm_t02a06_intersectionAntipodal x).1 : EuclideanSpace ℝ (Fin 3)) =
      -(x.1 : EuclideanSpace ℝ (Fin 3)) := rfl

/-- Antipodal negation is an involutive permutation of the common
intersection. -/
def apm_t02a06_intersectionAntipodalEquiv
    (normal₁ normal₂ : apm_t02a06_S2) :
    apm_t02a06_intersection normal₁ normal₂ ≃
      apm_t02a06_intersection normal₁ normal₂ where
  toFun := apm_t02a06_intersectionAntipodal
  invFun := apm_t02a06_intersectionAntipodal
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The antipodal involution has no fixed point on the unit-sphere
intersection. Thus every common point already supplies two distinct points. -/
lemma apm_t02a06_intersectionAntipodal_ne
    {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂) :
    apm_t02a06_intersectionAntipodal x ≠ x := by
  intro h
  have hv : -(x.1 : EuclideanSpace ℝ (Fin 3)) = x.1 := by
    exact congrArg (fun y : apm_t02a06_intersection normal₁ normal₂ =>
      (y.1 : EuclideanSpace ℝ (Fin 3))) h
  have hadd : (x.1 : EuclideanSpace ℝ (Fin 3)) + x.1 = 0 := by
    calc
      (x.1 : EuclideanSpace ℝ (Fin 3)) + x.1 = -x.1 + x.1 :=
        congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y + x.1) hv.symm
      _ = 0 := neg_add_cancel _
  have htwo : (2 : ℝ) • (x.1 : EuclideanSpace ℝ (Fin 3)) = 0 := by
    simpa [two_smul ℝ] using hadd
  have hx0 : (x.1 : EuclideanSpace ℝ (Fin 3)) = 0 := by
    rcases smul_eq_zero.mp htwo with h2 | hx
    · norm_num at h2
    · exact hx
  have hnorm : ‖(x.1 : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.1.property
  rw [hx0, norm_zero] at hnorm
  norm_num at hnorm

/-- At a transverse common point, antipodal negation reverses the local
intersection sign. -/
lemma apm_t02a06_localSign_antipodal
    {normal₁ normal₂ : apm_t02a06_S2}
    (x : apm_t02a06_intersection normal₁ normal₂)
    (hne : dotProduct
      (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))
      (x.1 : Fin 3 → ℝ) ≠ 0) :
    apm_t02a06_localSign (apm_t02a06_intersectionAntipodal x) =
      -apm_t02a06_localSign x := by
  let d := dotProduct
    (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))
    (x.1 : Fin 3 → ℝ)
  have hdot : dotProduct
      (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))
      ((apm_t02a06_intersectionAntipodal x).1 : Fin 3 → ℝ) = -d := by
    simp [d, dotProduct]
  have hdne : d ≠ 0 := hne
  unfold apm_t02a06_localSign
  rw [hdot]
  change (if 0 < -d then 1 else -1) = -(if 0 < d then 1 else -1)
  by_cases hd : 0 < d
  · simp [hd, not_lt.mpr hd.le]
  · have hdneg : d < 0 := lt_of_le_of_ne (not_lt.mp hd) hdne
    have hnegpos : 0 < -d := neg_pos.mpr hdneg
    simp [hd, hnegpos]

abbrev apm_t02a06_H3 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t02a06_H3Map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

/-- Why this unblocks the first conjunct of `apm_t02a06`: it is the missing
classification of the common unit vectors orthogonal to two nonproportional
unit normals.  The existing opposite-sign lemma and two-term cancellation
then supply the remaining signed-intersection assertion. -/
theorem apm_t02A06_bridge_1 :
    ∀ normal₁ normal₂ : apm_t02a06_S2,
      apm_t02a06_greatCircle normal₁ ≠ apm_t02a06_greatCircle normal₂ →
        ∃ e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂,
          apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1) := by
  sorry

/-- Why this unblocks the second conjunct of `apm_t02a06`: it is the exact
topological consequence of the missing computations
`H₂(S² × S²; ℤ) ≅ ℤ²` and `H₂(S⁴; ℤ) = 0`. -/
theorem apm_t02A06_bridge_2 :
    ¬ Nonempty ((apm_t02a06_S2 × apm_t02a06_S2) ≃ₜ apm_t02a06_S4) := by
  sorry

/-- Why this unblocks the third conjunct of `apm_t02a06`: every map from
`S³` to `T³` lifts to the contractible universal cover `ℝ³` and is therefore
nullhomotopic; this packages the resulting homology-map vanishing in exactly
the functorial form needed here. -/
theorem apm_t02A06_bridge_3 :
    ∀ f : C(apm_t02a06_S3, apm_t02a06_T3), apm_t02a06_H3Map f = 0 := by
  sorry

theorem apm_t02a06 :
    (∀ normal₁ normal₂ : apm_t02a06_S2,
      apm_t02a06_greatCircle normal₁ ≠ apm_t02a06_greatCircle normal₂ →
        ∃ e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂,
          apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1) ∧
          apm_t02a06_signedIntersection e = 0) ∧
    (¬Nonempty ((apm_t02a06_S2 × apm_t02a06_S2) ≃ₜ apm_t02a06_S4)) ∧
    (∀ f : C(apm_t02a06_S3, apm_t02a06_T3),
      apm_t02a06_H3Map f = 0) := by
  /-
  CLOSER HOP 1 boundary. Following the compiled sibling `t01A07`, the local-
  sign dichotomy and the final two-term cancellation are now proved above as
  `apm_t02a06_localSign_eq_one_or_neg_one` and
  `apm_t02a06_signedIntersection_eq_zero_of_opposite`.

  For the first conjunct, distinct great-circle sets must be converted into
  linear independence of their unit normals. Then their cross product is
  nonzero, its normalization and negative give the two intersection points,
  and orthogonal-complement dimension one proves exhaustiveness. Mathlib has
  `crossProduct` identities and finite-dimensional orthogonal-complement
  theory, but no theorem assembling this subtype equivalence or converting
  equality of the two great-circle zero sets into proportional normals.

  The second and third conjuncts are homological. The intended proofs use
  `H₂(S² × S²) ≅ ℤ²` versus `H₂(S⁴) = 0`, and `H₃(T³) = 0`, respectively.
  Mathlib's singular-homology functor is present, but searches found neither
  integral homology computations for metric spheres nor a Künneth theorem
  yielding the required product groups. Without those computations,
  homeomorphism invariance and functoriality alone cannot close either claim.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/` modules,
  closed sphere/homology/intersection artifacts (including `t01A07`),
  Mathlib's cross-product, orthogonal-complement, singular-homology, Künneth,
  and sphere sources, and git history. Only the elementary signed-sum pattern
  was reusable; the geometric classification and homology bridges remain.

  CLOSER HOP 2 progress. Antipodal negation is now bundled directly on the
  common-intersection subtype as `apm_t02a06_intersectionAntipodal` and the
  involutive equivalence `apm_t02a06_intersectionAntipodalEquiv`. The lemma
  `apm_t02a06_localSign_antipodal` proves, by an explicit dot-product
  calculation, that the two antipodal points have opposite local signs
  whenever the cross-product pairing at one point is nonzero. Thus the sign
  and cancellation portion no longer depends on choosing normalized cross-
  product coordinates.

  The remaining first-conjunct boundary is narrower: from inequality of the
  two great-circle zero sets, prove that the normals are not proportional;
  deduce their cross product is nonzero; and prove every unit vector
  orthogonal to both normals is one of the two antipodal normalized cross-
  product vectors. Renewed searches of the cross-product determinant lemmas,
  `Submodule.finrank_orthogonal_span`, one-dimensional submodule APIs, and
  `LinearIndependent`/Gram determinant sources found ingredients but no
  packaged subtype-cardinality or normalization theorem. The two homology
  conjuncts remain unchanged: no sphere computation or Künneth bridge was
  found in the newly consulted sphere-product and torus artifacts.

  CLOSER HOP 3: the antipodal pairing is now proved genuinely two-point at
  every common intersection point. `apm_t02a06_intersectionAntipodal_ne`
  proves the involution has no fixed point: equality with the antipode forces
  the ambient Euclidean vector to be zero, contradicting its unit norm. Thus
  existence of one intersection point automatically supplies a distinct
  antipodal partner; only existence and exhaustiveness remain in the first
  conjunct. Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
  cross-product/projectivization lemmas, finite-dimensional orthogonal
  complements, all problem artifacts, singular homology, and git history
  found `mk_eq_mk_iff_crossProduct_eq_zero` and
  `finrank_orthogonal_span_singleton`, but no compiled chain converting
  inequality of these zero-set subtypes into nonproportional normals and then
  classifying the common unit vectors. No metric-sphere homology computation
  or Künneth theorem appeared. The exhaustiveness and both homological
  conjuncts therefore remain open; the frozen statement is unchanged.
  -/
  sorry

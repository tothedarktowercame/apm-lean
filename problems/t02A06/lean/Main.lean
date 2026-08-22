import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.T02A06SphereOne
import ConstructionTargets.SimplyConnectedOpenCover
import ConstructionTargets.SingularHomologyHomotopy

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
open ConstructionTargets.SingularHomologyHomotopy

noncomputable section

abbrev apm_t02a06_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev apm_t02a06_S1 := apm_t02a06_Sphere 1
abbrev apm_t02a06_S2 := apm_t02a06_Sphere 2
abbrev apm_t02a06_S3 := apm_t02a06_Sphere 3
abbrev apm_t02a06_S4 := apm_t02a06_Sphere 4
abbrev apm_t02a06_T3 := apm_t02a06_S1 × apm_t02a06_S1 × apm_t02a06_S1

/-- The problem's own encoding of `S³` is simply connected. -/
theorem apm_t02a06_simplyConnectedSpace_S3 :
    SimplyConnectedSpace apm_t02a06_S3 := by
  let v : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv0 : v ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 4) ↦ x 0) h
    simpa [v] using this
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
    ⟨by simp [Module.finrank_fin_fun]⟩
  have hfin : Module.finrank ℝ (ℝ ∙ v)ᗮ = 3 :=
    Submodule.finrank_orthogonal_span_singleton hv0
  apply simplyConnectedSpace_sphere_of_pole v hv
  rw [← Module.finrank_eq_rank, hfin]
  norm_num

/-- The problem's Euclidean two-coordinate unit circle, identified with
Mathlib's complex unit circle by the standard orthonormal basis `(1, i)`. -/
def apm_t02a06_euclideanCircleHomeomorph : apm_t02a06_S1 ≃ₜ Circle := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph
  exact e.subtype fun x ↦ by
    change x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      e x ∈ Submonoid.unitSphere ℂ
    rw [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ e x ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- The universal covering of `AddCircle (2π)` transported to the problem's
Euclidean-coordinate circle. -/
theorem apm_t02a06_isCoveringMap_euclideanCircle :
    IsCoveringMap
      (apm_t02a06_euclideanCircleHomeomorph.symm ∘
        AddCircle.homeomorphCircle' ∘
        ((↑) : ℝ → AddCircle (2 * Real.pi))) :=
  ((AddCircle.isCoveringMap_coe (2 * Real.pi)).homeomorph_comp
    AddCircle.homeomorphCircle').homeomorph_comp
      apm_t02a06_euclideanCircleHomeomorph.symm

#print axioms apm_t02a06_simplyConnectedSpace_S3
#print axioms apm_t02a06_euclideanCircleHomeomorph
#print axioms apm_t02a06_isCoveringMap_euclideanCircle

/-- The problem's metric-sphere encoding of `S³` is locally path-connected,
via its standard three-dimensional Euclidean atlas. -/
@[reducible] def apm_t02a06_locPathConnectedSpace_S3 :
    LocPathConnectedSpace apm_t02a06_S3 :=
  ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) apm_t02a06_S3

/-- Every map from the problem's `S³` to its Euclidean circle has a continuous
real lift through the transported universal covering. -/
theorem apm_t02a06_exists_real_lift (g : C(apm_t02a06_S3, apm_t02a06_S1)) :
    ∃ G : C(apm_t02a06_S3, ℝ),
      (apm_t02a06_euclideanCircleHomeomorph.symm ∘
        AddCircle.homeomorphCircle' ∘
        ((↑) : ℝ → AddCircle (2 * Real.pi))) ∘ G = g := by
  letI : SimplyConnectedSpace apm_t02a06_S3 :=
    apm_t02a06_simplyConnectedSpace_S3
  letI : LocPathConnectedSpace apm_t02a06_S3 :=
    apm_t02a06_locPathConnectedSpace_S3
  let p : ℝ → apm_t02a06_S1 :=
    apm_t02a06_euclideanCircleHomeomorph.symm ∘
      AddCircle.homeomorphCircle' ∘
      ((↑) : ℝ → AddCircle (2 * Real.pi))
  have hp : IsCoveringMap p := apm_t02a06_isCoveringMap_euclideanCircle
  have hpsurj : Function.Surjective p :=
    apm_t02a06_euclideanCircleHomeomorph.symm.surjective.comp
      (AddCircle.homeomorphCircle'.surjective.comp QuotientAddGroup.mk_surjective)
  let a₀ : apm_t02a06_S3 := Classical.choice inferInstance
  obtain ⟨e₀, he₀⟩ := hpsurj (g a₀)
  obtain ⟨G, hG, -⟩ := hp.existsUnique_continuousMap_lifts g a₀ e₀ he₀
  exact ⟨G, hG.2⟩

#print axioms apm_t02a06_locPathConnectedSpace_S3
#print axioms apm_t02a06_exists_real_lift

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

lemma apm_t02a06_normal_ne_zero (normal : apm_t02a06_S2) :
    (normal : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
  intro h
  have hnorm : ‖(normal : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using normal.property
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

lemma apm_t02a06_normal_coe_ne_zero (normal : apm_t02a06_S2) :
    (normal : Fin 3 → ℝ) ≠ 0 := by
  intro h
  apply apm_t02a06_normal_ne_zero normal
  ext i
  exact congrFun h i

/-- Unequal great-circle zero sets force the unit normals to be genuinely
nonproportional.  In particular, this excludes antipodal normals, not merely
equal normals. -/
theorem apm_t02a06_normals_nonproportional
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    ¬ ∃ r : ℝ, (normal₁ : Fin 3 → ℝ) =
      r • (normal₂ : Fin 3 → ℝ) := by
  rintro ⟨r, hr⟩
  have hrE : (normal₁ : EuclideanSpace ℝ (Fin 3)) =
      r • (normal₂ : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    exact congrFun hr i
  have hr0 : r ≠ 0 := by
    intro hz
    apply apm_t02a06_normal_ne_zero normal₁
    rw [hrE, hz, zero_smul]
  apply hcircles
  ext x
  change inner ℝ (x : EuclideanSpace ℝ (Fin 3)) normal₁ = 0 ↔
    inner ℝ (x : EuclideanSpace ℝ (Fin 3)) normal₂ = 0
  rw [hrE, inner_smul_right]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hr0
  · intro h
    rw [h, mul_zero]

/-- Distinct great-circle zero sets therefore have a nonzero cross product of
their actual normals. -/
theorem apm_t02a06_crossProduct_ne_zero
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ) ≠ 0 := by
  rw [crossProduct_ne_zero_iff_linearIndependent,
    LinearIndependent.pair_symm_iff,
    LinearIndependent.pair_iff' (apm_t02a06_normal_coe_ne_zero normal₂)]
  intro r
  exact fun h ↦ apm_t02a06_normals_nonproportional normal₁ normal₂ hcircles ⟨r, h.symm⟩

/-- The cross product, regarded as a Euclidean vector and normalized to unit
length. -/
noncomputable def apm_t02a06_normalizedCrossVector
    (normal₁ normal₂ : apm_t02a06_S2) : EuclideanSpace ℝ (Fin 3) :=
  ‖WithLp.toLp 2 (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))‖⁻¹ •
    WithLp.toLp 2 (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))

theorem apm_t02a06_normalizedCrossVector_norm
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    ‖apm_t02a06_normalizedCrossVector normal₁ normal₂‖ = 1 := by
  let c := crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ)
  have hc : c ≠ 0 := apm_t02a06_crossProduct_ne_zero normal₁ normal₂ hcircles
  have hcLp : (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    apply hc
    have hof := congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ WithLp.ofLp z) h
    simpa using hof
  have hnorm : ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hcLp
  rw [apm_t02a06_normalizedCrossVector]
  change ‖‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖⁻¹ • WithLp.toLp 2 c‖ = 1
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]

/-- The normalized cross product as a point of the problem's unit sphere. -/
noncomputable def apm_t02a06_crossPoint
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) : apm_t02a06_S2 :=
  ⟨apm_t02a06_normalizedCrossVector normal₁ normal₂, by
    simpa [mem_sphere_zero_iff_norm] using
      apm_t02a06_normalizedCrossVector_norm normal₁ normal₂ hcircles⟩

/-- Its antipode, also packaged as a unit-sphere point. -/
noncomputable def apm_t02a06_negCrossPoint
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) : apm_t02a06_S2 :=
  ⟨-apm_t02a06_normalizedCrossVector normal₁ normal₂, by
    rw [mem_sphere_zero_iff_norm, norm_neg,
      apm_t02a06_normalizedCrossVector_norm normal₁ normal₂ hcircles]⟩

theorem apm_t02a06_crossPoint_mem_both
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_crossPoint normal₁ normal₂ hcircles ∈
      apm_t02a06_greatCircle normal₁ ∩ apm_t02a06_greatCircle normal₂ := by
  constructor
  · change inner ℝ
      (‖WithLp.toLp 2 (crossProduct (normal₁ : Fin 3 → ℝ)
        (normal₂ : Fin 3 → ℝ))‖⁻¹ •
        WithLp.toLp 2 (crossProduct (normal₁ : Fin 3 → ℝ)
          (normal₂ : Fin 3 → ℝ)))
      (WithLp.toLp 2 (normal₁ : Fin 3 → ℝ)) = 0
    rw [inner_smul_left]
    change (starRingEnd ℝ) _ * dotProduct (normal₁ : Fin 3 → ℝ)
      (star (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))) = 0
    simp [dotProduct_comm]
  · change inner ℝ
      (‖WithLp.toLp 2 (crossProduct (normal₁ : Fin 3 → ℝ)
        (normal₂ : Fin 3 → ℝ))‖⁻¹ •
        WithLp.toLp 2 (crossProduct (normal₁ : Fin 3 → ℝ)
          (normal₂ : Fin 3 → ℝ)))
      (WithLp.toLp 2 (normal₂ : Fin 3 → ℝ)) = 0
    rw [inner_smul_left]
    change (starRingEnd ℝ) _ * dotProduct (normal₂ : Fin 3 → ℝ)
      (star (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))) = 0
    simp [dotProduct_comm]

theorem apm_t02a06_negCrossPoint_mem_both
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_negCrossPoint normal₁ normal₂ hcircles ∈
      apm_t02a06_greatCircle normal₁ ∩ apm_t02a06_greatCircle normal₂ := by
  rcases apm_t02a06_crossPoint_mem_both normal₁ normal₂ hcircles with ⟨h₁, h₂⟩
  constructor <;> change inner ℝ
    (-apm_t02a06_normalizedCrossVector normal₁ normal₂) _ = 0
  · simpa using congrArg Neg.neg h₁
  · simpa using congrArg Neg.neg h₂

noncomputable def apm_t02a06_crossIntersectionPoint
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_intersection normal₁ normal₂ :=
  ⟨apm_t02a06_crossPoint normal₁ normal₂ hcircles,
    apm_t02a06_crossPoint_mem_both normal₁ normal₂ hcircles⟩

noncomputable def apm_t02a06_negCrossIntersectionPoint
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_intersection normal₁ normal₂ :=
  ⟨apm_t02a06_negCrossPoint normal₁ normal₂ hcircles,
    apm_t02a06_negCrossPoint_mem_both normal₁ normal₂ hcircles⟩

theorem apm_t02a06_crossIntersectionPoint_ne_neg
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles ≠
      apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles := by
  have heq : apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles =
      apm_t02a06_intersectionAntipodal
        (apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles) := rfl
  rw [heq]
  exact Ne.symm (apm_t02a06_intersectionAntipodal_ne
    (apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles))

/-- Exhaustiveness: every common unit vector is one of the two normalized
cross-product points. -/
theorem apm_t02a06_intersection_eq_cross_or_neg
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂)
    (x : apm_t02a06_intersection normal₁ normal₂) :
    x = apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles ∨
      x = apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles := by
  let c := crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ)
  let xF : Fin 3 → ℝ := (x.1 : Fin 3 → ℝ)
  have hc : c ≠ 0 := apm_t02a06_crossProduct_ne_zero normal₁ normal₂ hcircles
  rcases x.2 with ⟨hx₁, hx₂⟩
  have hd₁ : dotProduct (normal₁ : Fin 3 → ℝ) xF = 0 := by
    change inner ℝ (x.1 : EuclideanSpace ℝ (Fin 3)) normal₁ = 0 at hx₁
    simpa [EuclideanSpace.inner_eq_star_dotProduct, xF] using hx₁
  have hd₂ : dotProduct (normal₂ : Fin 3 → ℝ) xF = 0 := by
    change inner ℝ (x.1 : EuclideanSpace ℝ (Fin 3)) normal₂ = 0 at hx₂
    simpa [EuclideanSpace.inner_eq_star_dotProduct, xF] using hx₂
  have hcross : crossProduct c xF = 0 := by
    unfold c
    rw [cross_cross_eq_smul_sub_smul, hd₁, hd₂]
    simp
  have hnotLI : ¬ LinearIndependent ℝ ![c, xF] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact not_ne_iff.mpr hcross
  have hexists : ∃ r : ℝ, xF = r • c := by
    rw [LinearIndependent.pair_iff' hc] at hnotLI
    simpa only [not_forall, not_ne_iff, eq_comm] using hnotLI
  obtain ⟨r, hr⟩ := hexists
  have hrLp : (x.1 : EuclideanSpace ℝ (Fin 3)) =
      r • WithLp.toLp 2 c := by
    ext i
    exact congrFun hr i
  have hxnorm : ‖(x.1 : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using x.1.property
  have hcNorm : ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    apply hc
    have hof := congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ WithLp.ofLp z) h
    simpa using hof
  have hmul : |r| * ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have hn := congrArg norm hrLp
    rw [hxnorm, norm_smul, Real.norm_eq_abs] at hn
    exact hn.symm
  by_cases hrnonneg : 0 ≤ r
  · left
    have hrval : r = ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [abs_of_nonneg hrnonneg] using hmul)
    apply Subtype.ext
    apply Subtype.ext
    rw [hrLp, hrval]
    rfl
  · right
    have hrneg : r < 0 := lt_of_not_ge hrnonneg
    have hnegval : -r = ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [abs_of_neg hrneg] using hmul)
    have hrval : r = -‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖⁻¹ := by
      linarith
    apply Subtype.ext
    apply Subtype.ext
    rw [hrLp, hrval]
    simp [apm_t02a06_negCrossIntersectionPoint, apm_t02a06_negCrossPoint,
      apm_t02a06_normalizedCrossVector, c]

/-- The exact two-point enumeration, constructed from the classification above. -/
noncomputable def apm_t02a06_finTwoEquivIntersection
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂ where
  toFun i := if i = 0 then
    apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles
  else apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles
  invFun x := if x = apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles
    then 0 else 1
  left_inv i := by
    have hne := apm_t02a06_crossIntersectionPoint_ne_neg normal₁ normal₂ hcircles
    have hne' := Ne.symm hne
    fin_cases i <;> simp [hne, hne']
  right_inv x := by
    rcases apm_t02a06_intersection_eq_cross_or_neg normal₁ normal₂ hcircles x with h | h
    · simp [h]
    · have hne := apm_t02a06_crossIntersectionPoint_ne_neg normal₁ normal₂ hcircles
      simp [h, hne, Ne.symm hne]

@[simp] theorem apm_t02a06_finTwoEquivIntersection_zero
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_finTwoEquivIntersection normal₁ normal₂ hcircles 0 =
      apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles := by
  rfl

@[simp] theorem apm_t02a06_finTwoEquivIntersection_one
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    apm_t02a06_finTwoEquivIntersection normal₁ normal₂ hcircles 1 =
      apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles := by
  rfl

theorem apm_t02a06_crossPoint_tripleProduct_ne_zero
    (normal₁ normal₂ : apm_t02a06_S2)
    (hcircles : apm_t02a06_greatCircle normal₁ ≠
      apm_t02a06_greatCircle normal₂) :
    dotProduct (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ))
      ((apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles).1 :
        Fin 3 → ℝ) ≠ 0 := by
  let c := crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ)
  have hc : c ≠ 0 := apm_t02a06_crossProduct_ne_zero normal₁ normal₂ hcircles
  have hcLp : (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    apply hc
    have hof := congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ WithLp.ofLp z) h
    simpa using hof
  have hnormpos : 0 < ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr hcLp)
  have hself : 0 < dotProduct c c := by
    simpa using (Matrix.dotProduct_self_star_pos_iff (v := c)).mpr hc
  apply ne_of_gt
  change 0 < dotProduct c
    (‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin 3))‖⁻¹ • c)
  rw [dotProduct_smul]
  exact mul_pos hnormpos hself

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
  intro normal₁ normal₂ hcircles
  let e := apm_t02a06_finTwoEquivIntersection normal₁ normal₂ hcircles
  refine ⟨e, ?_⟩
  have hanti := apm_t02a06_localSign_antipodal
    (apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles)
    (apm_t02a06_crossPoint_tripleProduct_ne_zero normal₁ normal₂ hcircles)
  change apm_t02a06_localSign
      (apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles) =
    -apm_t02a06_localSign
      (apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles) at hanti
  change apm_t02a06_localSign
      (apm_t02a06_crossIntersectionPoint normal₁ normal₂ hcircles) =
    -apm_t02a06_localSign
      (apm_t02a06_negCrossIntersectionPoint normal₁ normal₂ hcircles)
  omega

theorem apm_t02a06_first_conjunct :
    ∀ normal₁ normal₂ : apm_t02a06_S2,
      apm_t02a06_greatCircle normal₁ ≠ apm_t02a06_greatCircle normal₂ →
        ∃ e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂,
          apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1) ∧
          apm_t02a06_signedIntersection e = 0 := by
  intro normal₁ normal₂ hcircles
  obtain ⟨e, hopposite⟩ := apm_t02A06_bridge_1 normal₁ normal₂ hcircles
  exact ⟨e, hopposite,
    apm_t02a06_signedIntersection_eq_zero_of_opposite e hopposite⟩

/-- Why this unblocks the second conjunct of `apm_t02a06`: it is the exact
topological consequence of the missing computations
`H₂(S² × S²; ℤ) ≅ ℤ²` and `H₂(S⁴; ℤ) = 0`. -/
theorem apm_t02A06_bridge_2 :
    ¬ Nonempty ((apm_t02a06_S2 × apm_t02a06_S2) ≃ₜ apm_t02a06_S4) := by
  exact
    ConstructionTargets.T02A06SphereOne.no_homeomorph_sphereTwo_product_sphereTwo_sphereFour

#print axioms apm_t02A06_bridge_2

/-- Why this unblocks the third conjunct of `apm_t02a06`: every map from
`S³` to `T³` lifts to the contractible universal cover `ℝ³` and is therefore
nullhomotopic; this packages the resulting homology-map vanishing in exactly
the functorial form needed here. -/
theorem apm_t02A06_bridge_3 :
    ∀ f : C(apm_t02a06_S3, apm_t02a06_T3), apm_t02a06_H3Map f = 0 := by
  intro f
  let f₀ : C(apm_t02a06_S3, apm_t02a06_S1) := ContinuousMap.fst.comp f
  let f₁ : C(apm_t02a06_S3, apm_t02a06_S1) :=
    ContinuousMap.fst.comp (ContinuousMap.snd.comp f)
  let f₂ : C(apm_t02a06_S3, apm_t02a06_S1) :=
    ContinuousMap.snd.comp (ContinuousMap.snd.comp f)
  obtain ⟨L₀, hL₀⟩ := apm_t02a06_exists_real_lift f₀
  obtain ⟨L₁, hL₁⟩ := apm_t02a06_exists_real_lift f₁
  obtain ⟨L₂, hL₂⟩ := apm_t02a06_exists_real_lift f₂
  let L : C(apm_t02a06_S3, ℝ × ℝ × ℝ) := L₀.prodMk (L₁.prodMk L₂)
  let p : C(ℝ, apm_t02a06_S1) :=
    ⟨apm_t02a06_euclideanCircleHomeomorph.symm ∘
      AddCircle.homeomorphCircle' ∘
      ((↑) : ℝ → AddCircle (2 * Real.pi)),
      apm_t02a06_isCoveringMap_euclideanCircle.continuous⟩
  let p₃ : C(ℝ × ℝ × ℝ, apm_t02a06_T3) :=
    (p.comp ContinuousMap.fst).prodMk
      ((p.comp (ContinuousMap.fst.comp ContinuousMap.snd)).prodMk
        (p.comp (ContinuousMap.snd.comp ContinuousMap.snd)))
  have hpL : p₃.comp L = f := by
    apply ContinuousMap.ext
    intro x
    apply Prod.ext
    · simpa [p₃, L, p, f₀] using congrFun hL₀ x
    · apply Prod.ext
      · simpa [p₃, L, p, f₁] using congrFun hL₁ x
      · simpa [p₃, L, p, f₂] using congrFun hL₂ x
  have hLnull : L.Nullhomotopic := by
    simpa using (id_nullhomotopic (ℝ × ℝ × ℝ)).comp_left L
  have hfnull : f.Nullhomotopic := by
    rw [← hpL]
    exact hLnull.comp_right p₃
  obtain ⟨c, hc⟩ := hfnull
  obtain ⟨H⟩ := hc
  have hmap := singularHomology_map_eq_of_topCatHomotopy
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ)
    (continuousMapHomotopyCylinder H)
    (continuousMapHomotopyCylinder_zero H)
    (continuousMapHomotopyCylinder_one H) 3
  change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f) = 0
  rw [hmap]
  let toPoint : C(apm_t02a06_S3, Unit) := ContinuousMap.const _ ()
  let fromPoint : C(Unit, apm_t02a06_T3) := ContinuousMap.const _ c
  have hconst : ContinuousMap.const apm_t02a06_S3 c = fromPoint.comp toPoint := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [hconst]
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 3).obj
    (ModuleCat.of ℤ ℤ)
  change F.map (TopCat.ofHom (fromPoint.comp toPoint)) = 0
  rw [show TopCat.ofHom (fromPoint.comp toPoint) =
      TopCat.ofHom toPoint ≫ TopCat.ofHom fromPoint by rfl, F.map_comp]
  have hzero : CategoryTheory.Limits.IsZero (F.obj (TopCat.of Unit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) 3 (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by norm_num)
  rw [hzero.eq_of_tgt (F.map (TopCat.ofHom toPoint)) 0]
  simp

#print axioms apm_t02A06_bridge_3

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
  exact ⟨apm_t02a06_first_conjunct, apm_t02A06_bridge_2, apm_t02A06_bridge_3⟩

#print axioms apm_t02a06_normals_nonproportional
#print axioms apm_t02a06_crossProduct_ne_zero
#print axioms apm_t02a06_localSign_antipodal
#print axioms apm_t02a06_signedIntersection_eq_zero_of_opposite
#print axioms apm_t02a06_normalizedCrossVector_norm
#print axioms apm_t02a06_crossPoint_mem_both
#print axioms apm_t02a06_negCrossPoint_mem_both
#print axioms apm_t02a06_crossIntersectionPoint_ne_neg
#print axioms apm_t02a06_intersection_eq_cross_or_neg
#print axioms apm_t02a06_finTwoEquivIntersection_zero
#print axioms apm_t02a06_finTwoEquivIntersection_one
#print axioms apm_t02a06_crossPoint_tripleProduct_ne_zero
#print axioms apm_t02A06_bridge_1
#print axioms apm_t02a06_first_conjunct
#print axioms apm_t02a06

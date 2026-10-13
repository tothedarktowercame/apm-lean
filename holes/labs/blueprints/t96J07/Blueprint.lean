import Mathlib
import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.RationalLefschetz

open CategoryTheory

/-!
# APM t96J07 — a diagonal map of real projective three-space

## Statement repairs

The nonzero-vector implication now encloses the axis equivalence explicitly.
The old parsed clause and its zero-vector refutation are retained below.
This repairs the statement; it is not a proof of the old frozen theorem.

## Encoding note

A projective point is represented by a nonzero vector modulo the explicit
relation “differ by a nonzero scalar.” Fixed points are therefore eigenlines;
the local indices are the signs of `det(I-df)` in the four affine charts.
-/

abbrev apm_t96j07_V := Fin 4 → ℝ

def apm_t96j07_projectivelyEq (x y : apm_t96j07_V) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ y = c • x

def apm_t96j07_A (x : apm_t96j07_V) : apm_t96j07_V :=
  fun i => (i.val + 1 : ℝ) * x i

def apm_t96j07_axis (i : Fin 4) : apm_t96j07_V :=
  fun j => if j = i then 1 else 0

abbrev apm_t96j07_RP3 := Projectivization ℝ apm_t96j07_V

noncomputable instance : TopologicalSpace apm_t96j07_RP3 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℝ) inferInstance

noncomputable abbrev apm_t96j07_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t96j07_RP3))

noncomputable def apm_t96j07_Hmap (k : ℕ) (f : C(apm_t96j07_RP3, apm_t96j07_RP3)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

noncomputable abbrev apm_t96j07_HQ (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of apm_t96j07_RP3))

noncomputable def apm_t96j07_HQmap (k : ℕ)
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)

/-- The global Lefschetz number is the alternating trace of the actual maps
induced by `f` on rational singular homology.  The isomorphisms are bases, not
assumptions about the value of any trace. -/
def apm_t96j07_HasLefschetzNumber
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3)) (L : ℚ) : Prop :=
  ∃ e0 : apm_t96j07_HQ 0 ≅ ModuleCat.of ℚ ℚ,
    ∃ e1 : apm_t96j07_HQ 1 ≅ ModuleCat.of ℚ (Fin 0 → ℚ),
    ∃ e2 : apm_t96j07_HQ 2 ≅ ModuleCat.of ℚ (Fin 0 → ℚ),
    ∃ e3 : apm_t96j07_HQ 3 ≅ ModuleCat.of ℚ ℚ,
      L = LinearMap.trace ℚ ℚ (e0.inv ≫ apm_t96j07_HQmap 0 f ≫ e0.hom).hom -
          LinearMap.trace ℚ (Fin 0 → ℚ) (e1.inv ≫ apm_t96j07_HQmap 1 f ≫ e1.hom).hom +
          LinearMap.trace ℚ (Fin 0 → ℚ) (e2.inv ≫ apm_t96j07_HQmap 2 f ≫ e2.hom).hom -
          LinearMap.trace ℚ ℚ (e3.inv ≫ apm_t96j07_HQmap 3 f ≫ e3.hom).hom

noncomputable abbrev apm_t96j07_E3 := EuclideanSpace ℝ (Fin 3)
noncomputable abbrev apm_t96j07_S2 := Metric.sphere (0 : apm_t96j07_E3) 1
noncomputable abbrev apm_t96j07_H2S2 :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t96j07_S2))

/-- Intrinsic local fixed-point index: in a chart around `q`, normalize the
actual displacement `x - f(x)` on a small linking sphere and take its degree.
The closed `r`-ball lies in the chart's target and is carried by `f` back into
its source, and `q` is the only fixed point in it, so the degree is the local
index of `f` at `q` (independent of the chart and of such `r`). -/
def apm_t96j07_HasLocalLefschetzNumber
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (q : apm_t96j07_RP3) (d : ℤ) : Prop :=
  ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
    q ∈ chart.source ∧ chart q = 0 ∧
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (0 : apm_t96j07_E3) r ⊆ chart.target ∧
      (∀ y ∈ Metric.closedBall (0 : apm_t96j07_E3) r,
        f (chart.symm y) ∈ chart.source) ∧
      (∀ y ∈ Metric.closedBall (0 : apm_t96j07_E3) r,
        chart (f (chart.symm y)) = y → y = 0) ∧
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        (∀ x, chart.symm (r • x.1) ∈ chart.source ∧
          f (chart.symm (r • x.1)) ∈ chart.source ∧
          ∃ hne : r • x.1 - chart (f (chart.symm (r • x.1))) ≠ 0,
            link x = ⟨‖r • x.1 - chart (f (chart.symm (r • x.1)))‖⁻¹ •
              (r • x.1 - chart (f (chart.symm (r • x.1)))), by
                rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
                  norm_norm]
                exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩) ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ a : apm_t96j07_H2S2,
            orientation.hom
              (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
                (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) a) =
              d * orientation.hom a

lemma apm_t96j07_A_ne_zero {x : apm_t96j07_V} (hx : x ≠ 0) :
    apm_t96j07_A x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  simp only [apm_t96j07_A, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by positivity)

noncomputable def apm_t96j07_localDeterminant (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (1 - (j.val + 1 : ℝ) / (i.val + 1 : ℝ))

noncomputable def apm_t96j07_localIndex (i : Fin 4) : ℤ :=
  if 0 < apm_t96j07_localDeterminant i then 1 else -1

/-- The first frozen conjunct is refuted at the zero vector. -/
lemma apm_t96j07_not_fixed_axis_clause :
    ¬(∀ x : apm_t96j07_V,
      (x ≠ 0 → apm_t96j07_projectivelyEq x (apm_t96j07_A x)) ↔
        ∃ i : Fin 4, apm_t96j07_projectivelyEq x (apm_t96j07_axis i)) := by
  intro h
  have hzero := (h 0).mp (by simp)
  rcases hzero with ⟨i, c, hc, haxis⟩
  have hi := congrFun haxis i
  simp [apm_t96j07_axis] at hi

/-- Superseded: the local index was defined to be the desired determinant sign,
and the global Lefschetz number was represented only by their sum. -/
theorem apm_t96j07_previous_encoding :
    (∀ x : apm_t96j07_V, x ≠ 0 →
      (apm_t96j07_projectivelyEq x (apm_t96j07_A x) ↔
        ∃ i : Fin 4, apm_t96j07_projectivelyEq x (apm_t96j07_axis i))) ∧
    apm_t96j07_localIndex 0 = -1 ∧
    apm_t96j07_localIndex 1 = 1 ∧
    apm_t96j07_localIndex 2 = -1 ∧
    apm_t96j07_localIndex 3 = 1 ∧
    (∑ i : Fin 4, apm_t96j07_localIndex i) = 0 := by
  constructor
  · intro x hx
    constructor
    · rintro ⟨c, hc, he⟩
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        apply hx
        funext i
        simpa using not_exists.mp h i
      have hci : (i.val + 1 : ℝ) = c := by
        apply mul_right_cancel₀ hi
        exact congrFun he i
      have hz : ∀ j, j ≠ i → x j = 0 := by
        intro j hji
        have hj := congrFun he j
        change (j.val + 1 : ℝ) * x j = c * x j at hj
        rw [← hci] at hj
        have hne : (j.val + 1 : ℝ) ≠ (i.val + 1 : ℝ) := by
          intro h
          have : j.val = i.val := by exact_mod_cast (add_right_cancel h)
          exact hji (Fin.ext this)
        exact (mul_eq_mul_right_iff.mp hj).resolve_left hne
      refine ⟨i, (x i)⁻¹, inv_ne_zero hi, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        simp [apm_t96j07_axis, hi]
      · simp [apm_t96j07_axis, hji, hz j hji]
    · rintro ⟨i, c, hc, he⟩
      refine ⟨(i.val + 1 : ℝ), by positivity, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        rfl
      · have hj := congrFun he j
        have hz : x j = 0 := by
          have : c * x j = 0 := by simpa [apm_t96j07_axis, hji] using hj.symm
          exact (mul_eq_zero.mp this).resolve_left hc
        simp [apm_t96j07_A, hz]
  · have h0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} := by decide
    have h1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
    have h2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
    have h3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} := by decide
    norm_num [apm_t96j07_localIndex, apm_t96j07_localDeterminant,
      Fin.sum_univ_succ, show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) from rfl, h0, h1, h2, h3, Finset.prod_insert,
      show (0 : Fin 4) ≠ 1 by decide, show (0 : Fin 4) ≠ 2 by decide,
      show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
      show (1 : Fin 4) ≠ 3 by decide, show (2 : Fin 4) ≠ 3 by decide]

/-- Construct the projectivized diagonal map and identify all fixed points. -/
theorem apm_t96j07_map_fixedPoints :
    ∃ f : C(apm_t96j07_RP3, apm_t96j07_RP3),
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0),
        f (Projectivization.mk ℝ x hx) =
          Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) ∧
      (∀ q, f q = q ↔ ∃ i : Fin 4,
        q = Projectivization.mk ℝ (apm_t96j07_axis i) (by
          intro h
          have := congrFun h i
          simp [apm_t96j07_axis] at this)) := by
  sorry

/-- Compute the four intrinsic local indices.  The action formula is supplied
as a hypothesis so this can be proved independently of map construction. -/
theorem apm_t96j07_local_numbers
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) :
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 0) (by
          intro h; have := congrFun h 0; simp [apm_t96j07_axis] at this)) (-1) ∧
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 1) (by
          intro h; have := congrFun h 1; simp [apm_t96j07_axis] at this)) 1 ∧
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 2) (by
          intro h; have := congrFun h 2; simp [apm_t96j07_axis] at this)) (-1) ∧
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 3) (by
          intro h; have := congrFun h 3; simp [apm_t96j07_axis] at this)) 1 := by
  sorry

/-- Compute the rational-homological Lefschetz number.  The action formula is
supplied directly so this lemma is parallel to map construction. -/
theorem apm_t96j07_global_number
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) :
    apm_t96j07_HasLefschetzNumber f 0 := by
  sorry

/-- Fixed points, local Lefschetz numbers, and the global homological
Lefschetz number for the stated diagonal self-map of `ℝP³`. -/
theorem apm_t96j07 :
    ∃ f : C(apm_t96j07_RP3, apm_t96j07_RP3),
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0),
        f (Projectivization.mk ℝ x hx) =
          Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) ∧
      (∀ q, f q = q ↔ ∃ i : Fin 4,
        q = Projectivization.mk ℝ (apm_t96j07_axis i) (by
          intro h
          have := congrFun h i
          simp [apm_t96j07_axis] at this)) ∧
      apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 0) (by
          intro h; have := congrFun h 0; simp [apm_t96j07_axis] at this)) (-1) ∧
      apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 1) (by
          intro h; have := congrFun h 1; simp [apm_t96j07_axis] at this)) 1 ∧
      apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 2) (by
          intro h; have := congrFun h 2; simp [apm_t96j07_axis] at this)) (-1) ∧
      apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 3) (by
          intro h; have := congrFun h 3; simp [apm_t96j07_axis] at this)) 1 ∧
      apm_t96j07_HasLefschetzNumber f 0 := by
  obtain ⟨f, hformula, hfixed⟩ := apm_t96j07_map_fixedPoints
  obtain ⟨h0, h1, h2, h3⟩ := apm_t96j07_local_numbers f hformula
  exact ⟨f, hformula, hfixed, h0, h1, h2, h3,
    apm_t96j07_global_number f hformula⟩

#print axioms apm_t96j07

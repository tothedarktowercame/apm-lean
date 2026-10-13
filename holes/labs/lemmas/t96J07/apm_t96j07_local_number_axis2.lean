import Mathlib
import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.CoefficientFirstReflection

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
  let lift : {x : apm_t96j07_V // x ≠ 0} → apm_t96j07_RP3 := fun x =>
    Projectivization.mk ℝ (apm_t96j07_A x.1) (apm_t96j07_A_ne_zero x.2)
  have hlift : Continuous lift := by
    change Continuous
      (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 3 ∘
        fun x : {x : apm_t96j07_V // x ≠ 0} =>
          ⟨apm_t96j07_A x.1, apm_t96j07_A_ne_zero x.2⟩)
    apply (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 3).comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_const.mul
      ((continuous_apply i).comp continuous_subtype_val)
  obtain ⟨f, hf⟩ :=
    ConstructionTargets.ProjectiveQuotientDescent.projectiveHomogeneousMapDescent
      ℝ lift hlift (by
        intro a b t hab
        apply (Projectivization.mk_eq_mk_iff ℝ _ _
          (apm_t96j07_A_ne_zero a.2) (apm_t96j07_A_ne_zero b.2)).mpr
        by_cases ht : t = 0
        · subst t
          exfalso
          apply a.2
          simpa using hab
        · refine ⟨Units.mk0 t ht, ?_⟩
          rw [hab]
          funext i
          simp [apm_t96j07_A]
          ring)
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    exact hf ⟨x, hx⟩
  · intro q
    induction q using Projectivization.ind with
    | h x hx =>
      have hf' := hf ⟨x, hx⟩
      change f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx) at hf'
      constructor
      · intro hfix
        have hfix' : Projectivization.mk ℝ (apm_t96j07_A x)
              (apm_t96j07_A_ne_zero hx) = Projectivization.mk ℝ x hx :=
          hf'.symm.trans hfix
        have hproj : apm_t96j07_projectivelyEq x (apm_t96j07_A x) := by
          obtain ⟨a, ha⟩ :=
            (Projectivization.mk_eq_mk_iff ℝ (apm_t96j07_A x) x
              (apm_t96j07_A_ne_zero hx) hx).mp hfix'
          exact ⟨(a : ℝ), Units.ne_zero a, ha.symm⟩
        obtain ⟨i, hi⟩ :=
          (apm_t96j07_previous_encoding.1 x hx).mp hproj
        refine ⟨i, ?_⟩
        rcases hi with ⟨c, hc, haxis⟩
        apply (Projectivization.mk_eq_mk_iff ℝ x (apm_t96j07_axis i) hx _).mpr
        refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc), ?_⟩
        rw [haxis]
        simpa [smul_smul, hc]
      · rintro ⟨i, hi⟩
        have hproj : apm_t96j07_projectivelyEq x (apm_t96j07_axis i) := by
          obtain ⟨a, ha⟩ :=
            (Projectivization.mk_eq_mk_iff ℝ (apm_t96j07_axis i) x _ hx).mp hi.symm
          exact ⟨(a : ℝ), Units.ne_zero a, ha.symm⟩
        obtain ⟨c, hc, hA⟩ :=
          (apm_t96j07_previous_encoding.1 x hx).mpr ⟨i, hproj⟩
        have hAx : Projectivization.mk ℝ (apm_t96j07_A x)
            (apm_t96j07_A_ne_zero hx) = Projectivization.mk ℝ x hx := by
          apply (Projectivization.mk_eq_mk_iff ℝ (apm_t96j07_A x) x
            (apm_t96j07_A_ne_zero hx) hx).mpr
          exact ⟨Units.mk0 c hc, hA.symm⟩
        exact hf'.trans hAx

/-- The degree calculation used in every affine chart.  An invertible diagonal
displacement on `R^3`, normalized to the unit sphere, acts on integral top
homology by the sign of its determinant. -/
theorem apm_t96j07_diagonal_link_degree :
    ∀ a : Fin 3 → ℝ, (∀ j, 1 - a j ≠ 0) →
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        (∀ x, ∃ hne : WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j) ≠ 0,
          link x = ⟨‖WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j)‖⁻¹ •
            WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j), by
              rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
                norm_norm]
              exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩) ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ z : apm_t96j07_H2S2,
            orientation.hom
                (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
                  (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) z) =
              (if 0 < ∏ j, (1 - a j) then 1 else -1) * orientation.hom z := by
  sorry

/-- Package the affine chart at the first coordinate axis.  The sphere-degree
input is explicit so this leaf is independent of its eventual proof. -/
theorem apm_t96j07_local_number_axis0
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx))
    (hdegree : ∀ a : Fin 3 → ℝ, (∀ j, 1 - a j ≠ 0) →
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        (∀ x, ∃ hne : WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j) ≠ 0,
          link x = ⟨‖WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j)‖⁻¹ •
            WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j), by
              rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
              exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩) ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ z : apm_t96j07_H2S2, orientation.hom
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) z) =
            (if 0 < ∏ j, (1 - a j) then 1 else -1) * orientation.hom z) :
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 0) (by
          intro h; have := congrFun h 0; simp [apm_t96j07_axis] at this)) (-1) := by
  sorry

/-- Package the affine chart at the second coordinate axis. -/
theorem apm_t96j07_local_number_axis1
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx))
    (hdegree : ∀ a : Fin 3 → ℝ, (∀ j, 1 - a j ≠ 0) →
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        (∀ x, ∃ hne : WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j) ≠ 0,
          link x = ⟨‖WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j)‖⁻¹ •
            WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j), by
              rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
              exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩) ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ z : apm_t96j07_H2S2, orientation.hom
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) z) =
            (if 0 < ∏ j, (1 - a j) then 1 else -1) * orientation.hom z) :
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 1) (by
          intro h; have := congrFun h 1; simp [apm_t96j07_axis] at this)) 1 := by
  sorry

/-- Package the affine chart at the third coordinate axis. -/
-- BEGIN SEAT AREA
noncomputable def apm_t96j07_local_number_axis2_aux_coord
    (x : apm_t96j07_RP3) : apm_t96j07_E3 :=
  WithLp.toLp 2 (fun j =>
    Projectivization.rep x (Fin.succAbove (2 : Fin 4) j) /
      Projectivization.rep x 2)

noncomputable def apm_t96j07_local_number_axis2_aux_inv
    (z : apm_t96j07_E3) : apm_t96j07_RP3 :=
  Projectivization.mk ℝ
    (fun j => if h : j = 2 then 1 else
      WithLp.ofLp z (Fin.predAbove (2 : Fin 3) j))
    (by
      intro h
      have h2 := congrFun h 2
      simp at h2)

lemma apm_t96j07_local_number_axis2_aux_source_open :
    IsOpen {x : apm_t96j07_RP3 | Projectivization.rep x 2 ≠ 0} := by
  rw [isOpen_coinduced]
  change IsOpen ((Projectivization.mk' ℝ) ⁻¹'
    {x : apm_t96j07_RP3 | Projectivization.rep x 2 ≠ 0})
  have heq : (Projectivization.mk' ℝ) ⁻¹'
      {x : apm_t96j07_RP3 | Projectivization.rep x 2 ≠ 0} =
      {v : {v : apm_t96j07_V // v ≠ 0} | v.1 2 ≠ 0} := by
    ext v
    change (Projectivization.mk ℝ v.1 v.2).rep 2 ≠ 0 ↔ v.1 2 ≠ 0
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1 v.2
    rw [← ha]
    change (a : ℝ) * v.1 2 ≠ 0 ↔ v.1 2 ≠ 0
    simp
  rw [heq]
  exact isOpen_compl_singleton.preimage
    ((continuous_apply 2).comp continuous_subtype_val)

lemma apm_t96j07_local_number_axis2_aux_coord_cont :
    ContinuousOn apm_t96j07_local_number_axis2_aux_coord
      {x : apm_t96j07_RP3 | Projectivization.rep x 2 ≠ 0} := by
  let s : Set apm_t96j07_RP3 :=
    {x | Projectivization.rep x 2 ≠ 0}
  let q : {v : apm_t96j07_V // v ≠ 0} → apm_t96j07_RP3 :=
    Projectivization.mk' ℝ
  let qr := s.restrictPreimage q
  have hqr : IsOpenQuotientMap qr := by
    refine ⟨?_, (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 3).restrictPreimage, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ :=
        ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℝ 3 x
      exact ⟨⟨v, hx⟩, rfl⟩
    · exact (ConstructionTargets.ProjectiveQuotientDescent.projectiveQuotientMap_isOpen ℝ 3).restrictPreimage s
  rw [continuousOn_iff_continuous_restrict]
  apply hqr.isQuotientMap.continuous_iff.mpr
  have hc : Continuous (fun v : q ⁻¹' s => WithLp.toLp 2 (fun j : Fin 3 =>
      v.1.1 (Fin.succAbove (2 : Fin 4) j) / v.1.1 2)) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    have hn : Continuous (fun v : q ⁻¹' s =>
        v.1.1 (Fin.succAbove (2 : Fin 4) j)) :=
      (continuous_apply _).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hd : Continuous (fun v : q ⁻¹' s => v.1.1 2) :=
      (continuous_apply _).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hd0 : ∀ v : q ⁻¹' s, v.1.1 2 ≠ 0 := by
      intro v
      have hv := v.2
      change Projectivization.rep (Projectivization.mk ℝ v.1.1 v.1.2) 2 ≠ 0 at hv
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1.1 v.1.2
      rw [← ha] at hv
      exact (mul_ne_zero_iff.mp hv).2
    exact hn.div hd hd0
  have heq : ({x : apm_t96j07_RP3 | Projectivization.rep x 2 ≠ 0}.restrict
      apm_t96j07_local_number_axis2_aux_coord ∘ qr) =
      (fun v : q ⁻¹' s => WithLp.toLp 2 (fun j : Fin 3 =>
        v.1.1 (Fin.succAbove (2 : Fin 4) j) / v.1.1 2)) := by
    funext v
    apply WithLp.ofLp_injective 2
    funext j
    change Projectivization.rep (Projectivization.mk ℝ v.1.1 v.1.2)
        (Fin.succAbove (2 : Fin 4) j) /
        Projectivization.rep (Projectivization.mk ℝ v.1.1 v.1.2) 2 = _
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1.1 v.1.2
    rw [← ha]
    change ((a : ℝ) * v.1.1 _ / ((a : ℝ) * v.1.1 2)) = _
    field_simp
  rw [heq]
  exact hc

lemma apm_t96j07_local_number_axis2_aux_inv_cont :
    Continuous apm_t96j07_local_number_axis2_aux_inv := by
  change Continuous (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 3 ∘
    fun z : apm_t96j07_E3 => ⟨(fun j => if h : j = 2 then 1 else
      WithLp.ofLp z (Fin.predAbove (2 : Fin 3) j)), by
        intro h
        have h2 := congrFun h 2
        simp at h2⟩)
  apply (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 3).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases h : j = 2
  · simpa [apm_t96j07_local_number_axis2_aux_inv, h] using
      (continuous_const : Continuous (fun _ : apm_t96j07_E3 => (1 : ℝ)))
  · simpa [apm_t96j07_local_number_axis2_aux_inv, h] using
      ((continuous_apply (Fin.predAbove (2 : Fin 3) j)).comp
        (PiLp.continuous_ofLp 2 _))

lemma apm_t96j07_local_number_axis2_aux_coord_inv (z : apm_t96j07_E3) :
    apm_t96j07_local_number_axis2_aux_coord
      (apm_t96j07_local_number_axis2_aux_inv z) = z := by
  apply WithLp.ofLp_injective 2
  funext j
  let v : Fin 4 → ℝ := fun k => if h : k = 2 then 1 else
    WithLp.ofLp z (Fin.predAbove (2 : Fin 3) k)
  have hv : v ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp [v] at h2
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  change (Projectivization.mk ℝ v hv).rep (Fin.succAbove (2 : Fin 4) j) /
      (Projectivization.mk ℝ v hv).rep 2 = WithLp.ofLp z j
  rw [← ha]
  change ((a : ℝ) * v (Fin.succAbove (2 : Fin 4) j)) /
      ((a : ℝ) * v 2) = _
  have hp : Fin.predAbove (2 : Fin 3) (Fin.succAbove (2 : Fin 4) j) = j := by
    fin_cases j <;> rfl
  simp [v, hp]

lemma apm_t96j07_local_number_axis2_aux_inv_coord
    (x : apm_t96j07_RP3) (hx : Projectivization.rep x 2 ≠ 0) :
    apm_t96j07_local_number_axis2_aux_inv
      (apm_t96j07_local_number_axis2_aux_coord x) = x := by
  rw [← Projectivization.mk_rep x]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨(Projectivization.rep x 2)⁻¹, ?_⟩
  funext j
  by_cases h : j = 2
  · subst j
    simp [apm_t96j07_local_number_axis2_aux_inv, hx]
  · have hp : Fin.succAbove (2 : Fin 4) (Fin.predAbove (2 : Fin 3) j) = j := by
      apply Fin.ext
      fin_cases j <;> simp_all [Fin.succAbove, Fin.predAbove]
    simp [apm_t96j07_local_number_axis2_aux_inv,
      apm_t96j07_local_number_axis2_aux_coord, h, div_eq_inv_mul, hp, hx]

noncomputable def apm_t96j07_local_number_axis2_aux_chart :
    OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3 where
  toPartialEquiv := {
    toFun := apm_t96j07_local_number_axis2_aux_coord
    invFun := apm_t96j07_local_number_axis2_aux_inv
    source := {x | Projectivization.rep x 2 ≠ 0}
    target := Set.univ
    map_source' := fun _ _ => Set.mem_univ _
    map_target' := by
      intro z _
      change Projectivization.rep (apm_t96j07_local_number_axis2_aux_inv z) 2 ≠ 0
      unfold apm_t96j07_local_number_axis2_aux_inv
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ
        (fun j : Fin 4 => if h : j = 2 then 1 else
          WithLp.ofLp z (Fin.predAbove (2 : Fin 3) j)) (by
            intro hh
            have hh2 := congrFun hh 2
            simp at hh2)
      rw [← ha]
      exact mul_ne_zero (Units.ne_zero a) one_ne_zero
    left_inv' := apm_t96j07_local_number_axis2_aux_inv_coord
    right_inv' := fun z _ => apm_t96j07_local_number_axis2_aux_coord_inv z }
  open_source := apm_t96j07_local_number_axis2_aux_source_open
  open_target := isOpen_univ
  continuousOn_toFun := apm_t96j07_local_number_axis2_aux_coord_cont
  continuousOn_invFun := apm_t96j07_local_number_axis2_aux_inv_cont.continuousOn

lemma apm_t96j07_local_number_axis2_aux_coord_mk
    (v : apm_t96j07_V) (hv : v ≠ 0) (hv2 : v 2 ≠ 0) :
    apm_t96j07_local_number_axis2_aux_coord (Projectivization.mk ℝ v hv) =
      WithLp.toLp 2 (fun j => v (Fin.succAbove (2 : Fin 4) j) / v 2) := by
  apply WithLp.ofLp_injective 2
  funext j
  change (Projectivization.mk ℝ v hv).rep (Fin.succAbove (2 : Fin 4) j) /
      (Projectivization.mk ℝ v hv).rep 2 = _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  rw [← ha]
  change ((a : ℝ) * v _ / ((a : ℝ) * v 2)) = _
  field_simp

lemma apm_t96j07_local_number_axis2_aux_inv_source (z : apm_t96j07_E3) :
    apm_t96j07_local_number_axis2_aux_inv z ∈
      apm_t96j07_local_number_axis2_aux_chart.source :=
  apm_t96j07_local_number_axis2_aux_chart.map_target (Set.mem_univ z)

lemma apm_t96j07_local_number_axis2_aux_action
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx))
    (z : apm_t96j07_E3) :
    f (apm_t96j07_local_number_axis2_aux_chart.symm z) ∈
        apm_t96j07_local_number_axis2_aux_chart.source ∧
    apm_t96j07_local_number_axis2_aux_chart
        (f (apm_t96j07_local_number_axis2_aux_chart.symm z)) =
      WithLp.toLp 2 (fun j =>
        ((Fin.succAbove (2 : Fin 4) j).val + 1 : ℝ) / 3 * WithLp.ofLp z j) := by
  let v : apm_t96j07_V := fun k => if h : k = 2 then 1 else
    WithLp.ofLp z (Fin.predAbove (2 : Fin 3) k)
  have hv : v ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp [v] at h2
  have hinv : apm_t96j07_local_number_axis2_aux_chart.symm z =
      Projectivization.mk ℝ v hv := rfl
  rw [hinv, hformula v hv]
  have hA2 : apm_t96j07_A v 2 ≠ 0 := by
    norm_num [apm_t96j07_A, v]
  constructor
  · change Projectivization.rep
      (Projectivization.mk ℝ (apm_t96j07_A v) (apm_t96j07_A_ne_zero hv)) 2 ≠ 0
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ
      (apm_t96j07_A v) (apm_t96j07_A_ne_zero hv)
    rw [← ha]
    exact mul_ne_zero (Units.ne_zero a) hA2
  · change apm_t96j07_local_number_axis2_aux_coord
      (Projectivization.mk ℝ (apm_t96j07_A v) (apm_t96j07_A_ne_zero hv)) = _
    rw [apm_t96j07_local_number_axis2_aux_coord_mk _ _ hA2]
    apply WithLp.ofLp_injective 2
    funext j
    have hp : Fin.predAbove (2 : Fin 3)
        (Fin.succAbove (2 : Fin 4) j) = j := by fin_cases j <;> rfl
    simp [apm_t96j07_A, v, hp]
    ring

theorem apm_t96j07_local_number_axis2
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx))
    (hdegree : ∀ a : Fin 3 → ℝ, (∀ j, 1 - a j ≠ 0) →
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        (∀ x, ∃ hne : WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j) ≠ 0,
          link x = ⟨‖WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j)‖⁻¹ •
            WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j), by
              rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
              exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩) ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ z : apm_t96j07_H2S2, orientation.hom
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) z) =
            (if 0 < ∏ j, (1 - a j) then 1 else -1) * orientation.hom z) :
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 2) (by
          intro h; have := congrFun h 2; simp [apm_t96j07_axis] at this)) (-1) := by
  let chart := apm_t96j07_local_number_axis2_aux_chart
  let a : Fin 3 → ℝ := ![(1 : ℝ) / 3, 2 / 3, 4 / 3]
  have haw : ∀ j, a j =
      ((Fin.succAbove (2 : Fin 4) j).val + 1 : ℝ) / 3 := by
    intro j
    fin_cases j <;> norm_num [a, Fin.succAbove, Fin.lt_iff_val_lt_val]
  have ha : ∀ j, 1 - a j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num [a]
  obtain ⟨link, hlink, orientation, horientation⟩ := hdegree a ha
  refine ⟨chart, ?_, ?_, 1, by norm_num, ?_, ?_, ?_, link, ?_, orientation, ?_⟩
  · change Projectivization.rep
      (Projectivization.mk ℝ (apm_t96j07_axis 2) _) 2 ≠ 0
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℝ
      (apm_t96j07_axis 2) (by
        intro h
        have := congrFun h 2
        simp [apm_t96j07_axis] at this)
    rw [← hu]
    exact mul_ne_zero (Units.ne_zero u) (by simp [apm_t96j07_axis])
  · change apm_t96j07_local_number_axis2_aux_coord
      (Projectivization.mk ℝ (apm_t96j07_axis 2) _) = 0
    rw [apm_t96j07_local_number_axis2_aux_coord_mk
      (apm_t96j07_axis 2) (by
        intro h
        have hh := congrFun h 2
        simp [apm_t96j07_axis] at hh) (by simp [apm_t96j07_axis])]
    apply WithLp.ofLp_injective 2
    funext j
    simp [apm_t96j07_axis]
  · intro y hy
    exact Set.mem_univ y
  · intro y hy
    exact (apm_t96j07_local_number_axis2_aux_action f hformula y).1
  · intro y hy heq
    have hact := (apm_t96j07_local_number_axis2_aux_action f hformula y).2
    rw [hact] at heq
    have heq' : WithLp.toLp 2 (fun j => a j * WithLp.ofLp y j) = y := by
      rw [show (fun j => a j * WithLp.ofLp y j) =
          (fun j => ((Fin.succAbove (2 : Fin 4) j).val + 1 : ℝ) / 3 *
            WithLp.ofLp y j) by funext j; rw [haw]]
      exact heq
    apply WithLp.ofLp_injective 2
    funext j
    have hj := congrArg (fun w : apm_t96j07_E3 => WithLp.ofLp w j) heq'
    simp only [WithLp.ofLp_toLp] at hj
    fin_cases j
    · norm_num [a] at hj
      simpa using (show WithLp.ofLp y 0 = 0 by linarith [hj])
    · norm_num [a] at hj
      simpa using (show WithLp.ofLp y 1 = 0 by linarith [hj])
    · norm_num [a] at hj
      change (4 / 3 : ℝ) * WithLp.ofLp y 2 = WithLp.ofLp y 2 at hj
      change WithLp.ofLp y 2 = 0
      linarith [hj]
  · intro x
    have hs := apm_t96j07_local_number_axis2_aux_inv_source x.1
    have hact := apm_t96j07_local_number_axis2_aux_action f hformula x.1
    change chart.symm x.1 ∈ chart.source at hs
    have hact_mem : f (chart.symm x.1) ∈ chart.source := by
      simpa [chart] using hact.1
    refine ⟨by simpa using hs, by simpa using hact_mem, ?_⟩
    have hdisp : x.1 - chart (f (chart.symm x.1)) =
        WithLp.toLp 2 (fun j => (1 - a j) * x.1 j) := by
      rw [show chart (f (chart.symm x.1)) =
          WithLp.toLp 2 (fun j =>
            ((Fin.succAbove (2 : Fin 4) j).val + 1 : ℝ) / 3 *
              WithLp.ofLp x.1 j) by simpa [chart] using hact.2]
      apply WithLp.ofLp_injective 2
      funext j
      change WithLp.ofLp x.1 j -
          ((Fin.succAbove (2 : Fin 4) j).val + 1 : ℝ) / 3 *
            WithLp.ofLp x.1 j = (1 - a j) * WithLp.ofLp x.1 j
      rw [← haw j]
      ring
    obtain ⟨hne, heq⟩ := hlink x
    refine ⟨by simpa only [one_smul] using (hdisp ▸ hne), ?_⟩
    rw [heq]
    apply Subtype.ext
    change ‖WithLp.toLp 2 (fun j => (1 - a j) * x.1 j)‖⁻¹ •
        WithLp.toLp 2 (fun j => (1 - a j) * x.1 j) = _
    simp only [one_smul]
    rw [hdisp]
  · intro z
    have hprod : (∏ j, (1 - a j)) = (-2 / 27 : ℝ) := by
      have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      have ha2 : a (2 : Fin 3) = (4 / 3 : ℝ) := by
        rw [haw]
        norm_num [Fin.succAbove, Fin.lt_def]
      rw [hu]
      norm_num [a, Finset.prod_insert,
        show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
        show (1 : Fin 3) ≠ 2 by decide, ha2]
    have hsign : (if 0 < ∏ j, (1 - a j) then (1 : ℤ) else -1) = -1 := by
      rw [hprod]
      norm_num
    simpa [hsign] using horientation z
-- END SEAT AREA

/-- Package the affine chart at the fourth coordinate axis. -/
theorem apm_t96j07_local_number_axis3
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx))
    (hdegree : ∀ a : Fin 3 → ℝ, (∀ j, 1 - a j ≠ 0) →
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        (∀ x, ∃ hne : WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j) ≠ 0,
          link x = ⟨‖WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j)‖⁻¹ •
            WithLp.toLp 2 (fun j ↦ (1 - a j) * x.1 j), by
              rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
              exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩) ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ z : apm_t96j07_H2S2, orientation.hom
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) z) =
            (if 0 < ∏ j, (1 - a j) then 1 else -1) * orientation.hom z) :
    apm_t96j07_HasLocalLefschetzNumber f
        (Projectivization.mk ℝ (apm_t96j07_axis 3) (by
          intro h; have := congrFun h 3; simp [apm_t96j07_axis] at this)) 1 := by
  sorry

/-- Compute the four intrinsic local indices.  This is only the sorry-free
assembly of the generic degree calculation and four independent chart leaves. -/
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
  exact ⟨apm_t96j07_local_number_axis0 f hformula apm_t96j07_diagonal_link_degree,
    apm_t96j07_local_number_axis1 f hformula apm_t96j07_diagonal_link_degree,
    apm_t96j07_local_number_axis2 f hformula apm_t96j07_diagonal_link_degree,
    apm_t96j07_local_number_axis3 f hformula apm_t96j07_diagonal_link_degree⟩

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

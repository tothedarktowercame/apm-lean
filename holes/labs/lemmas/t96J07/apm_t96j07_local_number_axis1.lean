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

lemma apm_t96j07_diagonal_link_degree_aux_interp
    (u v t : ℝ) (hu : u ≠ 0)
    (hsign : (0 < u ∧ v = 1) ∨ (u < 0 ∧ v = -1))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * u + t * v ≠ 0 := by
  rcases hsign with h | h
  · rw [h.2]
    have hp : 0 < (1 - t) * u + t * 1 := by
      by_cases ht : t = 1
      · subst t; norm_num
      · have : t < 1 := lt_of_le_of_ne ht1 ht
        have : 0 < (1 - t) * u := mul_pos (sub_pos.mpr this) h.1
        nlinarith
    exact ne_of_gt hp
  · rw [h.2]
    have hp : (1 - t) * u + t * (-1) < 0 := by
      by_cases ht : t = 1
      · subst t; norm_num
      · have : t < 1 := lt_of_le_of_ne ht1 ht
        have : (1 - t) * u < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr this) h.1
        nlinarith
    exact ne_of_lt hp

lemma apm_t96j07_diagonal_link_degree_aux_vector_ne_zero
    (b : Fin 3 → ℝ) (hb : ∀ j, b j ≠ 0) (x : apm_t96j07_S2) :
    WithLp.toLp 2 (fun j ↦ b j * x.1 j) ≠ 0 := by
  intro h
  have hx0 : x.1 ≠ 0 := by
    intro hx
    have hxnorm : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere] using x.2
    simp [hx] at hxnorm
  apply hx0
  ext j
  have hj := congrArg (fun y : apm_t96j07_E3 ↦ y j) h
  change b j * x.1 j = 0 at hj
  exact (mul_eq_zero.mp hj).resolve_left (hb j)

/-- `link` is the normalised diagonal map `x ↦ D x / ‖D x‖`, `D = diag b`. -/
def apm_t96j07_IsNormalizedDiagonal (b : Fin 3 → ℝ)
    (link : C(apm_t96j07_S2, apm_t96j07_S2)) : Prop :=
  ∀ x, ∃ hne : WithLp.toLp 2 (fun j ↦ b j * x.1 j) ≠ 0,
    link x = ⟨‖WithLp.toLp 2 (fun j ↦ b j * x.1 j)‖⁻¹ •
      WithLp.toLp 2 (fun j ↦ b j * x.1 j), by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)⟩

/-- Seat: the normalised diagonal map exists (continuous) when all `b j ≠ 0`. -/
theorem apm_t96j07_exists_normalizedDiagonal (b : Fin 3 → ℝ) (hb : ∀ j, b j ≠ 0) :
    ∃ link, apm_t96j07_IsNormalizedDiagonal b link := by
  let g : apm_t96j07_S2 → apm_t96j07_E3 := fun x =>
    WithLp.toLp 2 (fun j ↦ b j * x.1 j)
  have hg_ne : ∀ x, g x ≠ 0 := fun x =>
    apm_t96j07_diagonal_link_degree_aux_vector_ne_zero b hb x
  have hg : Continuous g := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact continuous_const.mul
      ((continuous_apply j).comp
        ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val))
  have hnormalized : Continuous (fun x => ‖g x‖⁻¹ • g x) := by
    exact ((continuous_norm.comp hg).inv₀
      (fun x => norm_ne_zero_iff.mpr (hg_ne x))).smul hg
  let link : C(apm_t96j07_S2, apm_t96j07_S2) :=
    ⟨fun x => ⟨‖g x‖⁻¹ • g x, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg_ne x))⟩,
      Continuous.subtype_mk hnormalized (fun x => by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg_ne x)))⟩
  refine ⟨link, ?_⟩
  intro x
  refine ⟨hg_ne x, ?_⟩
  rfl

/-- Seat: normalised diagonal maps for `b` and for the signs of `b` are homotopic
(straight line `(1 - t) b + t sign b` has nonzero entries). -/
theorem apm_t96j07_normalizedDiagonal_homotopic_sign (b : Fin 3 → ℝ)
    (hb : ∀ j, b j ≠ 0) (l l' : C(apm_t96j07_S2, apm_t96j07_S2))
    (hl : apm_t96j07_IsNormalizedDiagonal b l)
    (hl' : apm_t96j07_IsNormalizedDiagonal (fun j ↦ if 0 < b j then 1 else -1) l') :
    ContinuousMap.Homotopic l l' := by
  sorry

/-- Seat: a sign-diagonal map (a product of coordinate reflections) acts on
`H₂(S²; ℤ) ≅ ℤ` by the product of the signs
(`ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℤ 2`,
functoriality; `topIso ℤ 1` for the orientation). -/
theorem apm_t96j07_signDiagonal_H2 (ε : Fin 3 → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (l : C(apm_t96j07_S2, apm_t96j07_S2)) (hl : apm_t96j07_IsNormalizedDiagonal ε l) :
    ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
      ∀ z : apm_t96j07_H2S2,
        orientation.hom
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom l) z) =
          (if 0 < ∏ j, ε j then 1 else -1) * orientation.hom z := by
  sorry

/-- Seat (assembly from the three leaves above as hypotheses): homotopy
invariance (`SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`) and
`sign (∏ b j) = ∏ sign (b j)`. -/
theorem apm_t96j07_diagonal_link_degree_of_parts
    (hex : ∀ b : Fin 3 → ℝ, (∀ j, b j ≠ 0) → ∃ link, apm_t96j07_IsNormalizedDiagonal b link)
    (hhom : ∀ (b : Fin 3 → ℝ), (∀ j, b j ≠ 0) → ∀ l l' : C(apm_t96j07_S2, apm_t96j07_S2),
      apm_t96j07_IsNormalizedDiagonal b l →
      apm_t96j07_IsNormalizedDiagonal (fun j ↦ if 0 < b j then 1 else -1) l' →
      ContinuousMap.Homotopic l l')
    (hsign : ∀ (ε : Fin 3 → ℝ), (∀ j, ε j = 1 ∨ ε j = -1) →
      ∀ l : C(apm_t96j07_S2, apm_t96j07_S2), apm_t96j07_IsNormalizedDiagonal ε l →
      ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
        ∀ z : apm_t96j07_H2S2,
          orientation.hom
              (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
                (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom l) z) =
            (if 0 < ∏ j, ε j then 1 else -1) * orientation.hom z) :
    ∀ a : Fin 3 → ℝ, (∀ j, 1 - a j ≠ 0) →
      ∃ link : C(apm_t96j07_S2, apm_t96j07_S2),
        apm_t96j07_IsNormalizedDiagonal (fun j ↦ 1 - a j) link ∧
        ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
          ∀ z : apm_t96j07_H2S2,
            orientation.hom
                (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
                  (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom link) z) =
              (if 0 < ∏ j, (1 - a j) then 1 else -1) * orientation.hom z := by
  sorry

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
  exact apm_t96j07_diagonal_link_degree_of_parts
    apm_t96j07_exists_normalizedDiagonal
    apm_t96j07_normalizedDiagonal_homotopic_sign
    apm_t96j07_signDiagonal_H2

/-- Seat (claude-14): the standard affine chart of `RP³` at axis `i`:
`[x] ↦ (x (i.succAbove j) / x i)_j` on `{x i ≠ 0}` (well defined: invariant
under scaling), inverse `y ↦ [insertNth i 1 y]`; source open, target all of `ℝ³`.
Shared by the four axis leaves. -/
theorem apm_t96j07_affine_chart :
    ∀ i : Fin 4, ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
      (∀ p, p ∈ chart.source ↔ p.rep i ≠ 0) ∧ chart.target = Set.univ ∧
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0), x i ≠ 0 →
        chart (Projectivization.mk ℝ x hx) =
          WithLp.toLp 2 (fun j => x (i.succAbove j) / x i)) ∧
      (∀ y : apm_t96j07_E3, ∃ h, chart.symm y =
        Projectivization.mk ℝ (Fin.insertNth i 1 (WithLp.ofLp y)) h) := by
  sorry

noncomputable def apm_t96j07_local_number_axis0_coords
    (x : apm_t96j07_RP3) : apm_t96j07_E3 :=
  WithLp.toLp 2 (fun j => Projectivization.rep x j.succ /
    Projectivization.rep x 0)

noncomputable def apm_t96j07_local_number_axis0_inv
    (y : apm_t96j07_E3) : apm_t96j07_RP3 :=
  Projectivization.mk ℝ (Fin.cases 1 (WithLp.ofLp y)) (by
    intro h
    have := congrFun h 0
    simp at this)

lemma apm_t96j07_local_number_axis0_rep_ratio
    (v : apm_t96j07_V) (hv : v ≠ 0) (h0 : v 0 ≠ 0) :
    apm_t96j07_local_number_axis0_coords (Projectivization.mk ℝ v hv) =
      WithLp.toLp 2 (fun j => v j.succ / v 0) := by
  ext j
  unfold apm_t96j07_local_number_axis0_coords
  simp only [WithLp.ofLp_toLp]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  have hj := congrFun ha j.succ
  have hi := congrFun ha 0
  rw [← hj, ← hi]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ (Units.ne_zero a)

lemma apm_t96j07_local_number_axis0_inv_coords (y : apm_t96j07_E3) :
    apm_t96j07_local_number_axis0_coords
      (apm_t96j07_local_number_axis0_inv y) = y := by
  unfold apm_t96j07_local_number_axis0_inv
  rw [apm_t96j07_local_number_axis0_rep_ratio]
  · ext j
    simp [apm_t96j07_local_number_axis0_inv]
  · simp

lemma apm_t96j07_local_number_axis0_coords_inv (x : apm_t96j07_RP3)
    (hx : Projectivization.rep x 0 ≠ 0) :
    apm_t96j07_local_number_axis0_inv
      (apm_t96j07_local_number_axis0_coords x) = x := by
  rw [← Projectivization.mk_rep x]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨(Projectivization.rep x 0)⁻¹, ?_⟩
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [hx, apm_t96j07_local_number_axis0_inv]
  · simp [apm_t96j07_local_number_axis0_inv,
      apm_t96j07_local_number_axis0_coords, div_eq_inv_mul]

lemma apm_t96j07_local_number_axis0_aux_chart
    (hgen : ∀ i : Fin 4, ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
        (∀ p, p ∈ chart.source ↔ p.rep i ≠ 0) ∧ chart.target = Set.univ ∧
        (∀ (x : apm_t96j07_V) (hx : x ≠ 0), x i ≠ 0 →
          chart (Projectivization.mk ℝ x hx) =
            WithLp.toLp 2 (fun j => x (i.succAbove j) / x i)) ∧
        (∀ y : apm_t96j07_E3, ∃ h, chart.symm y =
          Projectivization.mk ℝ (Fin.insertNth i 1 (WithLp.ofLp y)) h))
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) :
    ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
      (Projectivization.mk ℝ (apm_t96j07_axis 0) (by
        intro h; have := congrFun h 0; simp [apm_t96j07_axis] at this)) ∈
          chart.source ∧
      chart (Projectivization.mk ℝ (apm_t96j07_axis 0) (by
        intro h; have := congrFun h 0; simp [apm_t96j07_axis] at this)) = 0 ∧
      chart.target = Set.univ ∧
      (∀ y, chart.symm y ∈ chart.source) ∧
      (∀ y, f (chart.symm y) ∈ chart.source) ∧
      (∀ y, chart (f (chart.symm y)) =
        WithLp.toLp 2 (fun j => (j.val + 2 : ℝ) * y j)) := by
  sorry

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
  obtain ⟨chart, hq, hq0, htarget, hinv, hfsource, haction⟩ :=
    apm_t96j07_local_number_axis0_aux_chart apm_t96j07_affine_chart f hformula
  refine ⟨chart, hq, hq0, 1, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [htarget]
    exact Set.subset_univ _
  · intro y hy
    exact hfsource y
  · intro y hy heq
    rw [haction] at heq
    ext j
    have hj := congrArg (fun z : apm_t96j07_E3 => z j) heq
    simp only [WithLp.ofLp_toLp] at hj
    have : (j.val + 1 : ℝ) * y j = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  · let a : Fin 3 → ℝ := fun j => (j.val + 2 : ℝ)
    obtain ⟨link, hlink, orientation, horientation⟩ := hdegree a (by
      intro j
      fin_cases j <;> norm_num [a])
    refine ⟨link, ?_, orientation, ?_⟩
    · intro x
      have hxsource := hinv ((1 : ℝ) • x.1)
      have hfxsource := hfsource ((1 : ℝ) • x.1)
      refine ⟨hxsource, hfxsource, ?_⟩
      obtain ⟨hne, heq⟩ := hlink x
      have hd : (1 : ℝ) • x.1 -
          chart (f (chart.symm ((1 : ℝ) • x.1))) =
          WithLp.toLp 2 (fun j => (1 - a j) * x.1 j) := by
        rw [haction]
        ext j
        simp [a]
        ring
      refine ⟨?_, ?_⟩
      · rw [hd]
        exact hne
      · rw [heq]
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        rw [hd]
    · intro z
      rw [horientation]
      norm_num [a, Fin.prod_univ_succ]

/-- Package the affine chart at the second coordinate axis. -/
-- BEGIN SEAT AREA
theorem apm_t96j07_local_number_axis1
    (hgen :
  ∀ i : Fin 4, ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
      (∀ p, p ∈ chart.source ↔ p.rep i ≠ 0) ∧ chart.target = Set.univ ∧
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0), x i ≠ 0 →
        chart (Projectivization.mk ℝ x hx) =
          WithLp.toLp 2 (fun j => x (i.succAbove j) / x i)) ∧
      (∀ y : apm_t96j07_E3, ∃ h, chart.symm y =
        Projectivization.mk ℝ (Fin.insertNth i 1 (WithLp.ofLp y)) h))
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
-- END SEAT AREA

/-- Package the affine chart at the third coordinate axis. -/
theorem apm_t96j07_local_number_axis2
    (hgen :
  ∀ i : Fin 4, ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
      (∀ p, p ∈ chart.source ↔ p.rep i ≠ 0) ∧ chart.target = Set.univ ∧
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0), x i ≠ 0 →
        chart (Projectivization.mk ℝ x hx) =
          WithLp.toLp 2 (fun j => x (i.succAbove j) / x i)) ∧
      (∀ y : apm_t96j07_E3, ∃ h, chart.symm y =
        Projectivization.mk ℝ (Fin.insertNth i 1 (WithLp.ofLp y)) h))
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
  sorry

/-- Package the affine chart at the fourth coordinate axis. -/
theorem apm_t96j07_local_number_axis3
    (hgen :
  ∀ i : Fin 4, ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
      (∀ p, p ∈ chart.source ↔ p.rep i ≠ 0) ∧ chart.target = Set.univ ∧
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0), x i ≠ 0 →
        chart (Projectivization.mk ℝ x hx) =
          WithLp.toLp 2 (fun j => x (i.succAbove j) / x i)) ∧
      (∀ y : apm_t96j07_E3, ∃ h, chart.symm y =
        Projectivization.mk ℝ (Fin.insertNth i 1 (WithLp.ofLp y)) h))
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
    apm_t96j07_local_number_axis1 apm_t96j07_affine_chart f hformula apm_t96j07_diagonal_link_degree,
    apm_t96j07_local_number_axis2 apm_t96j07_affine_chart f hformula apm_t96j07_diagonal_link_degree,
    apm_t96j07_local_number_axis3 apm_t96j07_affine_chart f hformula apm_t96j07_diagonal_link_degree⟩

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

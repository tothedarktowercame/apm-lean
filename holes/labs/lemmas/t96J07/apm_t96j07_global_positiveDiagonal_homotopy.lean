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
  let ε : Fin 3 → ℝ := fun j => if 0 < b j then 1 else -1
  have hsign (j : Fin 3) :
      (0 < b j ∧ ε j = 1) ∨ (b j < 0 ∧ ε j = -1) := by
    rcases lt_or_gt_of_ne (hb j) with hj | hj
    · exact Or.inr ⟨hj, by simp [ε, not_lt.mpr hj.le]⟩
    · exact Or.inl ⟨hj, by simp [ε, hj]⟩
  let c : Set.Icc (0 : ℝ) 1 × apm_t96j07_S2 → Fin 3 → ℝ :=
    fun tx j => (1 - (tx.1.1 : ℝ)) * b j + (tx.1.1 : ℝ) * ε j
  have hc_ne (tx : Set.Icc (0 : ℝ) 1 × apm_t96j07_S2) (j : Fin 3) :
      c tx j ≠ 0 := by
    exact apm_t96j07_diagonal_link_degree_aux_interp (b j) (ε j) tx.1.1
      (hb j) (hsign j) tx.1.2.1 tx.1.2.2
  let g : Set.Icc (0 : ℝ) 1 × apm_t96j07_S2 → apm_t96j07_E3 := fun tx =>
    WithLp.toLp 2 (fun j => c tx j * tx.2.1 j)
  have hg_ne (tx : Set.Icc (0 : ℝ) 1 × apm_t96j07_S2) : g tx ≠ 0 := by
    exact apm_t96j07_diagonal_link_degree_aux_vector_ne_zero
      (c tx) (hc_ne tx) tx.2
  have hg : Continuous g := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (by fun_prop : Continuous (fun tx : Set.Icc (0 : ℝ) 1 × apm_t96j07_S2 =>
      c tx j * tx.2.1 j))
  have hn : Continuous (fun tx => ‖g tx‖⁻¹ • g tx) :=
    ((continuous_norm.comp hg).inv₀
      (fun tx => norm_ne_zero_iff.mpr (hg_ne tx))).smul hg
  refine ⟨{
    toFun := fun tx => ⟨‖g tx‖⁻¹ • g tx, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg_ne tx))⟩
    continuous_toFun := Continuous.subtype_mk hn (fun tx => by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg_ne tx)))
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    rcases hl x with ⟨hx, hxl⟩
    apply Subtype.ext
    rw [hxl]
    simp [g, c]
  · intro x
    rcases hl' x with ⟨hx, hxl⟩
    apply Subtype.ext
    rw [hxl]
    simp [g, c, ε]

/-- Seat: a sign-diagonal map (a product of coordinate reflections) acts on
`H₂(S²; ℤ) ≅ ℤ` by the product of the signs
(`ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℤ 2`,
functoriality; `topIso ℤ 1` for the orientation). -/
noncomputable def apm_t96j07_signDiagonal_H2_aux_product :
    List (Fin 3) → C(apm_t96j07_S2, apm_t96j07_S2)
  | [] => ContinuousMap.id _
  | i :: s => ConstructionTargets.CoefficientCoordinateReflections.reflectionMap i |>.comp
      (apm_t96j07_signDiagonal_H2_aux_product s)

lemma apm_t96j07_signDiagonal_H2_aux_coordinate (s : List (Fin 3)) (hs : s.Nodup)
    (x : apm_t96j07_S2) (j : Fin 3) :
    (apm_t96j07_signDiagonal_H2_aux_product s x).1 j =
      if j ∈ s then -x.1 j else x.1 j := by
  induction s with
  | nil => simp [apm_t96j07_signDiagonal_H2_aux_product]
  | cons i s ih =>
    have hi := List.nodup_cons.mp hs
    change ConstructionTargets.CoefficientCoordinateReflections.reflection i
      (apm_t96j07_signDiagonal_H2_aux_product s x).1 j = _
    rw [ConstructionTargets.CoefficientCoordinateReflections.reflection_apply, ih hi.2]
    by_cases hji : j = i
    · subst j
      simp [hi.1]
    · simp [hji]

lemma apm_t96j07_signDiagonal_H2_aux_homology (s : List (Fin 3)) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (apm_t96j07_signDiagonal_H2_aux_product s)) =
      ((-1 : ℤ) ^ s.length) • 𝟙 _ := by
  induction s with
  | nil => simp [apm_t96j07_signDiagonal_H2_aux_product]
  | cons i s ih =>
    have hc : TopCat.ofHom (apm_t96j07_signDiagonal_H2_aux_product (i :: s)) =
        TopCat.ofHom (apm_t96j07_signDiagonal_H2_aux_product s) ≫
          TopCat.ofHom
            (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap i) := rfl
    rw [hc, Functor.map_comp, ih,
      ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℤ 2 (by decide) i]
    simp [pow_succ, Preadditive.comp_neg]

theorem apm_t96j07_signDiagonal_H2 (ε : Fin 3 → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (l : C(apm_t96j07_S2, apm_t96j07_S2)) (hl : apm_t96j07_IsNormalizedDiagonal ε l) :
    ∃ orientation : apm_t96j07_H2S2 ≅ ModuleCat.of ℤ ℤ,
      ∀ z : apm_t96j07_H2S2,
        orientation.hom
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom l) z) =
          (if 0 < ∏ j, ε j then 1 else -1) * orientation.hom z := by
  let s := ([0, 1, 2] : List (Fin 3)).filter (fun j => ε j = -1)
  have hs : s.Nodup := (by decide : ([0, 1, 2] : List (Fin 3)).Nodup).filter _
  have hcoord (x : apm_t96j07_S2) (j : Fin 3) :
      (apm_t96j07_signDiagonal_H2_aux_product s x).1 j = ε j * x.1 j := by
    rw [apm_t96j07_signDiagonal_H2_aux_coordinate s hs]
    rcases hε j with hj | hj
    · norm_num [s, hj]
    · have hjmem : j ∈ ([0, 1, 2] : List (Fin 3)) := by
        fin_cases j <;> simp
      simp [s, hj, hjmem]
  have hnorm (x : apm_t96j07_S2) :
      ‖WithLp.toLp 2 (fun j ↦ ε j * x.1 j)‖ = 1 := by
    have hv : WithLp.toLp 2 (fun j ↦ ε j * x.1 j) =
        (apm_t96j07_signDiagonal_H2_aux_product s x).1 := by
      ext j
      exact (hcoord x j).symm
    rw [hv]
    simpa [Metric.mem_sphere, dist_zero_right] using
      (apm_t96j07_signDiagonal_H2_aux_product s x).2
  have hl_eq : l = apm_t96j07_signDiagonal_H2_aux_product s := by
    ext x j
    obtain ⟨hne, hx⟩ := hl x
    rw [hx]
    change (‖WithLp.toLp 2 (fun k ↦ ε k * x.1 k)‖⁻¹ •
      WithLp.toLp 2 (fun k ↦ ε k * x.1 k)) j = _
    rw [hnorm]
    simp [hcoord]
  let e := ConstructionTargets.CoefficientFirstReflection.topIso ℤ 1
  refine ⟨e, ?_⟩
  intro z
  have hmap := apm_t96j07_signDiagonal_H2_aux_homology s
  rw [hl_eq, hmap]
  change e.hom.hom (((((-1 : ℤ) ^ s.length) • 𝟙 _) :
      apm_t96j07_H2S2 ⟶ apm_t96j07_H2S2).hom z) = _
  have hsign : (if 0 < ∏ j, ε j then (1 : ℤ) else -1) = (-1 : ℤ) ^ s.length := by
    have he : ε = ![ε 0, ε 1, ε 2] := by
      funext j
      fin_cases j <;> rfl
    rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;>
      rcases hε 2 with h2 | h2
    all_goals rw [he]
    all_goals norm_num [s, h0, h1, h2, Fin.prod_univ_succ]
  rw [hsign]
  rcases neg_one_pow_eq_or ℤ s.length with hp | hp
  · rw [hp]
    simp
  · rw [hp]
    simp

/-- Seat (assembly from the three leaves above as hypotheses): homotopy
invariance (`SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`) and
`sign (∏ b j) = ∏ sign (b j)`. -/
lemma apm_t96j07_diagonal_link_degree_of_parts_aux_sign
    (b : Fin 3 → ℝ) (hb : ∀ j, b j ≠ 0) :
    (0 < ∏ j, (if 0 < b j then (1 : ℝ) else -1)) ↔ 0 < ∏ j, b j := by
  have hneg : ∀ j, ¬ 0 < b j → b j < 0 := by
    intro j hj
    exact lt_of_le_of_ne (le_of_not_gt hj) (hb j)
  by_cases h0 : 0 < b 0 <;> by_cases h1 : 0 < b 1 <;>
      by_cases h2 : 0 < b 2
  all_goals simp [Fin.prod_univ_succ, h0, h1, h2]
  all_goals try have hn0 := hneg 0 h0
  all_goals try have hn1 := hneg 1 h1
  all_goals try have hn2 := hneg 2 h2
  all_goals try positivity
  all_goals try exact mul_pos_of_neg_of_neg hn1 hn2
  all_goals try exact mul_pos_of_neg_of_neg hn0 (mul_neg_of_pos_of_neg h1 hn2)
  all_goals try exact mul_pos_of_neg_of_neg hn0 (mul_neg_of_neg_of_pos hn1 h2)
  · constructor
    · norm_num
    · intro hp
      have hn : b 0 * (b 1 * b 2) < 0 :=
        mul_neg_of_neg_of_pos hn0 (mul_pos_of_neg_of_neg hn1 hn2)
      linarith

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
  intro a ha
  let b : Fin 3 → ℝ := fun j => 1 - a j
  obtain ⟨link, hlink⟩ := hex b ha
  let ε : Fin 3 → ℝ := fun j => if 0 < b j then 1 else -1
  have hεne : ∀ j, ε j ≠ 0 := by
    intro j
    simp only [ε]
    split_ifs <;> norm_num
  obtain ⟨signLink, hsignLink⟩ := hex ε hεne
  have hε : ∀ j, ε j = 1 ∨ ε j = -1 := by
    intro j
    simp only [ε]
    split_ifs <;> simp
  obtain ⟨orientation, horientation⟩ := hsign ε hε signLink hsignLink
  obtain ⟨H⟩ := hhom b ha link signLink hlink hsignLink
  have hmap :=
    ConstructionTargets.CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy
      ℤ (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder H)
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero H)
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one H) 2
  refine ⟨link, hlink, orientation, ?_⟩
  intro z
  rw [hmap]
  rw [horientation]
  have hp := apm_t96j07_diagonal_link_degree_of_parts_aux_sign b ha
  change (0 < ∏ j, ε j) ↔ 0 < ∏ j, b j at hp
  have heq : (if 0 < ∏ j, ε j then (1 : ℤ) else -1) =
      (if 0 < ∏ j, b j then 1 else -1) := by
    by_cases h : 0 < ∏ j, ε j
    · simp [h, hp.mp h]
    · have hn : ¬ 0 < ∏ j, b j := fun hb => h (hp.mpr hb)
      simp [h, hn]
  rw [heq]

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

lemma apm_t96j07_affine_chart_aux_rep_ratio (i : Fin 4)
    (x : apm_t96j07_V) (hx : x ≠ 0) :
    (WithLp.toLp 2 (fun j =>
        (Projectivization.mk ℝ x hx).rep (i.succAbove j) /
          (Projectivization.mk ℝ x hx).rep i) : apm_t96j07_E3) =
      (WithLp.toLp 2 (fun j => x (i.succAbove j) / x i) : apm_t96j07_E3) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ x hx
  ext j
  have hi := congrFun ha i
  have hj := congrFun ha (i.succAbove j)
  change (a : ℝ) * x i = _ at hi
  change (a : ℝ) * x (i.succAbove j) = _ at hj
  simp only [WithLp.ofLp_toLp]
  rw [← hi, ← hj]
  field_simp [Units.ne_zero a]

noncomputable def apm_t96j07_affine_chart_aux_insert (i : Fin 4)
    (y : apm_t96j07_E3) : apm_t96j07_V :=
  fun k => i.succAboveCases (1 : ℝ) (WithLp.ofLp y) k

lemma apm_t96j07_affine_chart_aux_insert_ne (i : Fin 4)
    (y : apm_t96j07_E3) : apm_t96j07_affine_chart_aux_insert i y ≠ 0 := by
  intro h
  have hi := congrFun h i
  simpa [apm_t96j07_affine_chart_aux_insert] using hi

noncomputable def apm_t96j07_affine_chart_aux_coord (i : Fin 4)
    (p : apm_t96j07_RP3) : apm_t96j07_E3 :=
  WithLp.toLp 2 (fun j => p.rep (i.succAbove j) / p.rep i)

noncomputable def apm_t96j07_affine_chart_aux_inv (i : Fin 4)
    (y : apm_t96j07_E3) : apm_t96j07_RP3 :=
  Projectivization.mk ℝ (apm_t96j07_affine_chart_aux_insert i y)
    (apm_t96j07_affine_chart_aux_insert_ne i y)

lemma apm_t96j07_affine_chart_aux_open (i : Fin 4) :
    IsOpen {p : apm_t96j07_RP3 | p.rep i ≠ 0} := by
  rw [isOpen_coinduced]
  change IsOpen ((Projectivization.mk' ℝ) ⁻¹'
    {p : apm_t96j07_RP3 | p.rep i ≠ 0})
  have heq : (Projectivization.mk' ℝ) ⁻¹'
      {p : apm_t96j07_RP3 | p.rep i ≠ 0} =
      {v : {v : apm_t96j07_V // v ≠ 0} | v.1 i ≠ 0} := by
    ext v
    change (Projectivization.mk ℝ v.1 v.2).rep i ≠ 0 ↔ v.1 i ≠ 0
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1 v.2
    rw [← ha]
    change (a : ℝ) * v.1 i ≠ 0 ↔ v.1 i ≠ 0
    simp
  rw [heq]
  exact isOpen_compl_singleton.preimage
    ((continuous_apply i).comp continuous_subtype_val)

lemma apm_t96j07_affine_chart_aux_coord_cont (i : Fin 4) :
    ContinuousOn (apm_t96j07_affine_chart_aux_coord i)
      {p : apm_t96j07_RP3 | p.rep i ≠ 0} := by
  let s : Set apm_t96j07_RP3 := {p | p.rep i ≠ 0}
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
      v.1.1 (i.succAbove j) / v.1.1 i)) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    apply Continuous.div
    · exact (continuous_apply _).comp
        (continuous_subtype_val.comp continuous_subtype_val)
    · exact (continuous_apply _).comp
        (continuous_subtype_val.comp continuous_subtype_val)
    · intro v
      have hv := v.2
      change (Projectivization.mk ℝ v.1.1 v.1.2).rep i ≠ 0 at hv
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1.1 v.1.2
      rw [← ha] at hv
      exact (mul_ne_zero_iff.mp hv).2
  have heq : ({p : apm_t96j07_RP3 | p.rep i ≠ 0}.restrict
      (apm_t96j07_affine_chart_aux_coord i) ∘ qr) =
      (fun v : q ⁻¹' s => WithLp.toLp 2 (fun j : Fin 3 =>
        v.1.1 (i.succAbove j) / v.1.1 i)) := by
    funext v
    apply WithLp.ofLp_injective 2
    funext j
    change (Projectivization.mk ℝ v.1.1 v.1.2).rep (i.succAbove j) /
      (Projectivization.mk ℝ v.1.1 v.1.2).rep i = _
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v.1.1 v.1.2
    rw [← ha]
    change ((a : ℝ) * v.1.1 _ / ((a : ℝ) * v.1.1 i)) = _
    field_simp
  rw [heq]
  exact hc

lemma apm_t96j07_affine_chart_aux_inv_cont (i : Fin 4) :
    Continuous (apm_t96j07_affine_chart_aux_inv i) := by
  change Continuous (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℝ 3 ∘
    fun y : apm_t96j07_E3 =>
      ⟨apm_t96j07_affine_chart_aux_insert i y,
        apm_t96j07_affine_chart_aux_insert_ne i y⟩)
  apply (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℝ 3).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  refine i.succAboveCases ?_ (fun j => ?_) k
  · simpa [apm_t96j07_affine_chart_aux_insert] using
      (continuous_const : Continuous (fun _ : apm_t96j07_E3 => (1 : ℝ)))
  · simpa [apm_t96j07_affine_chart_aux_insert] using
      ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))

lemma apm_t96j07_affine_chart_aux_coord_inv (i : Fin 4)
    (y : apm_t96j07_E3) :
    apm_t96j07_affine_chart_aux_coord i
      (apm_t96j07_affine_chart_aux_inv i y) = y := by
  change WithLp.toLp 2 (fun j =>
    (Projectivization.mk ℝ (apm_t96j07_affine_chart_aux_insert i y)
      (apm_t96j07_affine_chart_aux_insert_ne i y)).rep (i.succAbove j) /
    (Projectivization.mk ℝ (apm_t96j07_affine_chart_aux_insert i y)
      (apm_t96j07_affine_chart_aux_insert_ne i y)).rep i) = y
  rw [apm_t96j07_affine_chart_aux_rep_ratio]
  apply WithLp.ofLp_injective 2
  funext j
  simp [apm_t96j07_affine_chart_aux_insert]

lemma apm_t96j07_affine_chart_aux_inv_coord (i : Fin 4)
    (p : apm_t96j07_RP3) (hp : p.rep i ≠ 0) :
    apm_t96j07_affine_chart_aux_inv i
      (apm_t96j07_affine_chart_aux_coord i p) = p := by
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨(p.rep i)⁻¹, ?_⟩
  funext k
  refine i.succAboveCases ?_ (fun j => ?_) k
  · simp [apm_t96j07_affine_chart_aux_insert, hp]
  · simp [apm_t96j07_affine_chart_aux_insert,
      apm_t96j07_affine_chart_aux_coord, div_eq_inv_mul]

noncomputable def apm_t96j07_affine_chart_aux_chart (i : Fin 4) :
    OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3 where
  toPartialEquiv := {
    toFun := apm_t96j07_affine_chart_aux_coord i
    invFun := apm_t96j07_affine_chart_aux_inv i
    source := {p | p.rep i ≠ 0}
    target := Set.univ
    map_source' := fun _ _ => Set.mem_univ _
    map_target' := by
      intro y _
      change (apm_t96j07_affine_chart_aux_inv i y).rep i ≠ 0
      unfold apm_t96j07_affine_chart_aux_inv
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ
        (apm_t96j07_affine_chart_aux_insert i y)
        (apm_t96j07_affine_chart_aux_insert_ne i y)
      rw [← ha]
      change (a : ℝ) * apm_t96j07_affine_chart_aux_insert i y i ≠ 0
      simp [apm_t96j07_affine_chart_aux_insert]
    left_inv' := apm_t96j07_affine_chart_aux_inv_coord i
    right_inv' := fun y _ => apm_t96j07_affine_chart_aux_coord_inv i y }
  open_source := apm_t96j07_affine_chart_aux_open i
  open_target := isOpen_univ
  continuousOn_toFun := apm_t96j07_affine_chart_aux_coord_cont i
  continuousOn_invFun := (apm_t96j07_affine_chart_aux_inv_cont i).continuousOn

theorem apm_t96j07_affine_chart :
    ∀ i : Fin 4, ∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
      (∀ p, p ∈ chart.source ↔ p.rep i ≠ 0) ∧ chart.target = Set.univ ∧
      (∀ (x : apm_t96j07_V) (hx : x ≠ 0), x i ≠ 0 →
        chart (Projectivization.mk ℝ x hx) =
          WithLp.toLp 2 (fun j => x (i.succAbove j) / x i)) ∧
      (∀ y : apm_t96j07_E3, ∃ h, chart.symm y =
        Projectivization.mk ℝ (Fin.insertNth i 1 (WithLp.ofLp y)) h) := by
  intro i
  refine ⟨apm_t96j07_affine_chart_aux_chart i, ?_, rfl, ?_, ?_⟩
  · intro p
    rfl
  · intro x hx hxi
    exact apm_t96j07_affine_chart_aux_rep_ratio i x hx
  · intro y
    refine ⟨apm_t96j07_affine_chart_aux_insert_ne i y, ?_⟩
    rfl

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

lemma apm_t96j07_local_number_axis0_aux_chart_rep_ne
    (v : apm_t96j07_V) (hv : v ≠ 0) (i : Fin 4) (hi : v i ≠ 0) :
    (Projectivization.mk ℝ v hv).rep i ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  have hai := congrFun ha i
  rw [← hai]
  exact mul_ne_zero (Units.ne_zero a) hi

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
  obtain ⟨chart, hsource, htarget, hchart, hinv⟩ := hgen 0
  refine ⟨chart, ?_, ?_, htarget, ?_, ?_, ?_⟩
  · rw [hsource]
    apply apm_t96j07_local_number_axis0_aux_chart_rep_ne
    simp [apm_t96j07_axis]
  · rw [hchart _ _ (by simp [apm_t96j07_axis])]
    ext j
    simp [apm_t96j07_axis]
  · intro y
    apply chart.map_target
    rw [htarget]
    exact Set.mem_univ y
  · intro y
    obtain ⟨hv, hy⟩ := hinv y
    rw [hy, hformula]
    rw [hsource]
    apply apm_t96j07_local_number_axis0_aux_chart_rep_ne
    show apm_t96j07_A (Fin.insertNth 0 1 (WithLp.ofLp y)) 0 ≠ 0
    norm_num [apm_t96j07_A]
  · intro y
    obtain ⟨hv, hy⟩ := hinv y
    rw [hy, hformula]
    have hA0 : apm_t96j07_A (Fin.insertNth 0 1 (WithLp.ofLp y)) 0 ≠ 0 := by
      norm_num [apm_t96j07_A]
    rw [hchart _ _ hA0]
    ext j
    simp only [WithLp.ofLp_toLp, apm_t96j07_A, Fin.succAbove_zero,
      Fin.insertNth_zero, Fin.cons_succ, Fin.cons_zero]
    simp only [Fin.val_succ, Fin.val_zero, cast_eq, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_add, mul_one, div_one]
    ring

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
lemma apm_t96j07_local_number_axis1_aux_rep_ne
    (v : apm_t96j07_V) (hv : v ≠ 0) (i : Fin 4) (hi : v i ≠ 0) :
    (Projectivization.mk ℝ v hv).rep i ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  have hui := congrFun hu i
  rw [← hui]
  exact mul_ne_zero (Units.ne_zero u) hi

lemma apm_t96j07_local_number_axis1_aux_chart
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
      (Projectivization.mk ℝ (apm_t96j07_axis 1) (by
        intro h; have := congrFun h 1; simp [apm_t96j07_axis] at this)) ∈ chart.source ∧
      chart (Projectivization.mk ℝ (apm_t96j07_axis 1) (by
        intro h; have := congrFun h 1; simp [apm_t96j07_axis] at this)) = 0 ∧
      chart.target = Set.univ ∧
      (∀ y, chart.symm y ∈ chart.source) ∧
      (∀ y, f (chart.symm y) ∈ chart.source) ∧
      (∀ y, chart (f (chart.symm y)) =
        WithLp.toLp 2 (fun j => (![1 / 2, 3 / 2, 2] : Fin 3 → ℝ) j * y j)) := by
  obtain ⟨chart, hsource, htarget, hchart, hinv⟩ := hgen 1
  refine ⟨chart, ?_, ?_, htarget, ?_, ?_, ?_⟩
  · rw [hsource]
    apply apm_t96j07_local_number_axis1_aux_rep_ne
    simp [apm_t96j07_axis]
  · rw [hchart _ _ (by simp [apm_t96j07_axis])]
    ext j
    fin_cases j <;> simp [apm_t96j07_axis, Fin.succAbove]
  · intro y
    apply chart.map_target
    rw [htarget]
    exact Set.mem_univ y
  · intro y
    obtain ⟨hv, hy⟩ := hinv y
    rw [hy, hformula, hsource]
    apply apm_t96j07_local_number_axis1_aux_rep_ne
    show apm_t96j07_A (Fin.insertNth 1 1 (WithLp.ofLp y)) 1 ≠ 0
    norm_num [apm_t96j07_A]
  · intro y
    obtain ⟨hv, hy⟩ := hinv y
    rw [hy, hformula]
    have hA1 : apm_t96j07_A (Fin.insertNth 1 1 (WithLp.ofLp y)) 1 ≠ 0 := by
      norm_num [apm_t96j07_A]
    rw [hchart _ _ hA1]
    ext j
    fin_cases j <;> simp [apm_t96j07_A, Fin.succAbove, Fin.insertNth,
      Fin.succAboveCases, Fin.lt_def] <;> ring

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
  obtain ⟨chart, hq, hq0, htarget, hinv, hfsource, haction⟩ :=
    apm_t96j07_local_number_axis1_aux_chart hgen f hformula
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
    fin_cases j <;> norm_num at hj ⊢ <;> linarith
  · let a : Fin 3 → ℝ := ![1 / 2, 3 / 2, 2]
    obtain ⟨link, hlink, orientation, horientation⟩ := hdegree a (by
      intro j
      fin_cases j <;> norm_num [a])
    refine ⟨link, ?_, orientation, ?_⟩
    · intro x
      have hxsource := hinv ((1 : ℝ) • x.1)
      have hfxsource := hfsource ((1 : ℝ) • x.1)
      refine ⟨hxsource, hfxsource, ?_⟩
      obtain ⟨hne, heq⟩ := hlink x
      have hd : (1 : ℝ) • x.1 - chart (f (chart.symm ((1 : ℝ) • x.1))) =
          WithLp.toLp 2 (fun j => (1 - a j) * x.1 j) := by
        rw [haction]
        ext j
        fin_cases j <;> simp [a] <;> ring
      refine ⟨?_, ?_⟩
      · rw [hd]
        exact hne
      · rw [heq]
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        rw [hd]
    · intro z
      rw [horientation]
      have hp : 0 < ∏ j, (1 - a j) := by
        norm_num [a, Fin.prod_univ_succ]
      simp [hp]

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
  obtain ⟨chart, hsource, htarget, hcoord, hinv⟩ := hgen 3
  let a : Fin 3 → ℝ := ![(1 : ℝ) / 4, 1 / 2, 3 / 4]
  have haw : ∀ j, a j =
      ((Fin.succAbove (3 : Fin 4) j).val + 1 : ℝ) / 4 := by
    intro j
    fin_cases j <;> norm_num [a, Fin.succAbove, Fin.lt_iff_val_lt_val]
  have ha : ∀ j, 1 - a j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num [a]
  obtain ⟨link, hlink, orientation, horientation⟩ := hdegree a ha
  have haction : ∀ y : apm_t96j07_E3,
      f (chart.symm y) ∈ chart.source ∧
      chart (f (chart.symm y)) =
        WithLp.toLp 2 (fun j => a j * WithLp.ofLp y j) := by
    intro y
    obtain ⟨hv, hy⟩ := hinv y
    let v : apm_t96j07_V := Fin.insertNth 3 1 (WithLp.ofLp y)
    have hv3 : v 3 ≠ 0 := by simp [v]
    have hAv3 : apm_t96j07_A v 3 ≠ 0 := by
      norm_num [apm_t96j07_A, v]
    rw [hy, hformula v hv]
    constructor
    · rw [hsource]
      obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℝ
        (apm_t96j07_A v) (apm_t96j07_A_ne_zero hv)
      rw [← hu]
      exact mul_ne_zero (Units.ne_zero u) hAv3
    · rw [hcoord _ _ hAv3]
      apply WithLp.ofLp_injective 2
      funext j
      rw [WithLp.ofLp_toLp]
      have hs : v ((3 : Fin 4).succAbove j) = WithLp.ofLp y j := by
        fin_cases j <;> rfl
      simp only [apm_t96j07_A, hs]
      rw [show v 3 = 1 by simp [v], haw]
      fin_cases j <;> norm_num [Fin.succAbove, Fin.lt_def] <;> ring
  refine ⟨chart, ?_, ?_, 1, by norm_num, ?_, ?_, ?_, link, ?_, orientation, ?_⟩
  · rw [hsource]
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℝ
      (apm_t96j07_axis 3) (by
        intro h
        have hh := congrFun h 3
        simp [apm_t96j07_axis] at hh)
    rw [← hu]
    exact mul_ne_zero (Units.ne_zero u) (by simp [apm_t96j07_axis])
  · rw [hcoord (apm_t96j07_axis 3) (by
        intro h
        have hh := congrFun h 3
        simp [apm_t96j07_axis] at hh) (by simp [apm_t96j07_axis])]
    apply WithLp.ofLp_injective 2
    funext j
    simp [apm_t96j07_axis]
  · rw [htarget]
    exact Set.subset_univ _
  · intro y hy
    exact (haction y).1
  · intro y hy heq
    rw [(haction y).2] at heq
    apply WithLp.ofLp_injective 2
    funext j
    have hj := congrArg (fun w : apm_t96j07_E3 => WithLp.ofLp w j) heq
    simp only [WithLp.ofLp_toLp] at hj
    fin_cases j
    · norm_num [a] at hj
      simpa using (show WithLp.ofLp y 0 = 0 by linarith [hj])
    · norm_num [a] at hj
      simpa using (show WithLp.ofLp y 1 = 0 by linarith [hj])
    · norm_num [a] at hj
      change (3 / 4 : ℝ) * WithLp.ofLp y 2 = WithLp.ofLp y 2 at hj
      change WithLp.ofLp y 2 = 0
      linarith [hj]
  · intro x
    have hs : chart.symm x.1 ∈ chart.source := chart.map_target (by
      rw [htarget]
      exact Set.mem_univ _)
    have hact := haction x.1
    refine ⟨by simpa only [one_smul] using hs,
      by simpa only [one_smul] using hact.1, ?_⟩
    have hdisp : (1 : ℝ) • x.1 - chart (f (chart.symm ((1 : ℝ) • x.1))) =
        WithLp.toLp 2 (fun j => (1 - a j) * x.1 j) := by
      simp only [one_smul]
      rw [hact.2]
      apply WithLp.ofLp_injective 2
      funext j
      change WithLp.ofLp x.1 j - a j * WithLp.ofLp x.1 j =
          (1 - a j) * WithLp.ofLp x.1 j
      ring
    obtain ⟨hne, heq⟩ := hlink x
    refine ⟨by rw [hdisp]; exact hne, ?_⟩
    rw [heq]
    apply Subtype.ext
    simp only [Subtype.coe_mk]
    rw [hdisp]
  · intro z
    rw [horientation]
    have hprod : (∏ j, (1 - a j)) = (3 / 32 : ℝ) := by
      norm_num [a, Fin.prod_univ_succ]
    rw [hprod]
    norm_num

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

/-- Seat: the positive diagonal path `diag(1,1+t,1+2t,1+3t)` descends to a
homotopy from the identity to `f`. -/
-- BEGIN SEAT AREA
theorem apm_t96j07_global_positiveDiagonal_homotopy
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) :
    ContinuousMap.Homotopic (ContinuousMap.id apm_t96j07_RP3) f := by
  sorry
-- END SEAT AREA

/-- Seat: homotopic maps induce equal maps on rational singular homology.
The homotopy is an explicit hypothesis, so this leaf is independent of the
positive-diagonal construction. -/
theorem apm_t96j07_global_HQmap_eq_id
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hhom : ContinuousMap.Homotopic (ContinuousMap.id apm_t96j07_RP3) f) :
    ∀ k : ℕ, apm_t96j07_HQmap k f = 𝟙 (apm_t96j07_HQ k) := by
  sorry

/-- LIBRARY seat: the rational singular homology of `ℝP³` is `ℚ` in
degrees zero and three and zero in degrees one and two.  Keeping these four
bases together avoids duplicating the missing cellular-homology foundation. -/
theorem apm_t96j07_global_rationalHomology_bases :
    Nonempty (apm_t96j07_HQ 0 ≅ ModuleCat.of ℚ ℚ) ∧
    Nonempty (apm_t96j07_HQ 1 ≅ ModuleCat.of ℚ (Fin 0 → ℚ)) ∧
    Nonempty (apm_t96j07_HQ 2 ≅ ModuleCat.of ℚ (Fin 0 → ℚ)) ∧
    Nonempty (apm_t96j07_HQ 3 ≅ ModuleCat.of ℚ ℚ) := by
  sorry

/-- Sorry-free algebraic assembly of the homotopy and rational-homology
inputs.  Every substantial input is explicit, so its seats are parallel. -/
theorem apm_t96j07_global_number_of_parts
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hmap : ∀ k : ℕ, apm_t96j07_HQmap k f = 𝟙 (apm_t96j07_HQ k))
    (h0 : Nonempty (apm_t96j07_HQ 0 ≅ ModuleCat.of ℚ ℚ))
    (h1 : Nonempty (apm_t96j07_HQ 1 ≅ ModuleCat.of ℚ (Fin 0 → ℚ)))
    (h2 : Nonempty (apm_t96j07_HQ 2 ≅ ModuleCat.of ℚ (Fin 0 → ℚ)))
    (h3 : Nonempty (apm_t96j07_HQ 3 ≅ ModuleCat.of ℚ ℚ)) :
    apm_t96j07_HasLefschetzNumber f 0 := by
  rcases h0 with ⟨e0⟩
  rcases h1 with ⟨e1⟩
  rcases h2 with ⟨e2⟩
  rcases h3 with ⟨e3⟩
  refine ⟨e0, e1, e2, e3, ?_⟩
  rw [hmap 0, hmap 1, hmap 2, hmap 3]
  simp

/-- Compute the rational-homological Lefschetz number.  This is only the
sorry-free wiring of the independent geometric and homological leaves. -/
theorem apm_t96j07_global_number
    (f : C(apm_t96j07_RP3, apm_t96j07_RP3))
    (hformula : ∀ (x : apm_t96j07_V) (hx : x ≠ 0),
      f (Projectivization.mk ℝ x hx) =
        Projectivization.mk ℝ (apm_t96j07_A x) (apm_t96j07_A_ne_zero hx)) :
    apm_t96j07_HasLefschetzNumber f 0 := by
  apply apm_t96j07_global_number_of_parts f
  · exact apm_t96j07_global_HQmap_eq_id f
      (apm_t96j07_global_positiveDiagonal_homotopy f hformula)
  · exact apm_t96j07_global_rationalHomology_bases.1
  · exact apm_t96j07_global_rationalHomology_bases.2.1
  · exact apm_t96j07_global_rationalHomology_bases.2.2.1
  · exact apm_t96j07_global_rationalHomology_bases.2.2.2

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

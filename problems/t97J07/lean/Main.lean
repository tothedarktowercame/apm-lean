import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.t99J05Closure
import ConstructionTargets.CoefficientH0
import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.T99J05ArbitraryAffineChartContinuity
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

/-!
# APM t97J07 — Lefschetz data for a projective linear map

We use Mathlib's genuine projectivization of `ℂ³`.  The fixed component and
isolated fixed point are concrete subsets/points of that projectivization.
The affine parametrizations below pin the local representatives of the
projective map.  Thus the derivatives used for the local indices are derived
from the actual map rather than supplied as unrelated matrices.

## Statement repairs

The source alternates between `g` and `hat g`.  We reserve `t97J07Linear` for
the linear map `diag(1,1,3)` on `ℂ³` and `t97J07Map` for its projectivization.
-/

open scoped LinearAlgebra.Projectivization Matrix
open scoped ContinuousMap

abbrev T97J07CP2 := ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 2

def t97J07Linear : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun z i := if i = 2 then 3 * z i else z i
  map_add' x y := by
    funext i
    by_cases hi : i = 2 <;> simp [hi, mul_add]
  map_smul' c x := by
    funext i
    by_cases hi : i = 2 <;> simp [hi]
    ring

noncomputable def t97J07Map : T97J07CP2 → T97J07CP2 := fun p ↦
  p.map t97J07Linear (by
    intro x y h
    funext i
    have hi := congrFun h i
    by_cases h2 : i = 2
    · subst i
      simpa [t97J07Linear] using
        (mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hi)
    · simpa [t97J07Linear, h2] using hi)

def t97J07FixedLine : Set T97J07CP2 :=
  {p | p.rep 2 = 0}

noncomputable def t97J07IsolatedPoint : T97J07CP2 :=
  Projectivization.mk ℂ (Pi.single 2 1) (by
    intro h
    have := congrFun h 2
    simp at this)

/-- Affine coordinates normal to the fixed line, based at `[1:a:0]`. -/
noncomputable def t97J07LineChart (a u : ℂ) : T97J07CP2 :=
  Projectivization.mk ℂ ![1, a, u] (by
    intro h
    have := congrFun h 0
    simp at this)

/-- The local representative in the normal coordinate to the fixed line. -/
def t97J07LineLocal (u : ℂ) : ℂ := 3 * u

/-- Affine coordinates based at the isolated point `[0:0:1]`. -/
noncomputable def t97J07PointChart (w : Fin 2 → ℂ) : T97J07CP2 :=
  Projectivization.mk ℂ ![w 0, w 1, 1] (by
    intro h
    have := congrFun h 2
    simp at this)

/-- The local representative at `[0:0:1]`. -/
noncomputable def t97J07PointLocal (w : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i ↦ w i / 3

/-- Real determinant of `I-Dg` on the complex normal line to the fixed
projective line. -/
noncomputable def t97J07LineNormalDet : ℝ :=
  Complex.normSq (1 - fderiv ℂ t97J07LineLocal 0 1)

/-- Real determinant of `I-Dg` in the two complex affine coordinates at the
isolated fixed point. -/
noncomputable def t97J07PointDet : ℝ :=
  Complex.normSq
    ((1 - (fderiv ℂ t97J07PointLocal 0 (Pi.single 0 1)) 0) *
     (1 - (fderiv ℂ t97J07PointLocal 0 (Pi.single 1 1)) 1))

noncomputable def t97J07IndexFromDet (d : ℝ) : ℤ :=
  if 0 < d then 1 else if d < 0 then -1 else 0

/-- The fixed-line contribution is its Euler characteristic (`2`) times the
normal Lefschetz index. -/
noncomputable def t97J07LineContribution : ℤ :=
  2 * t97J07IndexFromDet t97J07LineNormalDet

/-- The normal derivative is the expected scalar multiplication. -/
lemma t97J07LineLocal_fderiv :
    fderiv ℂ t97J07LineLocal 0 1 = 3 := by
  have h := ((hasFDerivAt_id (𝕜 := ℂ) (0 : ℂ)).const_mul (3 : ℂ)).fderiv
  have h' := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) h
  simpa [t97J07LineLocal] using h'

lemma t97J07LineNormalDet_eq : t97J07LineNormalDet = 4 := by
  rw [t97J07LineNormalDet, t97J07LineLocal_fderiv]
  norm_num [Complex.normSq_apply]

lemma t97J07LineIndex_eq :
    t97J07IndexFromDet t97J07LineNormalDet = 1 := by
  simp [t97J07IndexFromDet, t97J07LineNormalDet_eq]

lemma t97J07LineContribution_eq : t97J07LineContribution = 2 := by
  simp [t97J07LineContribution, t97J07LineIndex_eq]

/-- The isolated-point affine representative has coordinatewise derivative
`1/3`. -/
lemma t97J07PointLocal_fderiv (i : Fin 2) :
    fderiv ℂ t97J07PointLocal 0 (Pi.single i 1) =
      Pi.single i (1 / 3) := by
  have hfun : t97J07PointLocal = (1 / 3 : ℂ) •
      (fun w : Fin 2 → ℂ ↦ w) := by
    funext w j
    simp [t97J07PointLocal, Pi.smul_apply, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have h := ((hasFDerivAt_id (𝕜 := ℂ) (0 : Fin 2 → ℂ)).const_smul
    (1 / 3 : ℂ)).fderiv
  have h' := congrArg
    (fun L : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) ↦ L (Pi.single i 1)) h
  ext j
  have h'' := congrArg (fun v : Fin 2 → ℂ ↦ v j) h'
  simpa [Function.id_def, Pi.single_apply] using h''

lemma t97J07PointDet_eq : t97J07PointDet = (16 : ℝ) / 81 := by
  rw [t97J07PointDet, t97J07PointLocal_fderiv, t97J07PointLocal_fderiv]
  norm_num [Complex.normSq_apply, Pi.single_apply]

lemma t97J07PointIndex_eq :
    t97J07IndexFromDet t97J07PointDet = 1 := by
  simp [t97J07IndexFromDet, t97J07PointDet_eq]

lemma t97J07TotalContribution_eq :
    t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3 := by
  simp [t97J07LineContribution_eq, t97J07PointIndex_eq]

lemma t97J07LineChart_map (a u : ℂ) :
    t97J07Map (t97J07LineChart a u) =
      t97J07LineChart a (t97J07LineLocal u) := by
  simp only [t97J07Map, t97J07LineChart, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [t97J07Linear, t97J07LineLocal]

lemma t97J07PointChart_map (w : Fin 2 → ℂ) :
    t97J07Map (t97J07PointChart w) =
      t97J07PointChart (t97J07PointLocal w) := by
  simp only [t97J07Map, t97J07PointChart, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨3, ?_⟩
  funext i
  fin_cases i <;> simp [t97J07Linear, t97J07PointLocal] <;> ring

lemma t97J07IsolatedPoint_not_mem :
    t97J07IsolatedPoint ∉ t97J07FixedLine := by
  intro h
  change (t97J07IsolatedPoint.rep 2) = 0 at h
  have hv : ((Pi.single (2 : Fin 3) (1 : ℂ)) : Fin 3 → ℂ) ≠ 0 := by
    intro hz
    have := congrFun hz 2
    simp at this
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    ((Pi.single (2 : Fin 3) (1 : ℂ)) : Fin 3 → ℂ) hv
  have ha2 := congrFun ha 2
  have hr : (Projectivization.mk ℂ
      ((Pi.single (2 : Fin 3) (1 : ℂ)) : Fin 3 → ℂ) hv).rep 2 = 0 := by
    simpa [t97J07IsolatedPoint] using h
  rw [hr] at ha2
  apply a.ne_zero
  simpa [Units.smul_def] using ha2

/-- Why this unblocks `apm_t97j07`: this is the missing classification of
all fixed points of the projectivized diagonal map.  It asserts that a fixed
projective class is exactly either a class with zero third coordinate or the
third coordinate axis, which is the sole unresolved conjunct below. -/
theorem apm_t97J07_bridge_1 :
    {p : T97J07CP2 | t97J07Map p = p} =
      t97J07FixedLine ∪ {t97J07IsolatedPoint} := by
  ext p
  constructor
  · intro hp
    change t97J07Map p = p at hp
    have hp' :
        Projectivization.mk ℂ (t97J07Linear p.rep)
            (by
              intro h
              apply p.rep_nonzero
              funext i
              have hi := congrFun h i
              by_cases h2 : i = 2
              · subst i
                have hi' : (3 : ℂ) * p.rep 2 = 3 * 0 := by
                  simpa [t97J07Linear] using hi
                exact mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hi'
              · simpa [t97J07Linear, h2] using hi) =
          Projectivization.mk ℂ p.rep p.rep_nonzero := by
      rw [← Projectivization.mk_rep p] at hp
      simpa only [t97J07Map, Projectivization.map_mk] using hp
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).1 hp'
    by_cases h2 : p.rep 2 = 0
    · exact Or.inl h2
    · right
      have ha2 := congrFun ha 2
      have ae : a = 3 := by
        simp only [Pi.smul_apply, smul_eq_mul, t97J07Linear, if_pos] at ha2
        exact mul_right_cancel₀ h2 ha2
      have h0 : p.rep 0 = 0 := by
        have ha0 := congrFun ha 0
        rw [ae] at ha0
        norm_num [t97J07Linear, show (0 : Fin 3) ≠ 2 by decide] at ha0
        apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
        linear_combination ha0
      have h1 : p.rep 1 = 0 := by
        have ha1 := congrFun ha 1
        rw [ae] at ha1
        norm_num [t97J07Linear, show (1 : Fin 3) ≠ 2 by decide] at ha1
        apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
        linear_combination ha1
      change p = t97J07IsolatedPoint
      rw [← Projectivization.mk_rep p]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨p.rep 2, ?_⟩
      funext i
      fin_cases i <;> simp [Pi.single_apply, h0, h1]
  · rintro (hp | hp)
    · change t97J07Map p = p
      change p.rep 2 = 0 at hp
      rw [← Projectivization.mk_rep p]
      simp only [t97J07Map, Projectivization.map_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨1, ?_⟩
      funext i
      by_cases hi : i = 2
      · subst i
        simp [t97J07Linear, hp]
      · simp [t97J07Linear, hi]
    · simp only [Set.mem_singleton_iff] at hp
      subst p
      change t97J07Map t97J07IsolatedPoint = t97J07IsolatedPoint
      simp only [t97J07Map, t97J07IsolatedPoint,
        Projectivization.map_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨3, ?_⟩
      funext i
      fin_cases i <;> simp [t97J07Linear, Pi.single_apply]

/-- The exact rational homology data needed to compute the Euler
characteristic of the literal quotient-topological `CP²`. -/
structure T97J07CP2RationalHomologyData where
  finiteDimensional : ∀ k,
    FiniteDimensional ℚ
      (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 k)
  vanishesAbove : ∀ k, 4 < k →
    Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 k)
  zeroEquiv :
    ConstructionTargets.RationalLefschetz.Homology T97J07CP2 0 ≃ₗ[ℚ] ℚ
  oneSubsingleton :
    Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 1)
  twoEquiv :
    ConstructionTargets.RationalLefschetz.Homology T97J07CP2 2 ≃ₗ[ℚ] ℚ
  threeSubsingleton :
    Subsingleton
      (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 3)
  fourEquiv :
    ConstructionTargets.RationalLefschetz.Homology T97J07CP2 4 ≃ₗ[ℚ] ℚ

/-- Specialize the shared finite-complex-projective-space homology interface
to the exact `CP²` certificate consumed below. -/
noncomputable def t97J07_cp2RationalHomologyData_of_shared
    (h : ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 2) :
    T97J07CP2RationalHomologyData where
  finiteDimensional := h.finiteDimensional
  vanishesAbove := h.vanishesAbove
  zeroEquiv := by
    simpa using h.evenEquiv (0 : Fin 3)
  oneSubsingleton := h.vanishesOdd 1 (by exact ⟨0, by omega⟩)
  twoEquiv := by
    simpa using h.evenEquiv (1 : Fin 3)
  threeSubsingleton := h.vanishesOdd 3 (by exact ⟨1, by omega⟩)
  fourEquiv := by
    simpa using h.evenEquiv (2 : Fin 3)

/-- The shared `CP⁰` base and one-cell successor theorem produce the exact
consumer certificate at dimension two. -/
noncomputable def t97J07_cp2RationalHomologyData_of_zero_of_step
    (hzero : ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 0)
    (hstep : ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyStep) :
    T97J07CP2RationalHomologyData :=
  t97J07_cp2RationalHomologyData_of_shared
    (ConstructionTargets.t99J05Closure.complexProjectiveRationalHomologyData_of_zero_of_step
      hzero hstep 2)

/-- The literal one-point quotient `CP⁰` supplies the base case for the shared
finite complex-projective-space filtration. -/
noncomputable def t97J07_complexProjectiveRationalHomologyData_zero :
    ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 0 := by
  letI : Subsingleton
      (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) :=
    ConstructionTargets.t99J05Closure.cp_zero_subsingleton
  let p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0 :=
    ConstructionTargets.ProjectiveSpaceTopology.coordinateLine ℂ 0 0
  letI : Nonempty
      (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) := ⟨p⟩
  letI : ContractibleSpace
      (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) := inferInstance
  let h0 := ConstructionTargets.CoefficientH0.h0Iso ℚ p
  refine {
    finiteDimensional := fun k => ?_
    vanishesAbove := fun k hk => ?_
    vanishesOdd := fun k hk => ?_
    evenEquiv := fun i => ?_ }
  · by_cases hk : k = 0
    · subst k
      exact h0.toLinearEquiv.symm.finiteDimensional
    · have hz := ConstructionTargets.CoefficientContractiblePair.higher_zero
          ℚ (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) k hk
      letI : Subsingleton
          (ConstructionTargets.RationalLefschetz.Homology
            (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) k) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact FiniteDimensional.of_injective
        (0 : ConstructionTargets.RationalLefschetz.Homology
          (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) k →ₗ[ℚ] ℚ)
        (Function.injective_of_subsingleton _)
  · exact ModuleCat.isZero_iff_subsingleton.mp
      (ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ
        (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) k (by omega))
  · exact ModuleCat.isZero_iff_subsingleton.mp
      (ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ
        (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 0) k (by
          rcases hk with ⟨j, rfl⟩
          omega))
  · have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa using h0.toLinearEquiv

/-- The nonzero-vector presentation of the literal complex projective line
is path connected. -/
theorem t97J07_cp1_nonzeroVectors_pathConnected :
    PathConnectedSpace
      (ConstructionTargets.ProjectiveSpaceTopology.NonzeroVectors ℂ 1) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  change IsPathConnected ({0}ᶜ : Set (Fin 2 → ℂ))
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank]
  norm_num [Module.finrank_fin_fun]

/-- Hence the exact quotient-topological `CP¹` used by the filtration is
path connected. -/
theorem t97J07_cp1_pathConnected :
    PathConnectedSpace
      (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1) := by
  letI : PathConnectedSpace
      (ConstructionTargets.ProjectiveSpaceTopology.NonzeroVectors ℂ 1) :=
    t97J07_cp1_nonzeroVectors_pathConnected
  exact (ConstructionTargets.ProjectiveSpaceTopology.surjective_quotientMap ℂ 1).pathConnectedSpace
    (ConstructionTargets.ProjectiveSpaceTopology.continuous_quotientMap ℂ 1)

/-- The degree-zero part of the bounded `CP⁰ → CP¹` filtration step. -/
noncomputable def t97J07_cp1_rationalH0Iso :
    ConstructionTargets.RationalLefschetz.Homology
        (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1) 0 ≃ₗ[ℚ] ℚ := by
  letI : PathConnectedSpace
      (ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1) :=
    t97J07_cp1_pathConnected
  exact (ConstructionTargets.CoefficientH0.h0Iso ℚ
    (ConstructionTargets.ProjectiveSpaceTopology.coordinateLine ℂ 1 0)).toLinearEquiv

/-- The two literal affine patches form the open cover of `CP¹` used by the
bounded Mayer--Vietoris computation. -/
theorem t97J07_cp1_twoAffine_openCover :
    IsOpen {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 |
      Projectivization.rep p 0 ≠ 0} ∧
    IsOpen {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 |
      Projectivization.rep p 1 ≠ 0} ∧
    {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 |
      Projectivization.rep p 0 ≠ 0} ∪
      {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 |
        Projectivization.rep p 1 ≠ 0} = Set.univ := by
  refine ⟨ConstructionTargets.ComplexProjectiveChartTargets.affineSource_isOpen 0,
    ConstructionTargets.ComplexProjectiveChartTargets.affineSource_isOpen 1, ?_⟩
  ext p
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  by_contra h
  push_neg at h
  apply p.rep_nonzero
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

/-- The inverse affine-coordinate construction really lands in its named
patch.  This is the point-set bridge needed before applying coefficient
homology to the two pieces and their punctured intersection. -/
theorem t97J07_cp1_chartInverse_rep_ne (i : Fin 2)
    (z : ConstructionTargets.ComplexProjectiveChartTargets.AffineCoordinates i) :
    Projectivization.rep
      (ConstructionTargets.ComplexProjectiveChartTargets.chartInverse i z) i ≠ 0 := by
  let v : Fin 2 → ℂ := fun j => if h : j = i then 1 else z ⟨j, h⟩
  have hv : v ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [v] at hi
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (Projectivization.mk ℂ v hv).rep i ≠ 0
  rw [← ha]
  change a.1 * v i ≠ 0
  simp [v]

/-- Each literal affine patch of `CP¹` is exactly its affine coordinate
space, at the level of points. -/
noncomputable def t97J07_cp1_affinePatchEquiv (i : Fin 2) :
    {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 //
      Projectivization.rep p i ≠ 0} ≃
      ConstructionTargets.ComplexProjectiveChartTargets.AffineCoordinates i where
  toFun p := ConstructionTargets.ComplexProjectiveChartTargets.coordinates i p.1
  invFun z := ⟨ConstructionTargets.ComplexProjectiveChartTargets.chartInverse i z,
    t97J07_cp1_chartInverse_rep_ne i z⟩
  left_inv p := by
    apply Subtype.ext
    exact ConstructionTargets.ComplexProjectiveChartTargets.chartInverse_coordinates
      i p.1 p.2
  right_inv z :=
    ConstructionTargets.ComplexProjectiveChartTargets.coordinates_chartInverse i z

/-- The shared arbitrary-affine-chart continuity theorem upgrades the exact
point-set equivalence to a homeomorphism. -/
noncomputable def t97J07_cp1_affinePatchHomeomorph (i : Fin 2) :
    {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 //
      Projectivization.rep p i ≠ 0} ≃ₜ
      ConstructionTargets.ComplexProjectiveChartTargets.AffineCoordinates i where
  toEquiv := t97J07_cp1_affinePatchEquiv i
  continuous_toFun := by
    exact continuousOn_iff_continuous_restrict.mp
      (ConstructionTargets.T99J05ArbitraryAffineChartContinuity.t99J05_coordinates_continuousOn i)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ConstructionTargets.T99J05ArbitraryAffineChartContinuity.t99J05_chartInverse_continuous i

/-- Each literal affine patch is contractible, transported from its affine
coordinate topological vector space. -/
theorem t97J07_cp1_affinePatch_contractible (i : Fin 2) :
    ContractibleSpace
      {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 //
        Projectivization.rep p i ≠ 0} := by
  exact (t97J07_cp1_affinePatchHomeomorph i).contractibleSpace

/-- Consequently, either affine patch has zero rational singular homology in
every positive degree. -/
theorem t97J07_cp1_affinePatch_higherHomology_isZero
    (i : Fin 2) (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (ConstructionTargets.RationalLefschetz.Homology
      {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 //
        Projectivization.rep p i ≠ 0} n) := by
  letI := t97J07_cp1_affinePatch_contractible i
  exact ConstructionTargets.CoefficientContractiblePair.higher_zero ℚ _ n hn

/-- In either affine chart, membership in the other chart is precisely the
nonvanishing of its sole affine coordinate. -/
theorem t97J07_cp1_chartInverse_other_rep_ne_iff (i j : Fin 2) (hji : j ≠ i)
    (z : ConstructionTargets.ComplexProjectiveChartTargets.AffineCoordinates i) :
    Projectivization.rep
        (ConstructionTargets.ComplexProjectiveChartTargets.chartInverse i z) j ≠ 0 ↔
      z ⟨j, hji⟩ ≠ 0 := by
  let v : Fin 2 → ℂ := fun k => if h : k = i then 1 else z ⟨k, h⟩
  have hv : v ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [v] at hi
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (Projectivization.mk ℂ v hv).rep j ≠ 0 ↔ z ⟨j, hji⟩ ≠ 0
  rw [← ha]
  change a.1 * v j ≠ 0 ↔ z ⟨j, hji⟩ ≠ 0
  simp [v, hji]

/-- The literal overlap, presented inside the zero affine patch. -/
abbrev T97J07CP1ZeroPatchOverlap :=
  {p : {p : ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 1 //
      Projectivization.rep p (0 : Fin 2) ≠ 0} //
    Projectivization.rep p.1 (1 : Fin 2) ≠ 0}

/-- The coordinate model of the overlap is the nonzero locus in the sole
affine coordinate. -/
abbrev T97J07CP1PuncturedAffine :=
  {z : ConstructionTargets.ComplexProjectiveChartTargets.AffineCoordinates
      (0 : Fin 2) // z ⟨1, by decide⟩ ≠ 0}

/-- The overlap characterization upgrades to an actual homeomorphism with
the punctured affine coordinate space. -/
noncomputable def t97J07_cp1_overlapHomeomorphPuncturedAffine :
    T97J07CP1ZeroPatchOverlap ≃ₜ T97J07CP1PuncturedAffine :=
  (t97J07_cp1_affinePatchHomeomorph 0).subtype (fun p => by
    change Projectivization.rep p.1 1 ≠ 0 ↔
      ConstructionTargets.ComplexProjectiveChartTargets.coordinates 0 p.1
        ⟨1, by decide⟩ ≠ 0
    have h := t97J07_cp1_chartInverse_other_rep_ne_iff 0 1 (by decide)
      (ConstructionTargets.ComplexProjectiveChartTargets.coordinates 0 p.1)
    rw [ConstructionTargets.ComplexProjectiveChartTargets.chartInverse_coordinates
      0 p.1 p.2] at h
    exact h)

/-- The one-coordinate punctured affine model is the ordinary punctured
complex line. -/
noncomputable def t97J07_cp1_puncturedAffineHomeomorphComplex :
    T97J07CP1PuncturedAffine ≃ₜ {z : ℂ // z ≠ 0} where
  toFun z := ⟨z.1 ⟨1, by decide⟩, z.2⟩
  invFun w := ⟨fun _ => w.1, w.2⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    have hj : j = ⟨1, by decide⟩ := by
      apply Subtype.ext
      exact Fin.eq_one_of_ne_zero j.1 j.2
    subst j
    rfl
  right_inv w := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply
      (⟨1, by decide⟩ : {j : Fin 2 // j ≠ (0 : Fin 2)})).comp
        continuous_subtype_val
  continuous_invFun := by fun_prop

/-- Radial normalization exhibits the punctured complex line as homotopy
equivalent to its unit circle. -/
noncomputable def t97J07_cp1_puncturedComplex_radialHomotopyEquiv :
    {z : ℂ // z ≠ 0} ≃ₕ Metric.sphere (0 : ℂ) 1 :=
  (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereHomotopyEquivPuncturedSpace
    ℂ).symm

/-- Only the first two filtration steps are needed by this consumer.  This
bounded adapter avoids requiring an all-dimensional successor theorem. -/
noncomputable def t97J07_cp2RationalHomologyData_of_two_steps
    (h01 :
      ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 0 →
        ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 1)
    (h12 :
      ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 1 →
        ConstructionTargets.t99J05Closure.ComplexProjectiveRationalHomologyData 2) :
    T97J07CP2RationalHomologyData :=
  t97J07_cp2RationalHomologyData_of_shared
    (h12 (h01 t97J07_complexProjectiveRationalHomologyData_zero))

/-- Once the CP² homology table is supplied, finite-dimensional trace
calculation gives Euler characteristic three. -/
theorem t97J07_eulerCharacteristic_of_homologyData
    (h : T97J07CP2RationalHomologyData) :
    ConstructionTargets.RationalLefschetz.HasEulerCharacteristic
      T97J07CP2 3 := by
  unfold ConstructionTargets.RationalLefschetz.HasEulerCharacteristic
  unfold ConstructionTargets.RationalLefschetz.HasLefschetzNumber
  constructor
  · exact h.finiteDimensional
  · refine ⟨4, h.vanishesAbove, ?_⟩
    letI (k : ℕ) : FiniteDimensional ℚ
        (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 k) :=
      h.finiteDimensional k
    have h0 : Module.finrank ℚ
        (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 0) = 1 := by
      rw [LinearEquiv.finrank_eq h.zeroEquiv]
      simp
    have h1 : Module.finrank ℚ
        (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 1) = 0 := by
      letI : Subsingleton
          (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 1) :=
        h.oneSubsingleton
      exact Module.finrank_eq_zero_of_subsingleton ℚ _
    have h2 : Module.finrank ℚ
        (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 2) = 1 := by
      rw [LinearEquiv.finrank_eq h.twoEquiv]
      simp
    have h3 : Module.finrank ℚ
        (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 3) = 0 := by
      letI : Subsingleton
          (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 3) :=
        h.threeSubsingleton
      exact Module.finrank_eq_zero_of_subsingleton ℚ _
    have h4 : Module.finrank ℚ
        (ConstructionTargets.RationalLefschetz.Homology T97J07CP2 4) = 1 := by
      rw [LinearEquiv.finrank_eq h.fourEquiv]
      simp
    simp only [ConstructionTargets.RationalLefschetz.induced,
      CategoryTheory.Functor.map_id, LinearMap.trace_id]
    norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4]

#print axioms t97J07_cp1_nonzeroVectors_pathConnected
#print axioms t97J07_cp1_pathConnected
#print axioms t97J07_cp1_rationalH0Iso
#print axioms t97J07_cp1_twoAffine_openCover
#print axioms t97J07_cp1_chartInverse_rep_ne
#print axioms t97J07_cp1_affinePatchEquiv
#print axioms t97J07_cp1_affinePatchHomeomorph
#print axioms t97J07_cp1_affinePatch_contractible
#print axioms t97J07_cp1_affinePatch_higherHomology_isZero
#print axioms t97J07_cp1_chartInverse_other_rep_ne_iff
#print axioms t97J07_cp1_overlapHomeomorphPuncturedAffine
#print axioms t97J07_cp1_puncturedAffineHomeomorphComplex
#print axioms t97J07_cp1_puncturedComplex_radialHomotopyEquiv

theorem apm_t97j07 :
    {p : T97J07CP2 | t97J07Map p = p} =
        t97J07FixedLine ∪ {t97J07IsolatedPoint} ∧
    t97J07IsolatedPoint ∉ t97J07FixedLine ∧
    (∀ a u : ℂ,
      t97J07Map (t97J07LineChart a u) =
        t97J07LineChart a (t97J07LineLocal u)) ∧
    (∀ w : Fin 2 → ℂ,
      t97J07Map (t97J07PointChart w) =
        t97J07PointChart (t97J07PointLocal w)) ∧
    fderiv ℂ t97J07LineLocal 0 1 = 3 ∧
    (∀ i : Fin 2,
      fderiv ℂ t97J07PointLocal 0 (Pi.single i 1) =
        Pi.single i (1 / 3)) ∧
    t97J07LineNormalDet = 4 ∧
    t97J07PointDet = 16 / 81 ∧
    t97J07IndexFromDet t97J07LineNormalDet = 1 ∧
    t97J07IndexFromDet t97J07PointDet = 1 ∧
    t97J07LineContribution = 2 ∧
    t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3 ∧
    ConstructionTargets.RationalLefschetz.HasEulerCharacteristic
      T97J07CP2 3 := by
  sorry

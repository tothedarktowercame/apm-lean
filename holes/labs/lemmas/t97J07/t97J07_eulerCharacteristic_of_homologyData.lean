import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveSpaceTopology

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

/-! ## Remaining proof boundaries

The elementary coordinate, derivative, determinant, and arithmetic results above
are reused from the solve loop.  The two declarations below isolate the actual
projective classification and global homology computation.
-/

/-- A fixed projective class of diag(1,1,3) lies in exactly one of its two
projectivized eigenspaces. -/
theorem t97J07_fixed_set :
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

/-- The exact rational singular-homology computation needed below.  Keeping
the isomorphisms as data (rather than merely recording dimensions) lets the
trace calculation use Mathlib's finite-dimensional linear-algebra API. -/
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

/-- LIBRARY: the cellular/singular comparison for the literal quotient model
of `CP²`.  This is the one genuinely missing topology foundation: one cell in
real dimensions `0`, `2`, and `4`, and no other rational homology. -/
theorem t97J07_cp2RationalHomologyData_exists :
    Nonempty T97J07CP2RationalHomologyData := by
  sorry

/-- Given the degree-by-degree homology computation, the remaining step is
finite-dimensional linear algebra: the identity induces identity maps, their
traces are `1, 0, 1, 0, 1`, and the alternating sum through degree four is
`3`.  The hypothesis makes this seat independent of the topology seat. -/
-- BEGIN SEAT AREA
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
-- END SEAT AREA

/-- The rational singular-homology Euler characteristic of complex
projective two-space is 3.  This declaration is only the assembly of the
topological homology certificate and the independent trace calculation. -/
theorem t97J07_eulerCharacteristic :
    ConstructionTargets.RationalLefschetz.HasEulerCharacteristic
      T97J07CP2 3 := by
  exact t97J07_cp2RationalHomologyData_exists.elim
    t97J07_eulerCharacteristic_of_homologyData

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
  exact ⟨t97J07_fixed_set, t97J07IsolatedPoint_not_mem,
    t97J07LineChart_map, t97J07PointChart_map,
    t97J07LineLocal_fderiv, t97J07PointLocal_fderiv,
    t97J07LineNormalDet_eq, t97J07PointDet_eq,
    t97J07LineIndex_eq, t97J07PointIndex_eq,
    t97J07LineContribution_eq, t97J07TotalContribution_eq,
    t97J07_eulerCharacteristic⟩

#print axioms apm_t97j07

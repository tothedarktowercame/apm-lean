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

/-- Why this unblocks `apm_t97j07`: this is the missing classification of
all fixed points of the projectivized diagonal map.  It asserts that a fixed
projective class is exactly either a class with zero third coordinate or the
third coordinate axis, which is the sole unresolved conjunct below. -/
theorem apm_t97J07_bridge_1 :
    {p : T97J07CP2 | t97J07Map p = p} =
      t97J07FixedLine ∪ {t97J07IsolatedPoint} := by
  sorry

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

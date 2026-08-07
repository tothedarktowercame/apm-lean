import Mathlib

/-!
# APM m96J06: A nonlinear functional equation near zero

## Statement repairs

None.

## Encoding questions

None. The open neighborhood is the explicit sup-norm ball
`{y ∈ C([-2,2]) | ‖y‖∞ < 1/48}`. Functions are represented on `ℝ` with all
continuity, bounds, and equations restricted to the exact interval `[-2,2]`.
-/

open Set

noncomputable section

def apm_m96J06_inNeighborhood (y : ℝ → ℝ) : Prop :=
  ContinuousOn y (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2, |y t| < (1 / 48 : ℝ)

def apm_m96J06_isSolution (x y : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2,
    x t - 2 * x 0 + x (t / 2 + 1) * x (t / 2 - 1) = y t

/-- The linearization at zero is its own inverse, even before restricting to
the continuous-function Banach space. -/
def apm_m96J06_linearPart (x : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ x t - 2 * x 0

lemma apm_m96J06_linearPart_involutive (x : ℝ → ℝ) :
    apm_m96J06_linearPart (apm_m96J06_linearPart x) = x := by
  funext t
  simp [apm_m96J06_linearPart]
  ring

/-- Both rescaled arguments in the quadratic term remain in the domain. -/
lemma apm_m96J06_half_shift_mem {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    t / 2 + 1 ∈ Icc (-2 : ℝ) 2 ∧ t / 2 - 1 ∈ Icc (-2 : ℝ) 2 := by
  constructor <;> constructor <;> linarith [ht.1, ht.2]

/-- The quadratic term preserves continuity on the restricted interval. -/
lemma apm_m96J06_quadratic_continuousOn {x : ℝ → ℝ}
    (hx : ContinuousOn x (Icc (-2 : ℝ) 2)) :
    ContinuousOn (fun t ↦ x (t / 2 + 1) * x (t / 2 - 1)) (Icc (-2 : ℝ) 2) := by
  have hp : ContinuousOn (fun t : ℝ ↦ t / 2 + 1) (Icc (-2 : ℝ) 2) :=
    ((continuous_id.div_const (2 : ℝ)).add continuous_const).continuousOn
  have hm : ContinuousOn (fun t : ℝ ↦ t / 2 - 1) (Icc (-2 : ℝ) 2) :=
    ((continuous_id.div_const (2 : ℝ)).sub continuous_const).continuousOn
  exact (hx.comp hp fun _ ht ↦ (apm_m96J06_half_shift_mem ht).1).mul
    (hx.comp hm fun _ ht ↦ (apm_m96J06_half_shift_mem ht).2)

/-- Pointwise form of the quadratic Lipschitz estimate on a sup-norm ball. -/
lemma apm_m96J06_quadratic_sub_bound
    {x z : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ r)
    (hz : ∀ t ∈ Icc (-2 : ℝ) 2, |z t| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    |x (t / 2 + 1) * x (t / 2 - 1) -
        z (t / 2 + 1) * z (t / 2 - 1)| ≤
      2 * r * max |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)| := by
  have hp := (apm_m96J06_half_shift_mem ht).1
  have hm := (apm_m96J06_half_shift_mem ht).2
  calc
    _ = |x (t / 2 + 1) * (x (t / 2 - 1) - z (t / 2 - 1)) +
        (x (t / 2 + 1) - z (t / 2 + 1)) * z (t / 2 - 1)| := by ring_nf
    _ ≤ |x (t / 2 + 1)| * |x (t / 2 - 1) - z (t / 2 - 1)| +
        |x (t / 2 + 1) - z (t / 2 + 1)| * |z (t / 2 - 1)| := by
      simpa [abs_mul] using abs_add_le
        (x (t / 2 + 1) * (x (t / 2 - 1) - z (t / 2 - 1)))
        ((x (t / 2 + 1) - z (t / 2 + 1)) * z (t / 2 - 1))
    _ ≤ r * |x (t / 2 - 1) - z (t / 2 - 1)| +
        |x (t / 2 + 1) - z (t / 2 + 1)| * r := by
      gcongr
      · exact hx _ hp
      · exact hz _ hm
    _ ≤ 2 * r * max |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)| := by
      have h1 := le_max_left |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)|
      have h2 := le_max_right |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)|
      nlinarith

theorem apm_m96j06 :
    ∀ y : ℝ → ℝ,
      apm_m96J06_inNeighborhood y →
        ∃ x : ℝ → ℝ,
          apm_m96J06_isSolution x y ∧
          ∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ (1 / 12 : ℝ) := by
  /-
  PARTIAL.  `apm_m96J06_linearPart_involutive` proves that the linearization
  `x ↦ x - 2 x(0)` is algebraically its own inverse, and
  `apm_m96J06_half_shift_mem` proves that both arguments of the quadratic term
  remain in `[-2,2]`.  This pass additionally proves
  `apm_m96J06_quadratic_continuousOn`, closing preservation of the restricted
  continuous-function space, and `apm_m96J06_quadratic_sub_bound`, the
  pointwise two-radius Lipschitz estimate from which the sup-norm contraction
  bound follows.

  The remaining construction must bundle continuous functions on `Icc (-2) 2`
  with their sup norm, define the quadratic self-map and prove the estimates
  the supplied pointwise estimate to the subtype sup norm, prove
  `‖L⁻¹‖ ≤ 3`, then apply
  `ContractingWith.exists_fixedPoint'` to the closed ball of radius `1/12`.
  Mathlib supplies that abstract fixed-point theorem (and sibling `t91A04`
  demonstrates its global wrapper), but searches of `LEMMA-INDEX.md`, 172
  closed artifacts, `ConstructionTargets/`, `YoungL2.lean`, and Mathlib's
  `ContinuousMap`/closed-ball fixed-point APIs found no helper assembling this
  custom restricted continuous-function space and its nonlinear self-map.
  -/
  sorry

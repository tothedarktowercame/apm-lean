import Mathlib
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-! # APM t92J08: complete integral curves of vector fields

## Statement repairs

None.

## Encoding notes

Vector fields and local/global integral curves use Mathlib's genuine tangent
bundle, `IsMIntegralCurveOn`, and `IsMIntegralCurve`. Compactness of a
boundaryless smooth manifold is the sufficient hypothesis. The counterexample
is the actual field `x ↦ x²` on `ℝ`, with solution `t ↦ 1/(1-t)` on `t < 1`.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t92J08_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t92J08_Model (n : ℕ) := 𝓘(ℝ, apm_t92J08_E n)

def apm_t92J08_quadraticField (x : ℝ) : TangentSpace (𝓘(ℝ, ℝ)) x :=
  x ^ 2

def apm_t92J08_blowupCurve (t : ℝ) : ℝ :=
  1 / (1 - t)

/-- The ordinary-calculus core of the blow-up counterexample. -/
lemma apm_t92J08_blowupCurve_hasDerivAt {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt apm_t92J08_blowupCurve
      ((apm_t92J08_blowupCurve t) ^ 2) t := by
  have hden : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
  unfold apm_t92J08_blowupCurve
  simp only [one_div]
  simpa using
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).inv hden)

/-- The ordinary derivative identity transported into the self-model manifold
derivative expected by `IsMIntegralCurveOn`. -/
lemma apm_t92J08_blowupCurve_isMIntegralCurveOn :
    IsMIntegralCurveOn apm_t92J08_blowupCurve
      apm_t92J08_quadraticField (Iio 1) := by
  intro t ht
  rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  exact (apm_t92J08_blowupCurve_hasDerivAt (ne_of_lt ht)).hasFDerivAt.hasFDerivWithinAt

/-- Why this unblocks the compact-manifold half of `apm_t92j08`: this is the
uniform local-existence radius extracted from pointwise ODE existence by a
finite compact subcover. It is exactly the hypothesis consumed by
`exists_isMIntegralCurve_of_isMIntegralCurveOn`. -/
theorem apm_t92J08_bridge_1
    (n : ℕ) (M : Type)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (apm_t92J08_E n) M]
    [IsManifold (apm_t92J08_Model n) ∞ M]
    [BoundarylessManifold (apm_t92J08_Model n) M]
    (v : (x : M) → TangentSpace (apm_t92J08_Model n) x)
    (hv : ContMDiff (apm_t92J08_Model n) (apm_t92J08_Model n).tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (apm_t92J08_Model n) M))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M,
      ∃ γ : ℝ → M, γ 0 = x ∧
        IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  sorry

/-- Why this unblocks the counterexample half of `apm_t92j08`: agreement
with `1/(1-t)` on `t < 1` contradicts continuity at `1` of any global
integral curve, because those values are unbounded as `t ↑ 1`. -/
theorem apm_t92J08_bridge_2 :
    ¬∃ δ : ℝ → ℝ,
      IsMIntegralCurve δ apm_t92J08_quadraticField ∧
      EqOn apm_t92J08_blowupCurve δ (Iio 1) := by
  sorry

theorem apm_t92j08 :
    (∀ (n : ℕ) (M : Type)
        [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
        [CompactSpace M] [ChartedSpace (apm_t92J08_E n) M]
        [IsManifold (apm_t92J08_Model n) ∞ M]
        [BoundarylessManifold (apm_t92J08_Model n) M]
        (v : (x : M) → TangentSpace (apm_t92J08_Model n) x),
      ContMDiff (apm_t92J08_Model n) (apm_t92J08_Model n).tangent 1
        (fun x ↦ (⟨x, v x⟩ : TangentBundle (apm_t92J08_Model n) M)) →
      ∀ (a b : ℝ) (γ : ℝ → M), a < 0 → 0 < b →
        IsMIntegralCurveOn γ v (Ioo a b) →
        ∃ δ : ℝ → M,
          IsMIntegralCurve δ v ∧ EqOn γ δ (Ioo a b)) ∧
    IsMIntegralCurveOn apm_t92J08_blowupCurve
      apm_t92J08_quadraticField (Iio 1) ∧
    ¬∃ δ : ℝ → ℝ,
      IsMIntegralCurve δ apm_t92J08_quadraticField ∧
      EqOn apm_t92J08_blowupCurve δ (Iio 1) := by
  /-
  Boundary (closer hop 1): Mathlib's imported `UniformTime.lean` contains
  `exists_isMIntegralCurve_of_isMIntegralCurveOn`, which globalizes curves
  once one uniform positive local-existence radius works at every point.
  The remaining compact-manifold step is to extract that uniform radius from
  `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` using a finite
  subcover; searches of `LEMMA-INDEX.md`, closed siblings,
  `ConstructionTargets/`, git history, and the manifold integral-curve APIs
  found no packaged compactness-to-uniform-time theorem.

  For the explicit counterexample, ordinary calculus proves
  `(1/(1-t))' = (1/(1-t))^2` on `Iio 1`.  Attempts using
  `hasMFDerivWithinAt_iff_hasFDerivWithinAt`, `HasDerivAt.inv`, and
  `hasDerivWithinAt_iff_hasFDerivWithinAt` reach an instance mismatch between
  the tangent-space module structures of the self-model on `ℝ` and the
  ordinary real normed-space derivative.  After that conversion, exclusion of
  a global extension can use continuity at `1` against the divergence of the
  frozen curve (or ODE uniqueness plus the same limit contradiction).

  Closer hop 2 now compiles the ordinary analytic identity as
  `apm_t92J08_blowupCurve_hasDerivAt`, avoiding the earlier derivative-rule
  elaboration issue. The remaining counterexample bridge is specifically its
  transport into `HasMFDerivWithinAt` with the tangent-space presentation,
  followed by the endpoint contradiction; the independent compact uniform-
  time construction remains open.

  CLOSER HOP 3 closes the derivative-transport bridge itself.
  `apm_t92J08_blowupCurve_isMIntegralCurveOn` unfolds the native integral-
  curve predicate pointwise, applies
  `hasMFDerivWithinAt_iff_hasFDerivWithinAt`, and transports the hop-2
  `HasDerivAt` proof through `hasFDerivAt` and restriction. Consequently the
  frozen theorem's entire middle conjunct is now available as a proved lemma,
  with no tangent-space instance mismatch remaining. The explicit
  counterexample now only needs the endpoint contradiction: a global integral
  curve is continuous, while agreement on `Iio 1` forces values
  `1/(1-t)` to be unbounded near `1`. Separately, the compact-manifold conjunct
  still needs extraction of a uniform local-existence radius. Searches of
  compact-image boundedness, sequential endpoint limits, and uniform-time
  integral-curve APIs found ingredients but no packaged combination. The
  frozen statement is unchanged.
  -/
  sorry

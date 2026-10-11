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
  rintro ⟨δ, hδ, heq⟩
  let u : ℕ → ℝ := fun n => 1 - 1 / (n + 1 : ℝ)
  have hu : Filter.Tendsto u Filter.atTop (nhds 1) := by
    simpa [u] using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1)).sub tendsto_one_div_add_atTop_nhds_zero_nat)
  have hfinite : Filter.Tendsto (fun n => δ (u n)) Filter.atTop (nhds (δ 1)) :=
    hδ.continuous.continuousAt.tendsto.comp hu
  apply (not_tendsto_atTop_of_tendsto_nhds hfinite)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      δ (u n) = (n + 1 : ℝ) := by
    filter_upwards with n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hul : u n < 1 := by simp [u, hn]
    rw [← heq hul]
    simp [u, apm_t92J08_blowupCurve]
  exact Filter.Tendsto.congr' (hevent.mono fun _ h => h.symm)
    (Filter.tendsto_atTop_add_const_right Filter.atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ)))

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
  refine ⟨?_, apm_t92J08_blowupCurve_isMIntegralCurveOn,
    apm_t92J08_bridge_2⟩
  intro n M _ _ _ _ _ _ _ v hv a b γ ha hb hγ
  obtain ⟨ε, hε, hlocal⟩ := apm_t92J08_bridge_1 n M v hv
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε hlocal (γ 0)
  refine ⟨δ, hδ, ?_⟩
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (show 0 ∈ Ioo a b from ⟨ha, hb⟩) hv hγ (hδ.isMIntegralCurveOn _)
  exact hδ0.symm

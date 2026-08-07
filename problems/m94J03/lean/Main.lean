import Mathlib

/-!
# APM m94J03

## Statement repairs

The resolvent `(z-A)⁻¹` exists only for `z` outside the spectrum, so the
printed quantifier "for all `z ∈ ℂ`" is minimally restricted to the
resolvent set. No value is assigned to a nonexistent inverse on the spectrum.

## Encoding questions

Mathlib's `resolvent A z` is the inverse of `z•1 - A` in the Banach algebra of
bounded operators. Distance to the spectrum is `Metric.infDist`.
-/

theorem apm_m94j03 :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A →
      IsSelfAdjoint A →
      ∀ z ∈ resolventSet ℂ A,
        ‖resolvent A z‖ ≤ (Metric.infDist z (spectrum ℂ A))⁻¹ := by
  intro H _ _ _ A _hcompact hself z hz
  rcases subsingleton_or_nontrivial H with hH | hH
  · simp
  letI : Nontrivial H := hH
  have hnot : z ∉ spectrum ℂ A := by
    simpa [spectrum] using hz
  have hspec_nonempty : (spectrum ℂ A).Nonempty := spectrum.nonempty A
  have hdist : 0 < Metric.infDist z (spectrum ℂ A) :=
    ((spectrum.isClosed A).notMem_iff_infDist_pos hspec_nonempty).mp hnot
  have hpointwise : ∀ (lam : ℂ), lam ∈ spectrum ℂ A →
      ‖(z - lam)⁻¹‖ ≤ (Metric.infDist z (spectrum ℂ A))⁻¹ := by
    intro lam hlam
    have hzl : z ≠ lam := by
      intro h
      apply hnot
      simpa [h] using hlam
    have hdle : Metric.infDist z (spectrum ℂ A) ≤ ‖z - lam‖ := by
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := z) hlam
    rw [norm_inv]
    exact inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hzl)) hdist |>.2 hdle
  let g : ℂ → ℂ := fun lam ↦ z - lam
  have hg : ContinuousOn g (spectrum ℂ A) :=
    continuous_const.sub continuous_id |>.continuousOn
  have hg_ne : ∀ lam ∈ spectrum ℂ A, g lam ≠ 0 := by
    intro lam hlam
    exact sub_ne_zero.mpr fun h ↦ hnot (h ▸ hlam)
  -- Mathlib CFC: `cfc_inv`, `cfc_sub`, `cfc_const`, and `cfc_id'`.
  have hres : resolvent A z = cfc (fun lam ↦ (z - lam)⁻¹) A := by
    have hcg : cfc g A = algebraMap ℂ (H →L[ℂ] H) z - A := by
      change cfc (fun lam : ℂ ↦ (fun _ : ℂ ↦ z) lam - (fun w : ℂ ↦ w) lam) A = _
      rw [cfc_sub (fun _ : ℂ ↦ z) (fun w : ℂ ↦ w) A
          continuousOn_const continuous_id.continuousOn,
        cfc_const z A hself.isStarNormal, cfc_id' ℂ A hself.isStarNormal]
    unfold resolvent
    calc
      Ring.inverse (algebraMap ℂ (H →L[ℂ] H) z - A) =
          Ring.inverse (cfc g A) := congrArg Ring.inverse hcg.symm
      _ = cfc (fun lam ↦ (g lam)⁻¹) A :=
        (cfc_inv g A hg_ne hg hself.isStarNormal).symm
      _ = cfc (fun lam ↦ (z - lam)⁻¹) A := rfl
  rw [hres]
  exact norm_cfc_le (le_of_lt (inv_pos.mpr hdist)) hpointwise

import Mathlib

/-!
# APM t96J04 — no continuous surjection onto the irrationals

## Statement repairs

None.
-/

abbrev apm_t96j04_Irrational := {x : ℝ // Irrational x}

theorem apm_t96j04 :
    ¬ ∃ f : ℝ × ℚ → apm_t96j04_Irrational,
      Continuous f ∧ Function.Surjective f := by
  rintro ⟨f, hf, hsurj⟩
  letI : TotallyDisconnectedSpace apm_t96j04_Irrational :=
    totallyDisconnectedSpace_subtype_iff.2 <| isTotallyDisconnected_iff_lt.2 <| by
      intro x hx y hy hxy
      obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
      exact ⟨(q : ℝ), q.not_irrational, hxq, hqy⟩
  have hconst (q : ℚ) (x : ℝ) : f (x, q) = f (0, q) := by
    apply TotallyDisconnectedSpace.eq_of_continuous (fun z : ℝ => f (z, q))
    · exact hf.comp (continuous_id.prodMk continuous_const)
  have hqsurj : Function.Surjective (fun q : ℚ => f (0, q)) := by
    intro y
    obtain ⟨⟨x, q⟩, hxy⟩ := hsurj y
    exact ⟨q, (hconst q x).symm.trans hxy⟩
  haveI : Countable apm_t96j04_Irrational := hqsurj.countable
  have hirr : {x : ℝ | Irrational x}.Countable :=
    (hqsurj.countable : Countable apm_t96j04_Irrational).to_set
  have hrat : {x : ℝ | ¬ Irrational x}.Countable := by
    refine (Set.countable_range fun q : ℚ => (q : ℝ)).mono ?_
    intro x hx
    obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hx
    exact ⟨q, hq.symm⟩
  exact Set.not_countable_univ (by
    rw [← Set.union_compl_self {x : ℝ | Irrational x}]
    exact hirr.union hrat)

import Mathlib

/-! # APM t93A01: open sets as cozero sets

## Statement repairs

None.
-/

open Set

theorem apm_t93a01
    {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    [SecondCountableTopology X] (U : Set X) (hU : IsOpen U) :
    (∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ U = ⋃ n, C n) ∧
    (∃ f : X → Set.Icc (0 : ℝ) 1, Continuous f ∧
      (∀ x ∈ U, 0 < (f x : ℝ)) ∧
      ∀ x ∉ U, f x = 0) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  constructor
  · obtain ⟨C, hCclosed, hCsub, hCunion, hCmono⟩ :=
      hU.exists_iUnion_isClosed
    exact ⟨C, hCclosed, hCunion.symm⟩
  · by_cases hUniv : U = univ
    · refine ⟨fun _ => ⟨1, by simp⟩, continuous_const, ?_, ?_⟩
      · simp [hUniv]
      · simp [hUniv]
    · have hproper : U ⊂ (univ : Set X) :=
        (ssubset_iff_subset_ne).2 ⟨subset_univ U, hUniv⟩
      have hcomp : Uᶜ.Nonempty := ssubset_univ_iff_nonempty_compl.mp hproper
      let f : X → Set.Icc (0 : ℝ) 1 := fun x =>
        ⟨min (Metric.infDist x Uᶜ) 1,
          ⟨le_min Metric.infDist_nonneg zero_le_one, min_le_right _ _⟩⟩
      refine ⟨f, ?_, ?_, ?_⟩
      · exact Continuous.subtype_mk
          ((Metric.continuous_infDist_pt (s := Uᶜ)).min continuous_const) _
      · intro x hx
        change 0 < min (Metric.infDist x Uᶜ) 1
        have hxnot : x ∉ Uᶜ := by simpa
        exact lt_min
          ((hU.isClosed_compl.notMem_iff_infDist_pos hcomp).mp hxnot) zero_lt_one
      · intro x hx
        apply Subtype.ext
        change min (Metric.infDist x Uᶜ) 1 = 0
        rw [Metric.infDist_zero_of_mem]
        · simp
        · simpa

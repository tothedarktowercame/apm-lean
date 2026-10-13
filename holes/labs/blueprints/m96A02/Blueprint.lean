import Mathlib

open Filter

/-!
# APM m96A02 — contraction mapping, iterates, and Picard existence

## Statement repairs

The two abstract metric-space clauses assume `Nonempty M`, as required by
Banach's theorem. The solution predicate also requires continuity on `[0,1]`,
so its endpoint value at `1` is not unconstrained.
-/

def apm_m96a02_IsContraction {M : Type*} [MetricSpace M] (T : M → M) : Prop :=
  ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ x y, dist (T x) (T y) ≤ k * dist x y

def apm_m96a02_Solves (f : ℝ → ℝ) (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Set.Icc 0 1) ∧ u 0 = u₀ ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u (f (u t)) t

/-! ## Remaining bridges -/

theorem apm_m96A02_banach_fixed_point
    (M : Type*) [MetricSpace M] [CompleteSpace M] [Nonempty M] (T : M → M)
    (hT : apm_m96a02_IsContraction T) :
    ∃ xstar : M, T xstar = xstar ∧
      (∀ x, Tendsto (fun n : ℕ => (T^[n]) x) atTop (nhds xstar)) ∧
      ∀ y, T y = y → y = xstar := by
  obtain ⟨k, hk0, hk1, hk⟩ := hT
  let K : NNReal := ⟨k, hk0⟩
  have hK : ContractingWith K T := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hk1
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa [K] using hk x y
  let xstar : M := ContractingWith.fixedPoint T hK
  refine ⟨xstar, ?_, ?_, ?_⟩
  · exact hK.fixedPoint_isFixedPt
  · intro x
    exact hK.tendsto_iterate_fixedPoint x
  · intro y hy
    exact hK.fixedPoint_unique hy

theorem apm_m96A02_iterate_contraction_fixed_point
    (M : Type*) [MetricSpace M] [CompleteSpace M] [Nonempty M] (T : M → M)
    (hT : ∃ N : ℕ, 1 ≤ N ∧ apm_m96a02_IsContraction (T^[N])) :
    ∃! x : M, T x = x := by
  obtain ⟨N, hN, k, hk0, hk1, hk⟩ := hT
  let K : NNReal := ⟨k, hk0⟩
  have hK : ContractingWith K (T^[N]) := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hk1
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa [K] using hk x y
  let xstar : M := ContractingWith.fixedPoint (T^[N]) hK
  refine ⟨xstar, ?_, ?_⟩
  · exact hK.isFixedPt_fixedPoint_iterate
  · intro y hy
    exact hK.fixedPoint_unique (Function.IsFixedPt.iterate hy N)

lemma apm_m96A02_lipschitz_ode_aux_lipschitzWith
    (f : ℝ → ℝ)
    (hf : ∃ L ≥ 0, ∀ x y, |f x - f y| ≤ L * |x - y|) :
    ∃ K : NNReal, LipschitzWith K f := by
  obtain ⟨L, hL, hf⟩ := hf
  refine ⟨⟨L, hL⟩, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa [Real.dist_eq] using hf x y

/-- Existence on `[0, 1]` for a globally Lipschitz right-hand side (Picard iteration on
`C([0,1])`, e.g. via `apm_m96A02_iterate_contraction_fixed_point`'s factorial estimate). -/
lemma apm_m96A02_lipschitz_ode_aux_exists_aux_linear_growth
    (f : ℝ → ℝ) (K : NNReal) (hK : LipschitzWith K f) (x : ℝ) :
    |f x| ≤ K * |x| + |f 0| := by
  calc
    |f x| = |(f x - f 0) + f 0| := by ring_nf
    _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
    _ ≤ K * |x - 0| + |f 0| := by
      gcongr
      simpa [Real.dist_eq] using hK.dist_le_mul x 0
    _ = K * |x| + |f 0| := by simp

/-- Picard iteration: a continuous solution of the integral equation on `[0, 1]`
(fixed point of `T u t = u₀ + ∫₀ᵗ f (u s) ds` on `C([0,1])`; some iterate is a contraction
by the `Kⁿ / n!` estimate, so `apm_m96A02_iterate_contraction_fixed_point` applies). -/
lemma apm_m96A02_lipschitz_ode_aux_exists_aux_integral_solution
    (f : ℝ → ℝ) (u₀ : ℝ) (K : NNReal) (hK : LipschitzWith K f) :
    ∃ u : ℝ → ℝ, Continuous u ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, u t = u₀ + ∫ s in (0 : ℝ)..t, f (u s) := by
  sorry

/-- A continuous solution of the integral equation solves the ODE. -/
lemma apm_m96A02_lipschitz_ode_aux_exists_aux_of_integral
    (f : ℝ → ℝ) (u₀ : ℝ) (K : NNReal) (hK : LipschitzWith K f) (u : ℝ → ℝ)
    (hu : Continuous u)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t = u₀ + ∫ s in (0 : ℝ)..t, f (u s)) :
    apm_m96a02_Solves f u₀ u := by
  have hfu : Continuous (fun s => f (u s)) := hK.continuous.comp hu
  refine ⟨hu.continuousOn, ?_, fun t ht => ?_⟩
  · rw [hint 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same, add_zero]
  · have hd : HasDerivAt (fun t => u₀ + ∫ s in (0 : ℝ)..t, f (u s)) (f (u t)) t :=
      (intervalIntegral.integral_hasDerivAt_right (hfu.intervalIntegrable _ _)
        hfu.aestronglyMeasurable.stronglyMeasurableAtFilter hfu.continuousAt).const_add u₀
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hint s ⟨hs.1.le, hs.2.le⟩

lemma apm_m96A02_lipschitz_ode_aux_exists
    (f : ℝ → ℝ) (u₀ : ℝ) (K : NNReal) (hK : LipschitzWith K f) :
    ∃ u : ℝ → ℝ, apm_m96a02_Solves f u₀ u := by
  obtain ⟨u, hu, hint⟩ := apm_m96A02_lipschitz_ode_aux_exists_aux_integral_solution f u₀ K hK
  exact ⟨u, apm_m96A02_lipschitz_ode_aux_exists_aux_of_integral f u₀ K hK u hu hint⟩

/-- Uniqueness on `[0, 1]` (Grönwall). -/
lemma apm_m96A02_lipschitz_ode_aux_unique
    (f : ℝ → ℝ) (u₀ : ℝ) (K : NNReal) (hK : LipschitzWith K f)
    (u v : ℝ → ℝ) (hu : apm_m96a02_Solves f u₀ u) (hv : apm_m96a02_Solves f u₀ v) :
    Set.EqOn u v (Set.Icc 0 1) := by
  have hendpoint (w : ℝ → ℝ) (hw : apm_m96a02_Solves f u₀ w) :
      HasDerivWithinAt w (f (w 0)) (Set.Ici 0) 0 := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
        (s := Set.Ioo (0 : ℝ) 1)
    · intro t ht
      exact (hw.2.2 t ht).differentiableAt.differentiableWithinAt
    · exact (hw.1.continuousWithinAt (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).mono
        Set.Ioo_subset_Icc_self
    · exact Ioo_mem_nhdsGT zero_lt_one
    · have hcontw : Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (w 0)) := by
        have hc := hw.1.continuousWithinAt (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
        apply hc.mono_left
        apply nhdsWithin_le_iff.mpr
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
        exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hfw : Tendsto (fun t ↦ f (w t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (f (w 0))) :=
        hK.continuous.continuousAt.tendsto.comp hcontw
      apply hfw.congr'
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      exact (hw.2.2 t ht).deriv.symm
  apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y : ℝ ↦ f y) (s := fun _ ↦ Set.univ) (K := K)
  · intro t ht
    exact hK.lipschitzOnWith
  · exact hu.1
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simpa using hendpoint u hu
    · exact (hu.2.2 t ⟨ht0, ht.2⟩).hasDerivWithinAt
  · intro t ht
    trivial
  · exact hv.1
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simpa using hendpoint v hv
    · exact (hv.2.2 t ⟨ht0, ht.2⟩).hasDerivWithinAt
  · intro t ht
    trivial
  · exact hu.2.1.trans hv.2.1.symm

theorem apm_m96A02_lipschitz_ode
    (f : ℝ → ℝ) (u₀ : ℝ)
    (hf : ∃ L ≥ 0, ∀ x y, |f x - f y| ≤ L * |x - y|) :
    ∃ u : ℝ → ℝ, apm_m96a02_Solves f u₀ u ∧
      ∀ v : ℝ → ℝ, apm_m96a02_Solves f u₀ v →
        Set.EqOn u v (Set.Icc 0 1) := by
  obtain ⟨K, hK⟩ := apm_m96A02_lipschitz_ode_aux_lipschitzWith f hf
  obtain ⟨u, hu⟩ := apm_m96A02_lipschitz_ode_aux_exists f u₀ K hK
  exact ⟨u, hu, fun v hv => apm_m96A02_lipschitz_ode_aux_unique f u₀ K hK u v hu hv⟩

theorem apm_m96a02 :
    (∀ (M : Type*) [MetricSpace M] [CompleteSpace M] [Nonempty M] (T : M → M),
      apm_m96a02_IsContraction T →
      ∃ xstar : M, T xstar = xstar ∧
        (∀ x, Tendsto (fun n : ℕ => (T^[n]) x) atTop (nhds xstar)) ∧
        ∀ y, T y = y → y = xstar) ∧
    (∀ (M : Type*) [MetricSpace M] [CompleteSpace M] [Nonempty M] (T : M → M),
      (∃ N : ℕ, 1 ≤ N ∧ apm_m96a02_IsContraction (T^[N])) →
      ∃! x : M, T x = x) ∧
    (∀ (f : ℝ → ℝ) (u₀ : ℝ),
      (∃ L ≥ 0, ∀ x y, |f x - f y| ≤ L * |x - y|) →
      ∃ u : ℝ → ℝ, apm_m96a02_Solves f u₀ u ∧
        ∀ v : ℝ → ℝ, apm_m96a02_Solves f u₀ v →
          Set.EqOn u v (Set.Icc 0 1)) := by
  /-
  SKIPPED (two frozen-statement defects).

  First, the first and second conjuncts omit `[Nonempty M]`.  Take
  `M := Empty`.  Mathlib defines its `MetricSpace Empty` instance in
  `Topology.MetricSpace.Defs`, and the current toolchain also synthesizes
  `CompleteSpace Empty`.
  Its unique self-map satisfies `apm_m96a02_IsContraction` vacuously (for
  example with `k = 0`), but neither conjunct's existential fixed-point
  conclusion can be inhabited.  Sibling `m01J05` documents exactly this
  counterexample for the same formulation.  Mathlib's
  `ContractingWith.fixedPoint` and sibling `t91A04` both explicitly require
  `[Nonempty M]`; the lower-level `ContractingWith.exists_fixedPoint` instead
  requires an explicit starting point.

  Second, `apm_m96a02_Solves` imposes the differential equation only on
  `Ioo 0 1` and fixes only `u 0`, whereas uniqueness is `EqOn` on `Icc 0 1`.
  In particular `u 1` is completely unconstrained.  For `f = 0` and `u₀ = 0`,
  take the zero solution and `v t := if t = 1 then 1 else 0`.  At every point
  of `Ioo 0 1`, a neighborhood avoids `1`, so `v` is locally the zero function
  and has derivative zero there.  Thus both functions satisfy the predicate,
  but they are not equal on `Icc 0 1`.  Adding
  `ContinuousOn u (Icc 0 1)` or weakening uniqueness to `Ico 0 1` would close
  this endpoint gap.

  Desk research found the abstract contraction and iterate APIs in Mathlib's
  `Topology.MetricSpace.Contracting` and local Picard existence in
  `Analysis.ODE.PicardLindelof`.  Sibling `t91A04` proves the valid nonempty
  contraction theorem.  Partial siblings `m00A05` and `m93J06` document the
  remaining globalization and predicate-conversion work for ODE existence.
  The fully closed artifact scan, `LEMMA-INDEX.md`, `ConstructionTargets/`,
  and `YoungL2.lean` supplied no convention or lemma that repairs either
  logical defect.  The statement is frozen, so it was not altered.
  -/
  exact ⟨apm_m96A02_banach_fixed_point,
    apm_m96A02_iterate_contraction_fixed_point,
    apm_m96A02_lipschitz_ode⟩

#print axioms apm_m96a02

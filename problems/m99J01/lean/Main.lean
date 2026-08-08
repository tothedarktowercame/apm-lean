import Mathlib

/-!
# APM m99J01

## Statement repairs

None.

## Encoding questions

A solution on the half-line is represented by a `C¹` function on `ℝ`, with the
differential equation and uniqueness asserted only for nonnegative times. This avoids
mistakenly identifying arbitrary extensions to negative time as different solutions.
-/

def apm_m99j01_IsSolution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 u ∧ u 0 = u₀ ∧
    ∀ t : ℝ, 0 ≤ t → deriv u t + u t = Real.cos (u t)

noncomputable def apm_m99j01_vectorField (x : ℝ) : ℝ := Real.cos x - x

/-- The autonomous vector field has the global Lipschitz bound needed by
Picard--Lindelöf and Grönwall uniqueness. -/
lemma apm_m99j01_vectorField_lipschitz :
    LipschitzWith 2 apm_m99j01_vectorField := by
  change LipschitzWith 2 (fun x : ℝ => Real.cos x - x)
  convert Real.lipschitzWith_cos.sub LipschitzWith.id using 1 <;> norm_num

/-- Every cosine fixed point gives the constant equilibrium solution in the
raw global-`C¹` encoding. -/
lemma apm_m99j01_fixed_isSolution {ξ : ℝ} (hξ : Real.cos ξ = ξ) :
    apm_m99j01_IsSolution ξ (fun _ => ξ) := by
  refine ⟨contDiff_const, rfl, ?_⟩
  intro t ht
  simpa [hξ]

lemma apm_m99j01_cos_fixed_unique {x y : ℝ}
    (hx : Real.cos x = x) (hy : Real.cos y = y) : x = y := by
  have fixed_mem (z : ℝ) (hz : Real.cos z = z) : z ∈ Set.Icc (0 : ℝ) Real.pi := by
    have hz_lower : -(1 : ℝ) ≤ z := by rw [← hz]; exact Real.neg_one_le_cos z
    have hz_upper : z ≤ 1 := by rw [← hz]; exact Real.cos_le_one z
    have hz_pos : 0 < z := by
      rw [← hz]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_gt_three]
    exact ⟨hz_pos.le, by nlinarith [Real.pi_gt_three]⟩
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := Real.strictAntiOn_cos (fixed_mem x hx) (fixed_mem y hy) hxy
    rw [hx, hy] at this
    exact (not_lt_of_ge hxy.le this).elim
  · exact hxy
  · have := Real.strictAntiOn_cos (fixed_mem y hy) (fixed_mem x hx) hxy
    rw [hx, hy] at this
    exact (not_lt_of_ge hxy.le this).elim

/-- The autonomous vector field points right below its equilibrium. -/
lemma apm_m99j01_vectorField_pos_of_lt_fixed {x ξ : ℝ}
    (hξ : Real.cos ξ = ξ) (hxξ : x < ξ) :
    0 < apm_m99j01_vectorField x := by
  unfold apm_m99j01_vectorField
  have hξ_le_one : ξ ≤ 1 := by rw [← hξ]; exact Real.cos_le_one ξ
  by_cases hxneg : x < 0
  · by_cases hxsmall : x < -1
    · linarith [Real.neg_one_le_cos x]
    · have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.pi_gt_three]
      linarith [Real.cos_pos_of_mem_Ioo hxmem]
  · have hx0 : 0 ≤ x := le_of_not_gt hxneg
    have hξ0 : 0 ≤ ξ := le_trans hx0 hxξ.le
    have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hx0, by nlinarith [Real.pi_gt_three]⟩
    have hξmem : ξ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hξ0, by nlinarith [Real.pi_gt_three]⟩
    have hcos := Real.strictAntiOn_cos hxmem hξmem hxξ
    rw [hξ] at hcos
    linarith

/-- The autonomous vector field points left above its equilibrium. -/
lemma apm_m99j01_vectorField_neg_of_fixed_lt {x ξ : ℝ}
    (hξ : Real.cos ξ = ξ) (hξx : ξ < x) :
    apm_m99j01_vectorField x < 0 := by
  unfold apm_m99j01_vectorField
  have hξ_ge_neg_one : -(1 : ℝ) ≤ ξ := by
    rw [← hξ]
    exact Real.neg_one_le_cos ξ
  have hξ_le_one : ξ ≤ 1 := by
    rw [← hξ]
    exact Real.cos_le_one ξ
  have hξ_pos : 0 < ξ := by
    rw [← hξ]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  by_cases hxlarge : 1 < x
  · linarith [Real.cos_le_one x]
  · have hx1 : x ≤ 1 := le_of_not_gt hxlarge
    have hξmem : ξ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hξ_pos.le, by nlinarith [Real.pi_gt_three]⟩
    have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨le_trans hξ_pos.le hξx.le, by nlinarith [Real.pi_gt_three]⟩
    have hcos := Real.strictAntiOn_cos hξmem hxmem hξx
    rw [hξ] at hcos
    linarith

/-- Global representatives satisfying the frozen half-line predicate are
unique on the half-line. -/
lemma apm_m99j01_solution_unique {u₀ : ℝ} {u v : ℝ → ℝ}
    (hu : apm_m99j01_IsSolution u₀ u)
    (hv : apm_m99j01_IsSolution u₀ v) :
    ∀ t : ℝ, 0 ≤ t → v t = u t := by
  intro t ht
  have huniq := ODE_solution_unique (K := 2)
    (v := fun _ : ℝ => apm_m99j01_vectorField)
    (f := v) (g := u) (a := (0 : ℝ)) (b := t)
    (fun _ => apm_m99j01_vectorField_lipschitz)
    hv.1.continuous.continuousOn
    (fun s hs => by
      have hd := (hv.1.differentiable one_ne_zero s).hasDerivAt
      apply HasDerivAt.hasDerivWithinAt
      convert hd using 1
      unfold apm_m99j01_vectorField
      linarith [hv.2.2 s hs.1])
    hu.1.continuous.continuousOn
    (fun s hs => by
      have hd := (hu.1.differentiable one_ne_zero s).hasDerivAt
      apply HasDerivAt.hasDerivWithinAt
      convert hd using 1
      unfold apm_m99j01_vectorField
      linarith [hu.2.2 s hs.1])
    (by rw [hu.2.1, hv.2.1])
  exact huniq ⟨ht, le_rfl⟩

/-- Why this unblocks `apm_m99j01`: this is the precise global continuation
statement missing from Mathlib's local Picard--Lindelöf API, expressed in the
frozen raw-`deriv` half-line solution predicate. -/
theorem apm_m99J01_bridge_global_solution (u₀ : ℝ) :
    ∃ u : ℝ → ℝ, apm_m99j01_IsSolution u₀ u := by
  sorry

/-- Why this unblocks `apm_m99j01`: the phase-line signs already proved above
imply trapping and the appropriate monotonicity direction; the final clause
identifies the resulting monotone limit with the equilibrium. -/
theorem apm_m99J01_bridge_trapping_and_convergence
    {ξ u₀ : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u) :
    ((u₀ ≤ ξ →
        MonotoneOn u (Set.Ici 0) ∧
        ∀ t : ℝ, 0 ≤ t → u t ≤ ξ) ∧
      (ξ ≤ u₀ →
        AntitoneOn u (Set.Ici 0) ∧
        ∀ t : ℝ, 0 ≤ t → ξ ≤ u t)) ∧
      Filter.Tendsto u Filter.atTop (nhds ξ) := by
  sorry

theorem apm_m99j01 :
    (∀ u₀ : ℝ,
      ∃ u : ℝ → ℝ,
        apm_m99j01_IsSolution u₀ u ∧
          ∀ v : ℝ → ℝ, apm_m99j01_IsSolution u₀ v →
            ∀ t : ℝ, 0 ≤ t → v t = u t) ∧
    ∃! ξ : ℝ,
      Real.cos ξ = ξ ∧
        ∀ (u₀ : ℝ) (u : ℝ → ℝ),
          apm_m99j01_IsSolution u₀ u →
            Filter.Tendsto u Filter.atTop (nhds ξ) := by
  have hexists_fixed : ∃ ξ : ℝ, Real.cos ξ = ξ := by
    let g : ℝ → ℝ := fun x ↦ Real.cos x - x
    have hg : Continuous g := Real.continuous_cos.sub continuous_id
    have hz : (0 : ℝ) ∈ Set.Icc (g 1) (g 0) := by
      refine ⟨?_, ?_⟩
      · exact sub_nonpos.mpr (Real.cos_le_one 1)
      · simp [g]
    obtain ⟨ξ, _hξ, hξ⟩ :=
      intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn hz
    exact ⟨ξ, sub_eq_zero.mp hξ⟩
  have hexists_unique_fixed : ∃! ξ : ℝ, Real.cos ξ = ξ := by
    obtain ⟨ξ, hξ⟩ := hexists_fixed
    exact ⟨ξ, hξ, fun y hy => apm_m99j01_cos_fixed_unique hy hξ⟩
  /-
  Boundary (closer hop 1): existence and uniqueness of the real cosine fixed point are proved
  above by the intermediate value theorem and `Real.strictAntiOn_cos`.
  This hop adds `apm_m99j01_vectorField_lipschitz`, proving the exact global
  Lipschitz constant `2` by combining `Real.lipschitzWith_cos` with
  `LipschitzWith.id`, and `apm_m99j01_fixed_isSolution`, which bundles every
  fixed point as the constant equilibrium in the frozen solution predicate.
  (Sibling: m00A05)

  Completing the frozen theorem requires global
  Picard--Lindelöf existence for the vector field `cos u - u`, half-line
  uniqueness for arbitrary global `C¹` extensions and the monotone-trapping
  convergence argument. I searched
  Mathlib's ODE flow/Picard--Lindelöf, global Lipschitz continuation, Grönwall,
  strict monotonicity, and autonomous-flow APIs; I did not find an assembled
  route from those APIs to this raw `deriv`-based solution predicate in this
  pass. Sibling `m00A05` reaches the same remaining globalization boundary;
  `m93J06`, `m96A02`, and `m96J02` likewise do not provide a closed global
  representative construction. Mathlib's `ODE_solution_unique_univ` can close
  uniqueness once a global `HasDerivAt` solution exists, but local Picard output
  is still interval-based and does not directly construct the required global
  `ContDiff ℝ 1` extension.

  Closer hop 2 closes half-line uniqueness outright in
  `apm_m99j01_solution_unique`. Rather than requiring an ODE on negative
  times, it applies `ODE_solution_unique` separately on every interval `[0,t]`
  and converts the frozen raw-`deriv` equation to `HasDerivWithinAt` there.
  Renewed inspection of `PicardLindelof.lean` found only local `Icc`/`Ioo`
  existence declarations (`exists_eq_forall_mem_Icc_hasDerivWithinAt` and its
  closed-ball variants), not a global continuation theorem. The remaining
  bridge is global construction of one compatible `C¹` representative,
  followed by monotone trapping and attraction to the fixed point; uniqueness
  is no longer part of the open boundary.

  Closer hop 3 proves the two global sign lemmas
  `apm_m99j01_vectorField_pos_of_lt_fixed` and
  `apm_m99j01_vectorField_neg_of_fixed_lt`: below the unique equilibrium the
  vector field is positive, and above it the vector field is negative.  The
  proof combines the elementary global cosine bounds with
  `Real.strictAntiOn_cos` only on `[0, π]`.  This closes the pointwise phase-line
  calculation needed by the trapping/attraction argument.  What remains open
  is still the global compatible `C¹` solution construction, followed by the
  calculus step upgrading these signs to monotonicity/trapping and convergence.
  -/
  sorry

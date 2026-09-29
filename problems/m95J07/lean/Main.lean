import Mathlib

/-!
# APM m95J07 — category and automatic continuity

## Statement repairs

None. “Second category” is read in its standard sense of “not meagre.”

## Encoding note

A function in `C[-1,1]` is differentiable at the interior point zero exactly
when its restriction has an ambient extension differentiable at zero; this
avoids replacing the sup-norm continuous-function space by all functions.
-/

abbrev apm_m95j07_C := ContinuousMap (Set.Icc (-1 : ℝ) 1) ℝ

def apm_m95j07_DifferentiableAtZero (f : apm_m95j07_C) : Prop :=
  ∃ F : ℝ → ℝ,
    (∀ t (ht : t ∈ Set.Icc (-1 : ℝ) 1), F t = f ⟨t, ht⟩) ∧
    DifferentiableAt ℝ F 0

/-- The absolute-value cusp, bundled in the frozen continuous-function space. -/
def apm_m95j07_cusp : apm_m95j07_C :=
  ⟨fun t ↦ |(t : ℝ)|, continuous_abs.comp continuous_subtype_val⟩

/-- The cusp has unit sup norm, so scalar cusp perturbations can be made
arbitrarily small while remaining nonzero. -/
lemma apm_m95j07_norm_cusp : ‖apm_m95j07_cusp‖ = 1 := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (by norm_num)]
    intro t
    change ‖|(t : ℝ)|‖ ≤ 1
    simpa only [Real.norm_eq_abs, abs_abs] using abs_le.mpr t.property
  · calc
      1 = ‖apm_m95j07_cusp ⟨1, by constructor <;> norm_num⟩‖ := by
        change 1 = ‖|(1 : ℝ)|‖
        norm_num
      _ ≤ ‖apm_m95j07_cusp‖ := ContinuousMap.norm_coe_le_norm _ _

/-- The ambient-extension encoding detects the standard cusp at zero. -/
lemma apm_m95j07_cusp_not_differentiable :
    ¬ apm_m95j07_DifferentiableAtZero apm_m95j07_cusp := by
  rintro ⟨F, hF, hdiff⟩
  apply not_differentiableAt_abs_zero
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
    with t ht
  symm
  exact hF t ⟨ht.1.le, ht.2.le⟩

/-- Every nonzero scalar multiple of the cusp remains excluded by the exact
ambient-extension differentiability predicate.  These arbitrarily small
cusps are the perturbations required in the eventual empty-interior proof. -/
lemma apm_m95j07_smul_cusp_not_differentiable (c : ℝ) (hc : c ≠ 0) :
    ¬ apm_m95j07_DifferentiableAtZero (c • apm_m95j07_cusp) := by
  rintro ⟨F, hF, hdiff⟩
  apply apm_m95j07_cusp_not_differentiable
  refine ⟨fun t => c⁻¹ * F t, ?_, hdiff.const_mul c⁻¹⟩
  intro t ht
  change c⁻¹ * F t = |t|
  rw [hF t ht]
  change c⁻¹ * (c * |t|) = |t|
  field_simp

/-- Adding a nonzero cusp perturbation to a function differentiable at zero
destroys differentiability there.  The proof works directly with the frozen
existential-extension encoding by subtracting the two hypothetical ambient
extensions. -/
lemma apm_m95j07_add_smul_cusp_not_differentiable
    (f : apm_m95j07_C) (hf : apm_m95j07_DifferentiableAtZero f)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ apm_m95j07_DifferentiableAtZero (f + c • apm_m95j07_cusp) := by
  rintro ⟨G, hG, hGdiff⟩
  rcases hf with ⟨F, hF, hFdiff⟩
  apply apm_m95j07_smul_cusp_not_differentiable c hc
  refine ⟨fun t => G t - F t, ?_, hGdiff.sub hFdiff⟩
  intro t ht
  change G t - F t = c * |t|
  rw [hG t ht, hF t ht]
  change (f ⟨t, ht⟩ + c * |t|) - f ⟨t, ht⟩ = c * |t|
  ring

/-- Functions whose secant slopes from zero are globally bounded by the
natural number `N`.  Differentiable functions lie in the union of these
closed sets. -/
def apm_m95j07_slopeControl (N : ℕ) : Set apm_m95j07_C :=
  {f | ∀ t : Set.Icc (-1 : ℝ) 1,
    dist (f t) (f ⟨0, by constructor <;> norm_num⟩) ≤ (N : ℝ) * |(t : ℝ)|}

/-- Concrete non-vacuity check for the slope-control construction. -/
lemma apm_m95j07_zero_mem_slopeControl (N : ℕ) :
    (0 : apm_m95j07_C) ∈ apm_m95j07_slopeControl N := by
  intro t
  simp
  positivity

lemma apm_m95j07_isClosed_slopeControl (N : ℕ) :
    IsClosed (apm_m95j07_slopeControl N) := by
  rw [show apm_m95j07_slopeControl N =
      ⋂ t : Set.Icc (-1 : ℝ) 1,
        {f : apm_m95j07_C |
          dist (f t) (f ⟨0, by constructor <;> norm_num⟩) ≤
            (N : ℝ) * |(t : ℝ)|} by
    ext f
    simp [apm_m95j07_slopeControl]]
  apply isClosed_iInter
  intro t
  apply isClosed_le
  · exact (continuous_eval_const t).dist
      (continuous_eval_const
        (⟨0, by constructor <;> norm_num⟩ : Set.Icc (-1 : ℝ) 1))
  · exact continuous_const

lemma apm_m95j07_differentiable_mem_iUnion_slopeControl
    (f : apm_m95j07_C) (hf : apm_m95j07_DifferentiableAtZero f) :
    f ∈ ⋃ N : ℕ, apm_m95j07_slopeControl N := by
  rcases hf with ⟨F, hF, hdiff⟩
  obtain ⟨c, hc⟩ := hdiff.isBigO_sub.bound
  rcases (Metric.mem_nhds_iff.mp hc) with ⟨ε, hε, hball⟩
  let C : ℝ := max c (2 * ‖f‖ / ε)
  obtain ⟨N : ℕ, hNC⟩ := exists_nat_ge C
  refine Set.mem_iUnion.2 ⟨N, ?_⟩
  intro t
  change dist (f t) (f ⟨0, by constructor <;> norm_num⟩) ≤
    (N : ℝ) * |(t : ℝ)|
  by_cases ht : |(t : ℝ)| < ε
  · have htb : (t : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Real.dist_eq] using ht
    have hloc := hball htb
    have htI : (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := t.property
    have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
    change ‖F (t : ℝ) - F 0‖ ≤ c * ‖(t : ℝ) - 0‖ at hloc
    rw [hF (t : ℝ) htI, hF 0 hzero] at hloc
    rw [dist_eq_norm]
    calc
      ‖f t - f ⟨0, hzero⟩‖ ≤ c * |(t : ℝ)| := by simpa using hloc
      _ ≤ C * |(t : ℝ)| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ (N : ℝ) * |(t : ℝ)| :=
        mul_le_mul_of_nonneg_right hNC (abs_nonneg _)

  · have htε : ε ≤ |(t : ℝ)| := le_of_not_gt ht
    have hf0 : ‖f ⟨0, by constructor <;> norm_num⟩‖ ≤ ‖f‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    have hft : ‖f t‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm _ _
    have hdist : dist (f t) (f ⟨0, by constructor <;> norm_num⟩) ≤ 2 * ‖f‖ := by
      rw [dist_eq_norm]
      calc
        ‖f t - f ⟨0, by constructor <;> norm_num⟩‖ ≤
            ‖f t‖ + ‖f ⟨0, by constructor <;> norm_num⟩‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add hft hf0
        _ = 2 * ‖f‖ := by ring
    calc
      dist (f t) (f ⟨0, by constructor <;> norm_num⟩) ≤ 2 * ‖f‖ := hdist
      _ ≤ (2 * ‖f‖ / ε) * |(t : ℝ)| := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hε).2
        exact mul_le_mul_of_nonneg_left htε (by positivity)
      _ ≤ C * |(t : ℝ)| :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
      _ ≤ (N : ℝ) * |(t : ℝ)| :=
        mul_le_mul_of_nonneg_right hNC (abs_nonneg _)

/-- A triangular spike of height `a` and half-width `w`, centered at zero. -/
noncomputable def apm_m95j07_spike (a w : ℝ) : apm_m95j07_C :=
  ⟨fun t ↦ a * max (1 - |(t : ℝ)| / w) 0,
    continuous_const.mul
      ((continuous_const.sub
        ((continuous_abs.comp continuous_subtype_val).div_const w)).max continuous_const)⟩

/-- Concrete non-vacuity: a positive-height spike takes that height at zero. -/
lemma apm_m95j07_spike_zero (a w : ℝ) :
    apm_m95j07_spike a w ⟨0, by constructor <;> norm_num⟩ = a := by
  simp [apm_m95j07_spike]

lemma apm_m95j07_spike_at_width {a w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    apm_m95j07_spike a w ⟨w, ⟨by linarith, hw1⟩⟩ = 0 := by
  simp [apm_m95j07_spike, abs_of_pos hw, hw.ne']

lemma apm_m95j07_norm_spike_le {a w : ℝ} (hw : 0 < w) :
    ‖apm_m95j07_spike a w‖ ≤ |a| := by
  rw [ContinuousMap.norm_le _ (abs_nonneg a)]
  intro t
  change ‖a * max (1 - |(t : ℝ)| / w) 0‖ ≤ |a|
  rw [norm_mul, Real.norm_eq_abs]
  have hq0 : 0 ≤ |(t : ℝ)| / w := div_nonneg (abs_nonneg _) hw.le
  have hm0 : 0 ≤ max (1 - |(t : ℝ)| / w) 0 := le_max_right _ _
  have hm1 : max (1 - |(t : ℝ)| / w) 0 ≤ 1 := by
    exact max_le (by linarith) (by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg hm0]
  nlinarith [abs_nonneg a]

lemma apm_m95j07_add_spike_not_mem_slopeControl
    (N : ℕ) (f : apm_m95j07_C) (hf : f ∈ apm_m95j07_slopeControl N)
    {a w : ℝ} (ha : 0 < a) (hw : 0 < w) (hw1 : w ≤ 1)
    (hlarge : 2 * (N : ℝ) * w < a) :
    f + apm_m95j07_spike a w ∉ apm_m95j07_slopeControl N := by
  intro hg
  let p0 : Set.Icc (-1 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let pw : Set.Icc (-1 : ℝ) 1 := ⟨w, by constructor <;> linarith⟩
  have hfbound := hf pw
  have hgbound := hg pw
  have hp0 : apm_m95j07_spike a w p0 = a := by
    change a * max (1 - |(0 : ℝ)| / w) 0 = a
    simp
  have hpw : apm_m95j07_spike a w pw = 0 := by
    change a * max (1 - |w| / w) 0 = 0
    simp [abs_of_pos hw, hw.ne']
  have hfa : dist (f p0) (f pw) ≤ (N : ℝ) * w := by
    change dist (f pw) (f p0) ≤ (N : ℝ) * |w| at hfbound
    rw [abs_of_pos hw] at hfbound
    rw [dist_comm]
    exact hfbound
  have hga : dist (f pw) (f p0 + a) ≤ (N : ℝ) * w := by
    change dist (f pw + apm_m95j07_spike a w pw)
      (f p0 + apm_m95j07_spike a w p0) ≤ (N : ℝ) * |w| at hgbound
    rw [hpw, hp0, add_zero, abs_of_pos hw] at hgbound
    exact hgbound
  have htri := dist_triangle (f p0) (f pw) (f p0 + a)
  have hleft : dist (f p0) (f p0 + a) = a := by
    rw [Real.dist_eq]
    simp [abs_of_pos ha]
  rw [hleft] at htri
  linarith

set_option maxHeartbeats 50000 in
lemma apm_m95j07_interior_slopeControl (N : ℕ) :
    interior (apm_m95j07_slopeControl N) = ∅ := by
  apply Set.Subset.antisymm
  · intro f hfint
    have hnh : apm_m95j07_slopeControl N ∈ nhds f :=
      mem_interior_iff_mem_nhds.mp hfint
    rcases Metric.mem_nhds_iff.mp hnh with ⟨r, hr, hball⟩
    let a : ℝ := r / 2
    let w : ℝ := min (1 / 2 : ℝ) (a / (4 * ((N : ℝ) + 1)))
    have ha : 0 < a := by dsimp [a]; linarith
    have har : a < r := by dsimp [a]; linarith
    have hden : 0 < 4 * ((N : ℝ) + 1) := by positivity
    have hw : 0 < w := by
      dsimp [w]
      exact lt_min (by norm_num) (div_pos ha hden)
    have hw1 : w ≤ 1 := by
      have := min_le_left (1 / 2 : ℝ) (a / (4 * ((N : ℝ) + 1)))
      dsimp [w]
      linarith
    have hwdiv : w ≤ a / (4 * ((N : ℝ) + 1)) := by
      exact min_le_right _ _
    have hwbound : w * (4 * ((N : ℝ) + 1)) ≤ a :=
      (le_div_iff₀ hden).mp hwdiv
    have hstrict : 2 * (N : ℝ) * w < a := by
      have hc : 2 * (N : ℝ) < 4 * ((N : ℝ) + 1) := by linarith
      calc
        2 * (N : ℝ) * w < (4 * ((N : ℝ) + 1)) * w :=
          mul_lt_mul_of_pos_right hc hw
        _ = w * (4 * ((N : ℝ) + 1)) := by ring
        _ ≤ a := hwbound
    let g : apm_m95j07_C := f + apm_m95j07_spike a w
    have hgf : dist g f < r := by
      rw [dist_eq_norm]
      change ‖(f + apm_m95j07_spike a w) - f‖ < r
      rw [add_sub_cancel_left]
      exact lt_of_le_of_lt (apm_m95j07_norm_spike_le hw)
        (by simpa [abs_of_pos ha] using har)
    have hgmem : g ∈ apm_m95j07_slopeControl N := hball hgf
    have hfmem : f ∈ apm_m95j07_slopeControl N := interior_subset hfint
    exact (apm_m95j07_add_spike_not_mem_slopeControl
      N f hfmem ha hw hw1 hstrict hgmem).elim
  · exact Set.empty_subset _

/-- The automatic-continuity conjunct, isolated as a reusable closed-graph
argument. -/
lemma apm_m95j07_automatic_continuity
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →ₗ[ℝ] X) (A : X →L[ℝ] X)
    (hA : Function.Injective A) (hAT : Continuous fun x ↦ A (T x)) :
    Continuous T := by
  apply T.continuous_of_seq_closed_graph
  intro u x y hu hTu
  apply hA
  exact tendsto_nhds_unique
    (A.continuous.continuousAt.tendsto.comp hTu)
    (hAT.continuousAt.tendsto.comp hu)

theorem apm_m95j07 :
    (¬ IsMeagre {f : apm_m95j07_C | ¬ apm_m95j07_DifferentiableAtZero f}) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (T : X →ₗ[ℝ] X) (A : X →L[ℝ] X),
      Function.Injective A → Continuous (fun x => A (T x)) → Continuous T) := by
  classical
  /-
  Boundary (closer hop 1): the entire automatic-continuity conjunct is now
  compiled as `apm_m95j07_automatic_continuity`.  It uses Mathlib's
  `LinearMap.continuous_of_seq_closed_graph`: if `uₙ → x` and `T uₙ → y`,
  continuity of `A` and `A ∘ T` gives `A y = A (T x)`, and injectivity of `A`
  closes the graph.  Thus part (b) is solved without needing an inverse for
  `A` or closedness of its range.

  Closer hop 2 addresses the encoding-specific perturbation issue rather than
  repeating the category search. `apm_m95j07_cusp` bundles `t ↦ |t|` in
  `C([-1,1])`, and `apm_m95j07_cusp_not_differentiable` proves that it does
  not satisfy the existential ambient-extension predicate. Indeed, every such
  extension agrees with `abs` on the neighborhood `(-1,1)` of zero, so local
  differentiability would contradict `not_differentiableAt_abs_zero`. This
  supplies a compiled cusp witness compatible with the exact frozen encoding.

  The remaining first conjunct is the Baire-category construction.  Searches
  of `LEMMA-INDEX.md`, `ConstructionTargets`, Mathlib's Baire/meagre APIs,
  closed artifacts involving `ContinuousMap`, and git history found no
  packaged theorem that nondifferentiability at one fixed point is nonmeagre.
  A local proof must still express differentiability at zero as a countable union of
  closed slope-bounded sets, prove each has empty interior by adding an
  arbitrarily small scalar multiples/translates of the compiled cusp or a
  zigzag near zero, and invoke that
  `C([-1,1])` is a Baire space.  The existential ambient-extension encoding
  additionally requires showing the countable slope condition equivalent to
  `apm_m95j07_DifferentiableAtZero`; the local-extension obstruction for the
  basic cusp is now closed.

  Closer hop 3 turns that single witness into the perturbation engine required
  by the category proof. `apm_m95j07_norm_cusp` proves the cusp has unit sup
  norm. `apm_m95j07_smul_cusp_not_differentiable` proves every nonzero scalar
  multiple still violates the frozen extension predicate, and
  `apm_m95j07_add_smul_cusp_not_differentiable` proves that adding such a cusp
  to any function differentiable at zero destroys differentiability. Hence
  arbitrarily small nondifferentiable perturbations of every differentiable
  function are now available in the actual Banach space.

  The final-hop search also inspected Mathlib's residual/meagre and Baire
  lemmas (`not_isMeagre_of_isGδ_of_dense` and the countable-union
  characterizations), plus the compact-domain `ContinuousMap` sup-norm API.
  These supplied the norm calculation above but no theorem making the frozen
  existential ambient-extension differentiability set an `Fσ` set. The
  remaining bridge is still to construct closed slope-control sets covering
  that predicate and prove each nowhere dense; the frozen statement is
  unchanged.

  Original boundary:
  SKIPPED: two-part functional analysis problem.
  -- (a) Nowhere-differentiable functions in C[-1,1] form a non-meagre set (second category).
  --     Classic Baire category theorem application.
  -- (b) Automatic continuity: if A∘T is continuous and A injective, then T continuous.
  --     Requires closed graph theorem or open mapping theorem.
  -- Blocker: (a) needs Baire category theorem application (meagre/non-meagre argument);
  -- (b) needs closed graph / open mapping theorem (may partially exist in Mathlib).
  APIs: `IsMeagre`, `ContinuousMap`, `ContinuousLinearMap`, `CompleteSpace`.
  -/
  refine ⟨?_, ?_⟩
  · intro hnondiff
    have hcontrol (N : ℕ) : IsMeagre (apm_m95j07_slopeControl N) :=
      ((apm_m95j07_isClosed_slopeControl N).isNowhereDense_iff.mpr
        (apm_m95j07_interior_slopeControl N)).isMeagre
    have hunion : IsMeagre (⋃ N : ℕ, apm_m95j07_slopeControl N) :=
      isMeagre_iUnion hcontrol
    let D : Set apm_m95j07_C :=
      {f | apm_m95j07_DifferentiableAtZero f}
    have hDsub : D ⊆ ⋃ N : ℕ, apm_m95j07_slopeControl N := by
      intro f hf
      exact apm_m95j07_differentiable_mem_iUnion_slopeControl f hf
    have hD : IsMeagre D := hunion.mono hDsub
    have hcover : D ∪ {f : apm_m95j07_C |
        ¬ apm_m95j07_DifferentiableAtZero f} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f
      by_cases hf : apm_m95j07_DifferentiableAtZero f
      · exact Or.inl hf
      · exact Or.inr hf
    have hall : IsMeagre (Set.univ : Set apm_m95j07_C) := by
      rw [← hcover]
      exact hD.union hnondiff
    exact (not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty) hall
  · intro X _ _ _ T A hA hAT
    exact apm_m95j07_automatic_continuity X T A hA hAT

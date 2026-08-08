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
  sorry

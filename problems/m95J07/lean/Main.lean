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

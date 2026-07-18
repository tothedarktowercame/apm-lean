import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville

/-!
# APM a03J08: Surjectivity of an analytic function blowing up at all boundary points

**Problem.** Let `F` be a finite subset of `ℂ` and `D = ℂ \\ F`. Let `f` be
analytic on `D` with `|f(z)| → ∞` as `|z| → ∞` and as `z → z_α` for each
`z_α ∈ F`. Show that `f(D) = ℂ`.

## Proof strategy

Suppose for contradiction that `w₀ ∉ f(D)`. Then `g(z) = 1/(f(z) - w₀)` is
analytic on `D` and tends to 0 near each point of `F` (since `|f| → ∞` there).
By the Riemann removable singularity theorem, `g` extends to an entire
function. Since `g → 0` as `|z| → ∞`, Liouville's theorem forces `g ≡ 0`,
contradicting `g(z) ≠ 0` on `D`.

## Key Mathlib tools

- `Complex.differentiableOn_update_limUnder_of_bddAbove` — Riemann removable
  singularity theorem
- `Differentiable.eq_const_of_tendsto_cocompact` — Liouville's theorem for
  functions tending to a constant at infinity
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Set Filter
open scoped Topology

namespace ApmCanaries.A03J08

/-! ## Auxiliary lemmas: norm estimates for reciprocal -/

/-- If `‖f(z)‖ → ∞` along a filter, then `‖f(z) - w₀‖ → ∞`. -/
lemma tendsto_norm_sub_atTop {α : Type*} {l : Filter α}
    {f : α → ℂ} (w₀ : ℂ)
    (hf : Tendsto (fun z => ‖f z‖) l atTop) :
    Tendsto (fun z => ‖f z - w₀‖) l atTop := by
  intro s hs
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp hs
  have hIci_mem : ∀ᶠ z in l, a + ‖w₀‖ ≤ ‖f z‖ := by
    have : ∀ᶠ y in atTop, y ∈ Set.Ici (a + ‖w₀‖) :=
      mem_atTop_sets.mpr ⟨a + ‖w₀‖, fun _ h => h⟩
    exact hf this
  exact hIci_mem.mono fun z hz => ha _ (by
    linarith [norm_sub_norm_le (f z) w₀])

/-- If `‖f(z)‖ → ∞` along a filter, then `‖1/(f(z) - w₀)‖ → 0`. -/
lemma tendsto_norm_reciprocal_zero {α : Type*} {l : Filter α}
    {f : α → ℂ} (w₀ : ℂ)
    (hf : Tendsto (fun z => ‖f z‖) l atTop) :
    Tendsto (fun z => ‖(f z - w₀)⁻¹‖) l (𝓝 0) := by
  have hsub := tendsto_norm_sub_atTop w₀ hf
  have hinv : Tendsto (fun z => (‖f z - w₀‖)⁻¹) l (𝓝 0) :=
    Tendsto.inv_tendsto_atTop hsub
  convert hinv using 1
  ext z; simp [norm_inv]

/-! ## Statement and proof -/

/-- Main theorem: if `f` is analytic on `ℂ \\ F` (F finite), `|f(z)| → ∞` as
    `|z| → ∞` and as `z → z_α` for each `z_α ∈ F`, then `f(ℂ \\ F) = ℂ`. -/
theorem analytic_blowup_surjective
    {F : Finset ℂ}
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (↑F : Set ℂ)ᶜ)
    (hf_infty : Tendsto (fun z => ‖f z‖) (cocompact ℂ) atTop)
    (hf_poles : ∀ zα ∈ F,
      Tendsto (fun z => ‖f z‖) (𝓝[≠] zα) atTop) :
    f '' (↑F : Set ℂ)ᶜ = univ := by
  -- Suppose for contradiction that f(D) ≠ ℂ.
  by_contra h
  -- Extract w₀ ∉ f(D).
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℂ, w₀ ∉ f '' (↑F : Set ℂ)ᶜ := by
    by_contra hneg
    push_neg at hneg
    exact h (Set.eq_univ_of_forall hneg)
  -- Define g(z) = (f z - w₀)⁻¹.
  -- g is differentiable on D = Fᶜ (since f ≠ w₀ on D).
  have hg_diff : DifferentiableOn ℂ (fun z => (f z - w₀)⁻¹) (↑F : Set ℂ)ᶜ := by
    refine DifferentiableOn.inv ?_ ?_
    · exact hf_holo.sub_const w₀
    · intro z hz
      exact sub_ne_zero.mpr (fun heq => hw₀ ⟨z, hz, heq⟩)
  -- ‖g(z)‖ → 0 near each point of F and at infinity.
  have hg_poles : ∀ zα ∈ F,
      Tendsto (fun z => ‖(f z - w₀)⁻¹‖) (𝓝[≠] zα) (𝓝 0) := fun zα hzα =>
    tendsto_norm_reciprocal_zero w₀ (hf_poles zα hzα)
  -- ‖g(z)‖ → 0 at infinity.
  have hg_infty : Tendsto (fun z => ‖(f z - w₀)⁻¹‖) (cocompact ℂ) (𝓝 0) :=
    tendsto_norm_reciprocal_zero w₀ hf_infty
  -- Define the extended function: g_ext(z) = 0 if z ∈ F, else (f z - w₀)⁻¹
  set g_ext : ℂ → ℂ := fun z => if z ∈ (F : Set ℂ) then 0 else (f z - w₀)⁻¹ with hg_ext_def
  -- g_ext is differentiable at every point of ℂ.
  -- **SORRY BOUNDARY: extending g across the finite set F via Riemann
  -- removable singularities.**
  -- The proof requires showing:
  -- (1) At each z ∈ F: g_ext is analytic via
  --   `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`.
  --   This needs (a) g_ext differentiable on a punctured neighborhood of z
  --   (follows from hg_diff + the fact that near z, g_ext = reciprocal
  --   since F is discrete), and (b) g_ext continuous at z (follows from
  --   hg_poles giving ‖g_ext‖ → 0 = g_ext z).
  -- (2) At each z ∉ F: g_ext equals (f-w₀)⁻¹ near z (open neighborhood
  --   avoiding F since F is closed/finite), hence differentiable.
  -- Both cases require non-trivial set/filter bookkeeping connecting the
  -- if-then-else definition with Mathlib's analytic API. Specifically:
  -- - Showing g_ext agrees with (f-w₀)⁻¹ on an open neighborhood of z ∉ F
  --   requires F being closed (hence Fᶜ open), and then using
  --   DifferentiableAt.eq_on_open or similar.
  -- - For z ∈ F, the `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  --   requires `∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ g_ext w`, which needs
  --   g_ext = (f-w₀)⁻¹ eventually near z (since F is discrete, the punctured
  --   neighborhood avoids F\{z}), plus hg_diff.
  -- - The continuity at z ∈ F requires converting the norm-tendsto (hg_poles)
  --   to a tendsto of the function itself, plus handling the if-then-else.
  -- These are all mathematically routine but require careful Mathlib API
  -- navigation through the filter/set/differentiability infrastructure.
  have hg_entire : Differentiable ℂ g_ext := by sorry
  -- g_ext tends to 0 at infinity.
  have hg_ext_infty : Tendsto g_ext (cocompact ℂ) (𝓝 0) := by
    have hF_compact : IsCompact (F : Set ℂ) := F.finite_toSet.isCompact
    -- Eventually z ∉ F
    have hFc_mem : (F : Set ℂ)ᶜ ∈ cocompact ℂ :=
      mem_cocompact.mpr ⟨(F : Set ℂ), hF_compact, fun _ h => h⟩
    have hFc_event : ∀ᶠ z in cocompact ℂ, z ∉ (F : Set ℂ) := hFc_mem
    -- g_ext = (f - w₀)⁻¹ eventually
    have hgeq : g_ext =ᶠ[cocompact ℂ] (fun z => (f z - w₀)⁻¹) :=
      hFc_event.mono fun z hz => by simp only [hg_ext_def, if_neg hz]
    -- ‖(f-w₀)⁻¹‖ → 0 implies (f-w₀)⁻¹ → 0
    exact tendsto_congr' hgeq |>.mpr
      (tendsto_zero_iff_norm_tendsto_zero.mpr hg_infty)
  -- By Liouville, g_ext is identically 0.
  have hg_const : g_ext = Function.const ℂ 0 :=
    hg_entire.eq_const_of_tendsto_cocompact hg_ext_infty
  -- g_ext ≠ 0 on D (since (f z - w₀)⁻¹ ≠ 0 for z ∈ D).
  -- Pick any z₀ ∉ F (since ℂ is infinite and F is finite).
  have hexists : ∃ z₀ : ℂ, z₀ ∈ (F : Set ℂ)ᶜ := by
    by_contra hneg
    push_neg at hneg
    have huniv : (univ : Set ℂ) ⊆ (F : Set ℂ) := fun z _ => by
      simp_all
    have h_infinite : (univ : Set ℂ).Infinite := Set.infinite_univ
    have h_finite : Set.Finite (univ : Set ℂ) := F.finite_toSet.subset huniv
    exact h_infinite h_finite
  obtain ⟨z₀, hz₀⟩ := hexists
  have hgz₀ : g_ext z₀ = (f z₀ - w₀)⁻¹ := by
    rw [hg_ext_def]
    exact if_neg hz₀
  -- g_ext z₀ ≠ 0
  have hne : g_ext z₀ ≠ 0 := by
    rw [hgz₀]
    exact inv_ne_zero (sub_ne_zero.mpr (fun heq => hw₀ ⟨z₀, hz₀, heq⟩))
  -- But g_ext ≡ 0
  rw [hg_const] at hne
  simp at hne

end ApmCanaries.A03J08

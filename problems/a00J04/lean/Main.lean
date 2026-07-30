import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# APM a00J04: Components of the complement of a polynomial lemniscate

**Problem.** Let `p(z)` be a polynomial of degree `N ≥ 1` and let
`L = {z ∈ ℂ | |p(z)| = 1}`. Prove that the open set `ℂ \ L` has at most `N + 1`
connected components.

**Informal proof sketch** (from the harvested informal solution):

1. *Each component is purely sublevel or superlevel.* If `U` is a connected
   component of `ℂ \ L`, then `|p|` is continuous on `U` and never equals `1`.
   Since `U` is connected and `(0,∞) \ {1} = (0,1) ∪ (1,∞)` is disconnected,
   `|p(U)|` lies entirely in one piece.

2. *Exactly one superlevel component.* A bounded open connected set with `|p| > 1`
   contradicts the maximum modulus principle (since `|p| = 1` on the boundary).
   So every superlevel component is unbounded. Since `|p(z)| → ∞`, the set
   `{|z| > R}` lies in the superlevel for large `R`, and this set is connected,
   so there is exactly one superlevel component.

3. *Each sublevel component contains a root.* A sublevel component `U` is bounded
   (since `|p| → ∞`). If `p` never vanished on `U`, then `1/p` would be
   holomorphic on `U` with `|1/p| = 1` on `∂U` and `|1/p| > 1` on `U`,
   contradicting the maximum modulus principle.

4. *Count.* Distinct components are disjoint, hence contain distinct roots.
   Since `p` has at most `N` roots, there are at most `N` sublevel components,
   plus one superlevel component = `N + 1` total.

**Formalization status.**

The analytic core of the proof — the maximum modulus principle applied to
bounded open sets, the root-count bound, and the intermediate-value-style
argument that connected sets avoiding the lemniscate are purely sublevel or
superlevel — is fully proved below using Mathlib's
`Complex.norm_le_of_forall_mem_frontier_norm_le` and related lemmas.

The topological counting argument is also fully proved. Connected components
of the open complement are represented as open connected subsets of `ℂ`;
their frontiers lie in the lemniscate. A radial rescaling of the punctured
plane proves that every strict exterior region `{z | R < ‖z‖}` is path
connected. This supplies the one-endedness argument identifying all
superlevel components. Finally, the components inject into the disjoint sum
of the distinct roots of `p` and one superlevel marker.

**Statement repair note.** The informal-solution-proposed Lean statement used
`Nat.card (ConnectedComponents (lemniscate p)ᶜ)`. The correct target type is
`ConnectedComponents ↥((lemniscate p)ᶜ)` — the connected components of the
*subtype* (i.e. the subspace topology on the complement). Writing
`(lemniscate p)ᶜ` directly in that position is a set-complement, not a type,
and does not elaborate. The repair is to pass the subtype `↥((lemniscate p)ᶜ)`.
-/

open Complex Polynomial Set Topology Metric Bornology

set_option linter.unusedVariables false in
noncomputable section

namespace ApmCanaries.A00J04

variable {p : ℂ[X]} (hp : 0 < p.natDegree)

/-- The polynomial lemniscate `L = {z | |p(z)| = 1}`. -/
def lemniscate (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖aeval z p‖ = 1}

/-- The superlevel set `{z | |p(z)| > 1}`. -/
def superlevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | 1 < ‖aeval z p‖}

/-- The sublevel set `{z | |p(z)| < 1}`. -/
def sublevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖aeval z p‖ < 1}

lemma isClosed_lemniscate : IsClosed (lemniscate p) := by
  exact isClosed_eq p.differentiable_aeval.continuous.norm
    (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ)))

private def componentSet (x : ↥((lemniscate p)ᶜ)) : Set ℂ :=
  Subtype.val '' connectedComponent x

private lemma componentSet_nonempty (x : ↥((lemniscate p)ᶜ)) :
    (componentSet x).Nonempty :=
  ⟨x, ⟨x, mem_connectedComponent, rfl⟩⟩

private lemma componentSet_subset_compl (x : ↥((lemniscate p)ᶜ)) :
    componentSet x ⊆ (lemniscate p)ᶜ := by
  rintro z ⟨y, _hy, rfl⟩
  exact y.2

private lemma componentSet_connected (x : ↥((lemniscate p)ᶜ)) :
    IsConnected (componentSet x) :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

private lemma componentSet_open (x : ↥((lemniscate p)ᶜ)) :
    IsOpen (componentSet x) := by
  have hcompl : IsOpen ((lemniscate p)ᶜ) := (isClosed_lemniscate (p := p)).isOpen_compl
  letI : LocallyConnectedSpace ↥((lemniscate p)ᶜ) := hcompl.locallyConnectedSpace
  exact hcompl.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_connectedComponent

private lemma componentSet_frontier_subset_lemniscate
    (x : ↥((lemniscate p)ᶜ)) :
    frontier (componentSet x) ⊆ lemniscate p := by
  have hcompl : IsOpen ((lemniscate p)ᶜ) := (isClosed_lemniscate (p := p)).isOpen_compl
  intro z hz
  by_contra hzL
  have hzcompl : z ∈ (lemniscate p)ᶜ := hzL
  let y : ↥((lemniscate p)ᶜ) := ⟨z, hzcompl⟩
  have hycl : y ∈ closure (connectedComponent x) := by
    rw [hcompl.isOpenEmbedding_subtypeVal.isEmbedding.closure_eq_preimage_closure_image]
    exact hz.1
  have hycomp : y ∈ connectedComponent x :=
    isClosed_connectedComponent.closure_subset_iff.mpr subset_rfl hycl
  have hzcomp : z ∈ componentSet x := ⟨y, hycomp, rfl⟩
  exact hz.2 (mem_interior_iff_mem_nhds.mpr
    (IsOpen.mem_nhds (componentSet_open (p := p) x) hzcomp))

private lemma componentSet_eq_of_common_point
    {x y : ↥((lemniscate p)ᶜ)} {z : ℂ}
    (hzx : z ∈ componentSet x) (hzy : z ∈ componentSet y) :
    (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y := by
  obtain ⟨zx, hzx, hzxval⟩ := hzx
  obtain ⟨zy, hzy, hzyval⟩ := hzy
  have hxy : zx = zy := Subtype.ext (hzxval.trans hzyval.symm)
  subst zy
  rw [ConnectedComponents.coe_eq_coe]
  exact (connectedComponent_eq_iff_mem.mpr hzx).symm.trans
    (connectedComponent_eq_iff_mem.mpr hzy)

private lemma exterior_pathConnected (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {z : ℂ | R < ‖z‖} := by
  let f : ℂ → ℂ := fun y => (((R + ‖y‖) * ‖y‖⁻¹ : ℝ) : ℂ) * y
  have hf : ContinuousOn f ({0}ᶜ : Set ℂ) := by
    intro y hy
    change ContinuousWithinAt
      (fun y : ℂ => (((R + ‖y‖) * ‖y‖⁻¹ : ℝ) : ℂ) * y) {0}ᶜ y
    exact ((Complex.continuous_ofReal.continuousAt.comp
      (((continuousAt_const.add continuousAt_id.norm).mul
        (ContinuousAt.inv₀ continuousAt_id.norm (by simpa using hy))))).mul
          continuousAt_id).continuousWithinAt
  have hpunctured : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 0
  have himage : IsPathConnected (f '' ({0}ᶜ : Set ℂ)) :=
    hpunctured.image' hf
  have heq : f '' ({0}ᶜ : Set ℂ) = {z : ℂ | R < ‖z‖} := by
    apply Set.Subset.antisymm
    · rintro _z ⟨y, hy, rfl⟩
      have hynorm : ‖y‖ ≠ 0 := by simpa using hy
      have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr (by simpa using hy)
      have hcoeff : 0 < (R + ‖y‖) * ‖y‖⁻¹ :=
        mul_pos (add_pos_of_nonneg_of_pos hR hynorm_pos) (inv_pos.mpr hynorm_pos)
      change R < ‖f y‖
      rw [show ‖f y‖ = R + ‖y‖ by
        simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (add_pos_of_nonneg_of_pos hR hynorm_pos),
          abs_of_pos (inv_pos.mpr hynorm_pos)]
        field_simp]
      linarith
    · intro z hz
      change R < ‖z‖ at hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hR hz
      let y : ℂ := (((‖z‖ - R) * ‖z‖⁻¹ : ℝ) : ℂ) * z
      have hycoeff : 0 < (‖z‖ - R) * ‖z‖⁻¹ :=
        mul_pos (sub_pos.mpr hz) (inv_pos.mpr hzpos)
      have hynorm : ‖y‖ = ‖z‖ - R := by
        simp only [y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (sub_pos.mpr hz), abs_of_pos (inv_pos.mpr hzpos)]
        field_simp
      have hy0 : y ≠ 0 := by
        intro hy
        have := congrArg norm hy
        rw [hynorm, norm_zero] at this
        linarith
      refine ⟨y, by simpa using hy0, ?_⟩
      have hzC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
      have hsubC : ((‖z‖ - R : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (sub_ne_zero.mpr hz.ne')
      have hsubC' : (‖z‖ : ℂ) - (R : ℂ) ≠ 0 := by
        exact_mod_cast (sub_ne_zero.mpr hz.ne')
      dsimp only [f, y]
      rw [hynorm]
      push_cast
      field_simp [hzC, hsubC, hsubC']
      ring
  rwa [heq] at himage

-- The function `z ↦ aeval z p` is entire (complex differentiable everywhere).
-- This is needed for all the maximum modulus arguments.
private lemma diffContOnCl_aeval (p : ℂ[X]) (U : Set ℂ) :
    DiffContOnCl ℂ (fun z : ℂ => aeval z p) U :=
  (p.differentiable_aeval).diffContOnCl

/-! ## Step 1: Connected sets avoiding the lemniscate are purely sublevel or superlevel

This is the intermediate-value theorem for connected sets: the continuous image
of a connected set is connected (an interval in ℝ), and a connected subset of
`(0,∞) \ {1}` lies entirely in `(0,1)` or `(1,∞)`.
-/

/-- A preconnected set disjoint from the lemniscate lies entirely in the
superlevel or entirely in the sublevel.

This is the key topological ingredient: the function `z ↦ ‖aeval z p‖` is
continuous, so its image of a preconnected set is a connected subset of ℝ
(an interval). If that image avoids `1`, it lies entirely below or entirely
above. We use Mathlib's `IsPreconnected.mapsTo_Ioi_or_Iio`. -/
lemma isPreconnected_subset_superlevel_or_sublevel
    {S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :
    S ⊆ superlevel p ∨ S ⊆ sublevel p := by
  let f : ℂ → ℝ := fun z => ‖aeval z p‖
  have hcont : Continuous f := p.differentiable_aeval.continuous.norm
  have hcontOn : ContinuousOn f S := hcont.continuousOn
  -- The function f avoids 1 on S.
  have hfb : ∀ x ∈ S, f x ≠ (1 : ℝ) := by
    intro x hx hfx
    have hempty : S ∩ lemniscate p = ∅ := disjoint_iff_inter_eq_empty.mp hSL
    have : x ∈ S ∩ lemniscate p := ⟨hx, by
      simp only [lemniscate, mem_setOf_eq]; exact hfx⟩
    exact (mem_empty_iff_false x).mp (hempty ▸ this)
  -- Split into Ioi or Iio
  rcases hS.mapsTo_Ioi_or_Iio hcontOn hfb with h | h
  · left
    intro z hz
    simp only [superlevel, mem_setOf_eq]
    exact h hz
  · right
    intro z hz
    simp only [sublevel, mem_setOf_eq]
    exact h hz

/-! ## Step 2: Bounded superlevel components are impossible (maximum modulus)

If `U` is a bounded open set with `|p| > 1` on `U` and `|p| = 1` on `∂U`,
then the maximum modulus principle gives `|p| ≤ 1` on `U`, contradicting `|p| > 1`.
-/

/-- A bounded open set contained in the superlevel, whose frontier lies in the
lemniscate, cannot exist — this is a direct application of the maximum modulus
principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`). -/
lemma not_bounded_isOpen_superlevel_frontier_lemniscate
    {U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p)
    (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) :
    False := by
  -- Maximum modulus: ‖aeval z p‖ ≤ 1 on closure U
  -- because ‖aeval z p‖ = 1 on frontier U.
  have hd : DiffContOnCl ℂ (fun z : ℂ => aeval z p) U := diffContOnCl_aeval p U
  have hfront : ∀ z ∈ frontier U, ‖aeval z p‖ ≤ (1 : ℝ) := by
    intro z hz
    have hlez : z ∈ lemniscate p := hF hz
    simp only [lemniscate, mem_setOf_eq] at hlez
    exact le_of_eq hlez
  obtain ⟨z₀, hz₀⟩ := hnonempty
  have hz₀cl : z₀ ∈ closure U := subset_closure hz₀
  have hle : ‖aeval z₀ p‖ ≤ (1 : ℝ) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hB hd hfront hz₀cl
  have hgt : 1 < ‖aeval z₀ p‖ := by
    have := hS hz₀
    simp only [superlevel, mem_setOf_eq] at this
    exact this
  linarith

/-! ## Step 3: Sublevel components contain roots (minimum modulus via 1/p)

If `U` is a bounded open set with `|p| < 1` on `U` and `|p| = 1` on `∂U`,
then `p` must have a zero in `U`. Otherwise `1/p` is holomorphic on `U` with
`|1/p| = 1` on `∂U`, and the maximum modulus principle gives `|1/p| ≤ 1`
on `U`, contradicting `|1/p| > 1` there.
-/

/-- A bounded open set contained in the sublevel, whose frontier lies in the
lemniscate, must contain a root of `p`. -/
lemma exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate
    {U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p)
    (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) :
    ∃ z ∈ U, aeval z p = 0 := by
  -- By contrapositive: assume p ≠ 0 on U, derive contradiction via 1/p and MMP.
  by_contra hcon
  push_neg at hcon
  -- p has no root in U.
  have hnozero : ∀ z ∈ U, aeval z p ≠ (0 : ℂ) := by
    intro z hz hzero
    exact hcon z hz hzero
  -- On the frontier, ‖p‖ = 1, so p ≠ 0 there as well.
  have hfront_ne : ∀ z ∈ frontier U, aeval z p ≠ (0 : ℂ) := by
    intro z hz hzero
    have hlez : z ∈ lemniscate p := hF hz
    simp only [lemniscate, mem_setOf_eq] at hlez
    rw [hzero, norm_zero] at hlez
    norm_num at hlez
  -- p ≠ 0 on closure U = U ∪ frontier U.
  have hnozero_cl : ∀ z ∈ closure U, aeval z p ≠ (0 : ℂ) := by
    intro z hz
    rw [closure_eq_self_union_frontier, mem_union] at hz
    rcases hz with hz | hz
    · exact hnozero z hz
    · exact hfront_ne z hz
  -- 1/(aeval z p) is differentiable on closure U (since p is entire and
  -- nonzero on closure U).
  have hpd : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
  have hinv_diff_cl : DifferentiableOn ℂ
      (fun z : ℂ => (aeval z p)⁻¹) (closure U) :=
    hpd.differentiableOn.inv hnozero_cl
  have hinv_dcc : DiffContOnCl ℂ (fun z : ℂ => (aeval z p)⁻¹) U :=
    hinv_diff_cl.diffContOnCl
  -- On the frontier: ‖1/p‖ = 1 (since ‖p‖ = 1 there).
  have hfront_inv : ∀ z ∈ frontier U, ‖(aeval z p)⁻¹‖ ≤ (1 : ℝ) := by
    intro z hz
    have hlez : z ∈ lemniscate p := hF hz
    simp only [lemniscate, mem_setOf_eq] at hlez
    rw [norm_inv, hlez]
    norm_num
  -- Maximum modulus on 1/p: ‖1/p(z)‖ ≤ 1 on closure U.
  obtain ⟨z₀, hz₀⟩ := hnonempty
  have hz₀cl : z₀ ∈ closure U := subset_closure hz₀
  have hle_inv : ‖(aeval z₀ p)⁻¹‖ ≤ (1 : ℝ) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hB hinv_dcc hfront_inv hz₀cl
  -- But ‖1/p(z₀)‖ > 1 since ‖p(z₀)‖ < 1 and p(z₀) ≠ 0.
  have hsub : ‖aeval z₀ p‖ < 1 := by
    have := hS hz₀
    simp only [sublevel, mem_setOf_eq] at this
    exact this
  have hne : aeval z₀ p ≠ (0 : ℂ) := hnozero z₀ hz₀
  have hpos : 0 < ‖aeval z₀ p‖ := norm_pos_iff.mpr (mod_cast hne)
  have hgt_inv : 1 < ‖(aeval z₀ p)⁻¹‖ := by
    rw [norm_inv, (one_lt_inv₀ hpos)]
    exact_mod_cast hsub
  linarith

/-! ## Step 4: Root count ≤ degree

This is a standard Mathlib result.
-/

/-- The number of distinct roots of `p` is at most its degree. -/
lemma card_roots_le_degree (hp : 0 < p.natDegree) :
    (Polynomial.roots p).toFinset.card ≤ p.natDegree := by
  exact le_trans (Multiset.toFinset_card_le (α := ℂ) _)
    (Polynomial.card_roots' p)

private lemma isBounded_sublevel (hp : 0 < p.natDegree) :
    IsBounded (sublevel p) := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hp
  have hcompact :
      IsCompact ((fun z : ℂ => p.eval z) ⁻¹' closedBall 0 1) :=
    (p.isProperMap_eval hdeg).isCompact_preimage (isCompact_closedBall 0 1)
  apply hcompact.isBounded.subset
  intro z hz
  simp only [sublevel, mem_setOf_eq] at hz
  simp only [mem_preimage, mem_closedBall, dist_zero_right]
  simpa only [← coe_aeval_eq_eval] using hz.le

private lemma componentSet_subset_superlevel_or_sublevel
    (x : ↥((lemniscate p)ᶜ)) :
    componentSet x ⊆ superlevel p ∨ componentSet x ⊆ sublevel p := by
  apply isPreconnected_subset_superlevel_or_sublevel (p := p)
    (componentSet_connected (p := p) x).isPreconnected
  exact Set.disjoint_left.2 fun z hzcomp hzlem =>
    (componentSet_subset_compl (p := p) x hzcomp) hzlem

private lemma exists_root_in_componentSet_of_subset_sublevel
    (hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ))
    (hsub : componentSet x ⊆ sublevel p) :
    ∃ z ∈ componentSet x, aeval z p = 0 :=
  exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate (p := p)
    (componentSet_open (p := p) x)
    ((isBounded_sublevel (p := p) hp).subset hsub) hsub
    (componentSet_frontier_subset_lemniscate (p := p) x)
    (componentSet_nonempty (p := p) x)

private lemma not_isBounded_componentSet_of_subset_superlevel
    (x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) :
    ¬ IsBounded (componentSet x) := by
  intro hbounded
  exact not_bounded_isOpen_superlevel_frontier_lemniscate (p := p)
    (componentSet_open (p := p) x) hbounded hsuper
    (componentSet_frontier_subset_lemniscate (p := p) x)
    (componentSet_nonempty (p := p) x)

private lemma component_eq_of_subset_superlevel
    (hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)}
    (hxsuper : componentSet x ⊆ superlevel p)
    (hysuper : componentSet y ⊆ superlevel p) :
    (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hp
  have htend :
      Filter.Tendsto (fun z : ℂ => ‖aeval z p‖) (cobounded ℂ) Filter.atTop := by
    simpa only [← coe_aeval_eq_eval] using
      p.tendsto_norm_atTop hdeg tendsto_norm_cobounded_atTop
  have hcob : IsCobounded (superlevel p) :=
    htend (Filter.eventually_gt_atTop (1 : ℝ))
  obtain ⟨r, hr⟩ := hcob.closedBall_compl_subset (0 : ℂ)
  let R := max r 0
  have hR : 0 ≤ R := le_max_right _ _
  have hextsuper : {z : ℂ | R < ‖z‖} ⊆ superlevel p := by
    intro z hz
    apply hr
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
    exact (le_max_left r 0).trans_lt hz
  have hextcompl : {z : ℂ | R < ‖z‖} ⊆ (lemniscate p)ᶜ := by
    intro z hz hzlem
    have hzsuper := hextsuper hz
    simp only [superlevel, mem_setOf_eq] at hzsuper
    simp only [lemniscate, mem_setOf_eq] at hzlem
    linarith
  have hmeet (u : ↥((lemniscate p)ᶜ))
      (husuper : componentSet u ⊆ superlevel p) :
      ∃ z ∈ componentSet u, R < ‖z‖ := by
    by_contra h
    push_neg at h
    have hubounded : IsBounded (componentSet u) := by
      apply Metric.isBounded_closedBall.subset
      intro z hz
      show z ∈ closedBall (0 : ℂ) R
      simp only [mem_closedBall, dist_zero_right]
      exact h z hz
    exact not_isBounded_componentSet_of_subset_superlevel (p := p) u husuper hubounded
  obtain ⟨zx, hzxcomp, hzxext⟩ := hmeet x hxsuper
  obtain ⟨zy, hzycomp, hzyext⟩ := hmeet y hysuper
  obtain ⟨ax, haxcomp, haxval⟩ := hzxcomp
  obtain ⟨ay, haycomp, hayval⟩ := hzycomp
  have hpath :
      IsPathConnected (Subtype.val ⁻¹' {z : ℂ | R < ‖z‖} :
        Set ↥((lemniscate p)ᶜ)) :=
    (exterior_pathConnected R hR).preimage_coe hextcompl
  have haxext : ax ∈ Subtype.val ⁻¹' {z : ℂ | R < ‖z‖} := by
    simpa [haxval] using hzxext
  have hayext : ay ∈ Subtype.val ⁻¹' {z : ℂ | R < ‖z‖} := by
    simpa [hayval] using hzyext
  have hay_in_ax : ay ∈ connectedComponent ax :=
    pathComponent_subset_component ax (hpath.joinedIn ax haxext ay hayext).joined
  rw [ConnectedComponents.coe_eq_coe]
  exact (connectedComponent_eq_iff_mem.mpr haxcomp).symm.trans <|
    (connectedComponent_eq_iff_mem.mpr hay_in_ax).symm.trans <|
      connectedComponent_eq_iff_mem.mpr haycomp

/-! ## Step 5: The final assembly

This step assembles the preceding ingredients into a bound on
`ConnectedComponents ↥((lemniscate p)ᶜ)`:

(a) **Classification of connected components.** Each connected component of
    `(lemniscate p)ᶜ` is an open connected set whose frontier lies in the
    lemniscate, so by Step 1 it is purely sublevel or superlevel.

(b) **The superlevel has one component.** Using `|p(z)| → ∞` (from
    `Polynomial.tendsto_norm_atTop`) one shows that a strict exterior region
    lies in the superlevel. Radial rescaling realizes this exterior as a
    continuous image of the punctured plane, hence it is path connected.
    Every unbounded superlevel component meets it.

(c) **Injection from sublevel components to roots.** By Step 3, each bounded
    sublevel component contains a root; distinct components are disjoint, so
    they contain distinct roots; hence at most `N` sublevel components.
-/

/-- **Main theorem.** The complement of the lemniscate `{z | |p(z)| = 1}` has
at most `natDegree p + 1` connected components.

This is the target theorem. The proof combines:
- at most one superlevel component (Step 2 kills bounded ones; polynomial
  growth forces a unique unbounded one),
- at most `natDegree p` sublevel components (Step 3 + root count).
-/
theorem connectedComponents_complement_lemniscate_le :
    Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1 := by
  classical
  by_cases hp : 0 < p.natDegree
  swap
  · have hdeg : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
    let c := p.coeff 0
    have peq : p = C c := eq_C_of_natDegree_eq_zero hdeg
    rw [peq]
    by_cases hc : ‖c‖ = 1
    · have hlem : lemniscate (C c) = Set.univ := by
        ext z
        simp [lemniscate, hc]
      rw [hlem]
      letI : IsEmpty ↥((Set.univ : Set ℂ)ᶜ) :=
        ⟨fun x => by simpa using x.2⟩
      letI : IsEmpty (ConnectedComponents ↥((Set.univ : Set ℂ)ᶜ)) :=
        ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
      simp [Nat.card_of_isEmpty]
    · have hlem : lemniscate (C c) = ∅ := by
        ext z
        simp [lemniscate, hc]
      rw [hlem]
      letI : PreconnectedSpace ↥((∅ : Set ℂ)ᶜ) :=
        isPreconnected_iff_preconnectedSpace.mp (by simpa using isPreconnected_univ)
      simpa using (Finite.card_le_one_iff_subsingleton
        (α := ConnectedComponents ↥((∅ : Set ℂ)ᶜ))).mpr inferInstance
  have hp0 : p ≠ 0 := by
    intro hpzero
    subst p
    simp at hp
  let rootOf (x : ↥((lemniscate p)ᶜ))
      (hxsub : componentSet x ⊆ sublevel p) :
      {z // z ∈ (Polynomial.roots p).toFinset} :=
    ⟨Classical.choose
        (exists_root_in_componentSet_of_subset_sublevel (p := p) hp x hxsub),
      by
        have hz := Classical.choose_spec
          (exists_root_in_componentSet_of_subset_sublevel (p := p) hp x hxsub)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots_iff_aeval_eq_zero hp0]
        exact hz.2⟩
  let tag :
      ConnectedComponents ↥((lemniscate p)ᶜ) →
        {z // z ∈ (Polynomial.roots p).toFinset} ⊕ Unit :=
    fun c =>
      let x := Quotient.out c
      if hxsub : componentSet x ⊆ sublevel p then
        Sum.inl (rootOf x hxsub)
      else
        Sum.inr ()
  have htag : Function.Injective tag := by
    intro c d hcd
    let x : ↥((lemniscate p)ᶜ) := Quotient.out c
    let y : ↥((lemniscate p)ᶜ) := Quotient.out d
    have hxc : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = c :=
      Quotient.out_eq c
    have hyd : (y : ConnectedComponents ↥((lemniscate p)ᶜ)) = d :=
      Quotient.out_eq d
    by_cases hxsub : componentSet x ⊆ sublevel p
    · by_cases hysub : componentSet y ⊆ sublevel p
      · have hroots : rootOf x hxsub = rootOf y hysub := by
          simpa [tag, x, y, hxsub, hysub] using hcd
        have hxspec := Classical.choose_spec
          (exists_root_in_componentSet_of_subset_sublevel (p := p) hp x hxsub)
        have hyspec := Classical.choose_spec
          (exists_root_in_componentSet_of_subset_sublevel (p := p) hp y hysub)
        have hcomp :
            (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y := by
          apply componentSet_eq_of_common_point (p := p)
            (z := Classical.choose
              (exists_root_in_componentSet_of_subset_sublevel (p := p) hp x hxsub))
          · exact hxspec.1
          · rw [show Classical.choose
                (exists_root_in_componentSet_of_subset_sublevel (p := p) hp x hxsub) =
              Classical.choose
                (exists_root_in_componentSet_of_subset_sublevel (p := p) hp y hysub) by
                exact congrArg Subtype.val hroots]
            exact hyspec.1
        exact hxc ▸ hyd ▸ hcomp
      · simp [tag, x, y, hxsub, hysub] at hcd
    · by_cases hysub : componentSet y ⊆ sublevel p
      · simp [tag, x, y, hxsub, hysub] at hcd
      · have hxsuper : componentSet x ⊆ superlevel p :=
          (componentSet_subset_superlevel_or_sublevel (p := p) x).resolve_right hxsub
        have hysuper : componentSet y ⊆ superlevel p :=
          (componentSet_subset_superlevel_or_sublevel (p := p) y).resolve_right hysub
        have hcomp :
            (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y :=
          component_eq_of_subset_superlevel (p := p) hp hxsuper hysuper
        exact hxc ▸ hyd ▸ hcomp
  calc
    Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ))
        ≤ Nat.card ({z // z ∈ (Polynomial.roots p).toFinset} ⊕ Unit) :=
          Nat.card_le_card_of_injective tag htag
    _ = (Polynomial.roots p).toFinset.card + 1 := by
      rw [Nat.card_sum]
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_unique]
    _ ≤ p.natDegree + 1 :=
      Nat.add_le_add_right (card_roots_le_degree (p := p) hp) 1

end ApmCanaries.A00J04

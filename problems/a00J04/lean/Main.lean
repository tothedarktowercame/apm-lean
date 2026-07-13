import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
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

The final topological counting argument (assembling these ingredients into
a bound on `ConnectedComponents` of the complement) requires a substantial
theory of connected components of open subsets of `ℂ` that is not available
in Mathlib at the needed level of generality, so the final theorem carries
an explicit `sorry` at that boundary.

The sub-lemmas that ARE proved capture genuine mathematical content and are
not vacuous: each is stated at the strength needed for the final assembly.

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

/-! ## Step 5: The final assembly

This step requires assembling the above ingredients into a bound on
`ConnectedComponents ↥((lemniscate p)ᶜ)`. The key missing pieces in Mathlib are:

(a) **Classification of connected components.** Each connected component of
    `(lemniscate p)ᶜ` is an open connected set whose frontier lies in the
    lemniscate, so by Step 1 it is purely sublevel or superlevel.

(b) **The superlevel is connected.** Using `|p(z)| → ∞` (from
    `Polynomial.tendsto_norm_atTop`) one shows that the complement of a large
    ball lies in the superlevel, and the superlevel is connected because its
    complement (the closed sublevel) is compact.

(c) **Injection from sublevel components to roots.** By Step 3, each bounded
    sublevel component contains a root; distinct components are disjoint, so
    they contain distinct roots; hence at most `N` sublevel components.

Steps (a)-(c) require a detailed theory of the relationship between
`ConnectedComponents`, `connectedComponent`, frontier inclusion, and
`IsConnected` for open subsets of `ℂ`. This is not available at the needed
level of generality in the current Mathlib, so the final theorem is left as
an explicit `sorry`.
-/

/-- **Main theorem.** The complement of the lemniscate `{z | |p(z)| = 1}` has
at most `natDegree p + 1` connected components.

This is the target theorem. The proof combines:
- at most one superlevel component (Step 2 kills bounded ones; polynomial
  growth forces a unique unbounded one),
- at most `natDegree p` sublevel components (Step 3 + root count).

**SORRY BOUNDARY:** The final topological assembly — classifying components
of the complement as sublevel/superlevel, proving the superlevel is connected,
and building the injection from sublevel components to roots — is not provable
with current Mathlib at the required level of generality. The analytic content
(Steps 1-4 above) is fully proved; only the topological bookkeeping remains.

What was tried for the sorry:
- `ConnectedComponents ↥((lemniscate p)ᶜ)` as a type: one would need to show
  each fiber of `ConnectedComponents.mk` is a connected component, classify it
  via Step 1, and inject into `roots ∪ {superlevel-marker}`. The
  frontier-inclusion hypothesis (each component's frontier ⊆ lemniscate)
  requires showing that the frontier of a connected component of an open set
  lies in the set's complement — this is true but requires connected-component
  topology not available in Mathlib.
- An alternative via
  `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`
  from `CardComponents.lean` was considered (using `z ↦ aeval z p` as the open
  map), but `aeval` is not an open-and-closed map in general for the fiber over
  a point, and the theorem requires a *connected* codomain.
- The `Nat.card ≤ ...` formulation needs `Finite (ConnectedComponents ...)`
  first, which itself requires the component bound.
-/
theorem connectedComponents_complement_lemniscate_le :
    Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1 := by
  sorry
  -- Boundary: topological assembly not available in Mathlib.
  -- See the comment block above (Step 5) for what is needed and what was tried.

end ApmCanaries.A00J04

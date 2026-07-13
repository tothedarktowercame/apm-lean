import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# APM a01A08: Components of the complement of a polynomial lemniscate

**Problem (from `a01A08.tex`).** Let `p(z)` be a polynomial of degree `N ≥ 1`
and define `L = {z ∈ ℂ | |p(z)| = 1}`. Prove that the open set `ℂ \\ L` has at
most `N + 1` connected components.

**Note:** The TeX solution says "This is exactly the same as a00J04" and indeed
the problem statements are identical. This file adapts the a00J04 formalization
(the informal proof file `apm-a01A08.md` was harvested with the wrong content —
it contains the proof for a01A07, not a01A08).

**Informal proof sketch:**

1. *Each component is purely sublevel or superlevel.* Connected component of
   `ℂ \\ L` → continuous `|p|` avoids `1` → image is a connected subset of
   `(0,∞) \ {1}` → entirely in `(0,1)` or `(1,∞)`.

2. *Exactly one superlevel component.* Bounded open set with `|p| > 1` and
   `|p| = 1` on boundary contradicts the maximum modulus principle. So all
   superlevel components are unbounded; since `|p(z)| → ∞`, there is exactly one.

3. *Each sublevel component contains a root.* Bounded open set with `|p| < 1`
   and `|p| = 1` on boundary: if `p` has no root there, then `1/p` is
   holomorphic with `|1/p| = 1` on boundary and `|1/p| > 1` inside —
   contradicting the maximum modulus principle.

4. *Count.* At most `N` roots → at most `N` sublevel components + 1 superlevel
   = at most `N + 1` total.

**Statement repair note.**

The informal proof file was harvested with the wrong content (a01A07's proof
about L¹ convergence of analytic functions, not this polynomial lemniscate
problem). The actual problem from `a01A08.tex` is identical to `a00J04.tex`.
This file adapts the a00J04 formalization.

As in a00J04, the target type is `ConnectedComponents ↥((lemniscate p)ᶜ)` —
the connected components of the subspace topology on the complement.
-/

open Complex Polynomial Set Topology Metric Bornology

set_option linter.unusedVariables false in
noncomputable section

namespace ApmCanaries.A01A08

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

-- The function `z ↦ aeval z p` is entire.
private lemma diffContOnCl_aeval (p : ℂ[X]) (U : Set ℂ) :
    DiffContOnCl ℂ (fun z : ℂ => aeval z p) U :=
  (p.differentiable_aeval).diffContOnCl

/-! ## Step 1: Connected sets avoiding the lemniscate are purely sublevel or superlevel -/

/-- A preconnected set disjoint from the lemniscate lies entirely in the
superlevel or entirely in the sublevel.

Uses `IsPreconnected.mapsTo_Ioi_or_Iio`: the continuous function `z ↦ ‖aeval z p‖`
maps a preconnected set to a connected subset of ℝ; if it avoids `1`, it lies
entirely above or entirely below. -/
lemma isPreconnected_subset_superlevel_or_sublevel
    {S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :
    S ⊆ superlevel p ∨ S ⊆ sublevel p := by
  let f : ℂ → ℝ := fun z => ‖aeval z p‖
  have hcont : Continuous f := p.differentiable_aeval.continuous.norm
  have hcontOn : ContinuousOn f S := hcont.continuousOn
  have hfb : ∀ x ∈ S, f x ≠ (1 : ℝ) := by
    intro x hx hfx
    have hempty : S ∩ lemniscate p = ∅ := disjoint_iff_inter_eq_empty.mp hSL
    have : x ∈ S ∩ lemniscate p := ⟨hx, by
      simp only [lemniscate, mem_setOf_eq]; exact hfx⟩
    exact (mem_empty_iff_false x).mp (hempty ▸ this)
  rcases hS.mapsTo_Ioi_or_Iio hcontOn hfb with h | h
  · left
    intro z hz
    simp only [superlevel, mem_setOf_eq]
    exact h hz
  · right
    intro z hz
    simp only [sublevel, mem_setOf_eq]
    exact h hz

/-! ## Step 2: Bounded superlevel components are impossible (maximum modulus) -/

/-- A bounded open set contained in the superlevel, whose frontier lies in the
lemniscate, cannot exist — direct application of the maximum modulus principle. -/
lemma not_bounded_isOpen_superlevel_frontier_lemniscate
    {U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p)
    (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) :
    False := by
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

/-! ## Step 3: Sublevel components contain roots (minimum modulus via 1/p) -/

/-- A bounded open set contained in the sublevel, whose frontier lies in the
lemniscate, must contain a root of `p`. -/
lemma exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate
    {U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p)
    (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) :
    ∃ z ∈ U, aeval z p = 0 := by
  by_contra hcon
  push_neg at hcon
  have hnozero : ∀ z ∈ U, aeval z p ≠ (0 : ℂ) := by
    intro z hz hzero
    exact hcon z hz hzero
  have hfront_ne : ∀ z ∈ frontier U, aeval z p ≠ (0 : ℂ) := by
    intro z hz hzero
    have hlez : z ∈ lemniscate p := hF hz
    simp only [lemniscate, mem_setOf_eq] at hlez
    rw [hzero, norm_zero] at hlez
    norm_num at hlez
  have hnozero_cl : ∀ z ∈ closure U, aeval z p ≠ (0 : ℂ) := by
    intro z hz
    rw [closure_eq_self_union_frontier, mem_union] at hz
    rcases hz with hz | hz
    · exact hnozero z hz
    · exact hfront_ne z hz
  have hpd : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
  have hinv_diff_cl : DifferentiableOn ℂ
      (fun z : ℂ => (aeval z p)⁻¹) (closure U) :=
    hpd.differentiableOn.inv hnozero_cl
  have hinv_dcc : DiffContOnCl ℂ (fun z : ℂ => (aeval z p)⁻¹) U :=
    hinv_diff_cl.diffContOnCl
  have hfront_inv : ∀ z ∈ frontier U, ‖(aeval z p)⁻¹‖ ≤ (1 : ℝ) := by
    intro z hz
    have hlez : z ∈ lemniscate p := hF hz
    simp only [lemniscate, mem_setOf_eq] at hlez
    rw [norm_inv, hlez]
    norm_num
  obtain ⟨z₀, hz₀⟩ := hnonempty
  have hz₀cl : z₀ ∈ closure U := subset_closure hz₀
  have hle_inv : ‖(aeval z₀ p)⁻¹‖ ≤ (1 : ℝ) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hB hinv_dcc hfront_inv hz₀cl
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

/-! ## Step 4: Root count ≤ degree -/

/-- The number of distinct roots of `p` is at most its degree. -/
lemma card_roots_le_degree (hp : 0 < p.natDegree) :
    (Polynomial.roots p).toFinset.card ≤ p.natDegree := by
  exact le_trans (Multiset.toFinset_card_le (α := ℂ) _)
    (Polynomial.card_roots' p)

/-! ## Step 5: The final assembly -/

/-- **Main theorem.** The complement of the lemniscate `{z | |p(z)| = 1}` has
at most `natDegree p + 1` connected components.

**SORRY BOUNDARY:** The final topological assembly — classifying components
of the complement as sublevel/superlevel, proving the superlevel is connected,
and building the injection from sublevel components to roots — is not provable
with current Mathlib at the required level of generality.

What was tried:
- `ConnectedComponents ↥((lemniscate p)ᶜ)` as a type: need to show each fiber
  of `ConnectedComponents.mk` is a connected component, classify it via Step 1,
  and inject into `roots ∪ {superlevel-marker}`. The frontier-inclusion
  hypothesis requires connected-component topology not in Mathlib.
- An alternative via `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`
  was considered but `aeval` is not open-and-closed for fibers.
- `Nat.card ≤ ...` formulation needs `Finite (ConnectedComponents ...)` first.

This is the same boundary as a00J04. The analytic content (Steps 1-4) is fully
proved; only the topological bookkeeping remains. -/
theorem connectedComponents_complement_lemniscate_le :
    Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1 := by
  sorry

end ApmCanaries.A01A08

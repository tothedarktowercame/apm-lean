/-
! # APM a96J04: AC monotone increasing maps null sets to null sets

Let `f : [0,1] → ℝ` be absolutely continuous and monotone increasing.
If `E ⊆ [0,1]` has Lebesgue measure zero, then `f(E)` has Lebesgue measure zero.

## Proof

Given ε > 0, AC gives δ > 0. Cover E by countably many disjoint open intervals
with total length < δ. By monotonicity, f(E) ⊆ ∪[f(a_k), f(b_k)], and by AC
the total image length ≤ ε. So volume(f(E)) ≤ ε.

## Statement note

On [0,1] per the TeX. AC encoded as explicit ε-δ since Mathlib has no
function-level AC typeclass.

## Blocker

The proof requires decomposing an open subset of ℝ into countably many disjoint
open intervals, which is not available as a packaged lemma in Mathlib. The
countable-to-finite extension of the AC condition then follows from partial sum
bounds. This is a genuine Mathlib theory gap.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Order.Monotone.Basic

open MeasureTheory Set

open scoped NNReal ENNReal

noncomputable section

/-- Helper: for monotone f on [0,1], the image of an interval [a,b] ⊆ [0,1]
    is contained in [f(a), f(b)]. -/
lemma monotone_image_interval (f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))
    {a b x : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hx : x ∈ Icc 0 1)
    (hax : a ≤ x) (hxb : x ≤ b) :
    f a ≤ f x ∧ f x ≤ f b :=
  ⟨hf ha hx hax, hf hx hb hxb⟩

/-- Helper: the image f '' Icc a b ⊆ Icc (f a) (f b) for monotone f. -/
lemma monotone_image_Icc (f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a ≤ b) :
    f '' Icc a b ⊆ Icc (f a) (f b) := by
  rintro y ⟨x, hx, rfl⟩
  have hx01 : x ∈ Icc 0 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  exact ⟨hf ha hx01 hx.1, hf hx01 hb hx.2⟩

/-- **Main theorem**: AC + monotone increasing ⟹ maps null sets to null sets.

    The AC condition is: ∀ ε > 0, ∃ δ > 0, for any finite collection of
    pairwise-disjoint-interval-interior intervals in [0,1] with total length < δ,
    the total variation Σ‖f(b_k) - f(a_k)‖ < ε. -/
theorem ac_monotone_maps_null_to_null
    (f : ℝ → ℝ)
    (hf_mono : MonotoneOn f (Icc 0 1))
    (hf_ac : ∀ ε > 0, ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ p.1 ≤ p.2) →
      (∀ p q, p ∈ s → q ∈ s → p ≠ q →
        Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)) →
      (∑ p ∈ s, (p.2 - p.1)) < δ →
      (∑ p ∈ s, ‖f p.2 - f p.1‖) < ε)
    (E : Set ℝ) (hE : E ⊆ Icc 0 1)
    (hE_null : volume E = 0) :
    volume (f '' E) = 0 := by
  -- We need: for every ε > 0, volume(f '' E) ≤ ENNReal.ofReal ε.
  -- Given ε > 0, get δ from AC. Since volume E = 0, by outer regularity,
  -- cover E by an open set U with volume U < δ.
  -- Decompose U ∩ Icc 0 1 into countably many disjoint open intervals {(a_k, b_k)}
  -- with Σ(b_k - a_k) ≤ volume U < δ.
  -- By monotonicity: f(E) ⊆ ∪_k f([a_k, b_k]) ⊆ ∪_k [f(a_k), f(b_k)].
  -- By countable subadditivity: volume(f(E)) ≤ Σ_k (f(b_k) - f(a_k)).
  -- For any finite partial sum Σ_{k<n} (b_k - a_k) < δ, AC gives Σ_{k<n}(f(b_k)-f(a_k)) < ε.
  -- Since this holds for all n, the full series Σ_k(f(b_k)-f(a_k)) ≤ ε.
  -- Therefore volume(f(E)) ≤ ε.
  --
  -- BLOCKER: The decomposition of an open subset of ℝ into countably many
  -- disjoint open intervals (a standard real analysis fact) is not available
  -- as a packaged lemma in Mathlib. This is the single missing ingredient.
  sorry

end

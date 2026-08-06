import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a03J01

## Statement repairs

None.

## Encoding notes

The paper's one-based sequence `(E_k)_{k ≥ 1}` is reindexed by `ℕ`. The set of
indices containing a point is counted by `Set.encard`, so infinite multiplicity is
represented honestly by `⊤`; `apmMultiplicitySet E j` is exactly the set `F_j`.
The ambient `ℝ^d` is encoded as `EuclideanSpace ℝ (Fin d)`.
-/

def apmMultiplicitySet {d : ℕ}
    (E : ℕ → Set (EuclideanSpace ℝ (Fin d))) (j : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | Set.encard {k : ℕ | x ∈ E k} = j}

-- Pointwise decomposition lemma: for n : ℕ,
--   (n : ℝ≥0∞) = ∑' j, (j+1) * (if n = j+1 then 1 else 0)
-- This is the discrete layer-cake: only the j = n-1 term is nonzero.
-- -- (Memory: math-informal/monotone-approximation — level-set decomposition)
private lemma nat_tsum_decomp (n : ℕ) :
    ((n : ℕ) : ENNReal) =
      ∑' j : ℕ, ((j + 1 : ℕ) : ENNReal) *
        (if (n = (j + 1 : ℕ)) then (1 : ENNReal) else 0) := by
  by_cases hn : n = 0
  · subst hn
    have hne : ∀ j : ℕ, (0 : ℕ) ≠ j + 1 := fun j h => by simp_all
    simp only [hne, if_false, mul_zero, tsum_zero, Nat.cast_zero]
  · have hn1 : 0 < n := Nat.pos_of_ne_zero hn
    have hj0 : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    rw [tsum_eq_single (n - 1)]
    · rw [if_pos hj0.symm, mul_one, hj0]
    · intro j' hj'
      rw [if_neg, mul_zero]
      intro heq
      apply hj'
      have h2 : n - 1 + 1 = j' + 1 := hj0 ▸ heq
      omega

-- The counting function N(x) = #{k : x ∈ E_k}, valued in ℝ≥0∞.
private def apmN {d : ℕ} (E : ℕ → Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) → ENNReal :=
  fun x => ∑' k, (E k).indicator (fun _ => (1 : ENNReal)) x

-- The encard-valued counting function.
private def apmEc {d : ℕ} (E : ℕ → Set (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℕ∞ :=
  Set.encard {k : ℕ | x ∈ E k}

-- Bridge: N(x) = (encard {k | x ∈ E_k} : ℝ≥0∞).
-- Uses tsum_subtype and ENNReal.tsum_set_one.
-- -- (Memory: math-informal/count-over-a-decomposition)
private lemma apmN_eq_apmEc {d : ℕ} (E : ℕ → Set (EuclideanSpace ℝ (Fin d))) :
    ∀ x, apmN E x = (apmEc E x : ENNReal) := by
  intro x
  classical
  simp only [apmN, apmEc]
  set s := {k : ℕ | x ∈ E k} with hs
  rw [show ∑' (k : ℕ), (E k).indicator (fun _ => (1 : ENNReal)) x =
       ∑' (k : ℕ), s.indicator (fun _ => (1 : ENNReal)) k from
    tsum_congr fun k => by
      rw [Set.indicator_apply, Set.indicator_apply]; simp [hs]]
  rw [← tsum_subtype s (fun _ => (1 : ENNReal))]
  exact ENNReal.tsum_set_one s

theorem apm_a03j01
    {d : ℕ}
    (E : ℕ → Set (EuclideanSpace ℝ (Fin d)))
    (A : ENNReal)
    (hE : ∀ k, MeasurableSet (E k))
    (hA : A = ∑' k, volume (E k))
    (hA_finite : A < ⊤) :
    A = ∑' j : ℕ,
      (((j + 1 : ℕ) : ENNReal) * volume (apmMultiplicitySet E (j + 1))) := by
  -- Step 0: apmN E is measurable (tsum of measurable indicators)
  have hN_meas : Measurable (apmN E) :=
    Measurable.ennreal_tsum (fun k => measurable_const.indicator (hE k))
  -- Step 1: ∑' k, volume (E k) = ∫⁻ x, apmN E x  (Tonelli / monotone convergence)
  -- -- (Memory: math-informal/monotone-approximation)
  have hstep1 : ∑' k, volume (E k) = ∫⁻ x, apmN E x := by
    show ∑' k, volume (E k) =
      ∫⁻ x, (∑' k, (E k).indicator (fun _ => (1 : ENNReal)) x)
    rw [lintegral_tsum (fun k => (measurable_const.indicator (hE k)).aemeasurable)]
    congr 1; ext k
    rw [lintegral_indicator_const (hE k), one_mul]
  -- The integral is finite (from hA_finite)
  have hint_finite : (∫⁻ x, apmN E x) < ⊤ := by
    rw [← hstep1, ← hA]; exact hA_finite
  -- a.e. finiteness: apmEc E x ≠ ⊤ a.e. (since the integral is finite)
  -- -- (Memory: math-informal/monotone-approximation — Markov/Borel-Cantelli)
  have hae_finite :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), apmEc E x ≠ ⊤ := by
    have hae := ae_lt_top hN_meas (ne_of_lt hint_finite)
    filter_upwards [hae] with x hx
    have hx' : (apmEc E x : ENNReal) < ⊤ := apmN_eq_apmEc E x ▸ hx
    exact ne_of_lt (ENat.toENNReal_lt_top.mp hx')
  -- Level sets are measurable: apmMultiplicitySet E j = preimage of {j} under N E
  have hLS_meas : ∀ j, MeasurableSet (apmMultiplicitySet E j) := by
    intro j
    have hpreim : apmMultiplicitySet E j = (apmN E) ⁻¹' {((j : ℕ) : ENNReal)} := by
      ext x
      simp only [apmMultiplicitySet, Set.mem_preimage, Set.mem_singleton_iff]
      show Set.encard {k : ℕ | x ∈ E k} = ↑j ↔ apmN E x = ↑j
      rw [apmN_eq_apmEc]
      exact ENat.toENNReal_inj.symm
    rw [hpreim]
    exact hN_meas (MeasurableSet.singleton _)
  -- Step 4: On the a.e. set, apmN E x = ∑' j, (j+1) * indicator(LS j+1) x
  -- -- (Memory: math-informal/count-over-a-decomposition — level-set decomposition)
  have hdecomp : ∀ x, apmEc E x ≠ ⊤ → apmN E x =
      ∑' j : ℕ, ((j + 1 : ℕ) : ENNReal) *
        (apmMultiplicitySet E (j+1)).indicator (fun _ => (1 : ENNReal)) x := by
    intro x hfin
    rw [apmN_eq_apmEc]
    classical
    set n := (apmEc E x).toNat with hn
    have hcoe : apmEc E x = ↑n := by rw [hn]; exact (ENat.coe_toNat hfin).symm
    have hcast : (apmEc E x : ENNReal) = n := by rw [hcoe]; exact ENat.toENNReal_coe n
    rw [hcast, nat_tsum_decomp n]
    refine tsum_congr fun j => ?_
    rw [apmMultiplicitySet, Set.indicator_apply]
    by_cases heq : n = j + 1
    · have hmem : Set.encard {k : ℕ | x ∈ E k} = ↑(j + 1) := by
        show apmEc E x = ↑(j + 1); exact hcoe ▸ congrArg _ heq
      rw [if_pos heq, if_pos (by simp [Set.mem_setOf_eq]; exact hmem)]
    · have hnemem : ¬(Set.encard {k : ℕ | x ∈ E k} = ↑(j + 1)) := by
        show ¬(apmEc E x = ↑(j + 1))
        rw [hcoe]; intro h; exact heq (Nat.cast_inj.mp h)
      rw [if_neg heq, if_neg (by simp [Set.mem_setOf_eq]; exact hnemem)]
  -- Step 5: a.e. congruence of integrals
  have hint_decomp : (∫⁻ x, apmN E x) =
      ∫⁻ x, ∑' j : ℕ, ((j + 1 : ℕ) : ENNReal) *
        (apmMultiplicitySet E (j+1)).indicator (fun _ => (1 : ENNReal)) x := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae_finite] with x hx using hdecomp x hx
  -- Step 6: swap tsum and integral (Tonelli for nonneg functions)
  -- -- (Memory: math-informal/monotone-approximation — Tonelli swap)
  have hint_swap :
      (∫⁻ x, ∑' j : ℕ, ((j + 1 : ℕ) : ENNReal) *
        (apmMultiplicitySet E (j+1)).indicator (fun _ => (1 : ENNReal)) x) =
        ∑' j : ℕ, ((j + 1 : ℕ) : ENNReal) *
          volume (apmMultiplicitySet E (j+1)) := by
    rw [lintegral_tsum]
    · congr 1; ext j
      have hrew : ∀ x, ((j+1 : ℕ) : ENNReal) *
          (apmMultiplicitySet E (j+1)).indicator (fun _ => 1) x =
          (apmMultiplicitySet E (j+1)).indicator (fun _ => ((j+1 : ℕ) : ENNReal)) x := by
        intro x
        classical
        by_cases hx : x ∈ apmMultiplicitySet E (j+1)
        · rw [Set.indicator_apply, if_pos hx, Set.indicator_apply, if_pos hx, mul_one]
        · rw [Set.indicator_apply, if_neg hx, mul_zero, Set.indicator_apply, if_neg hx]
      rw [show (∫⁻ a, ((j+1 : ℕ) : ENNReal) *
          (apmMultiplicitySet E (j+1)).indicator (fun _ => 1) a) =
          (∫⁻ a, (apmMultiplicitySet E (j+1)).indicator (fun _ => ((j+1 : ℕ) : ENNReal)) a) from
          lintegral_congr hrew]
      rw [lintegral_indicator_const (hLS_meas (j+1))]
    · intro j
      exact (measurable_const.mul
        (measurable_const.indicator (hLS_meas (j+1)))).aemeasurable
  -- Chain everything together
  calc A = ∑' k, volume (E k) := hA
    _ = ∫⁻ x, apmN E x := hstep1
    _ = ∫⁻ x, ∑' j, ((j+1 : ℕ) : ENNReal) *
        (apmMultiplicitySet E (j+1)).indicator (fun _ => 1) x := hint_decomp
    _ = ∑' j, ((j+1 : ℕ) : ENNReal) *
        volume (apmMultiplicitySet E (j+1)) := hint_swap

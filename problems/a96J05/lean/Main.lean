import Mathlib

/-!
# APM a96J05 — the sum of two Lp spaces

## Statement repairs

None.

The underlying measure is Lebesgue measure restricted to `[0,1]`.  Membership
in `L^p + L^q` and the infimum norm are represented directly using Mathlib's
`Lp` and `AEEqFun` types.  Completeness is stated by the Cauchy criterion for
this norm, avoiding any surrogate normed-space structure.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a96J05_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def apm_a96J05_mem (p q : ℝ≥0∞)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) : Prop :=
  ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) +
        (h : AEEqFun ℝ ℝ apm_a96J05_measure) = f

def apm_a96J05_norm (p q : ℝ≥0∞)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) : ℝ :=
  sInf {r : ℝ | ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) +
          (h : AEEqFun ℝ ℝ apm_a96J05_measure) = f ∧
        ‖g‖ + ‖h‖ = r}

/-- On the finite measure space `[0,1]`, `L^q` embeds in `L^p` for `p ≤ q`.
Consequently the algebraic sum encoded by `apm_a96J05_mem` is exactly the
image of `L^p` in `AEEqFun`.  This is the key simplification beyond the
quotient-space approach: completeness can ultimately be inherited directly
from `Lp ℝ p`. -/
lemma apm_a96J05_mem_iff_exists_Lp
    {p q : ℝ≥0∞} (hpq : p ≤ q)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) :
    apm_a96J05_mem p q f ↔
      ∃ k : Lp ℝ p apm_a96J05_measure,
        (k : AEEqFun ℝ ℝ apm_a96J05_measure) = f := by
  letI : IsFiniteMeasure apm_a96J05_measure := by
    unfold apm_a96J05_measure
    infer_instance
  constructor
  · rintro ⟨g, h, rfl⟩
    have hh : (h : AEEqFun ℝ ℝ apm_a96J05_measure) ∈
        Lp ℝ p apm_a96J05_measure :=
      Lp.antitone hpq h.prop
    let h' : Lp ℝ p apm_a96J05_measure := ⟨h, hh⟩
    refine ⟨g + h', ?_⟩
    rfl
  · rintro ⟨k, rfl⟩
    refine ⟨k, 0, ?_⟩
    simp

lemma apm_a96J05_antitone_norm_le {p q : ℝ≥0∞} (hpq : p ≤ q)
    (h : Lp ℝ q apm_a96J05_measure) (h' : Lp ℝ p apm_a96J05_measure)
    (heq : (h' : AEEqFun ℝ ℝ apm_a96J05_measure) = h) :
    ‖h'‖ ≤ ‖h‖ := by
  letI : IsFiniteMeasure apm_a96J05_measure := by
    unfold apm_a96J05_measure
    infer_instance
  letI : IsProbabilityMeasure apm_a96J05_measure := ⟨by
    unfold apm_a96J05_measure
    rw [Measure.restrict_apply_univ]
    simp⟩
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono
  · exact ne_of_lt h.prop
  · rw [show eLpNorm h' p apm_a96J05_measure =
        eLpNorm h p apm_a96J05_measure by rw [heq]]
    exact eLpNorm_le_eLpNorm_of_exponent_le hpq (Lp.aestronglyMeasurable h)

lemma apm_a96J05_norm_eq_Lp_norm {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) (k : Lp ℝ p apm_a96J05_measure)
    (hk : (k : AEEqFun ℝ ℝ apm_a96J05_measure) = f) :
    apm_a96J05_norm p q f = ‖k‖ := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : Fact (1 ≤ q) := ⟨hp.trans hpq⟩
  letI : IsFiniteMeasure apm_a96J05_measure := by
    unfold apm_a96J05_measure
    infer_instance
  let S : Set ℝ := {r | ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) + h = f ∧ ‖g‖ + ‖h‖ = r}
  have hSnonempty : S.Nonempty := by
    refine ⟨‖k‖, k, 0, ?_, by simp⟩
    simpa [hk]
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨g, h, _, rfl⟩
    exact add_nonneg (norm_nonneg g) (norm_nonneg h)
  change sInf S = ‖k‖
  apply le_antisymm
  · apply csInf_le hSbdd
    exact ⟨k, 0, by simpa [hk], by simp⟩
  · apply le_csInf hSnonempty
    rintro r ⟨g, h, hsum, rfl⟩
    let h' : Lp ℝ p apm_a96J05_measure := ⟨h, Lp.antitone hpq h.prop⟩
    have hkh : k = g + h' := by
      apply Subtype.ext
      exact hk.trans (hsum.symm.trans rfl)
    rw [hkh]
    calc
      ‖g + h'‖ ≤ ‖g‖ + ‖h'‖ := norm_add_le _ _
      _ ≤ ‖g‖ + ‖h‖ := add_le_add (le_refl _)
        (apm_a96J05_antitone_norm_le hpq h h' rfl)

theorem apm_a96j05 (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p < q) :
    let X := apm_a96J05_mem p q
    let N := apm_a96J05_norm p q
    -- `X` is a real vector space.
    X 0 ∧
    (∀ f g, X f → X g → X (f + g)) ∧
    (∀ (c : ℝ) f, X f → X (c • f)) ∧
    -- The displayed infimum is a norm on `X`.
    (∀ f, X f → 0 ≤ N f) ∧
    (∀ f, X f → (N f = 0 ↔ f = 0)) ∧
    (∀ (c : ℝ) f, X f → N (c • f) = |c| * N f) ∧
    (∀ f g, X f → X g → N (f + g) ≤ N f + N g) ∧
    -- Every Cauchy sequence in this norm converges in `X`.
    (∀ u : ℕ → AEEqFun ℝ ℝ apm_a96J05_measure,
      (∀ n, X (u n)) →
      (∀ ε > 0, ∃ k, ∀ m ≥ k, ∀ n ≥ k, N (u m - u n) < ε) →
      ∃ f, X f ∧ Tendsto (fun n => N (u n - f)) atTop (nhds 0)) := by
  dsimp only
  have hpqle : p ≤ q := hpq.le
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : Fact (1 ≤ q) := ⟨hp.trans hpqle⟩
  have hmem := apm_a96J05_mem_iff_exists_Lp (p := p) (q := q) hpqle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmem 0).2 ⟨0, by simp⟩
  · intro f g hf hg
    obtain ⟨kf, hkf⟩ := (hmem f).1 hf
    obtain ⟨kg, hkg⟩ := (hmem g).1 hg
    exact (hmem (f + g)).2 ⟨kf + kg, by simpa [hkf, hkg]⟩
  · intro c f hf
    obtain ⟨k, hk⟩ := (hmem f).1 hf
    apply (hmem (c • f)).2
    refine ⟨c • k, ?_⟩
    change c • (k : AEEqFun ℝ ℝ apm_a96J05_measure) = c • f
    rw [hk]
  · intro f hf
    obtain ⟨k, hk⟩ := (hmem f).1 hf
    rw [apm_a96J05_norm_eq_Lp_norm hp hpqle f k hk]
    exact norm_nonneg k
  · intro f hf
    obtain ⟨k, hk⟩ := (hmem f).1 hf
    rw [apm_a96J05_norm_eq_Lp_norm hp hpqle f k hk, norm_eq_zero]
    constructor
    · intro hk0
      rw [← hk]
      simp [hk0]
    · intro hf0
      apply Subtype.ext
      simpa [hf0] using hk
  · intro c f hf
    obtain ⟨k, hk⟩ := (hmem f).1 hf
    have hck : ((c • k : Lp ℝ p apm_a96J05_measure) :
        AEEqFun ℝ ℝ apm_a96J05_measure) = c • f := by
      change c • (k : AEEqFun ℝ ℝ apm_a96J05_measure) = c • f
      rw [hk]
    rw [apm_a96J05_norm_eq_Lp_norm hp hpqle f k hk,
      apm_a96J05_norm_eq_Lp_norm hp hpqle (c • f) (c • k) hck,
      norm_smul, Real.norm_eq_abs]
  · intro f g hf hg
    obtain ⟨kf, hkf⟩ := (hmem f).1 hf
    obtain ⟨kg, hkg⟩ := (hmem g).1 hg
    rw [apm_a96J05_norm_eq_Lp_norm hp hpqle f kf hkf,
      apm_a96J05_norm_eq_Lp_norm hp hpqle g kg hkg,
      apm_a96J05_norm_eq_Lp_norm hp hpqle (f + g) (kf + kg) (by simpa [hkf, hkg])]
    exact norm_add_le _ _
  · intro u hu hCauchy
    choose v hv using fun n ↦ (hmem (u n)).1 (hu n)
    have hvCauchy : CauchySeq v := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := hCauchy ε hε
      refine ⟨k, fun m hm n hn ↦ ?_⟩
      have hcoe : ((v m - v n : Lp ℝ p apm_a96J05_measure) :
          AEEqFun ℝ ℝ apm_a96J05_measure) = u m - u n := by
        simpa [hv m, hv n]
      simpa [dist_eq_norm,
        apm_a96J05_norm_eq_Lp_norm hp hpqle (u m - u n) (v m - v n) hcoe]
        using hk m hm n hn
    obtain ⟨k, hk⟩ := cauchySeq_tendsto_of_complete hvCauchy
    refine ⟨(k : AEEqFun ℝ ℝ apm_a96J05_measure),
      (hmem k).2 ⟨k, rfl⟩, ?_⟩
    have hnorm : Tendsto (fun n ↦ ‖v n - k‖) atTop (nhds 0) := by
      simpa [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.1 hk)
    convert hnorm using 1
    funext n
    apply apm_a96J05_norm_eq_Lp_norm hp hpqle
    simpa [hv n]

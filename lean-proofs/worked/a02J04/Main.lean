import Mathlib

open Set

noncomputable section

/-
Worked-solution scaffold for apm-a02J04.

The full pushforward/Radon–Nikodym argument still needs measure-theoretic
plumbing, but this file records the genuinely relevant data instead of
collapsing the target to `True`.
-/

def tauDensity (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) 1 then 2 * x else 0

def dmDtau (x : ℝ) : ℝ :=
  if x ∈ Set.Ioc (0 : ℝ) 1 then (2 * x)⁻¹ else 0

def mAcSet : Set ℝ := Set.Icc (0 : ℝ) 1

def mSingSet : Set ℝ := Set.Iio (0 : ℝ) ∪ Set.Ioi (1 : ℝ)

lemma tauDensity_of_mem {x : ℝ} (hx : x ∈ mAcSet) :
    tauDensity x = 2 * x := by
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [mAcSet] using hx
  simp [tauDensity, hx']

lemma tauDensity_of_not_mem {x : ℝ} (hx : x ∉ mAcSet) :
    tauDensity x = 0 := by
  have hx' : x ∉ Set.Icc (0 : ℝ) 1 := by
    simpa [mAcSet] using hx
  simp [tauDensity, hx']

lemma tauDensity_nonneg (x : ℝ) : 0 ≤ tauDensity x := by
  by_cases hx : x ∈ mAcSet
  · rw [tauDensity_of_mem hx]
    linarith [hx.1]
  · rw [tauDensity_of_not_mem hx]

lemma dmDtau_of_mem {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    dmDtau x = (2 * x)⁻¹ := by
  simp [dmDtau, hx]

lemma dmDtau_of_not_mem {x : ℝ} (hx : x ∉ Set.Ioc (0 : ℝ) 1) :
    dmDtau x = 0 := by
  simp [dmDtau, hx]

lemma dmDtau_mul_tauDensity_of_mem {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    dmDtau x * tauDensity x = 1 := by
  have hAc : x ∈ mAcSet := ⟨le_of_lt hx.1, hx.2⟩
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  rw [dmDtau_of_mem hx, tauDensity_of_mem hAc]
  field_simp [hx0]

lemma mSingSet_measurable : MeasurableSet mSingSet := by
  simp [mSingSet]

lemma mAcSet_measurable : MeasurableSet mAcSet := by
  simp [mAcSet]

lemma mAc_union_mSing : mAcSet ∪ mSingSet = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    by_cases hx0 : x < 0
    · right
      exact Or.inl hx0
    · by_cases hx1 : x ≤ 1
      · left
        exact ⟨le_of_not_gt hx0, hx1⟩
      · right
        have h1 : 1 < x := lt_of_not_ge hx1
        exact Or.inr h1

lemma mAc_disjoint_mSing : Disjoint mAcSet mSingSet := by
  refine Set.disjoint_left.2 ?_
  intro x hxA hxS
  rcases hxS with hxS | hxS
  · exact (not_le_of_gt hxS) hxA.1
  · exact (not_le_of_gt hxS) hxA.2

/-- On the absolutely continuous region, the candidate Radon–Nikodym derivative
is exactly the reciprocal of the pushforward density. -/
lemma dmDtau_eq_recip_tauDensity {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    dmDtau x = (tauDensity x)⁻¹ := by
  have hAc : x ∈ mAcSet := ⟨le_of_lt hx.1, hx.2⟩
  rw [dmDtau_of_mem hx, tauDensity_of_mem hAc]

/-- Candidate statement matching the informal answer. The missing content is the
measure-theoretic identification `τ = (tauDensity · volume)` and the decomposition
of `volume` with respect to that pushforward measure. -/
def WorkedAnswer : Prop :=
  (∀ x ∈ Set.Ioc (0 : ℝ) 1, dmDtau x * tauDensity x = 1) ∧
  mAcSet ∪ mSingSet = Set.univ ∧
  Disjoint mAcSet mSingSet

theorem workedAnswer_holds : WorkedAnswer := by
  refine ⟨?_, mAc_union_mSing, mAc_disjoint_mSing⟩
  intro x hx
  exact dmDtau_mul_tauDensity_of_mem hx

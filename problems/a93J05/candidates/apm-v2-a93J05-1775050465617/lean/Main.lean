import Mathlib
import ApmCanaries.Frames.A93J05.Apm_v2_a93J05_1775050465617.Scratch

noncomputable section

open scoped Real
open Set Bornology

namespace ApmCanaries.Frames.A93J05.Apm_v2_a93J05_1775050465617.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

namespace Local

/-- The standard unit square that serves as a fundamental domain for the lattice `ℤ + iℤ`. -/
def fundamentalDomain : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1} ∩ {z : ℂ | z.im ∈ Set.Icc (0 : ℝ) 1}

@[simp]
lemma mem_fundamentalDomain {z : ℂ} :
    z ∈ fundamentalDomain ↔
      z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1 := Iff.rfl

lemma fundamentalDomain_nonempty : (fundamentalDomain).Nonempty := by
  refine ⟨0, ?_⟩
  simp [fundamentalDomain]

lemma fundamentalDomain_isCompact : IsCompact fundamentalDomain := by
  classical
  let square := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hSquare : IsCompact square := (isCompact_Icc).prod isCompact_Icc
  let φ : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hφ : Continuous φ := by
    have h₁ : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) :=
      Complex.continuous_ofReal.comp continuous_fst
    have h₂ : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    simpa [φ] using h₁.add (h₂.mul continuous_const)
  have hImage : φ '' square = fundamentalDomain := by
    ext z; constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hx, hy⟩
      simp [φ, fundamentalDomain, hx.1, hx.2, hy.1, hy.2]
    · intro hz
      refine ⟨⟨z.re, z.im⟩, ⟨hz.1, hz.2⟩, ?_⟩
      simp [φ, Complex.re_add_im]
  simpa [hImage] using hSquare.image hφ

lemma exists_fundamentalDomain_translate (z : ℂ) :
    ∃ n m : ℤ,
      z - ((n : ℂ) + (m : ℂ) * Complex.I) ∈ fundamentalDomain := by
  classical
  refine ⟨Int.floor z.re, Int.floor z.im, ?_⟩
  set n : ℤ := Int.floor z.re
  set m : ℤ := Int.floor z.im
  have hRe :
      (z - ((n : ℂ) + (m : ℂ) * Complex.I)).re = z.re - n := by
    simp [n, m, sub_eq_add_neg]
  have hIm :
      (z - ((n : ℂ) + (m : ℂ) * Complex.I)).im = z.im - m := by
    simp [n, m, sub_eq_add_neg]
  have hRe_le : (n : ℝ) ≤ z.re := by simpa [n] using (Int.floor_le (z.re))
  have hIm_le : (m : ℝ) ≤ z.im := by simpa [m] using (Int.floor_le (z.im))
  have hRe_nonneg : 0 ≤ z.re - n := sub_nonneg.mpr hRe_le
  have hIm_nonneg : 0 ≤ z.im - m := sub_nonneg.mpr hIm_le
  have hRe_le_one : z.re - n ≤ 1 := by
    have : z.re - n < (1 : ℝ) :=
      sub_lt_iff_lt_add'.mpr (by simpa [n] using Int.lt_floor_add_one (z.re))
    exact this.le
  have hIm_le_one : z.im - m ≤ 1 := by
    have : z.im - m < (1 : ℝ) :=
      sub_lt_iff_lt_add'.mpr (by simpa [m] using Int.lt_floor_add_one (z.im))
    exact this.le
  refine And.intro ?_ ?_
  · have : z.re - n ∈ Set.Icc (0 : ℝ) 1 := ⟨hRe_nonneg, hRe_le_one⟩
    simpa [fundamentalDomain, hRe] using this
  · have : z.im - m ∈ Set.Icc (0 : ℝ) 1 := ⟨hIm_nonneg, hIm_le_one⟩
    simpa [fundamentalDomain, hIm] using this

lemma exists_value_in_fundamentalDomain
    {f : ℂ → ℂ}
    (hper : ∀ z (n m : ℤ), f (z + n + m * Complex.I) = f z)
    (z : ℂ) :
    ∃ w ∈ fundamentalDomain, f z = f w := by
  classical
  obtain ⟨n, m, hmem⟩ := exists_fundamentalDomain_translate z
  refine ⟨z - ((n : ℂ) + (m : ℂ) * Complex.I), hmem, ?_⟩
  have hrewrite :
      z - ((n : ℂ) + (m : ℂ) * Complex.I) + n + m * Complex.I = z := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have := hper (z - ((n : ℂ) + (m : ℂ) * Complex.I)) n m
  simpa [hrewrite] using this

lemma range_bounded_of_periodic
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z (n m : ℤ), f (z + n + m * Complex.I) = f z) :
    IsBounded (Set.range f) := by
  classical
  have hK := fundamentalDomain_isCompact
  obtain ⟨z₀, hz₀mem, hz₀max⟩ :=
    hK.exists_isMaxOn fundamentalDomain_nonempty
      hf.continuous.norm.continuousOn
  have hbound :
      ∀ z ∈ fundamentalDomain, ‖f z‖ ≤ ‖f z₀‖ := hz₀max
  have hfac :
      ∀ z : ℂ, ‖f z‖ ≤ ‖f z₀‖ := by
    intro z
    obtain ⟨w, hwmem, hwval⟩ := exists_value_in_fundamentalDomain hper z
    have := hbound w hwmem
    simpa [hwval] using this
  refine
    (Metric.isBounded_iff_subset_closedBall (s := Set.range f) (0 : ℂ)).2 ?_
  refine ⟨‖f z₀‖, ?_⟩
  intro y hy
  rcases hy with ⟨z, rfl⟩
  have := hfac z
  simpa [Metric.mem_closedBall] using this

theorem lattice_periodic_entire_const
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z (n m : ℤ), f (z + n + m * Complex.I) = f z) :
    ∀ z w, f z = f w := by
  classical
  have hfBounded : IsBounded (Set.range f) := range_bounded_of_periodic hf hper
  exact hf.apply_eq_apply_of_bounded hfBounded

end Local

open Local

-- Expose the lattice periodic Liouville consequence in the main namespace.
theorem lattice_periodic_entire_const
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z (n m : ℤ), f (z + n + m * Complex.I) = f z) :
    ∀ z w, f z = f w :=
  Local.lattice_periodic_entire_const f hf hper

end ApmCanaries.Frames.A93J05.Apm_v2_a93J05_1775050465617.Main

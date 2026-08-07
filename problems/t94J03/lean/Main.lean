import Mathlib

/-!
# APM t94J03

## Statement repairs

None.

## Encoding questions

None.  `ℝⁿ` is the genuine Euclidean space, `Sⁿ` is the unit sphere in
`ℝⁿ⁺¹`, and maps on a closed subspace or open neighborhood use the
corresponding subtype topology.
-/

open Set

abbrev apm_t94J03_Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t94J03_Sn (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

theorem apm_t94j03
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (A : Set X) (hA : IsClosed A) (n : ℕ) :
    (∀ f : C(A, apm_t94J03_Rn n),
      ∃ F : C(X, apm_t94J03_Rn n),
        ∀ a : A, F a = f a) ∧
    (∀ f : C(A, apm_t94J03_Sn n),
      ∃ (U : Set X) (hUopen : IsOpen U) (hAU : A ⊆ U)
        (F : C(U, apm_t94J03_Sn n)),
        ∀ a : A, F ⟨a, hAU a.2⟩ = f a) := by
  constructor
  · intro f
    obtain ⟨F, hF⟩ := f.exists_restrict_eq hA
    refine ⟨F, ?_⟩
    intro a
    exact DFunLike.congr_fun hF a
  · intro f
    let g : C(A, apm_t94J03_Rn (n + 1)) :=
      ⟨fun a => (f a).1, continuous_subtype_val.comp f.continuous⟩
    obtain ⟨G, hG⟩ := g.exists_restrict_eq hA
    let U : Set X := {x | G x ≠ 0}
    have hUopen : IsOpen U := isOpen_ne_fun G.continuous continuous_const
    have hAU : A ⊆ U := by
      intro a ha
      change G a ≠ 0
      have hGa : G a = (f ⟨a, ha⟩).1 := DFunLike.congr_fun hG ⟨a, ha⟩
      rw [hGa]
      exact fun hzero => by
        have := (f ⟨a, ha⟩).2
        simp [hzero] at this
    refine ⟨U, hUopen, hAU, ?_, ?_⟩
    · refine ⟨fun x => ⟨NormedSpace.normalize (G x), ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right]
        exact NormedSpace.norm_normalize x.2
      · apply Continuous.subtype_mk
        change Continuous fun x : U => ‖G x‖⁻¹ • G x
        exact ((G.continuous.comp continuous_subtype_val).norm.inv₀
          (fun x => norm_ne_zero_iff.mpr x.2)).smul
          (G.continuous.comp continuous_subtype_val)
    · intro a
      apply Subtype.ext
      change NormedSpace.normalize (G a) = (f a).1
      have hGa : G a = (f a).1 := DFunLike.congr_fun hG a
      rw [hGa]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (by simpa using a.property)

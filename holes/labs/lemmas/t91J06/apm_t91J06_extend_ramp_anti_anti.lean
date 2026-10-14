import Mathlib
import ConstructionTargets.NestedEmbeddingTransition
import ConstructionTargets.t91J06Closure

/-! # Blueprint for APM t91J06

The registered theorem is true.  The old unregistered glue helper is not used:
without an embedding hypothesis it is false.  The corrected gluing lemma below
retains `hf`.
-/

open Set

noncomputable section

abbrev apm_t91J06_I := Set.Icc (0 : ℝ) 1

/-- The points of the unit interval lying in its real-line interior. -/
def apm_t91J06_Iinterior : Set apm_t91J06_I :=
  {x | x.1 ∈ Ioo (0 : ℝ) 1}

def apm_t91J06_stage {X : Type*} (f : ℕ → apm_t91J06_I → X) (n : ℕ) : Set X :=
  f n '' univ

lemma apm_t91J06_stage_compact
    {X : Type*} [TopologicalSpace X] (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n)) (n : ℕ) :
    IsCompact (apm_t91J06_stage f n) := by
  exact isCompact_univ.image (hf n).continuous

lemma apm_t91J06_stage_mono
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior) :
    Monotone (apm_t91J06_stage f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  rcases hnested n hx with ⟨y, hy, rfl⟩
  exact ⟨y, mem_univ y, rfl⟩

lemma apm_t91J06_exists_mem_stage
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x : X) : ∃ n, x ∈ apm_t91J06_stage f n := by
  have hx : x ∈ (⋃ n, f n '' (univ : Set apm_t91J06_I)) := by
    rw [hcover]
    exact mem_univ x
  simpa only [mem_iUnion] using hx

lemma apm_t91J06_exists_mem_stage_interior
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x : X) : ∃ n, x ∈ f n '' apm_t91J06_Iinterior := by
  obtain ⟨n, hn⟩ := apm_t91J06_exists_mem_stage f hcover x
  exact ⟨n + 1, hnested n hn⟩

lemma apm_t91J06_exists_pair_mem_stage_interior
    {X : Type*} (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (x y : X) :
    ∃ n, x ∈ f n '' apm_t91J06_Iinterior ∧
      y ∈ f n '' apm_t91J06_Iinterior := by
  obtain ⟨nx, hx⟩ := apm_t91J06_exists_mem_stage f hcover x
  obtain ⟨ny, hy⟩ := apm_t91J06_exists_mem_stage f hcover y
  have hmono := apm_t91J06_stage_mono f hnested
  have hxmax : x ∈ apm_t91J06_stage f (max nx ny) :=
    hmono (Nat.le_max_left _ _) hx
  have hymax : y ∈ apm_t91J06_stage f (max nx ny) :=
    hmono (Nat.le_max_right _ _) hy
  exact ⟨max nx ny + 1, hnested (max nx ny) hxmax,
    hnested (max nx ny) hymax⟩

/-- The explicit three-piece affine construction when both coordinates have
positive orientation. -/
lemma apm_t91J06_extend_ramp_mono_mono
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (ht : Continuous t) (htint : Set.range t ⊆ apm_t91J06_Iinterior)
    (q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (htmono : StrictMono t)
    (hqmono : StrictMono (fun x ↦ (q x : ℝ))) :
    ∃ F : apm_t91J06_I → ℝ,
      Continuous F ∧ StrictMono F ∧
      (∀ x, F x ∈ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ)) ∧
      F ⟨0, by norm_num⟩ = -(n + 2 : ℝ) ∧
      F ⟨1, by norm_num⟩ = (n + 2 : ℝ) ∧
      ∀ x, F (t x) = (q x : ℝ) := by
  let z : apm_t91J06_I := ⟨0, by norm_num⟩
  let o : apm_t91J06_I := ⟨1, by norm_num⟩
  let u : ℝ := t z
  let v : ℝ := t o
  let A : ℝ := n + 2
  let tr : apm_t91J06_I → ℝ := fun x => t x
  let r : ℝ → ℝ := fun y => -A + ((q z : ℝ) + A) * y / u
  let s : ℝ → ℝ := fun y => (q o : ℝ) + (A - (q o : ℝ)) * (y - v) / (1 - v)
  let m : ℝ → ℝ := fun y => (q (Function.invFun tr y) : ℝ)
  have hu0 : 0 < u := (htint ⟨z, rfl⟩).1
  have hv1 : v < 1 := (htint ⟨o, rfl⟩).2
  have huv : u < v := htmono (by simp [z, o])
  have htrinj : Function.Injective tr := fun x y h => htmono.injective (Subtype.ext h)
  have htr_left (x : apm_t91J06_I) : Function.invFun tr (tr x) = x :=
    Function.leftInverse_invFun htrinj x
  have hrange : Set.range tr = Set.Icc u v := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨htmono.monotone (show z ≤ x by exact Subtype.coe_le_coe.1 x.2.1),
        htmono.monotone (show x ≤ o by exact x.2.2)⟩
    · intro y hy
      rcases intermediate_value_Icc (show z ≤ o by simp [z, o])
          (continuous_subtype_val.comp ht).continuousOn hy with ⟨x, hx, hxy⟩
      exact ⟨x, hxy⟩
  have hm_cont : ContinuousOn m (Set.Icc u v) := by
    let e : apm_t91J06_I ≃ₜ Set.range tr :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofInjective tr htrinj) ((continuous_subtype_val.comp ht).subtype_mk _)
    let ei : Set.Icc u v ≃ₜ apm_t91J06_I :=
      (Homeomorph.setCongr hrange.symm).trans e.symm
    rw [continuousOn_iff_continuous_restrict]
    apply Continuous.congr (continuous_subtype_val.comp (q.continuous.comp ei.continuous))
    intro y
    change (q (ei y) : ℝ) = (q (Function.invFun tr y) : ℝ)
    apply congrArg (fun x => (q x : ℝ))
    apply htrinj
    have hei : tr (ei y) = y := Subtype.ext_iff.mp (e.apply_symm_apply
      ((Homeomorph.setCongr hrange.symm) y))
    rw [hei]
    exact (Function.invFun_eq (by
      show (y : ℝ) ∈ Set.range tr
      rw [hrange]
      exact y.2)).symm
  have hm_strict : StrictMonoOn m (Set.Icc u v) := by
    intro x hx y hy hxy
    have ex : tr (Function.invFun tr x) = x := by
      apply Function.invFun_eq
      show x ∈ Set.range tr
      rw [hrange]
      exact hx
    have ey : tr (Function.invFun tr y) = y := by
      apply Function.invFun_eq
      show y ∈ Set.range tr
      rw [hrange]
      exact hy
    apply hqmono
    apply lt_of_not_ge
    intro h
    have hh := htmono.monotone h
    change tr (Function.invFun tr y) ≤ tr (Function.invFun tr x) at hh
    rw [ey, ex] at hh
    exact (not_le_of_gt hxy) hh
  have hr_cont : Continuous r := by fun_prop
  have hs_cont : Continuous s := by fun_prop
  have hr_u : r u = m u := by
    have hz : tr z = u := rfl
    rw [show m u = (q z : ℝ) by simp [m, ← hz, htr_left]]
    dsimp [r]
    field_simp
    ring
  have hs_v : s v = m v := by
    have ho : tr o = v := rfl
    rw [show m v = (q o : ℝ) by simp [m, ← ho, htr_left]]
    simp [s, hv1.ne]
  let G : ℝ → ℝ := fun y => if y ≤ u then r y else if v ≤ y then s y else m y
  have hG_cont : Continuous G := by
    dsimp [G]
    rw [← continuousOn_univ]
    apply ContinuousOn.piecewise (s := Set.univ) (t := Set.Iic u)
    · intro x hx
      have he : x = u := by simpa using hx.2
      subst x
      simp [not_le_of_gt huv, hr_u]
    · exact hr_cont.continuousOn.mono (by intro x hx; exact hx.1)
    · refine (ContinuousOn.piecewise (s := Set.Ici u) (t := Set.Ici v) ?_ ?_ ?_).mono ?_
      · intro x hx
        have he : x = v := by simpa using hx.2
        subst x
        exact hs_v
      · exact hs_cont.continuousOn.mono (by intro x hx; exact hx.1)
      · exact hm_cont.mono (by
          intro x hx
          exact ⟨hx.1, by simpa using hx.2⟩)
      · intro x hx
        simpa using hx
  have hqz : -(n + 1 : ℝ) ≤ (q z : ℝ) := (q z).2.1
  have hqo : (q o : ℝ) ≤ (n + 1 : ℝ) := (q o).2.2
  have hr_strict : StrictMono r := by
    dsimp [r, A]
    intro x y hxy
    have hp : 0 < (q z : ℝ) + (n + 2 : ℝ) := by linarith
    change -(n + 2 : ℝ) + _ < -(n + 2 : ℝ) + _
    gcongr
  have hs_strict : StrictMono s := by
    dsimp [s, A]
    intro x y hxy
    have hp : 0 < (n + 2 : ℝ) - (q o : ℝ) :=
      sub_pos.mpr (lt_of_le_of_lt hqo (by norm_num))
    have hd : 0 < 1 - v := sub_pos.mpr hv1
    change (q o : ℝ) + _ < (q o : ℝ) + _
    gcongr
  have hG_strict : StrictMono G := by
    intro x y hxy
    by_cases hyu : y ≤ u
    · simp [G, hyu, hxy.le.trans hyu, hr_strict hxy]
    by_cases hxu : x ≤ u
    · have hru : r x ≤ m u := by simpa [hr_u] using hr_strict.monotone hxu
      by_cases hyv : v ≤ y
      · have hsv : m v ≤ s y := by
          rw [← hs_v]
          exact hs_strict.monotone hyv
        have hms : m u < s y :=
          (hm_strict ⟨le_rfl, huv.le⟩ ⟨huv.le, le_rfl⟩ huv).trans_le hsv
        simpa [G, hxu, hyu, hyv] using hru.trans_lt hms
      · have hmm := hm_strict ⟨le_rfl, huv.le⟩ ⟨le_of_not_ge hyu, le_of_not_ge hyv⟩
          (lt_of_not_ge hyu)
        simpa [G, hxu, hyu, hyv] using hru.trans_lt hmm
    · have hux : u < x := lt_of_not_ge hxu
      by_cases hxv : v ≤ x
      · have hyv : v ≤ y := hxv.trans hxy.le
        simpa [G, hxu, hyu, hxv, hyv] using hs_strict hxy
      · by_cases hyv : v ≤ y
        · have hmy : m x < m v := hm_strict ⟨hux.le, le_of_not_ge hxv⟩ ⟨huv.le, le_rfl⟩
              (lt_of_not_ge hxv)
          have hsv : s v ≤ s y := hs_strict.monotone hyv
          have hsv' : m v ≤ s y := by rw [← hs_v]; exact hsv
          simpa [G, hxu, hyu, hxv, hyv] using hmy.trans_le hsv'
        · simpa [G, hxu, hyu, hxv, hyv] using
            hm_strict ⟨hux.le, le_of_not_ge hxv⟩
              ⟨le_of_not_ge hyu, le_of_not_ge hyv⟩ hxy
  refine ⟨fun x => G x, hG_cont.comp continuous_subtype_val, ?_, ?_, ?_, ?_, ?_⟩
  · exact hG_strict.comp (Subtype.strictMono_coe _)
  · intro x
    have hG0 : G 0 = -A := by simp [G, r, hu0.le]
    have hG1 : G 1 = A := by
      have hu1 : ¬(1 : ℝ) ≤ u := not_le_of_gt (huv.trans hv1)
      have hvle : v ≤ (1 : ℝ) := hv1.le
      simp only [G, hu1, ↓reduceIte, hvle, s]
      have hdne : 1 - v ≠ 0 := ne_of_gt (sub_pos.mpr hv1)
      rw [mul_div_cancel_right₀ _ hdne]
      ring
    constructor
    · have hh := hG_strict.monotone (show (0 : ℝ) ≤ x by exact x.2.1)
      rw [hG0] at hh
      exact hh
    · have hh := hG_strict.monotone (show (x : ℝ) ≤ 1 by exact x.2.2)
      rw [hG1] at hh
      exact hh
  · change G 0 = -(n + 2 : ℝ)
    simp [G, r, A, hu0.le]
  · have hu1 : ¬(1 : ℝ) ≤ u := not_le_of_gt (huv.trans hv1)
    change G 1 = (n + 2 : ℝ)
    simp only [G, hu1, ↓reduceIte, hv1.le, s, A]
    have hdne : 1 - v ≠ 0 := ne_of_gt (sub_pos.mpr hv1)
    rw [mul_div_cancel_right₀ _ hdne]
    ring
  · intro x
    have hut : u ≤ (t x : ℝ) := htmono.monotone (show z ≤ x by exact x.2.1)
    have htv : (t x : ℝ) ≤ v := htmono.monotone (show x ≤ o by exact x.2.2)
    by_cases htu : (t x : ℝ) ≤ u
    · have heq : (t x : ℝ) = u := le_antisymm htu hut
      have hxz : x = z := htrinj heq
      subst x
      change G u = (q z : ℝ)
      rw [show G u = r u by simp [G]]
      rw [hr_u]
      change (q (Function.invFun tr u) : ℝ) = (q z : ℝ)
      rw [← show tr z = u from rfl, htr_left]
    · by_cases hvt : v ≤ (t x : ℝ)
      · have heq : (t x : ℝ) = v := le_antisymm htv hvt
        have hxo : x = o := htrinj heq
        subst x
        change G v = (q o : ℝ)
        rw [show G v = s v by simp [G, not_le_of_gt huv]]
        rw [hs_v]
        change (q (Function.invFun tr v) : ℝ) = (q o : ℝ)
        rw [← show tr o = v from rfl, htr_left]
      · simp [G, htu, hvt, m, tr, htr_left]

/-- The explicit three-piece affine construction when both coordinates have
negative orientation. -/
-- BEGIN SEAT AREA
lemma apm_t91J06_extend_ramp_anti_anti
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (ht : Continuous t) (htint : Set.range t ⊆ apm_t91J06_Iinterior)
    (q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (htanti : StrictAnti t)
    (hqanti : StrictAnti (fun x ↦ (q x : ℝ))) :
    ∃ F : apm_t91J06_I → ℝ,
      Continuous F ∧ StrictMono F ∧
      (∀ x, F x ∈ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ)) ∧
      F ⟨0, by norm_num⟩ = -(n + 2 : ℝ) ∧
      F ⟨1, by norm_num⟩ = (n + 2 : ℝ) ∧
      ∀ x, F (t x) = (q x : ℝ) := by
  sorry
-- END SEAT AREA

/-- The explicit three-piece affine construction when `t` preserves and `q`
reverses orientation. -/
lemma apm_t91J06_extend_ramp_mono_anti
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (ht : Continuous t) (htint : Set.range t ⊆ apm_t91J06_Iinterior)
    (q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (htmono : StrictMono t)
    (hqanti : StrictAnti (fun x ↦ (q x : ℝ))) :
    ∃ F : apm_t91J06_I → ℝ,
      Continuous F ∧ StrictAnti F ∧
      (∀ x, F x ∈ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ)) ∧
      F ⟨0, by norm_num⟩ = (n + 2 : ℝ) ∧
      F ⟨1, by norm_num⟩ = -(n + 2 : ℝ) ∧
      ∀ x, F (t x) = (q x : ℝ) := by
  sorry

/-- The explicit three-piece affine construction when `t` reverses and `q`
preserves orientation. -/
lemma apm_t91J06_extend_ramp_anti_mono
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (ht : Continuous t) (htint : Set.range t ⊆ apm_t91J06_Iinterior)
    (q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (htanti : StrictAnti t)
    (hqmono : StrictMono (fun x ↦ (q x : ℝ))) :
    ∃ F : apm_t91J06_I → ℝ,
      Continuous F ∧ StrictAnti F ∧
      (∀ x, F x ∈ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ)) ∧
      F ⟨0, by norm_num⟩ = (n + 2 : ℝ) ∧
      F ⟨1, by norm_num⟩ = -(n + 2 : ℝ) ∧
      ∀ x, F (t x) = (q x : ℝ) := by
  sorry

/-- IVT surjectivity for a continuous increasing coordinate with prescribed
endpoint values. -/
lemma apm_t91J06_mono_endpoint_surjective
    {a b : ℝ} (F : apm_t91J06_I → ℝ) (hF : Continuous F)
    (h0 : F ⟨0, by norm_num⟩ = a) (h1 : F ⟨1, by norm_num⟩ = b) :
    ∀ y : Set.Icc a b, ∃ x, F x = y := by
  intro y
  let x0 : apm_t91J06_I := ⟨0, by norm_num⟩
  let x1 : apm_t91J06_I := ⟨1, by norm_num⟩
  have hx01 : x0 ≤ x1 := by
    change (0 : ℝ) ≤ 1
    norm_num
  have hy : (y : ℝ) ∈ Set.Icc (F x0) (F x1) := by
    change F ⟨0, by norm_num⟩ ≤ (y : ℝ) ∧
      (y : ℝ) ≤ F ⟨1, by norm_num⟩
    rw [h0, h1]
    exact y.property
  rcases intermediate_value_Icc hx01 hF.continuousOn hy with
    ⟨x, _hx, hxy⟩
  exact ⟨x, hxy⟩

/-- IVT surjectivity for a continuous decreasing coordinate with prescribed
endpoint values. -/
lemma apm_t91J06_anti_endpoint_surjective
    {a b : ℝ} (F : apm_t91J06_I → ℝ) (hF : Continuous F)
    (h0 : F ⟨0, by norm_num⟩ = b) (h1 : F ⟨1, by norm_num⟩ = a) :
    ∀ y : Set.Icc a b, ∃ x, F x = y := by
  intro y
  let x0 : apm_t91J06_I := ⟨0, by norm_num⟩
  let x1 : apm_t91J06_I := ⟨1, by norm_num⟩
  have hx01 : x0 ≤ x1 := by
    change (0 : ℝ) ≤ 1
    norm_num
  have hy : (y : ℝ) ∈ Set.Icc (F x1) (F x0) := by
    change F ⟨1, by norm_num⟩ ≤ (y : ℝ) ∧
      (y : ℝ) ≤ F ⟨0, by norm_num⟩
    rw [h0, h1]
    exact y.property
  rcases intermediate_value_Icc' hx01 hF.continuousOn hy with
    ⟨x, _hx, hxy⟩
  exact ⟨x, hxy⟩

/-- Package a continuous bijective real coordinate as a homeomorphism. -/
lemma apm_t91J06_package_interval_coordinate
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (F : apm_t91J06_I → ℝ) (hF : Continuous F)
    (hFinj : Function.Injective F)
    (hFmem : ∀ x, F x ∈ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ))
    (hFsurj : ∀ y : Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ), ∃ x, F x = y)
    (hext : ∀ x, F (t x) = (q x : ℝ)) :
    ∃ Q : apm_t91J06_I ≃ₜ
        Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ),
      ∀ x, (Q (t x) : ℝ) = (q x : ℝ) := by
  let f : apm_t91J06_I → Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ) :=
    fun x ↦ ⟨F x, hFmem x⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply hFinj
    exact congrArg Subtype.val hxy
  have hf_surjective : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hFsurj y
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  let e : apm_t91J06_I ≃ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ) :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  have he_continuous : Continuous e := by
    change Continuous f
    exact hF.subtype_mk hFmem
  let Q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ) :=
    he_continuous.homeoOfEquivCompactToT2
  refine ⟨Q, ?_⟩
  intro x
  change F (t x) = (q x : ℝ)
  exact hext x

/-- Extend arbitrary prescribed coordinates across an interval embedded
strictly inside the unit interval. -/
theorem apm_t91J06_extend_interval_embedding_coordinates
    (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I)
    (ht : Continuous t) (hi : Function.Injective t)
    (htint : Set.range t ⊆ apm_t91J06_Iinterior)
    (q : apm_t91J06_I ≃ₜ
      Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ)) :
    ∃ Q : apm_t91J06_I ≃ₜ
        Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ),
      ∀ x, (Q (t x) : ℝ) = (q x : ℝ) := by
  rcases t91J06Closure.intervalEmbedding_homeomorph_four_orientations
      t ht hi q with ⟨htmono | htanti, hqmono | hqanti⟩
  · rcases apm_t91J06_extend_ramp_mono_mono n t ht htint q htmono hqmono with
      ⟨F, hF, hFmono, hFmem, h0, h1, hext⟩
    exact apm_t91J06_package_interval_coordinate n t q F hF hFmono.injective hFmem
      (apm_t91J06_mono_endpoint_surjective F hF h0 h1) hext
  · rcases apm_t91J06_extend_ramp_mono_anti n t ht htint q htmono hqanti with
      ⟨F, hF, hFanti, hFmem, h0, h1, hext⟩
    exact apm_t91J06_package_interval_coordinate n t q F hF hFanti.injective hFmem
      (apm_t91J06_anti_endpoint_surjective F hF h0 h1) hext
  · rcases apm_t91J06_extend_ramp_anti_mono n t ht htint q htanti hqmono with
      ⟨F, hF, hFanti, hFmem, h0, h1, hext⟩
    exact apm_t91J06_package_interval_coordinate n t q F hF hFanti.injective hFmem
      (apm_t91J06_anti_endpoint_surjective F hF h0 h1) hext
  · rcases apm_t91J06_extend_ramp_anti_anti n t ht htint q htanti hqanti with
      ⟨F, hF, hFmono, hFmem, h0, h1, hext⟩
    exact apm_t91J06_package_interval_coordinate n t q F hF hFmono.injective hFmem
      (apm_t91J06_mono_endpoint_surjective F hF h0 h1) hext

/-- Recursively choose coordinates on all compact stages.  The extension
contract is an explicit parameter so this lemma can be developed in parallel
with the library lemma above. -/
noncomputable def apm_t91J06_compatible_stage_coordinates_aux_stageHomeo
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X) (hf : ∀ n, Topology.IsEmbedding (f n))
    (n : ℕ) : ↥(apm_t91J06_stage f n) ≃ₜ apm_t91J06_I :=
  (Homeomorph.setCongr (by simp [apm_t91J06_stage])).trans
    (hf n).toHomeomorph.symm

theorem apm_t91J06_compatible_stage_coordinates
    (hExtend : ∀ (n : ℕ) (t : apm_t91J06_I → apm_t91J06_I),
      Continuous t → Function.Injective t →
      Set.range t ⊆ apm_t91J06_Iinterior →
      ∀ q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ),
        ∃ Q : apm_t91J06_I ≃ₜ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ),
          ∀ x, (Q (t x) : ℝ) = (q x : ℝ))
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior) :
    ∃ g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
        Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ),
      ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
        ((g (n + 1))
            ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
        ((g n) ⟨x, hx⟩ : ℝ) := by
  let hsub : ∀ n, Set.range (f n) ⊆ Set.range (f (n + 1)) := fun n => by
    simpa only [image_univ] using
      (hnested n).trans (image_subset_range (f (n + 1)) apm_t91J06_Iinterior)
  let t : ∀ n, apm_t91J06_I → apm_t91J06_I := fun n =>
    ConstructionTargets.NestedEmbeddingTransition.transition
      (f n) (f (n + 1)) (hf (n + 1)) (hsub n)
  have ht_cont : ∀ n, Continuous (t n) := fun n => by
    exact ConstructionTargets.NestedEmbeddingTransition.continuous_transition
      (f n) (f (n + 1)) (hf n).continuous (hf (n + 1)) (hsub n)
  have ht_inj : ∀ n, Function.Injective (t n) := fun n => by
    exact ConstructionTargets.NestedEmbeddingTransition.injective_transition
      (f n) (f (n + 1)) (hf n).injective (hf (n + 1)) (hsub n)
  have ht_int : ∀ n, Set.range (t n) ⊆ apm_t91J06_Iinterior := fun n => by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ConstructionTargets.NestedEmbeddingTransition.transition_mem_of_range_subset_image
      (f n) (f (n + 1)) (hf (n + 1)) apm_t91J06_Iinterior
      (by simpa only [image_univ] using hnested n) x
  let q : ∀ n : ℕ, apm_t91J06_I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ) :=
    fun (n : ℕ) => Nat.rec (motive := fun k : ℕ =>
        apm_t91J06_I ≃ₜ Set.Icc (-(k + 1 : ℝ)) (k + 1 : ℝ))
      (by
        exact (Homeomorph.setCongr (show apm_t91J06_I = Set.Icc (0 : ℝ) 1 from rfl)).trans
          ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm.trans
            (Homeomorph.setCongr (by norm_num))))
      (fun k qk => by
        let w := hExtend k (t k) (ht_cont k) (ht_inj k) (ht_int k) qk
        exact (Classical.choose w).trans (Homeomorph.setCongr (by
          congr 1 <;> norm_num [Nat.cast_succ] <;> ring)) ) n
  have hq : ∀ n x, ((q (n + 1)) (t n x) : ℝ) = ((q n) x : ℝ) := by
    intro n x
    simp only [q]
    exact Classical.choose_spec
      (hExtend n (t n) (ht_cont n) (ht_inj n) (ht_int n) (q n)) x
  refine ⟨fun n =>
    (apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n).trans (q n), ?_⟩
  intro n x hx
  have hxnext : x ∈ apm_t91J06_stage f (n + 1) :=
    apm_t91J06_stage_mono f hnested (Nat.le_succ n) hx
  change ((q (n + 1))
      ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf (n + 1))
        ⟨x, hxnext⟩) : ℝ) =
    ((q n) ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n)
      ⟨x, hx⟩) : ℝ)
  have heq : t n
      ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n) ⟨x, hx⟩) =
      (apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf (n + 1))
        ⟨x, hxnext⟩ := by
    apply (hf (n + 1)).injective
    change f (n + 1) (t n _) = f (n + 1) _
    rw [show t n = ConstructionTargets.NestedEmbeddingTransition.transition
      (f n) (f (n + 1)) (hf (n + 1)) (hsub n) from rfl]
    rw [ConstructionTargets.NestedEmbeddingTransition.g_transition
      (f n) (f (n + 1)) (hf (n + 1)) (hsub n)
      ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n) ⟨x, hx⟩)]
    have hn : f n
        ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf n) ⟨x, hx⟩) = x := by
      exact congrArg Subtype.val ((hf n).toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr (by simp [apm_t91J06_stage])) ⟨x, hx⟩))
    have hn1 : f (n + 1)
        ((apm_t91J06_compatible_stage_coordinates_aux_stageHomeo f hf (n + 1))
          ⟨x, hxnext⟩) = x := by
      exact congrArg Subtype.val ((hf (n + 1)).toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr (by simp [apm_t91J06_stage])) ⟨x, hxnext⟩))
    exact hn.trans hn1.symm
  rw [← heq]
  exact hq n _

/-- Glue compatible stage coordinates.  Unlike the false helper in the
source file, this statement retains `hf`, which is needed to obtain local
inverse charts and hence continuity of the inverse. -/
lemma apm_t91J06_glue_with_embeddings_aux_coord_eq
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior)
    (g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
      Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (hcompat : ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
      ((g (n + 1))
          ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
        ((g n) ⟨x, hx⟩ : ℝ))
    (m n : ℕ) (hmn : m ≤ n) (x : X)
    (hm : x ∈ apm_t91J06_stage f m) (hn : x ∈ apm_t91J06_stage f n) :
    ((g n) ⟨x, hn⟩ : ℝ) = ((g m) ⟨x, hm⟩ : ℝ) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [hcompat n x (apm_t91J06_stage_mono f hnested hmn hm)]
      exact ih (apm_t91J06_stage_mono f hnested hmn hm)

theorem apm_t91J06_glue_with_embeddings
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆
        f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C)
    (g : ∀ n, ↥(apm_t91J06_stage f n) ≃ₜ
      Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ))
    (hcompat : ∀ (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n),
      ((g (n + 1))
          ⟨x, (apm_t91J06_stage_mono f hnested (Nat.le_succ n)) hx⟩ : ℝ) =
        ((g n) ⟨x, hx⟩ : ℝ)) :
    Nonempty (X ≃ₜ ℝ) := by
  let hmem : ∀ x : X, ∃ n, x ∈ apm_t91J06_stage f n :=
    apm_t91J06_exists_mem_stage f hcover
  let ind : X → ℕ := fun x => Classical.choose (hmem x)
  have hind (x : X) : x ∈ apm_t91J06_stage f (ind x) :=
    Classical.choose_spec (hmem x)
  let F : X → ℝ := fun x => (g (ind x) ⟨x, hind x⟩ : ℝ)
  have F_eq (n : ℕ) (x : X) (hx : x ∈ apm_t91J06_stage f n) :
      F x = (g n ⟨x, hx⟩ : ℝ) := by
    let k := max (ind x) n
    calc
      F x = (g k ⟨x, apm_t91J06_stage_mono f hnested
          (Nat.le_max_left _ _) (hind x)⟩ : ℝ) :=
        (apm_t91J06_glue_with_embeddings_aux_coord_eq f hnested g hcompat
          (ind x) k (Nat.le_max_left _ _) x (hind x) _).symm
      _ = (g n ⟨x, hx⟩ : ℝ) :=
        apm_t91J06_glue_with_embeddings_aux_coord_eq f hnested g hcompat
          n k (Nat.le_max_right _ _) x hx _
  have hFinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨n, hx, hy⟩ :=
      apm_t91J06_exists_pair_mem_stage_interior f hnested hcover x y
    have hx' : x ∈ apm_t91J06_stage f n := by
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨z, mem_univ z, rfl⟩
    have hy' : y ∈ apm_t91J06_stage f n := by
      rcases hy with ⟨z, hz, rfl⟩
      exact ⟨z, mem_univ z, rfl⟩
    have hg : g n ⟨x, hx'⟩ = g n ⟨y, hy'⟩ := by
      apply Subtype.ext
      simpa [F_eq n x hx', F_eq n y hy'] using hxy
    exact congrArg Subtype.val ((g n).injective hg)
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt |y|
    have hyI : y ∈ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
      constructor
      · have := neg_le_abs y
        norm_num at hn ⊢
        linarith
      · have := le_abs_self y
        norm_num at hn ⊢
        linarith
    let z := (g n).symm ⟨y, hyI⟩
    refine ⟨z.1, ?_⟩
    rw [F_eq n z.1 z.2]
    exact congrArg Subtype.val ((g n).apply_symm_apply ⟨y, hyI⟩)
  have hFcont : Continuous F := by
    rw [continuous_iff_isClosed]
    intro C hC
    apply hweak
    intro n
    have heq : f n ⁻¹' (F ⁻¹' C) =
        (fun z : apm_t91J06_I => (g n ⟨f n z, ⟨z, mem_univ z, rfl⟩⟩ : ℝ)) ⁻¹' C := by
      ext z
      simp only [mem_preimage]
      rw [F_eq n (f n z) ⟨z, mem_univ z, rfl⟩]
    rw [heq]
    exact hC.preimage (continuous_subtype_val.comp ((g n).continuous.comp
      ((hf n).continuous.subtype_mk (fun z => ⟨z, mem_univ z, rfl⟩))))
  let e : X ≃ ℝ := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  have he_apply (x : X) : e x = F x := rfl
  have hFopen : IsOpenMap F := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rcases hy with ⟨x, hxU, rfl⟩
    obtain ⟨n, hx⟩ := apm_t91J06_exists_mem_stage f hcover x
    let N := n + 1
    have hxN : x ∈ apm_t91J06_stage f N :=
      apm_t91J06_stage_mono f hnested (Nat.le_succ n) hx
    let S : Set ↥(apm_t91J06_stage f N) := {z | z.1 ∈ U}
    have hS : IsOpen S := hU.preimage continuous_subtype_val
    have hgS : IsOpen ((g N) '' S) := (g N).isOpenMap S hS
    obtain ⟨V, hV, hVeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hgS
    let J : Set ℝ := Set.Ioo (-(N + 1 : ℝ)) (N + 1 : ℝ)
    have hFxin : F x ∈ J := by
      rw [F_eq n x hx]
      constructor
      · have hb := (g n ⟨x, hx⟩).2.1
        norm_num [N] at hb ⊢
        linarith
      · have hb := (g n ⟨x, hx⟩).2.2
        norm_num [N] at hb ⊢
        linarith
    have hmemV : F x ∈ V := by
      have hz : (g N ⟨x, hxN⟩) ∈ (g N) '' S := by
        refine ⟨⟨x, hxN⟩, hxU, rfl⟩
      have hz' : (g N ⟨x, hxN⟩) ∈ Subtype.val ⁻¹' V := hVeq.symm ▸ hz
      simpa [F_eq N x hxN] using hz'
    filter_upwards [Filter.inter_mem (hV.mem_nhds hmemV)
      (isOpen_Ioo.mem_nhds hFxin)] with z hz
    rcases hz with ⟨hzV, hzJ⟩
    have hzI : z ∈ Set.Icc (-(N + 1 : ℝ)) (N + 1 : ℝ) := ⟨le_of_lt hzJ.1, le_of_lt hzJ.2⟩
    have hzimg : (⟨z, hzI⟩ : Set.Icc (-(N + 1 : ℝ)) (N + 1 : ℝ)) ∈ (g N) '' S := by
      rw [← hVeq]
      exact hzV
    rcases hzimg with ⟨w, hwU, hw⟩
    refine ⟨w.1, hwU, ?_⟩
    rw [F_eq N w.1 w.2]
    exact congrArg Subtype.val hw
  exact ⟨e.toHomeomorph (by
    intro U
    constructor
    · intro hpre
      have himg : e '' (e ⁻¹' U) = U := Set.image_preimage_eq U e.surjective
      rw [← himg]
      exact hFopen _ hpre
    · intro h
      exact hFcont.isOpen_preimage U h)⟩

theorem apm_t91j06
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → apm_t91J06_I → X)
    (hf : ∀ n, Topology.IsEmbedding (f n))
    (hnested : ∀ n,
      f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior)
    (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X))
    (hweak : ∀ C : Set X, (∀ n, IsClosed (f n ⁻¹' C)) → IsClosed C) :
    Nonempty (X ≃ₜ ℝ) := by
  obtain ⟨g, hg⟩ := apm_t91J06_compatible_stage_coordinates
    apm_t91J06_extend_interval_embedding_coordinates f hf hnested
  exact apm_t91J06_glue_with_embeddings f hf hnested hcover hweak g hg

#print axioms apm_t91j06

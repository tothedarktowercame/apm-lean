import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# APM a93A04: AC functions are exactly BV-limits of Lipschitz functions

**Problem.** f : [0,1] → ℝ is absolutely continuous iff there exist Lipschitz
functions fₙ on [0,1] with V(fₙ - f) → 0, where V is total variation.

## Proof strategy

**(⟸)** Lipschitz ⟹ AC (Mathlib: `LipschitzOnWith.absolutelyContinuousOnInterval`).
If fₙ are AC and V(fₙ - f) → 0, then f is AC (ε-δ argument using the variation
bound).

**(⟹)** If f is AC, then f(x) = f(0) + ∫₀ˣ f'(t) dt with f' ∈ L¹. Truncate:
gₙ = clamp(f', -n, n), fₙ = f(0) + ∫₀ˣ gₙ. Then fₙ is Lipschitz (|gₙ| ≤ n)
and V(fₙ - f) = ∫|gₙ - f'| → 0 by DCT.

## Statement repair note

The informal proof defines `totalVariation` from scratch. Mathlib already has
`eVariationOn` (extended-real-valued variation on a set). We use Mathlib's
`AbsolutelyContinuousOnInterval` for AC and `LipschitzOnWith` for Lipschitz.
The problem reduces to showing the AC functions are the closure of Lipschitz
functions in the `eVariationOn` norm.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace ApmCanaries.A93A04

/-- Lipschitz on [0,1]. -/
def LipschitzOn01 (f : ℝ → ℝ) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K f (uIcc (0:ℝ) 1)

/-- Total variation of f on [0,1] as a real number. -/
noncomputable def totalVariation (f : ℝ → ℝ) : ENNReal :=
  eVariationOn f (uIcc (0:ℝ) 1)

/-- The variation of an indefinite integral is bounded by the `L¹` norm of its integrand. -/
lemma eVariationOn_intervalIntegral_le_integral_norm
    {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ Icc a b) :
    eVariationOn (fun x ↦ ∫ t in c..x, g t) (Icc a b) ≤
      ENNReal.ofReal (∫ t in a..b, ‖g t‖) := by
  rw [eVariationOn, iSup_le_iff]
  rintro ⟨n, u, hu, hus⟩
  simp only [edist_dist]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ i ∈ Finset.range n,
        dist (∫ t in c..u (i + 1), g t) (∫ t in c..u i, g t))
        ≤ ∑ i ∈ Finset.range n, ∫ t in u i..u (i + 1), ‖g t‖ := by
          gcongr with i hi
          rw [Real.dist_eq,
            intervalIntegral.integral_interval_sub_left
              (hg.mono_set' (by grind)) (hg.mono_set' (by grind))]
          simpa only [abs_neg] using
            intervalIntegral.abs_integral_le_integral_abs (hu (Nat.le_add_right i 1))
    _ = ∫ t in u 0..u n, ‖g t‖ := by
          apply intervalIntegral.sum_integral_adjacent_intervals
          intro k hk
          exact hg.norm.mono_set' (by grind)
    _ ≤ ∫ t in a..b, ‖g t‖ := by
          apply intervalIntegral.integral_mono_interval
          · exact (hus 0).1
          · exact hu (Nat.zero_le n)
          · exact (hus n).2
          · exact Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)
          · exact hg.norm

/-- Lipschitz ⟹ AC on [0,1].

    Zero-sorry: follows from `LipschitzOnWith.absolutelyContinuousOnInterval`. -/
theorem lipschitz_implies_ac {f : ℝ → ℝ} (h : LipschitzOn01 f) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  obtain ⟨K, hK⟩ := h
  exact hK.absolutelyContinuousOnInterval

/-- The sum of endpoint increments over a finite disjoint family of unoriented intervals is
bounded by the variation on the ambient interval. -/
lemma sum_edist_le_eVariationOn_of_mem_disjWithin
    {g : ℝ → ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hE : (n, I) ∈ AbsolutelyContinuousOnInterval.disjWithin (0 : ℝ) 1) :
    (∑ i ∈ Finset.range n, edist (g (I i).1) (g (I i).2)) ≤
      eVariationOn g (uIcc (0 : ℝ) 1) := by
  classical
  rw [AbsolutelyContinuousOnInterval.disjWithin] at hE
  rcases hE with ⟨hmem, hdisj⟩
  let l : Fin n → ℝ := fun i ↦ min (I i).1 (I i).2
  let r : Fin n → ℝ := fun i ↦ max (I i).1 (I i).2
  let A := {i : Fin n // l i < r i}
  let la : A → ℝ := fun i ↦ l i.1
  let ra : A → ℝ := fun i ↦ r i.1
  have hdisjA (i j : A) (hij : i ≠ j) :
      Disjoint (Ioc (la i) (ra i)) (Ioc (la j) (ra j)) := by
    have hd := hdisj (Finset.mem_range.mpr i.1.isLt)
      (Finset.mem_range.mpr j.1.isLt) (by
        intro h
        apply hij
        apply Subtype.ext
        apply Fin.ext
        exact h)
    simpa only [uIoc] using hd
  have hl_inj : Function.Injective (fun i : A ↦ la i) := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hd := Set.Ioc_disjoint_Ioc.mp (hdisjA i j (by
      intro h
      exact hne (congrArg Subtype.val h)))
    have hi := i.property
    have hj := j.property
    change la i = la j at hij
    rw [hij, max_self] at hd
    grind
  have hsep {i j : A} (hij : la i < la j) : ra i ≤ la j := by
    have hd := Set.Ioc_disjoint_Ioc.mp (hdisjA i j (by
      intro heq
      subst j
      exact lt_irrefl _ hij))
    rw [max_eq_right hij.le] at hd
    have hj := j.property
    grind
  have haux : ∀ L : List A, L.Pairwise (fun i j ↦ la i < la j) →
      (L.map fun i ↦ edist (g (la i)) (g (ra i))).sum ≤
        eVariationOn g (⋃ i ∈ L.toFinset, Icc (la i) (ra i)) := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      rw [List.pairwise_cons] at hL
      have hin : i ∉ L.toFinset := by
        intro hi
        have := hL.1 i (by simpa using hi)
        exact lt_irrefl _ this
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      calc
        edist (g (la i)) (g (ra i)) +
              (L.map fun j ↦ edist (g (la j)) (g (ra j))).sum
            ≤ eVariationOn g (Icc (la i) (ra i)) +
                eVariationOn g (⋃ j ∈ L.toFinset, Icc (la j) (ra j)) := by
              gcongr
              · exact eVariationOn.edist_le g (left_mem_Icc.mpr i.property.le)
                  (right_mem_Icc.mpr i.property.le)
              · exact ih hL.2
        _ ≤ eVariationOn g (Icc (la i) (ra i) ∪
              ⋃ j ∈ L.toFinset, Icc (la j) (ra j)) := by
              apply eVariationOn.add_le_union
              intro x hx y hy
              simp only [mem_iUnion] at hy
              obtain ⟨j, hjL, hyj⟩ := hy
              have hij : la i < la j := hL.1 j (by simpa using hjL)
              exact hx.2.trans ((hsep hij).trans hyj.1)
        _ = eVariationOn g (⋃ j ∈ insert i L.toFinset, Icc (la j) (ra j)) := by
              congr 1
              ext z
              simp
  let e₀ : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let σ : Equiv.Perm (Fin (Fintype.card A)) := Tuple.sort (fun k ↦ la (e₀ k))
  let e : Fin (Fintype.card A) ≃ A := σ.trans e₀
  have he_mono : Monotone (fun k ↦ la (e k)) := by
    simpa only [e, σ, Equiv.trans_apply, Function.comp_apply] using
      Tuple.monotone_sort (fun k ↦ la (e₀ k))
  have he_inj : Function.Injective (fun k ↦ la (e k)) := hl_inj.comp e.injective
  have he_strict : StrictMono (fun k ↦ la (e k)) := he_mono.strictMono_of_injective he_inj
  let L : List A := List.ofFn e
  have hsorted : L.Pairwise (fun i j ↦ la i < la j) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simpa only [L, List.get_ofFn] using he_strict hij
  have hactive :
      (∑ i : A, edist (g (la i)) (g (ra i))) ≤ eVariationOn g (uIcc (0 : ℝ) 1) := by
    calc
      (∑ i : A, edist (g (la i)) (g (ra i))) =
          ∑ k : Fin (Fintype.card A), edist (g (la (e k))) (g (ra (e k))) := by
            exact (Equiv.sum_comp e (fun i : A ↦ edist (g (la i)) (g (ra i)))).symm
      _ = (L.map fun i ↦ edist (g (la i)) (g (ra i))).sum := by
            change (∑ k, edist (g (la (e k))) (g (ra (e k)))) =
              ((List.ofFn e).map fun i ↦ edist (g (la i)) (g (ra i))).sum
            rw [List.map_ofFn, List.sum_ofFn]
            rfl
      _ ≤ eVariationOn g (⋃ i ∈ L.toFinset, Icc (la i) (ra i)) := haux L hsorted
      _ ≤ eVariationOn g (uIcc (0 : ℝ) 1) := by
        apply eVariationOn.mono
        intro x hx
        simp only [mem_iUnion] at hx
        obtain ⟨i, _, hxi⟩ := hx
        have hi := hmem i.1 (Finset.mem_range.mpr i.1.isLt)
        have hi1 : 0 ≤ (I i.1).1 ∧ (I i.1).1 ≤ 1 := by
          simpa [uIcc] using hi.1
        have hi2 : 0 ≤ (I i.1).2 ∧ (I i.1).2 ≤ 1 := by
          simpa [uIcc] using hi.2
        have hla : 0 ≤ la i := by
          dsimp only [la, l]
          exact le_min hi1.1 hi2.1
        have hra : ra i ≤ 1 := by
          dsimp only [ra, r]
          exact max_le hi1.2 hi2.2
        have : x ∈ Icc (0 : ℝ) 1 := ⟨hla.trans hxi.1, hxi.2.trans hra⟩
        simpa [uIcc] using this
  calc
    (∑ i ∈ Finset.range n, edist (g (I i).1) (g (I i).2)) =
        ∑ i : Fin n, edist (g (I i).1) (g (I i).2) := Finset.sum_range _
    _ = ∑ i : A, edist (g (la i)) (g (ra i)) := by
      calc
        (∑ i : Fin n, edist (g (I i).1) (g (I i).2)) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ l i < r i),
              edist (g (I i).1) (g (I i).2) := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro i hi
                by_cases h : l i < r i
                · simp [h]
                · have heq : (I i).1 = (I i).2 := by
                    by_contra hne
                    exact h (min_lt_max.mpr hne)
                  simp [h, heq]
        _ = ∑ i : A, edist (g (I i.1).1) (g (I i.1).2) := by
              apply Finset.sum_subtype
              intro i
              simp
        _ = ∑ i : A, edist (g (la i)) (g (ra i)) := by
              apply Fintype.sum_congr
              intro i
              rcases le_total (I i.1).1 (I i.1).2 with hab | hba
              · simp only [la, ra, l, r, min_eq_left hab, max_eq_right hab]
              · simp only [la, ra, l, r, min_eq_right hba, max_eq_left hba]
                exact edist_comm _ _
    _ ≤ _ := hactive

/-- **(⟸) Reverse direction:** If fₙ are Lipschitz and V(fₙ - f) → 0,
    then f is AC.

    The proof uses that each fₙ is AC (from Lipschitz) and that V-convergence
    preserves AC. The ε-δ argument is:
    for disjoint intervals with Σ(bᵢ-aᵢ) < δ:
    Σ|f(bᵢ)-f(aᵢ)| ≤ Σ|(f-fₙ)(bᵢ)-(f-fₙ)(aᵢ)| + Σ|fₙ(bᵢ)-fₙ(aᵢ)|
                     ≤ V(f-fₙ) + ε/2 < ε.
    `sum_edist_le_eVariationOn_of_mem_disjWithin` supplies the bridge from an
    arbitrary disjoint interval family to `eVariationOn`. -/
theorem lipschitz_V_limit_implies_ac
    {f : ℝ → ℝ} {fₙ : ℕ → ℝ → ℝ}
    (hlip : ∀ n, LipschitzOn01 (fₙ n))
    (hconv : Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hbpos : (0 : ENNReal) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr hhalf
  have hev : ∀ᶠ n in atTop,
      totalVariation (fun x ↦ fₙ n x - f x) < ENNReal.ofReal (ε / 2) :=
    hconv.eventually (Iio_mem_nhds hbpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hacN : AbsolutelyContinuousOnInterval (fₙ N) 0 1 := lipschitz_implies_ac (hlip N)
  rw [absolutelyContinuousOnInterval_iff] at hacN
  obtain ⟨δ, hδ, hacδ⟩ := hacN (ε / 2) hhalf
  refine ⟨δ, hδ, ?_⟩
  rintro E hE hlen
  have hfn :
      ∑ i ∈ Finset.range E.1, dist (fₙ N (E.2 i).1) (fₙ N (E.2 i).2) < ε / 2 :=
    hacδ E hE hlen
  let q : ℝ → ℝ := fun x ↦ fₙ N x - f x
  have hqvar : totalVariation q < ENNReal.ofReal (ε / 2) := hN N le_rfl
  have hqsumE :
      (∑ i ∈ Finset.range E.1, edist (q (E.2 i).1) (q (E.2 i).2)) ≤
        totalVariation q := by
    exact sum_edist_le_eVariationOn_of_mem_disjWithin hE
  have hqsum :
      ∑ i ∈ Finset.range E.1, dist (q (E.2 i).1) (q (E.2 i).2) < ε / 2 := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hhalf]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
    simpa only [edist_dist] using hqsumE.trans_lt hqvar
  calc
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
        ≤ ∑ i ∈ Finset.range E.1,
            (dist (fₙ N (E.2 i).1) (fₙ N (E.2 i).2) +
              dist (q (E.2 i).1) (q (E.2 i).2)) := by
          gcongr with i hi
          have ha : f (E.2 i).1 = fₙ N (E.2 i).1 - q (E.2 i).1 := by simp [q]
          have hb : f (E.2 i).2 = fₙ N (E.2 i).2 - q (E.2 i).2 := by simp [q]
          rw [ha, hb]
          exact dist_sub_sub_le _ _ _ _
    _ = (∑ i ∈ Finset.range E.1, dist (fₙ N (E.2 i).1) (fₙ N (E.2 i).2)) +
          ∑ i ∈ Finset.range E.1, dist (q (E.2 i).1) (q (E.2 i).2) := by
          exact Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 := add_lt_add hfn hqsum
    _ = ε := by ring

/-- **(⟹) Forward direction:** If f is AC, there exist Lipschitz fₙ with
    V(fₙ - f) → 0.

    **SORRY BOUNDARY:** The proof constructs fₙ(x) = f(0) + ∫₀ˣ gₙ(t) dt
    where gₙ = clamp(f', -n, n). Key steps:
    (1) f is AC ⟹ f' exists a.e. and is integrable (FTC for AC functions)
    (2) gₙ is bounded ⟹ fₙ is Lipschitz (|∫ₓʸ gₙ| ≤ n|x-y|)
    (3) V(fₙ-f) = ∫|gₙ-f'| → 0 by DCT (|gₙ-f'| ≤ 2|f'|, gₙ → f' a.e.)
    Each step uses deep Mathlib API: `ae_differentiableAt` for (1),
    `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` for (2),
    and `tendsto_integral_of_dominated_convergence` for (3).
    The identity V(fₙ-f) = ∫|gₙ-f'| for AC functions requires
    `eVariationOn_sub_eq_integral_norm_deriv` or similar. -/
theorem ac_implies_lipschitz_V_approx
    {f : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval f 0 1) :
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  let d : ℝ → ℝ := deriv f
  let g : ℕ → ℝ → ℝ := fun n x ↦ if ‖d x‖ ≤ n then d x else 0
  let fₙ : ℕ → ℝ → ℝ := fun n x ↦ f 0 + ∫ t in 0..x, g n t
  have hd : IntervalIntegrable d volume 0 1 := hac.intervalIntegrable_deriv
  have hg_meas (n : ℕ) : StronglyMeasurable (g n) := by
    apply Measurable.stronglyMeasurable
    exact (measurable_deriv f).ite
      (measurableSet_le (measurable_deriv f).norm measurable_const) measurable_const
  have hg_norm (n : ℕ) (x : ℝ) : ‖g n x‖ ≤ n := by
    simp only [g]
    split_ifs with h
    · exact h
    · simp
  have hg (n : ℕ) : IntervalIntegrable (g n) volume 0 1 := by
    apply hd.mono_fun (hg_meas n).aestronglyMeasurable
    filter_upwards with x
    simp only [g]
    split_ifs <;> simp_all
  refine ⟨fₙ, ?_, ?_⟩
  · intro n
    refine ⟨n, ?_⟩
    intro x hx y hy
    rw [edist_dist, edist_dist]
    have hncoe : ((n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by simp
    rw [hncoe]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ n)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.dist_eq, Real.dist_eq]
    dsimp only [fₙ]
    simp only [add_sub_add_left_eq_sub]
    rw [intervalIntegral.integral_interval_sub_left
      (hg n |>.mono_set' (by grind [uIcc])) (hg n |>.mono_set' (by grind [uIcc]))]
    calc
      |∫ t in y..x, g n t| = ‖∫ t in y..x, g n t‖ := by simp
      _ ≤ (n : ℝ) * |x - y| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun z hz ↦ hg_norm n z)
      _ = (n : ℝ≥0) * dist x y := by simp [Real.dist_eq]
  · let q : ℕ → ℝ → ℝ := fun n x ↦ ‖g n x - d x‖
    have hq_meas (n : ℕ) :
        AEStronglyMeasurable (q n) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ((hg_meas n).sub (measurable_deriv f).stronglyMeasurable).norm.aestronglyMeasurable
    have hq_bound (n : ℕ) : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖q n x‖ ≤ ‖d x‖ := by
      filter_upwards with x
      simp only [q, norm_norm, g]
      split_ifs <;> simp_all
    have hq_lim : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        Tendsto (fun n ↦ q n x) atTop (𝓝 0) := by
      filter_upwards with x
      obtain ⟨N, hN⟩ := exists_nat_ge ‖d x‖
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hdn : ‖d x‖ ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      have hdn' : |d x| ≤ (n : ℝ) := by simpa [Real.norm_eq_abs] using hdn
      simp [q, g, hdn']
    have hq_int : Tendsto
        (fun n ↦ ∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)) atTop (𝓝 0) := by
      convert tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (Ioc (0 : ℝ) 1)) (fun x ↦ ‖d x‖)
        hq_meas hd.norm.1 hq_bound hq_lim using 1 <;> simp
    have hbound (n : ℕ) :
        totalVariation (fun x ↦ fₙ n x - f x) ≤
          ENNReal.ofReal (∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)) := by
      have hcongr : Set.EqOn (fun x ↦ fₙ n x - f x)
          (fun x ↦ ∫ t in 0..x, g n t - d t) (Icc (0 : ℝ) 1) := by
        intro x hx
        have hftc : ∫ t in 0..x, d t = f x - f 0 := by
          exact (hac.mono (by grind [uIcc_of_le])).integral_deriv_eq_sub
        simp only [fₙ]
        rw [intervalIntegral.integral_sub (hg n |>.mono_set' (by grind))
          (hd.mono_set' (by grind)), hftc]
        ring
      rw [totalVariation, uIcc_of_le (by norm_num),
        eVariationOn.congr hcongr]
      calc
        eVariationOn (fun x ↦ ∫ t in 0..x, g n t - d t) (Icc 0 1)
            ≤ ENNReal.ofReal (∫ t in 0..1, ‖g n t - d t‖) :=
          eVariationOn_intervalIntegral_le_integral_norm (by norm_num)
            ((hg n).sub hd) (by norm_num)
        _ = ENNReal.ofReal (∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)) := by
          congr 1
          rw [intervalIntegral.integral_of_le (by norm_num)]
    have hofReal : Tendsto
        (fun n ↦ ENNReal.ofReal (∫ x, q n x ∂volume.restrict (Ioc (0 : ℝ) 1)))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto 0 |>.comp hq_int)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0))
      hofReal
      (fun _ ↦ bot_le) hbound

/-- **Main theorem:** f is AC on [0,1] iff f is a V-limit of Lipschitz functions. -/
theorem ac_iff_lipschitz_V_approx (f : ℝ → ℝ) :
    AbsolutelyContinuousOnInterval f 0 1 ↔
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  refine ⟨ac_implies_lipschitz_V_approx, ?_⟩
  rintro ⟨fₙ, hlip, hconv⟩
  exact lipschitz_V_limit_implies_ac hlip hconv

end ApmCanaries.A93A04

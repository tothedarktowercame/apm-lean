import Mathlib

/-! # APM m03J02: global dynamics of `u' + u = cos u`

## Statement repairs

Part (b) calls the problem a “boundary value problem”; it is the initial value
problem from part (a), so the formal statement refers to the same IVP.
-/

open Filter

noncomputable section

/-- A global classical solution on the whole real time axis.

The ODE is imposed at every `t : ℝ` (not only `t ≥ 0`) so that solutions are
unique as functions `ℝ → ℝ`; constraining only the nonnegative half-axis
would leave the past values free and refute the `∃!` conjunct. -/
def IsM03J02Solution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  u 0 = u₀ ∧ ∀ t : ℝ, HasDerivAt u (Real.cos (u t) - u t) t

/-- The autonomous vector field is globally Lipschitz.  This is the uniform
estimate needed both for Grönwall uniqueness and for global continuation of
the local Picard--Lindelöf solution. -/
lemma m03J02_lipschitz_vectorField :
    LipschitzWith 2 (fun x : ℝ ↦ Real.cos x - x) := by
  convert Real.lipschitzWith_cos.sub LipschitzWith.id using 1 <;> norm_num

/-- The vector field has at most linear growth.  This is the a-priori bound
that prevents a finite-time escape when local solutions are continued. -/
lemma m03J02_vectorField_norm_le (x : ℝ) :
    ‖Real.cos x - x‖ ≤ ‖x‖ + 1 := by
  calc
    ‖Real.cos x - x‖ ≤ ‖Real.cos x‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ 1 + ‖x‖ := by
      simpa [Real.norm_eq_abs] using add_le_add_right (Real.abs_cos_le_one x) ‖x‖
    _ = ‖x‖ + 1 := by ring

/-- The local Picard--Lindelöf producer specialized to this vector field.
The continuation construction can invoke it at every endpoint. -/
lemma m03J02_local_solution (t₀ x₀ : ℝ) :
    ∃ u : ℝ → ℝ, u t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt u (Real.cos (u t) - u t) t := by
  exact ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    ((Real.contDiff_cos.sub contDiff_id).contDiffAt (x := x₀)) t₀

/-- The local existence time can be chosen uniformly over all initial
states.  The spatial Picard ball grows with `|x|`, absorbing the linear
growth of the vector field while leaving a fixed time radius. -/
lemma m03J02_uniform_local_solution (x₀ : ℝ) :
    ∃ u : ℝ → ℝ, u 0 = x₀ ∧ ∀ t ∈ Set.Ioo (-(1 / 3 : ℝ)) (1 / 3 : ℝ),
      HasDerivAt u (Real.cos (u t) - u t) t := by
  let A : NNReal := ⟨|x₀| + 1, by positivity⟩
  let L : NNReal := 3 * A
  have hb : ∀ x ∈ Metric.closedBall x₀ (A : ℝ),
      ‖Real.cos x - x‖ ≤ (L : ℝ) := by
    intro x hx
    have hdist : |x - x₀| ≤ (A : ℝ) := by
      simpa [Real.dist_eq] using hx
    have hxabs : |x| ≤ |x₀| + (A : ℝ) := by
      calc
        |x| = |(x - x₀) + x₀| := by ring_nf
        _ ≤ |x - x₀| + |x₀| := abs_add_le _ _
        _ ≤ |x₀| + (A : ℝ) := by linarith
    calc
      ‖Real.cos x - x‖ ≤ ‖x‖ + 1 := m03J02_vectorField_norm_le x
      _ ≤ (L : ℝ) := by
        change |x| ≤ |x₀| + (|x₀| + 1) at hxabs
        change |x| + 1 ≤ 3 * (|x₀| + 1)
        linarith [abs_nonneg x₀]
  let t₀ : Set.Icc (-(1 / 3 : ℝ)) (1 / 3 : ℝ) := ⟨0, by norm_num⟩
  have hpl : IsPicardLindelof (fun _ x : ℝ ↦ Real.cos x - x) t₀ x₀ A 0 L 2 := by
    apply IsPicardLindelof.of_time_independent hb m03J02_lipschitz_vectorField.lipschitzOnWith
    simp [t₀, A, L]
    ring_nf
    exact le_rfl
  obtain ⟨u, hu0, hu⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (Metric.mem_closedBall_self (by simp))
  refine ⟨u, hu0, fun t ht ↦ ?_⟩
  exact (hu t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The ODE equation on a time set, used by the continuation construction. -/
def IsM03J02CurveOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt u (Real.cos (u t) - u t) t

/-- Uniform local existence centered at an arbitrary time. -/
lemma m03J02_uniform_local_solution_at (t₀ x₀ : ℝ) :
    ∃ u : ℝ → ℝ, u t₀ = x₀ ∧
      IsM03J02CurveOn u (Set.Ioo (t₀ - 1 / 3) (t₀ + 1 / 3)) := by
  obtain ⟨u, hu0, hu⟩ := m03J02_uniform_local_solution x₀
  refine ⟨fun t ↦ u (t - t₀), by simpa using hu0, ?_⟩
  intro t ht
  have hs : t - t₀ ∈ Set.Ioo (-(1 / 3 : ℝ)) (1 / 3 : ℝ) := by
    constructor <;> linarith [ht.1, ht.2]
  convert (hu (t - t₀) hs).comp t ((hasDerivAt_id t).sub_const t₀) using 1 <;> simp

/-- Local solutions agreeing once agree throughout the overlap of their open
intervals. -/
lemma m03J02_eqOn_overlap {u v : ℝ → ℝ} {a b a' b' t₀ : ℝ}
    (hu : IsM03J02CurveOn u (Set.Ioo a b))
    (hv : IsM03J02CurveOn v (Set.Ioo a' b'))
    (ht₀ : t₀ ∈ Set.Ioo a b ∩ Set.Ioo a' b') (h₀ : u t₀ = v t₀) :
    Set.EqOn u v (Set.Ioo (max a a') (min b b')) := by
  apply ODE_solution_unique_of_mem_Ioo (v := fun _ x : ℝ ↦ Real.cos x - x)
      (s := fun _ ↦ Set.univ) (K := 2) (t₀ := t₀)
  · exact fun _ _ ↦ m03J02_lipschitz_vectorField.lipschitzOnWith
  · exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
  · intro t ht
    exact ⟨hu t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩,
      Set.mem_univ _⟩
  · intro t ht
    exact ⟨hv t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩,
      Set.mem_univ _⟩
  · exact h₀

/-- Two overlapping local solutions can be patched to their union. -/
lemma m03J02_curveOn_piecewise {u v : ℝ → ℝ} {a b a' b' t₀ : ℝ}
    (hu : IsM03J02CurveOn u (Set.Ioo a b))
    (hv : IsM03J02CurveOn v (Set.Ioo a' b'))
    (ht₀ : t₀ ∈ Set.Ioo a b ∩ Set.Ioo a' b') (h₀ : u t₀ = v t₀) :
    IsM03J02CurveOn (Set.piecewise (Set.Ioo a b) u v)
      (Set.Ioo a b ∪ Set.Ioo a' b') := by
  intro t ht
  by_cases hmem : t ∈ Set.Ioo a b
  · have hevent : (Set.piecewise (Set.Ioo a b) u v) =ᶠ[nhds t] u := by
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with z hz
      simp [Set.piecewise, hz]
    convert (hu t hmem).congr_of_eventuallyEq hevent using 1 <;>
      simp [Set.piecewise, hmem]
  · have ht' : t ∈ Set.Ioo a' b' := ht.resolve_left hmem
    have hover := m03J02_eqOn_overlap hu hv ht₀ h₀
    have hevent : (Set.piecewise (Set.Ioo a b) u v) =ᶠ[nhds t] v := by
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with z hz
      by_cases hzu : z ∈ Set.Ioo a b
      · rw [Set.piecewise, if_pos hzu]
        exact hover ⟨max_lt hzu.1 hz.1, lt_min hzu.2 hz.2⟩
      · simp [Set.piecewise, hzu]
    convert (hv t ht').congr_of_eventuallyEq hevent using 1 <;>
      simp [Set.piecewise, hmem]

/-- A solution on a sufficiently large symmetric interval extends by the
fixed amount `1/6` at both ends. -/
lemma m03J02_extend_symmetric {u : ℝ → ℝ} {u₀ a : ℝ}
    (ha : 1 / 6 < a) (hu0 : u 0 = u₀)
    (hu : IsM03J02CurveOn u (Set.Ioo (-a) a)) :
    ∃ v : ℝ → ℝ, v 0 = u₀ ∧
      IsM03J02CurveOn v (Set.Ioo (-(a + 1 / 6)) (a + 1 / 6)) := by
  let tl : ℝ := -a + 1 / 6
  let tr : ℝ := a - 1 / 6
  obtain ⟨ul, hul0, hul⟩ := m03J02_uniform_local_solution_at tl (u tl)
  obtain ⟨ur, hur0, hur⟩ := m03J02_uniform_local_solution_at tr (u tr)
  have htl : tl ∈ Set.Ioo (-a) a ∩ Set.Ioo (tl - 1 / 3) (tl + 1 / 3) := by
    constructor <;> constructor <;> dsimp [tl] <;> linarith
  let vl := Set.piecewise (Set.Ioo (-a) a) u ul
  have hvlUnion : IsM03J02CurveOn vl
      (Set.Ioo (-a) a ∪ Set.Ioo (tl - 1 / 3) (tl + 1 / 3)) :=
    m03J02_curveOn_piecewise hu hul htl hul0.symm
  have hvl : IsM03J02CurveOn vl (Set.Ioo (-(a + 1 / 6)) a) := by
    intro t ht
    apply hvlUnion t
    by_cases hta : -a < t
    · exact Or.inl ⟨hta, ht.2⟩
    · right
      dsimp [tl]
      constructor <;> linarith [ht.1, ht.2]
  have htr : tr ∈ Set.Ioo (-(a + 1 / 6)) a ∩ Set.Ioo (tr - 1 / 3) (tr + 1 / 3) := by
    constructor <;> constructor <;> dsimp [tr] <;> linarith
  let v := Set.piecewise (Set.Ioo (-(a + 1 / 6)) a) vl ur
  have hvUnion : IsM03J02CurveOn v
      (Set.Ioo (-(a + 1 / 6)) a ∪ Set.Ioo (tr - 1 / 3) (tr + 1 / 3)) :=
    m03J02_curveOn_piecewise hvl hur htr (by
      dsimp [vl]
      rw [Set.piecewise, if_pos (show tr ∈ Set.Ioo (-a) a by
        dsimp [tr]; constructor <;> linarith), hur0])
  refine ⟨v, ?_, ?_⟩
  · dsimp [v, vl]
    rw [Set.piecewise, if_pos (show 0 ∈ Set.Ioo (-(a + 1 / 6)) a by
      constructor <;> linarith), Set.piecewise,
      if_pos (show 0 ∈ Set.Ioo (-a) a by constructor <;> linarith), hu0]
  · intro t ht
    apply hvUnion t
    by_cases hta : t < a
    · exact Or.inl ⟨ht.1, hta⟩
    · right
      dsimp [tr]
      constructor <;> linarith [ht.1, ht.2]

/-- Iterating the symmetric extension step gives solutions on an unbounded
sequence of centered intervals. -/
lemma m03J02_exists_on_nat_radius (u₀ : ℝ) : ∀ n : ℕ,
    ∃ u : ℝ → ℝ, u 0 = u₀ ∧
      IsM03J02CurveOn u
        (Set.Ioo (-((n : ℝ) / 6 + 1 / 3)) ((n : ℝ) / 6 + 1 / 3)) := by
  intro n
  induction n with
  | zero =>
      obtain ⟨u, hu0, hu⟩ := m03J02_uniform_local_solution u₀
      exact ⟨u, hu0, by simpa [IsM03J02CurveOn] using hu⟩
  | succ n ih =>
      obtain ⟨u, hu0, hu⟩ := ih
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have ha : 1 / 6 < (n : ℝ) / 6 + 1 / 3 := by norm_num; linarith
      obtain ⟨v, hv0, hv⟩ := m03J02_extend_symmetric ha hu0 hu
      refine ⟨v, hv0, ?_⟩
      convert hv using 1 <;> push_cast <;> ring

/-- A centered solution exists on every prescribed finite radius. -/
lemma m03J02_exists_on_radius (u₀ a : ℝ) :
    ∃ u : ℝ → ℝ, u 0 = u₀ ∧ IsM03J02CurveOn u (Set.Ioo (-a) a) := by
  obtain ⟨n : ℕ, hn : a < n⟩ := exists_nat_gt a
  obtain ⟨u, hu0, hu⟩ := m03J02_exists_on_nat_radius u₀ (6 * n)
  refine ⟨u, hu0, fun t ht ↦ hu t ?_⟩
  push_cast at hn ⊢
  constructor <;> norm_num at * <;> linarith

/-- Two global solutions with the same initial value coincide. -/
lemma m03J02_solution_unique {u₀ : ℝ} {u v : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hv : IsM03J02Solution u₀ v) : u = v := by
  apply ODE_solution_unique_univ (v := fun _ x : ℝ ↦ Real.cos x - x)
      (s := fun _ ↦ Set.univ) (K := 2) (t₀ := 0)
  · exact fun _ ↦ m03J02_lipschitz_vectorField.lipschitzOnWith
  · exact fun t ↦ ⟨hu.2 t, Set.mem_univ _⟩
  · exact fun t ↦ ⟨hv.2 t, Set.mem_univ _⟩
  · exact hu.1.trans hv.1.symm

/-- Global uniqueness based at an arbitrary time. -/
lemma m03J02_trajectory_unique_at {u v : ℝ → ℝ} {t₀ : ℝ}
    (hu : ∀ t, HasDerivAt u (Real.cos (u t) - u t) t)
    (hv : ∀ t, HasDerivAt v (Real.cos (v t) - v t) t)
    (h₀ : u t₀ = v t₀) : u = v := by
  apply ODE_solution_unique_univ (v := fun _ x : ℝ ↦ Real.cos x - x)
      (s := fun _ ↦ Set.univ) (K := 2) (t₀ := t₀)
  · exact fun _ ↦ m03J02_lipschitz_vectorField.lipschitzOnWith
  · exact fun t ↦ ⟨hu t, Set.mem_univ _⟩
  · exact fun t ↦ ⟨hv t, Set.mem_univ _⟩
  · exact h₀

/-- The vector field has an equilibrium between `0` and `π / 2`. -/
lemma m03J02_exists_equilibrium :
    ∃ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) ∧ Real.cos ξ = ξ := by
  let G : ℝ → ℝ := fun x ↦ Real.cos x - x
  have hzero : 0 ∈ G '' Set.Icc (0 : ℝ) (Real.pi / 2) := by
    apply intermediate_value_Icc' (by positivity)
      ((Real.continuous_cos.sub continuous_id).continuousOn)
    constructor
    · dsimp [G]
      rw [Real.cos_pi_div_two]
      nlinarith [Real.pi_pos]
    · norm_num [G]
  obtain ⟨ξ, hξIcc, hξ⟩ := hzero
  refine ⟨ξ, hξIcc, ?_⟩
  dsimp [G] at hξ
  linarith

/-- On the only interval where fixed points can occur, `x - cos x` is
strictly increasing. -/
lemma m03J02_strictMono_sub_cos :
    StrictMonoOn (fun z : ℝ ↦ z - Real.cos z) (Set.Icc (-1) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_id.sub Real.continuous_cos).continuousOn
    intro z hz
    rw [interior_Icc] at hz
    have hzabs : |z| < 1 := abs_lt.mpr hz
    have hsin : -1 < Real.sin z := by
      rcases eq_or_ne z 0 with rfl | hz0
      · norm_num
      · have hs := Real.abs_sin_lt_abs hz0
        have hn := neg_abs_le (Real.sin z)
        linarith
    have hd : HasDerivAt (fun w : ℝ ↦ w - Real.cos w) (1 + Real.sin z) z := by
      simpa only [id_eq, sub_neg_eq_add] using
        (hasDerivAt_id z).sub (Real.hasDerivAt_cos z)
    rw [show deriv (fun w : ℝ ↦ id w - Real.cos w) z = 1 + Real.sin z by
      simpa only [id_eq] using hd.deriv]
    linarith

/-- The equilibrium is unique.  Restricting possible fixed points to
`[-1,1]` turns the derivative estimate for `x - cos x` into a strict one. -/
lemma m03J02_equilibrium_unique {x y : ℝ}
    (hx : Real.cos x = x) (hy : Real.cos y = y) : x = y := by
  have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hx]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hyI : y ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hy]
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  apply m03J02_strictMono_sub_cos.injOn hxI hyI
  simp [hx, hy]

/-- Above the equilibrium the vector field points strictly downwards. -/
lemma m03J02_vectorField_neg_above {x ξ : ℝ} (hξ : Real.cos ξ = ξ) (hx : ξ < x) :
    Real.cos x - x < 0 := by
  by_cases hx1 : x ≤ 1
  · have hξI : ξ ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hξ]
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hxI : x ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨hξI.1.trans (le_of_lt hx), hx1⟩
    have := m03J02_strictMono_sub_cos hξI hxI hx
    dsimp only at this
    rw [hξ] at this
    linarith
  · have hx' : 1 < x := lt_of_not_ge hx1
    linarith [Real.cos_le_one x]

/-- Below the equilibrium the vector field points strictly upwards. -/
lemma m03J02_vectorField_pos_below {x ξ : ℝ} (hξ : Real.cos ξ = ξ) (hx : x < ξ) :
    0 < Real.cos x - x := by
  by_cases hx1 : -1 ≤ x
  · have hξI : ξ ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hξ]
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hxI : x ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨hx1, (le_of_lt hx).trans hξI.2⟩
    have h := m03J02_strictMono_sub_cos hxI hξI hx
    dsimp only at h
    rw [hξ] at h
    linarith
  · have hx' : x < -1 := lt_of_not_ge hx1
    linarith [Real.neg_one_le_cos x]

/-- An equilibrium gives a global constant solution. -/
lemma m03J02_const_solution {u₀ : ℝ} (hu₀ : Real.cos u₀ = u₀) :
    IsM03J02Solution u₀ (fun _ ↦ u₀) := by
  refine ⟨rfl, fun t ↦ ?_⟩
  convert hasDerivAt_const (x := t) (c := u₀) using 1
  simp [hu₀]

/-- A non-equilibrium global trajectory never reaches the equilibrium. -/
lemma m03J02_solution_ne_equilibrium {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) (h₀ : u₀ ≠ ξ) :
    ∀ t, u t ≠ ξ := by
  intro t hut
  have hc : ∀ s : ℝ, HasDerivAt (fun _ : ℝ ↦ ξ)
      (Real.cos ((fun _ : ℝ ↦ ξ) s) - (fun _ : ℝ ↦ ξ) s) s := by
    intro s
    convert hasDerivAt_const (x := s) (c := ξ) using 1
    simp [hξ]
  have heq : u = fun _ : ℝ ↦ ξ :=
    m03J02_trajectory_unique_at hu.2 hc (by simpa using hut)
  apply h₀
  rw [← hu.1, heq]

/-- A trajectory starting above the equilibrium stays above it for all time. -/
lemma m03J02_solution_above {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) (h₀ : ξ < u₀) :
    ∀ t, ξ < u t := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun t ↦ (hu.2 t).continuousAt
  have hne := m03J02_solution_ne_equilibrium hu hξ (ne_of_gt h₀)
  intro t
  apply lt_of_le_of_ne (le_of_not_gt ?_) (Ne.symm (hne t))
  intro hut
  have hmem : ξ ∈ Set.uIcc (u 0) (u t) := by
    rw [Set.mem_uIcc]
    right
    exact ⟨hut.le, by simpa [hu.1] using h₀.le⟩
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hcont.continuousOn hmem
  exact hne s hs

/-- A trajectory starting below the equilibrium stays below it for all time. -/
lemma m03J02_solution_below {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) (h₀ : u₀ < ξ) :
    ∀ t, u t < ξ := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun t ↦ (hu.2 t).continuousAt
  have hne := m03J02_solution_ne_equilibrium hu hξ (ne_of_lt h₀)
  intro t
  apply lt_of_le_of_ne (le_of_not_gt ?_) (hne t)
  intro hut
  have hmem : ξ ∈ Set.uIcc (u 0) (u t) := by
    rw [Set.mem_uIcc]
    left
    exact ⟨by simpa [hu.1] using h₀.le, hut.le⟩
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hcont.continuousOn hmem
  exact hne s hs

/-- A solution starting above equilibrium is globally antitone. -/
lemma m03J02_solution_antitone {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) (h₀ : ξ < u₀) :
    Antitone u := by
  apply antitone_of_hasDerivAt_nonpos hu.2
  intro t
  exact (m03J02_vectorField_neg_above hξ (m03J02_solution_above hu hξ h₀ t)).le

/-- A solution starting below equilibrium is globally monotone. -/
lemma m03J02_solution_monotone {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) (h₀ : u₀ < ξ) :
    Monotone u := by
  apply monotone_of_hasDerivAt_nonneg hu.2
  intro t
  exact (m03J02_vectorField_pos_below hξ (m03J02_solution_below hu hξ h₀ t)).le

/-- Every non-equilibrium solution has a finite forward limit. -/
lemma m03J02_solution_exists_limit {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) (h₀ : u₀ ≠ ξ) :
    ∃ l : ℝ, Tendsto u atTop (nhds l) := by
  rcases lt_or_gt_of_ne h₀ with hbelow | habove
  · rcases tendsto_atTop_of_monotone (m03J02_solution_monotone hu hξ hbelow) with hinf | hlim
    · have hev : ∀ᶠ t in atTop, ξ < u t := hinf (eventually_gt_atTop ξ)
      have hbound : ∀ᶠ t in atTop, u t < ξ :=
        Filter.Eventually.of_forall (m03J02_solution_below hu hξ hbelow)
      exact (hev.and hbound).exists.elim fun _ h ↦ (not_lt_of_ge h.2.le h.1).elim
    · exact hlim
  · rcases tendsto_atTop_of_antitone (m03J02_solution_antitone hu hξ habove) with hinf | hlim
    · have hev : ∀ᶠ t in atTop, u t < ξ := hinf (eventually_lt_atBot ξ)
      have hbound : ∀ᶠ t in atTop, ξ < u t :=
        Filter.Eventually.of_forall (m03J02_solution_above hu hξ habove)
      exact (hev.and hbound).exists.elim fun _ h ↦ (not_lt_of_ge h.2.le h.1).elim
    · exact hlim

/-- A finite forward limit of a global trajectory must be a fixed point of
the vector field.  Rolle's slope theorem on each `[n,n+1]` supplies sample
times tending to infinity where the ODE value equals a vanishing secant. -/
lemma m03J02_limit_is_equilibrium {u₀ l : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hl : Tendsto u atTop (nhds l)) :
    Real.cos l = l := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun t ↦ (hu.2 t).continuousAt
  have hslope (n : ℕ) : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ),
      Real.cos (u c) - u c = u (n + 1) - u n := by
    obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope u
      (fun t ↦ Real.cos (u t) - u t) (by norm_num : (n : ℝ) < n + 1)
      hcont.continuousOn (fun x _ ↦ hu.2 x)
    refine ⟨c, hc, ?_⟩
    simpa using heq
  choose c hc hceq using hslope
  have hcTop : Tendsto c atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)) b
    exact ⟨N, fun n hn ↦ (hN n hn).trans (hc n).1.le⟩
  have hnTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hn1Top : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp hnTop) b
    exact ⟨N, fun n hn ↦ (hN n hn).trans (by norm_num)⟩
  have hleft : Tendsto (fun n ↦ Real.cos (u (c n)) - u (c n)) atTop
      (nhds (Real.cos l - l)) :=
    (Real.continuous_cos.sub continuous_id).continuousAt.tendsto.comp (hl.comp hcTop)
  have hright : Tendsto (fun n : ℕ ↦ u (n + 1) - u n) atTop (nhds 0) := by
    convert (hl.comp hn1Top).sub (hl.comp hnTop) using 1 <;> simp
  have hzero : Real.cos l - l = 0 :=
    tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall fun n ↦ (hceq n).symm))
  linarith

/-- Every global solution converges to the unique equilibrium. -/
lemma m03J02_solution_tendsto {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : IsM03J02Solution u₀ u) (hξ : Real.cos ξ = ξ) :
    Tendsto u atTop (nhds ξ) := by
  by_cases h₀ : u₀ = ξ
  · have hc : IsM03J02Solution u₀ (fun _ ↦ ξ) := by
      subst u₀
      exact m03J02_const_solution hξ
    rw [m03J02_solution_unique hu hc]
    exact tendsto_const_nhds
  · obtain ⟨l, hl⟩ := m03J02_solution_exists_limit hu hξ h₀
    have hlξ : l = ξ := m03J02_equilibrium_unique (m03J02_limit_is_equilibrium hu hl) hξ
    simpa [hlξ] using hl

/-- Global continuation of the local Picard solutions. -/
lemma m03J02_global_exists (u₀ : ℝ) :
    ∃ u : ℝ → ℝ, IsM03J02Solution u₀ u := by
  choose γ hγ0 hγ using m03J02_exists_on_radius u₀
  let u : ℝ → ℝ := fun t ↦ γ (|t| + 1) t
  refine ⟨u, ?_, ?_⟩
  · dsimp [u]
    simpa using hγ0 1
  · intro t
    let A : ℝ := |t| + 2
    have htA : t ∈ Set.Ioo (-A) A := by
      dsimp [A]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have hevent : u =ᶠ[nhds t] γ A := by
      filter_upwards [Ioo_mem_nhds (sub_lt_self t zero_lt_one)
        (lt_add_of_pos_right t zero_lt_one)] with s hs
      have hst : |s - t| < 1 := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsA : s ∈ Set.Ioo (-A) A := by
        have habs : |s| ≤ |s - t| + |t| := by
          calc
            |s| = |(s - t) + t| := by ring_nf
            _ ≤ |s - t| + |t| := abs_add_le _ _
        dsimp [A]
        constructor <;> linarith [neg_abs_le s, le_abs_self s]
      have hsOwn : s ∈ Set.Ioo (-(|s| + 1)) (|s| + 1) := by
        constructor <;> linarith [neg_abs_le s, le_abs_self s]
      have hzero : 0 ∈ Set.Ioo (-(|s| + 1)) (|s| + 1) ∩ Set.Ioo (-A) A := by
        constructor <;> constructor <;> dsimp [A] <;>
          linarith [abs_nonneg s, abs_nonneg t]
      have hover := m03J02_eqOn_overlap (hγ (|s| + 1)) (hγ A) hzero
        ((hγ0 (|s| + 1)).trans (hγ0 A).symm)
      dsimp [u]
      exact hover ⟨max_lt hsOwn.1 hsA.1, lt_min hsOwn.2 hsA.2⟩
    have hd := hγ A t htA
    convert hd.congr_of_eventuallyEq hevent using 1 <;>
      simp only [Filter.EventuallyEq.eq_of_nhds hevent]

/-- Every initial value gives exactly one global solution, and all such
solutions converge to the same equilibrium. -/
theorem apm_m03j02 :
    (∀ u₀ : ℝ, ∃! u : ℝ → ℝ, IsM03J02Solution u₀ u) ∧
    (∃ ξ : ℝ, ∀ (u₀ : ℝ) (u : ℝ → ℝ),
      IsM03J02Solution u₀ u → Tendsto u atTop (nhds ξ)) := by
  constructor
  · intro u₀
    obtain ⟨u, hu⟩ := m03J02_global_exists u₀
    exact ⟨u, hu, fun v hv ↦ m03J02_solution_unique hv hu⟩
  · obtain ⟨ξ, -, hξ⟩ := m03J02_exists_equilibrium
    exact ⟨ξ, fun _ _ hu ↦ m03J02_solution_tendsto hu hξ⟩

#print axioms apm_m03j02

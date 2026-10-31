import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.PeriodicCircleHomotopyWinding
import ConstructionTargets.FiniteFreeHurewiczNaturality
import ConstructionTargets.CircleHurewiczIsomorphism
import ConstructionTargets.CircleExponentialPathLift

/-!
# Blueprint for APM t91J03

The only unproved boundary is the geometric universal-cover theorem saying
that winding twice forces a collision.  The remaining two lemmas and the
frozen theorem are elementary wiring and are proved here.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t91J03_Annulus := Circle × Set.Icc (0 : ℝ) 1

def apm_t91J03_firstProjection : C(apm_t91J03_Annulus, Circle) :=
  ⟨Prod.fst, continuous_fst⟩

def apm_t91J03_circleMap
    (gamma : C(Circle, apm_t91J03_Annulus)) : C(Circle, Circle) :=
  apm_t91J03_firstProjection.comp gamma

abbrev apm_t91J03_H1Circle :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle))

def apm_t91J03_H1Map
    (gamma : C(Circle, apm_t91J03_Annulus)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (apm_t91J03_circleMap gamma))

def apm_t91J03_HasWindingNumber
    (gamma : C(Circle, apm_t91J03_Annulus)) (n : ℤ) : Prop :=
  ∃ orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ,
    ∀ a : apm_t91J03_H1Circle,
      orientation.hom (apm_t91J03_H1Map gamma a) =
        n * orientation.hom a

def apm_t91J03_height
    (gamma : C(Circle, apm_t91J03_Annulus)) (z : Circle) : ℝ :=
  (gamma z).2.1

/-- Distinct points of an embedded annular circle with equal circle coordinate
have unequal height. -/
lemma apm_t91J03_height_ne_of_circleMap_eq
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    {z w : Circle} (hzw : z ≠ w)
    (hprojection : apm_t91J03_circleMap gamma z =
      apm_t91J03_circleMap gamma w) :
    apm_t91J03_height gamma z ≠ apm_t91J03_height gamma w := by
  intro hheight
  apply hzw
  apply hgamma.injective
  apply Prod.ext
  · exact hprojection
  · exact Subtype.ext hheight

/-! ### Route (claude-14, 2026-10-31; holes/labs/topology-routes/routes-1.md, t91J03)
No Jordan curve theorem. Lift the curve to the strip `ℝ × [0,1]`. If it winds `|d| ≥ 2` times, the
lift `L₀` and its deck translate `L₁` are disjoint, but a planar crossing lemma makes them meet. -/

open unitInterval in
/-- Poincaré–Miranda in angle form. No continuous angle on the square can have `cos < 0` on the
left edge, `cos > 0` on the right, `sin ≥ 0` on the bottom and `sin ≤ 0` on the top. Do NOT use
`fin_cases` or winding numbers. A continuous `g` on an interval with `0 ≤ sin ∘ g` stays in one
strip `[2πa, 2πa + π]` (likewise `sin ≤ 0`, `cos > 0`, `cos < 0`; the sets are disjoint unions of
strips, and `I` is connected). Prove that once, then chase the four corners: start at corner
`(0,0)` in `(π/2, π] + 2πa`, go along the bottom to `[0, π/2) + 2πa`, up the right edge to
`(-π/2, 0] + 2πa`, along the top to `[-π, -π/2) + 2πa`; but the left edge from `(0,0)` stays in
`(π/2, 3π/2) + 2πa`, which is disjoint from that. -/
lemma apm_t91J03_crossing_aux_corners_aux_neg (a : ℤ) (y : ℝ)
    (h1 : 2 * Real.pi * a + Real.pi < y) (h2 : y < 2 * Real.pi * a + 2 * Real.pi) :
    Real.sin y < 0 := by
  have h := Real.sin_sub_int_mul_two_pi y (a + 1)
  rw [← h]
  push_cast
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith

open unitInterval in
/-- A continuous function on `I` with `0 ≤ sin` stays in one strip `[2πa, 2πa + π]`. -/
lemma apm_t91J03_crossing_aux_corners_aux_strip (g : C(I, ℝ)) (h : ∀ t, 0 ≤ Real.sin (g t)) :
    ∃ a : ℤ, ∀ t, 2 * Real.pi * a ≤ g t ∧ g t ≤ 2 * Real.pi * a + Real.pi := by
  have hp := Real.pi_pos
  have h2p : 0 < 2 * Real.pi := by linarith
  let a : ℤ := ⌊g 0 / (2 * Real.pi)⌋
  have ha1 : 2 * Real.pi * a ≤ g 0 := by
    have := Int.floor_le (g 0 / (2 * Real.pi))
    rwa [le_div_iff₀ h2p, mul_comm] at this
  have ha2 : g 0 < 2 * Real.pi * a + 2 * Real.pi := by
    have := Int.lt_floor_add_one (g 0 / (2 * Real.pi))
    rw [div_lt_iff₀ h2p] at this
    nlinarith
  have ha3 : g 0 ≤ 2 * Real.pi * a + Real.pi := by
    by_contra hc
    exact absurd (h 0) (not_le.2 (apm_t91J03_crossing_aux_corners_aux_neg a _ (not_le.1 hc) ha2))
  refine ⟨a, fun t => ⟨?_, ?_⟩⟩
  · by_contra hc
    push_neg at hc
    let y := max (g t) (2 * Real.pi * a - Real.pi / 2)
    have hy1 : g t ≤ y := le_max_left _ _
    have hy2 : y < 2 * Real.pi * a := max_lt hc (by linarith)
    obtain ⟨u, hu⟩ := mem_range_of_exists_le_of_exists_ge g.continuous ⟨t, hy1⟩
      ⟨0, by linarith⟩
    have hy3 : 2 * Real.pi * a - Real.pi / 2 ≤ y := le_max_right _ _
    have := apm_t91J03_crossing_aux_corners_aux_neg (a - 1) y
      (by push_cast; nlinarith) (by push_cast; nlinarith)
    have h' := h u
    rw [hu] at h'
    linarith
  · by_contra hc
    push_neg at hc
    let y := min (g t) (2 * Real.pi * a + 3 * Real.pi / 2)
    have hy1 : y ≤ g t := min_le_left _ _
    have hy2 : 2 * Real.pi * a + Real.pi < y := lt_min hc (by linarith)
    obtain ⟨u, hu⟩ := mem_range_of_exists_le_of_exists_ge g.continuous ⟨0, by linarith⟩
      ⟨t, hy1⟩
    have hy3 : y ≤ 2 * Real.pi * a + 3 * Real.pi / 2 := min_le_right _ _
    have := apm_t91J03_crossing_aux_corners_aux_neg a y hy2 (by linarith)
    have h' := h u
    rw [hu] at h'
    linarith

lemma apm_t91J03_crossing_aux_corners_aux_int (u v : ℤ) (c : ℝ) (hc : c < 2)
    (h : 2 * Real.pi * u ≤ 2 * Real.pi * v + c * Real.pi) : u ≤ v := by
  have hp := Real.pi_pos
  have h1 : (2 * (u : ℝ) - 2 * v - c) * Real.pi ≤ 0 := by nlinarith
  have h2 : 2 * (u : ℝ) - 2 * v - c ≤ 0 := by
    by_contra hn
    exact absurd h1 (not_le.2 (mul_pos (not_le.1 hn) hp))
  have h3 : (u : ℝ) < v + 1 := by linarith
  have h4 : u < v + 1 := by exact_mod_cast h3
  omega

open unitInterval in
lemma apm_t91J03_crossing_aux_corners (θ : C(I × I, ℝ))
    (hL : ∀ t, Real.cos (θ (0, t)) < 0) (hR : ∀ t, 0 < Real.cos (θ (1, t)))
    (hB : ∀ s, 0 ≤ Real.sin (θ (s, 0))) (hT : ∀ s, Real.sin (θ (s, 1)) ≤ 0) : False := by
  have hp := Real.pi_pos
  let gB : C(I, ℝ) := ⟨fun s => θ (s, 0), by fun_prop⟩
  let gT : C(I, ℝ) := ⟨fun s => θ (s, 1) + Real.pi, by fun_prop⟩
  let gL : C(I, ℝ) := ⟨fun t => θ (0, t) - Real.pi / 2, by fun_prop⟩
  let gR : C(I, ℝ) := ⟨fun t => θ (1, t) + Real.pi / 2, by fun_prop⟩
  obtain ⟨b, hb⟩ := apm_t91J03_crossing_aux_corners_aux_strip gB hB
  obtain ⟨c, hc⟩ := apm_t91J03_crossing_aux_corners_aux_strip gT (fun s => by
    change 0 ≤ Real.sin (θ (s, 1) + Real.pi)
    rw [Real.sin_add_pi]
    linarith [hT s])
  obtain ⟨a, ha⟩ := apm_t91J03_crossing_aux_corners_aux_strip gL (fun t => by
    change 0 ≤ Real.sin (θ (0, t) - Real.pi / 2)
    rw [Real.sin_sub_pi_div_two]
    linarith [hL t])
  obtain ⟨d, hd⟩ := apm_t91J03_crossing_aux_corners_aux_strip gR (fun t => by
    change 0 ≤ Real.sin (θ (1, t) + Real.pi / 2)
    rw [Real.sin_add_pi_div_two]
    exact (hR t).le)
  have ib := hb 0; have ib' := hb 1; have ic := hc 0; have ic' := hc 1
  have ia := ha 0; have ia' := ha 1; have id := hd 0; have id' := hd 1
  simp only [gB, gT, gL, gR, ContinuousMap.coe_mk] at ib ib' ic ic' ia ia' id id'
  have e1 : b ≤ a := apm_t91J03_crossing_aux_corners_aux_int b a (3 / 2) (by norm_num) (by linarith)
  have e2 : a ≤ b := apm_t91J03_crossing_aux_corners_aux_int a b (1 / 2) (by norm_num) (by linarith)
  have e3 : d ≤ b := apm_t91J03_crossing_aux_corners_aux_int d b (3 / 2) (by norm_num) (by linarith)
  have e4 : b ≤ d := apm_t91J03_crossing_aux_corners_aux_int b d (1 / 2) (by norm_num) (by linarith)
  have e5 : c ≤ d := apm_t91J03_crossing_aux_corners_aux_int c d (3 / 2) (by norm_num) (by linarith)
  have e6 : d ≤ c := apm_t91J03_crossing_aux_corners_aux_int d c (1 / 2) (by norm_num) (by linarith)
  have hab : a = b := le_antisymm e2 e1
  have hdb : d = b := le_antisymm e3 e4
  have hcd : c = d := le_antisymm e5 e6
  subst hab hdb hcd
  linarith

open unitInterval in
/-- Planar crossing lemma: a curve `α` in the strip from the left of `β` to the right of `β` meets
a curve `β` from height `0` to height `1`. Otherwise `F (s, t) = α s - β t`, as a complex number, never
vanishes; lift `F / ‖F‖` through `Circle.exp` on the square
(`ConstructionTargets.PeriodicCircleHomotopyWinding.liftedSquare`, `exp_liftedSquare`) and apply
`_aux_corners`. -/
lemma apm_t91J03_crossing (α β : C(I, ℝ × ℝ))
    (hα : ∀ s, 0 ≤ (α s).2 ∧ (α s).2 ≤ 1) (hβ0 : (β 0).2 = 0) (hβ1 : (β 1).2 = 1)
    (hl : ∀ t, (α 0).1 < (β t).1) (hr : ∀ t, (β t).1 < (α 1).1) :
    ∃ s t, α s = β t := by
  sorry

/-- The periodic lift of a circle self-map, by `Circle.isCoveringMap_exp` and
`IsCoveringMap.existsUnique_continuousMap_lifts` on `ℝ` (or `CircleExponentialPathLift`).
`θ (t + 1) - θ t` is a continuous multiple of `2π`, so it is constant, equal to `2π d`. -/
lemma apm_t91J03_periodic_lift (c : C(Circle, Circle)) :
    ∃ (θ : C(ℝ, ℝ)) (d : ℤ), (∀ t, Circle.exp (θ t) = c (Circle.exp (2 * Real.pi * t))) ∧
      ∀ t, θ (t + 1) = θ t + 2 * Real.pi * d := by
  sorry

/-- The lift displacement is the action on `H₁`. Both sides are additive in `a`, and `H₁(Circle)`
is generated by the Hurewicz image of the positive loop
(`DegreeOneHurewiczSurjective.fundamentalGroupH1Hom_surjective`,
`CircleHurewiczIsomorphism`). `fundamentalGroupH1Hom_naturality` (used in
`FiniteFreeHurewiczNaturality`) moves `c` onto the loop; the lift `θ` shows that `c ∘ loop` is
`d` times the positive loop in `H₁`, using free homotopy of loops to change basepoint. -/
lemma apm_t91J03_degree (c : C(Circle, Circle)) (θ : C(ℝ, ℝ)) (d : ℤ)
    (hθ : ∀ t, Circle.exp (θ t) = c (Circle.exp (2 * Real.pi * t)))
    (hper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * d)
    (orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ) (a : apm_t91J03_H1Circle) :
    orientation.hom
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom c) a) = d * orientation.hom a := by
  sorry

/-- The lift and its deck translate are disjoint when `2 ≤ |d|`. Equal points give equal `gamma`
values (`Circle.exp` of equal angles; equal heights), so `exp(2πs) = exp(2πt)` by injectivity,
so `s = t + m` for an integer `m`, so `θ s = θ t + 2π d m`, so `d m = 1`, impossible. -/
lemma apm_t91J03_disjoint (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding (gamma : Circle → apm_t91J03_Annulus))
    (θ : C(ℝ, ℝ)) (d : ℤ)
    (hθ : ∀ t, Circle.exp (θ t) =
      apm_t91J03_circleMap gamma (Circle.exp (2 * Real.pi * t)))
    (hper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * d) (hd : 2 ≤ d.natAbs) (s t : ℝ)
    (hx : θ s = θ t + 2 * Real.pi)
    (hh : apm_t91J03_height gamma (Circle.exp (2 * Real.pi * s)) =
      apm_t91J03_height gamma (Circle.exp (2 * Real.pi * t))) : False := by
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  -- Integer-shift law for `θ`, from one-step periodicity `hper`.
  have key : ∀ (k : ℤ) (u : ℝ),
      θ (u + (k : ℝ)) = θ u + 2 * Real.pi * (d : ℝ) * k := by
    intro k
    induction k using Int.induction_on with
    | zero => intro u; simp
    | succ n ih =>
        intro u
        rw [show u + ((↑n + 1 : ℤ) : ℝ) = (u + ((↑n : ℤ) : ℝ)) + 1 by push_cast; ring,
          hper, ih u]
        push_cast
        ring
    | pred n ih =>
        intro u
        have hb : θ ((u + ((-↑n : ℤ) : ℝ)) - 1) =
            θ (u + ((-↑n : ℤ) : ℝ)) - 2 * Real.pi * d := by
          have h := hper (u + ((-↑n : ℤ) : ℝ) - 1)
          rw [show u + ((-↑n : ℤ) : ℝ) - 1 + 1 = u + ((-↑n : ℤ) : ℝ) by ring] at h
          linarith
        rw [show u + ((-↑n - 1 : ℤ) : ℝ) = (u + ((-↑n : ℤ) : ℝ)) - 1 by
          push_cast; ring, hb, ih u]
        push_cast
        ring
  -- The two circle points have equal `gamma` values, hence are equal.
  have hexp : Circle.exp (θ s) = Circle.exp (θ t) := by
    rw [hx]
    exact Circle.exp_add_two_pi _
  have hproj : apm_t91J03_circleMap gamma (Circle.exp (2 * Real.pi * s)) =
      apm_t91J03_circleMap gamma (Circle.exp (2 * Real.pi * t)) := by
    rw [← hθ s, ← hθ t, hexp]
  have hval : gamma (Circle.exp (2 * Real.pi * s)) =
      gamma (Circle.exp (2 * Real.pi * t)) := by
    apply Prod.ext
    · exact hproj
    · exact Subtype.ext hh
  have hzw : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
    hgamma.injective hval
  -- So `s = t + m` for an integer `m`.
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hzw
  have hsm : s = t + (m : ℝ) := by
    have h2 : 2 * Real.pi * s = 2 * Real.pi * (t + (m : ℝ)) := by
      linarith [hm]
    exact mul_left_cancel₀ hπ h2
  -- Then `hx` forces `d * m = 1`, contradicting `2 ≤ |d|`.
  rw [hsm, key m t] at hx
  have hdm : d * m = 1 := by
    have hmul : (d : ℝ) * (m : ℝ) = 1 := by
      have h2 : 2 * Real.pi * ((d : ℝ) * (m : ℝ)) = 2 * Real.pi * 1 := by
        linarith [hx]
      exact mul_left_cancel₀ hπ h2
    exact_mod_cast hmul
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdm with h | h <;>
    subst h <;> norm_num at hd

open unitInterval in
/-- The barrier. With `h t` the height of `gamma (exp 2πt)` and `L₁ t = (θ t + 2π, h t)`, take a
lowest and a highest point of `L₁` on `[0, 1]` (compactness; periodicity makes them global).
`β` is the vertical segment from the bottom edge up to the lowest point, the arc of `L₁`
between them, then the vertical segment to the top edge. It misses `L₀`: on the arc by
`_disjoint`, and on the segments because `L₀` has the same height range as `L₁`, and at equal height
the endpoint of the segment is a point of `L₁`, not of `L₀`. Concatenate with `Path.trans` or
explicit piecewise maps on `I`. -/
-- BEGIN SEAT AREA
lemma apm_t91J03_no_wind_aux_barrier (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding (gamma : Circle → apm_t91J03_Annulus))
    (θ : C(ℝ, ℝ)) (d : ℤ)
    (hθ : ∀ t, Circle.exp (θ t) =
      apm_t91J03_circleMap gamma (Circle.exp (2 * Real.pi * t)))
    (hper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * d) (hd : 2 ≤ d.natAbs) :
    ∃ β : C(I, ℝ × ℝ), (β 0).2 = 0 ∧ (β 1).2 = 1 ∧ ∀ s t,
      β t ≠ (θ s, apm_t91J03_height gamma (Circle.exp (2 * Real.pi * s))) := by
  sorry
-- END SEAT AREA

open unitInterval in
/-- An embedded circle winds at most once. Otherwise take the barrier `β`, and `α`, the affine
reparametrization to `I` of `s ↦ (θ s, h s)` on a long interval `[-N, N]` (reversed when `d < 0`):
`θ (t + k) = θ t + 2π d k` is unbounded, and `β` has compact image, so `α 0` lies left of `β`
and `α 1` right of it. `apm_t91J03_crossing` then contradicts the barrier. -/
lemma apm_t91J03_no_wind (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding (gamma : Circle → apm_t91J03_Annulus))
    (θ : C(ℝ, ℝ)) (d : ℤ)
    (hθ : ∀ t, Circle.exp (θ t) =
      apm_t91J03_circleMap gamma (Circle.exp (2 * Real.pi * t)))
    (hper : ∀ t, θ (t + 1) = θ t + 2 * Real.pi * d) : d.natAbs ≤ 1 := by
  sorry

/-- **LIBRARY: classification of embedded circles in the closed annulus.**

For every choice of generator of `H₁(S¹; ℤ)`, the first projection of an
embedded annular circle acts by multiplication by `-1`, `0`, or `1`.

This is the genuine missing topological foundation.  One proof lifts the
embedded circle to the closed strip and uses Jordan separation to show that a
deck translate cannot cross it; equivalently, an essential simple closed curve
in an annulus represents a primitive homology class. -/
lemma apm_t91J03_embedded_annular_circle_homology_bound
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ) :
    ∃ m : ℤ, m.natAbs ≤ 1 ∧
      ∀ a : apm_t91J03_H1Circle,
        orientation.hom (apm_t91J03_H1Map gamma a) =
          m * orientation.hom a := by
  obtain ⟨θ, d, hθ, hper⟩ := apm_t91J03_periodic_lift (apm_t91J03_circleMap gamma)
  exact ⟨d, apm_t91J03_no_wind gamma hgamma θ d hθ hper,
    fun a => apm_t91J03_degree _ θ d hθ hper orientation a⟩

/-- A scalar describing an endomorphism of a rank-one module is unique.
This is deliberately independent of the annulus classification lemma. -/
lemma apm_t91J03_rank_one_scalar_unique
    (f : apm_t91J03_H1Circle ⟶ ModuleCat.of ℤ ℤ)
    (orientation : apm_t91J03_H1Circle ≅ ModuleCat.of ℤ ℤ)
    (n m : ℤ)
    (hn : ∀ a : apm_t91J03_H1Circle,
      f a = n * orientation.hom a)
    (hm : ∀ a : apm_t91J03_H1Circle,
      f a = m * orientation.hom a) :
    n = m := by
  have h := (hn (orientation.inv 1)).symm.trans (hm (orientation.inv 1))
  simpa using h

/-- An integer of absolute value two cannot have absolute value at most one.
Kept separate so this leaf has no topological dependencies. -/
lemma apm_t91J03_natAbs_two_not_le_one
    (n : ℤ) (htwo : n.natAbs = 2) (hle : n.natAbs ≤ 1) : False := by
  omega

/-- An embedded annular circle cannot have homological winding of absolute
value two.  This assembly is sorry-free; its three inputs can be proved in
parallel. -/
lemma apm_t91J03_no_embedded_winding_two
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (n : ℤ) (hn : apm_t91J03_HasWindingNumber gamma n)
    (habs : n.natAbs = 2) : False := by
  obtain ⟨orientation, hn⟩ := hn
  obtain ⟨m, hm_bound, hm⟩ :=
    apm_t91J03_embedded_annular_circle_homology_bound gamma hgamma orientation
  have hnm : n = m := apm_t91J03_rank_one_scalar_unique
    (apm_t91J03_H1Map gamma ≫ orientation.hom) orientation n m hn hm
  subst m
  exact apm_t91J03_natAbs_two_not_le_one n habs hm_bound

/-- An embedded circle in the closed annulus whose first projection has
homological degree of absolute value two would contain two distinct parameter
points with the same annular coordinates.  The hypotheses are inconsistent by
the annular-circle classification above, so the collision follows. -/
theorem apm_t91J03_winding_two_forces_annulus_collision
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (n : ℤ) (hn : apm_t91J03_HasWindingNumber gamma n)
    (habs : n.natAbs = 2) :
    ∃ z w : Circle, z ≠ w ∧
      apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w ∧
      apm_t91J03_height gamma z = apm_t91J03_height gamma w := by
  exact False.elim
    (apm_t91J03_no_embedded_winding_two gamma hgamma n hn habs)

/-- The final contradiction, once the geometric collision is available. -/
lemma apm_t91J03_no_two_of_forced_fiber_collision
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus))
    (hcollision : ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n →
      n.natAbs = 2 →
      ∃ z w : Circle, z ≠ w ∧
        apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w ∧
        apm_t91J03_height gamma z = apm_t91J03_height gamma w) :
    ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2 := by
  intro n hn habs
  obtain ⟨z, w, hzw, hprojection, hheight⟩ := hcollision n hn habs
  exact (apm_t91J03_height_ne_of_circleMap_eq gamma hgamma hzw hprojection)
    hheight

theorem apm_t91j03
    (gamma : C(Circle, apm_t91J03_Annulus))
    (hgamma : Topology.IsEmbedding
      (gamma : Circle → apm_t91J03_Annulus)) :
    ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2 := by
  apply apm_t91J03_no_two_of_forced_fiber_collision gamma hgamma
  intro n hn habs
  exact apm_t91J03_winding_two_forces_annulus_collision gamma hgamma n hn habs

#print axioms apm_t91j03

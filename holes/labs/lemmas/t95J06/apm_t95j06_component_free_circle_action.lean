import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SurfaceClassification

open CategoryTheory
open scoped Manifold

noncomputable section

abbrev apm_t95j06_C3 := EuclideanSpace ℂ (Fin 3)
abbrev apm_t95j06_S5 := Metric.sphere (0 : apm_t95j06_C3) 1

def apm_t95j06_isHopfFlow
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5) : Prop :=
  ∀ zt, (H zt).1 = Complex.exp (Complex.I * zt.2) • zt.1.1

def apm_t95j06_T : Set apm_t95j06_S5 :=
  {z | ∃ θ φ : ℝ,
    z.1 = WithLp.toLp 2
      ![(Real.cos θ : ℂ) * Complex.exp (Complex.I * φ),
        (Real.sin θ : ℂ) * Complex.exp (Complex.I * φ), 0]}

def apm_t95j06_IsInvariant
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (F : Set apm_t95j06_S5) : Prop :=
  ∀ z ∈ F, ∀ t : ℝ, H (z, t) ∈ F

abbrev apm_t95j06_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t95j06_I2 := 𝓘(ℝ, apm_t95j06_E2)

abbrev apm_t95j06_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t95j06_IsCompactOrientableSurface
    (F : Set apm_t95j06_S5) : Prop :=
  IsCompact F ∧
  ∃ charts : ChartedSpace apm_t95j06_E2 F,
    let _ := charts
    IsManifold apm_t95j06_I2 (⊤ : ℕ∞) F ∧
    ∀ x : F,
      Nonempty
        (apm_t95j06_H 2 {y : F // y ∈ connectedComponent x} ≅
          ModuleCat.of ℤ ℤ)

def apm_t95j06_EveryComponentDiffeomorphicToTorus
    (F : Set apm_t95j06_S5) : Prop :=
  ∀ x : F,
    Nonempty ({y : F // y ∈ connectedComponent x} ≃ₜ Circle × Circle)

/-- Concrete data of a jointly continuous free circle action.  This definition
records action data, rather than baking in the desired torus conclusion. -/
def apm_t95j06_HasFreeContinuousCircleAction
    (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ act : Circle × X → X,
    Continuous act ∧
    (∀ x, act (1, x) = x) ∧
    (∀ g h x, act (g, act (h, x)) = act (g * h, x)) ∧
    (∀ g x, act (g, x) = x → g = 1)

lemma apm_t95j06_T_invariant
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H) :
    apm_t95j06_IsInvariant H apm_t95j06_T := by
  intro z hz t
  rcases hz with ⟨θ, φ, hz⟩
  refine ⟨θ, φ + t, ?_⟩
  rw [hH, hz]
  ext i
  fin_cases i <;> simp [PiLp.smul_apply]
  · rw [mul_add, Complex.exp_add]
    ring
  · rw [mul_add, Complex.exp_add]
    ring

lemma apm_t95j06_flow_periodic
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H) (z : apm_t95j06_S5) (t : ℝ) :
    H (z, t + 2 * Real.pi) = H (z, t) := by
  apply Subtype.ext
  rw [hH, hH]
  congr 1
  rw [show Complex.I * (↑(t + 2 * Real.pi) : ℂ) =
      Complex.I * (t : ℂ) + Complex.I * (2 * Real.pi : ℝ) by push_cast; ring,
    Complex.exp_add]
  simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.exp_two_pi_mul_I

lemma apm_t95j06_flow_zero
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H) (z : apm_t95j06_S5) :
    H (z, 0) = z := by
  apply Subtype.ext
  rw [hH]
  simp

lemma apm_t95j06_flow_add
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H) (z : apm_t95j06_S5) (s t : ℝ) :
    H (H (z, s), t) = H (z, s + t) := by
  apply Subtype.ext
  rw [hH, hH, hH]
  rw [show Complex.I * (↑(s + t) : ℂ) =
      Complex.I * (s : ℂ) + Complex.I * (t : ℂ) by push_cast; ring,
    Complex.exp_add]
  simp only [smul_smul]
  ring_nf

/-- The Hopf scalar action restricts to a free continuous circle action on
each connected component of an invariant set. -/
-- BEGIN SEAT AREA
theorem apm_t95j06_component_free_circle_action
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H)
    (F : Set apm_t95j06_S5)
    (hF_invariant : apm_t95j06_IsInvariant H F) :
    ∀ x : F,
      apm_t95j06_HasFreeContinuousCircleAction
        {y : F // y ∈ connectedComponent x} := by
  intro x
  let actF : Circle × F → F := fun gy =>
    ⟨H (gy.2.1, Complex.arg (gy.1 : ℂ)),
      hF_invariant gy.2.1 gy.2.2 _⟩
  have hactF_cont : Continuous actF := by
    apply continuous_induced_rng.2
    apply continuous_induced_rng.2
    rw [continuous_iff_continuousAt]
    intro gy
    apply Continuous.continuousAt
    have : Continuous (fun gy : Circle × F =>
        (gy.1 : ℂ) • gy.2.1.1) := by fun_prop
    rw [show ((fun q : apm_t95j06_S5 => q.1) ∘ Subtype.val ∘ actF) = (fun gy : Circle × F =>
        (gy.1 : ℂ) • gy.2.1.1) by
      funext gy
      simp only [Function.comp_apply, actF]
      rw [hH]
      rw [show
        Complex.exp (Complex.I * (Complex.arg (gy.1 : ℂ) : ℂ)) = (gy.1 : ℂ) by
          rw [show Complex.I * (Complex.arg (gy.1 : ℂ) : ℂ) =
              (Complex.arg (gy.1 : ℂ) : ℂ) * Complex.I by ring,
            ← Circle.coe_exp, Circle.exp_arg]]]
    exact this
  have horbit (g : Circle) : actF (g, x) ∈ connectedComponent x := by
    let f : ℝ → F := fun t => ⟨H (x.1, t), hF_invariant x.1 x.2 t⟩
    have hfcont : Continuous f := by
      apply continuous_induced_rng.2
      apply continuous_induced_rng.2
      rw [continuous_iff_continuousAt]
      intro t
      apply Continuous.continuousAt
      have : Continuous (fun t : ℝ =>
          Complex.exp (Complex.I * (t : ℂ)) • x.1.1) := by fun_prop
      rw [show ((fun q : apm_t95j06_S5 => q.1) ∘ Subtype.val ∘ f) = (fun t : ℝ =>
          Complex.exp (Complex.I * (t : ℂ)) • x.1.1) by
        funext t
        exact hH (x.1, t)]
      exact this
    have himg : IsConnected (Set.range f) :=
      isConnected_range hfcont
    apply himg.subset_connectedComponent
      (show x ∈ Set.range f from ⟨0, Subtype.ext (apm_t95j06_flow_zero H hH x.1)⟩)
    refine ⟨Complex.arg (g : ℂ), ?_⟩
    rfl
  let act : Circle × {y : F // y ∈ connectedComponent x} →
      {y : F // y ∈ connectedComponent x} := fun gy => by
    refine ⟨actF (gy.1, gy.2.1), ?_⟩
    have hc := (isConnected_connectedComponent (x := x)).image
      (fun y : F => actF (gy.1, y))
      (hactF_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hm := hc.subset_connectedComponent
      (show actF (gy.1, x) ∈ (fun y : F => actF (gy.1, y)) '' connectedComponent x from
        ⟨x, mem_connectedComponent, rfl⟩)
      ⟨gy.2.1, gy.2.2, rfl⟩
    rw [← connectedComponent_eq (horbit gy.1)] at hm
    exact hm
  refine ⟨act, ?_, ?_, ?_, ?_⟩
  · apply continuous_induced_rng.2
    exact hactF_cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simp [act, actF, apm_t95j06_flow_zero H hH]
  · intro g h y
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simp only [act, actF]
    rw [hH, hH, hH]
    have hexp (k : Circle) :
        Complex.exp (Complex.I * (Complex.arg (k : ℂ) : ℂ)) = (k : ℂ) := by
      rw [show Complex.I * (Complex.arg (k : ℂ) : ℂ) =
          (Complex.arg (k : ℂ) : ℂ) * Complex.I by ring,
        ← Circle.coe_exp, Circle.exp_arg]
    rw [hexp, hexp, hexp]
    simp [mul_smul]
  · intro g y hgy
    have hv : y.1.1.1 ≠ 0 := by
      intro hz
      have hs := y.1.1.2
      rw [Metric.mem_sphere, dist_zero_right, hz, norm_zero] at hs
      norm_num at hs
    have hs : (g : ℂ) • y.1.1.1 = y.1.1.1 := by
      have := congrArg (fun q => q.1.1.1) hgy
      change (H (y.1.1, Complex.arg (g : ℂ))).1 = y.1.1.1 at this
      rw [hH] at this
      simpa only [hH, show
          Complex.exp (Complex.I * (Complex.arg (g : ℂ) : ℂ)) = (g : ℂ) by
            rw [show Complex.I * (Complex.arg (g : ℂ) : ℂ) =
                (Complex.arg (g : ℂ) : ℂ) * Complex.I by ring,
              ← Circle.coe_exp, Circle.exp_arg]] using this
    apply Circle.coe_injective
    apply sub_eq_zero.mp
    rw [← smul_eq_zero_iff_left hv]
    change ((g : ℂ) - 1) • y.1.1.1 = 0
    rw [sub_smul, hs, one_smul, sub_self]
-- END SEAT AREA

/-- LIBRARY: a compact orientable topological surface with a free continuous
circle action has every connected component homeomorphic to the torus. -/
theorem apm_t95j06_freeCircleAction_surface_classification
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hact : ∀ x : F,
      apm_t95j06_HasFreeContinuousCircleAction
        {y : F // y ∈ connectedComponent x}) :
    apm_t95j06_EveryComponentDiffeomorphicToTorus F := by
  sorry

theorem apm_t95J06_bridge_1
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H)
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hF_invariant : apm_t95j06_IsInvariant H F) :
    apm_t95j06_EveryComponentDiffeomorphicToTorus F := by
  apply apm_t95j06_freeCircleAction_surface_classification F hF
  exact apm_t95j06_component_free_circle_action H hH F hF_invariant

theorem apm_t95j06
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H) :
    apm_t95j06_IsInvariant H apm_t95j06_T ∧
    ∀ F : Set apm_t95j06_S5,
      apm_t95j06_IsCompactOrientableSurface F →
      apm_t95j06_IsInvariant H F →
      apm_t95j06_EveryComponentDiffeomorphicToTorus F := by
  constructor
  · exact apm_t95j06_T_invariant H hH
  · exact fun F hF hFinv => apm_t95J06_bridge_1 H hH F hF hFinv

#print axioms apm_t95j06

import Mathlib
import ConstructionTargets.t00J02Closure
import ConstructionTargets.SingularHomologyHomotopy
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.CollaredConnectedSumHomology

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

/-- Invariance under the literal scalar Circle action on the ambient sphere,
stated without choosing an `SMul` instance on a subtype. -/
def apm_t95j06_IsCircleInvariant (F : Set apm_t95j06_S5) : Prop :=
  ∀ z ∈ F, ∀ g : Circle, ∃ w ∈ F, w.1 = (g : ℂ) • z.1

/-- A concrete principal Circle-bundle interface.  The global free transitive
Circle action on every fibre excludes the reflected-fibre mapping torus; the
local product charts are fibre-preserving and Circle-equivariant (claude-14 review: an
abstract homeomorphism `{x // proj x ∈ U} ≃ₜ U × Circle` would not tie the chart to `proj`). -/
structure apm_t95j06_PrincipalCircleBundle
    (X B : Type*) [TopologicalSpace X] [TopologicalSpace B] where
  proj : X → B
  act : Circle × X → X
  continuous_proj : Continuous proj
  continuous_act : Continuous act
  one_act : ∀ x, act (1, x) = x
  mul_act : ∀ g h x, act (g, act (h, x)) = act (g * h, x)
  free : ∀ g x, act (g, x) = x → g = 1
  invariant : ∀ g x, proj (act (g, x)) = proj x
  orbit_fiber : ∀ x y, proj x = proj y → ∃ g, act (g, x) = y
  surjective_proj : Function.Surjective proj
  local_trivial : ∀ b, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ φ : {x : X // proj x ∈ U} ≃ₜ U × Circle,
      (∀ x, ((φ x).1 : B) = proj x.1) ∧
      ∀ g x, (φ ⟨act (g, x.1), by rw [invariant]; exact x.2⟩).2 = g * (φ x).2

/-- A space is locally a real line, in the exact chart form needed by the
compact one-manifold classification leaf. -/
def apm_t95j06_IsLocallyRealLine (B : Type*) [TopologicalSpace B] : Prop :=
  ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ V : Set ℝ, IsOpen V ∧ Nonempty (U ≃ₜ V)

/-- **Hopf quotient leaf (estimated 250--450 lines).**  The explicit coordinate
slices `z_k ≠ 0`, normalized by `conj z_k / |z_k|`, cover the sphere and
give the orbit quotient of every component the displayed principal-bundle
presentation.  The quotient is compact, connected, Hausdorff and second
countable.

Proof route: use `Complex.continuous_abs`, continuity of inversion away from
zero, `Circle.coe_exp`/`Circle.exp_arg`, and compact-to-Hausdorff quotient
facts.  The cover follows because a norm-one vector cannot have all three
coordinates zero.  Empty `F` is vacuous; each indexed component is nonempty.
Freeness uses the nonzero vector, and compactness is essential for the stated
base compactness. -/
structure apm_t95j06_hopf_slices_component_principalBundle_aux_Core
    (F : Set apm_t95j06_S5) (x : F) (B : Type*) [TopologicalSpace B] where
  proj : {y : F // y ∈ connectedComponent x} → B
  act : Circle × {y : F // y ∈ connectedComponent x} →
    {y : F // y ∈ connectedComponent x}
  continuous_proj : Continuous proj
  quotient_proj : Topology.IsQuotientMap proj
  open_proj : IsOpenMap proj
  continuous_act : Continuous act
  one_act : ∀ y, act (1, y) = y
  mul_act : ∀ g h y, act (g, act (h, y)) = act (g * h, y)
  free : ∀ g y, act (g, y) = y → g = 1
  invariant : ∀ g y, proj (act (g, y)) = proj y
  orbit_fiber : ∀ y z, proj y = proj z → ∃ g, act (g, y) = z
  surjective_proj : Function.Surjective proj
  scalar_act : ∀ g y, (act (g, y)).1.1.1 = (g : ℂ) • y.1.1.1

/-- **Remaining sub-leaf, quotient core (estimated 180--300 lines).**  In
words: the scalar Circle action on a compact connected component has an orbit
quotient which is compact, connected, Hausdorff and second countable, and the
quotient map has exactly the scalar orbits as fibres.

Why true: put the quotient topology on the orbit relation.  Compactness and
connectedness descend along the quotient map.  The action relation is closed
because it is the image of the compact Circle parameter in the Hausdorff
component, giving Hausdorff quotient; the quotient map is open, so
`Topology.IsQuotientMap.secondCountableTopology` supplies second countability.
The chosen component is nonempty.  A constant action cannot meet `scalar_act`
and `free`, and compactness is used essentially for closedness of the orbit
relation. -/
structure apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_Action
    (F : Set apm_t95j06_S5) (x : F) where
  act : Circle × {y : F // y ∈ connectedComponent x} →
    {y : F // y ∈ connectedComponent x}
  continuous_act : Continuous act
  one_act : ∀ y, act (1, y) = y
  mul_act : ∀ g h y, act (g, act (h, y)) = act (g * h, y)
  free : ∀ g y, act (g, y) = y → g = 1
  scalar_act : ∀ g y, (act (g, y)).1.1.1 = (g : ℂ) • y.1.1.1

/-- **Remaining sub-leaf, component action (estimated 100--180 lines).**  In
words: scalar multiplication restricts to a continuous free Circle action on
each connected component of a Circle-invariant subset of the unit sphere.

Why true: `hinv` gives membership in `F`.  For fixed `g`, the scalar orbit of
`y` is connected because it is the continuous image of connected `Circle`;
it contains `y` at `1`, hence stays in `connectedComponent x`.  Continuity and
the action laws descend from complex scalar multiplication.  If `g • y = y`,
some coordinate of the norm-one vector `y` is nonzero, so cancellation gives
`g = 1`.  Empty components do not occur because they are indexed by `x`. -/
def apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul
    (g : Circle) (z : apm_t95j06_S5) : apm_t95j06_S5 :=
  ⟨(g : ℂ) • z.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul]
    have hz : ‖z.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using z.2
    rw [hz]
    simp⟩

@[simp] theorem apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul_val
    (g : Circle) (z : apm_t95j06_S5) :
    (apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul g z).1 =
      (g : ℂ) • z.1 := rfl

theorem apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul_continuous :
    Continuous (fun p : Circle × apm_t95j06_S5 ↦
      apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul p.1 p.2) := by
  apply continuous_induced_rng.2
  fun_prop

theorem apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_componentAction
    (F : Set apm_t95j06_S5) (hinv : apm_t95j06_IsCircleInvariant F) (x : F) :
    Nonempty
      (apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_Action F x) := by
  let sf : Circle → F → F := fun g y ↦
    ⟨apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul g y.1, by
      obtain ⟨w, hw, heq⟩ := hinv y.1 y.2 g
      have hweq : w =
          apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul g y.1 := by
        apply Subtype.ext
        exact heq
      exact hweq ▸ hw⟩
  have hsf_cont : Continuous (fun p : Circle × F ↦ sf p.1 p.2) := by
    apply continuous_induced_rng.2
    exact apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hsf_one (y : F) : sf 1 y = y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [sf, apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul]
  have hsf_mul (g h : Circle) (y : F) : sf g (sf h y) = sf (g * h) y := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [sf,
      apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul_val]
    rw [← mul_smul]
    rfl
  have hcomponent (g : Circle)
      (y : {y : F // y ∈ connectedComponent x}) : sf g y.1 ∈ connectedComponent x := by
    let f : ℝ → F := fun t ↦ sf (Circle.exp (t * Complex.arg (g : ℂ))) y.1
    have hf : Continuous f := by
      simpa only [f, Function.comp_apply] using
        hsf_cont.comp ((Circle.exp.continuous.comp
          (continuous_id.mul continuous_const)).prodMk continuous_const)
    have hc : IsConnected (Set.range f) := isConnected_range hf
    have hy : y.1 ∈ Set.range f := by
      refine ⟨0, ?_⟩
      simpa [f] using hsf_one y.1
    have hg : sf g y.1 ∈ Set.range f := by
      refine ⟨1, ?_⟩
      simp only [f, one_mul, Circle.exp_arg]
    have hmem := hc.subset_connectedComponent hy hg
    have heq : connectedComponent (y.1 : F) = connectedComponent x :=
      (connectedComponent_eq y.2).symm
    simpa only [heq] using hmem
  let act : Circle × {y : F // y ∈ connectedComponent x} →
      {y : F // y ∈ connectedComponent x} := fun p ↦
    ⟨sf p.1 p.2.1, hcomponent p.1 p.2⟩
  refine ⟨{
    act := act
    continuous_act := ?_
    one_act := ?_
    mul_act := ?_
    free := ?_
    scalar_act := ?_ }⟩
  · apply continuous_induced_rng.2
    exact hsf_cont.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · intro y
    apply Subtype.ext
    exact hsf_one y.1
  · intro g h y
    apply Subtype.ext
    exact hsf_mul g h y.1
  · intro g y hgy
    have hs : (g : ℂ) • y.1.1.1 = y.1.1.1 := by
      have := congrArg (fun q ↦ q.1.1.1) hgy
      simpa only [act, sf,
        apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_sphereSmul_val]
        using this
    have hy0 : y.1.1.1 ≠ 0 := by
      intro hy
      have hn := y.1.1.2
      rw [Metric.mem_sphere, dist_zero_right, hy, norm_zero] at hn
      norm_num at hn
    apply Circle.coe_injective
    apply sub_eq_zero.mp
    rw [← smul_eq_zero_iff_left hy0]
    change ((g : ℂ) - 1) • y.1.1.1 = 0
    rw [sub_smul, hs, one_smul, sub_self]
  · intro g y
    rfl

/-- **Remaining sub-leaf, compact orbit quotient (estimated 140--240 lines).**
In words: the orbit space of the supplied continuous free Circle action on a
compact connected component is compact, connected, Hausdorff and second
countable, with an open quotient projection and precisely the action orbits
as fibres.

Why true: use `MulAction.orbitRel.Quotient` with its quotient topology.  The
projection is open because the saturation of `U` is the union of the open
translates `g • U`.  The orbit relation is closed: it is the image of compact
`Circle × component` under `(g,y) ↦ (y,g•y)` into a Hausdorff product.
The closed equivalence relation gives a Hausdorff quotient.  Compactness and
connectedness descend along the surjective quotient map, and
`Topology.IsQuotientMap.secondCountableTopology` applies to the open quotient
of the second-countable component. -/
theorem apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_orbitQuotient
    (F : Set apm_t95j06_S5) (hF : apm_t95j06_IsCompactOrientableSurface F)
    (x : F)
    (A : apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_Action F x) :
    ∃ (B : Type) (tB : TopologicalSpace B),
      @CompactSpace B tB ∧ @ConnectedSpace B tB ∧ @T2Space B tB ∧
      @SecondCountableTopology B tB ∧
      Nonempty (@apm_t95j06_hopf_slices_component_principalBundle_aux_Core
        F x B tB) := by
  let X := {y : F // y ∈ connectedComponent x}
  letI : SMul Circle X := ⟨fun g y ↦ A.act (g, y)⟩
  letI : MulAction Circle X := {
    one_smul y := A.one_act y
    mul_smul g h y := (A.mul_act g h y).symm }
  have hFc : CompactSpace F := isCompact_iff_compactSpace.mp hF.1
  letI : CompactSpace F := hFc
  have hXc : CompactSpace X :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : CompactSpace X := hXc
  have hXconn : ConnectedSpace X :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : ConnectedSpace X := hXconn
  letI : ContinuousConstSMul Circle X := {
    continuous_const_smul g :=
      A.continuous_act.comp (continuous_const.prodMk continuous_id) }
  letI : ProperSMul Circle X := {
    isProperMap_smul_pair :=
      (A.continuous_act.prodMk continuous_snd).isProperMap }
  letI orbitSetoid : Setoid X := MulAction.orbitRel Circle X
  let B := Quotient orbitSetoid
  let tB : TopologicalSpace B := inferInstance
  letI : TopologicalSpace B := tB
  have hBc : CompactSpace B := inferInstance
  have hBconn : ConnectedSpace B := inferInstance
  have hB2 : T2Space B := inferInstance
  have hBsc : SecondCountableTopology B :=
    ContinuousConstSMul.secondCountableTopology
  refine ⟨B, tB, hBc, hBconn, hB2, hBsc, ⟨?_⟩⟩
  let proj : X → B := Quotient.mk'
  exact
    { proj := proj
      act := A.act
      continuous_proj := continuous_quot_mk
      quotient_proj := isQuotientMap_quotient_mk'
      open_proj := isOpenMap_quotient_mk'_mul
      continuous_act := A.continuous_act
      one_act := A.one_act
      mul_act := A.mul_act
      free := A.free
      invariant := by
        intro g y
        exact Quotient.sound ⟨g, rfl⟩
      orbit_fiber := by
        intro y z hyz
        have hyz' : y ∈ MulAction.orbit Circle z := Quotient.exact hyz
        exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp hyz')
      surjective_proj := Quotient.mk'_surjective
      scalar_act := A.scalar_act }

theorem apm_t95j06_hopf_slices_component_principalBundle_aux_core
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hinv : apm_t95j06_IsCircleInvariant F) :
    ∀ x : F, ∃ (B : Type) (tB : TopologicalSpace B),
      @CompactSpace B tB ∧ @ConnectedSpace B tB ∧ @T2Space B tB ∧
      @SecondCountableTopology B tB ∧
      Nonempty (@apm_t95j06_hopf_slices_component_principalBundle_aux_Core
        F x B tB) := by
  intro x
  obtain ⟨A⟩ :=
    apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_componentAction
      F hinv x
  exact apm_t95j06_hopf_slices_component_principalBundle_aux_core_aux_orbitQuotient
    F hF x A

abbrev apm_t95j06_hopf_component
    (F : Set apm_t95j06_S5) (x : F) :=
  {y : F // y ∈ connectedComponent x}

def apm_t95j06_hopf_coordinate
    {F : Set apm_t95j06_S5} {x : F} (k : Fin 3)
    (y : apm_t95j06_hopf_component F x) : ℂ :=
  y.1.1.1 k

def apm_t95j06_hopf_slice
    {F : Set apm_t95j06_S5} {x : F} (k : Fin 3) :
    Set (apm_t95j06_hopf_component F x) :=
  {y | apm_t95j06_hopf_coordinate k y ≠ 0}

/-- Every point of the unit sphere has a nonzero complex coordinate. -/
lemma apm_t95j06_hopf_exists_coordinate_ne_zero
    {F : Set apm_t95j06_S5} {x : F}
    (y : apm_t95j06_hopf_component F x) :
    ∃ k : Fin 3, apm_t95j06_hopf_coordinate k y ≠ 0 := by
  by_contra h
  push_neg at h
  have hyzero : y.1.1.1 = 0 := by
    ext k
    exact h k
  have hsphere := y.1.1.2
  rw [Metric.mem_sphere, dist_zero_right, hyzero, norm_zero] at hsphere
  norm_num at hsphere

/-- A nonzero-coordinate Hopf slice is open in the component. -/
lemma apm_t95j06_hopf_slice_isOpen
    {F : Set apm_t95j06_S5} {x : F} (k : Fin 3) :
    IsOpen (apm_t95j06_hopf_slice (F := F) (x := x) k) := by
  have hcoord : Continuous
      (apm_t95j06_hopf_coordinate (F := F) (x := x) k) := by
    change Continuous (fun y : apm_t95j06_hopf_component F x => y.1.1.1 k)
    fun_prop
  rw [show apm_t95j06_hopf_slice (F := F) (x := x) k =
      apm_t95j06_hopf_coordinate k ⁻¹' ({0}ᶜ : Set ℂ) by
    ext y
    simp [apm_t95j06_hopf_slice]]
  exact isClosed_singleton.isOpen_compl.preimage hcoord

/-- The scalar action preserves every nonzero-coordinate slice. -/
lemma apm_t95j06_hopf_slice_invariant
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) (g : Circle) (y : apm_t95j06_hopf_component F x)
    (hy : y ∈ apm_t95j06_hopf_slice (F := F) (x := x) k) :
    Q.act (g, y) ∈ apm_t95j06_hopf_slice (F := F) (x := x) k := by
  change (Q.act (g, y)).1.1.1 k ≠ 0
  have hcoord := congrArg (fun v : apm_t95j06_C3 => v k) (Q.scalar_act g y)
  simp only [PiLp.smul_apply] at hcoord
  rw [hcoord]
  have hg : (g : ℂ) ≠ 0 := by
    intro hg
    have hnorm : ‖(g : ℂ)‖ = 1 := by
      rw [← mem_sphere_zero_iff_norm]
      exact g.property
    simp [hg] at hnorm
  exact smul_ne_zero hg hy

/-- The normalized phase of a nonzero complex coordinate. -/
noncomputable def apm_t95j06_hopf_phase
    {F : Set apm_t95j06_S5} {x : F} (k : Fin 3)
    (y : apm_t95j06_hopf_slice (F := F) (x := x) k) : Circle :=
  ⟨apm_t95j06_hopf_coordinate k y.1 /
      ‖apm_t95j06_hopf_coordinate k y.1‖,
    by
      change apm_t95j06_hopf_coordinate k y.1 /
        (‖apm_t95j06_hopf_coordinate k y.1‖ : ℂ) ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm]
      rw [norm_div, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _), div_self]
      exact norm_ne_zero_iff.mpr y.2⟩

/-- Normalized phase varies continuously on a nonzero-coordinate slice. -/
lemma apm_t95j06_hopf_phase_continuous
    {F : Set apm_t95j06_S5} {x : F} (k : Fin 3) :
    Continuous (apm_t95j06_hopf_phase (F := F) (x := x) k) := by
  apply continuous_induced_rng.2
  let coord : apm_t95j06_hopf_slice (F := F) (x := x) k → ℂ :=
    fun y => apm_t95j06_hopf_coordinate k y.1
  have hcoord : Continuous coord := by
    dsimp only [coord, apm_t95j06_hopf_coordinate]
    fun_prop
  change Continuous (fun y => coord y / (‖coord y‖ : ℂ))
  apply hcoord.div
    (Complex.continuous_ofReal.comp (continuous_norm.comp hcoord))
  intro y
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr y.2)

/-- Normalized coordinate phase is equivariant for the scalar action. -/
lemma apm_t95j06_hopf_phase_act
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) (g : Circle)
    (y : apm_t95j06_hopf_slice (F := F) (x := x) k) :
    apm_t95j06_hopf_phase k
        ⟨Q.act (g, y.1), apm_t95j06_hopf_slice_invariant Q k g y.1 y.2⟩ =
      g * apm_t95j06_hopf_phase k y := by
  apply Circle.coe_injective
  change (Q.act (g, y.1)).1.1.1 k / ‖(Q.act (g, y.1)).1.1.1 k‖ =
    (g : ℂ) * (y.1.1.1.1 k / ‖y.1.1.1.1 k‖)
  have hcoord := congrArg (fun v : apm_t95j06_C3 => v k) (Q.scalar_act g y.1)
  simp only [PiLp.smul_apply] at hcoord
  rw [hcoord]
  simp only [norm_smul, Circle.norm_coe, one_mul]
  exact mul_div_assoc (g : ℂ) (y.1.1.1.1 k) (‖y.1.1.1.1 k‖ : ℂ)

noncomputable def apm_t95j06_hopf_normalize
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) (y : apm_t95j06_hopf_slice (F := F) (x := x) k) :
    apm_t95j06_hopf_component F x :=
  Q.act ((apm_t95j06_hopf_phase k y)⁻¹, y.1)

lemma apm_t95j06_hopf_normalize_continuous
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) :
    Continuous (apm_t95j06_hopf_normalize Q k) := by
  apply Q.continuous_act.comp
  exact (apm_t95j06_hopf_phase_continuous k).inv.prodMk continuous_subtype_val

lemma apm_t95j06_hopf_normalize_phase
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) (y : apm_t95j06_hopf_slice (F := F) (x := x) k) :
    apm_t95j06_hopf_phase k
        ⟨apm_t95j06_hopf_normalize Q k y,
          apm_t95j06_hopf_slice_invariant Q k _ y.1 y.2⟩ = 1 := by
  unfold apm_t95j06_hopf_normalize
  rw [apm_t95j06_hopf_phase_act]
  simp

lemma apm_t95j06_hopf_normalize_eq_of_proj_eq
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) (y z : apm_t95j06_hopf_slice (F := F) (x := x) k)
    (h : Q.proj y.1 = Q.proj z.1) :
    apm_t95j06_hopf_normalize Q k y = apm_t95j06_hopf_normalize Q k z := by
  obtain ⟨g, hg⟩ := Q.orbit_fiber y.1 z.1 h
  have hp : apm_t95j06_hopf_phase k z = g * apm_t95j06_hopf_phase k y := by
    rw [← apm_t95j06_hopf_phase_act Q k g y]
    congr 1
    exact Subtype.ext hg.symm
  simp only [apm_t95j06_hopf_normalize, hp]
  rw [mul_inv_rev, ← hg, Q.mul_act]
  simp

/-- **Section descent (estimated 80--140 lines).** On the image of any
nonzero-coordinate slice there is a continuous normalized representative.
It projects to the given base point and has coordinate phase one. -/
theorem apm_t95j06_hopf_normalized_section
    {F : Set apm_t95j06_S5} {x : F} {B : Type} {tB : TopologicalSpace B}
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB)
    (k : Fin 3) :
    ∃ s : (Q.proj '' apm_t95j06_hopf_slice (F := F) (x := x) k) →
        apm_t95j06_hopf_component F x,
      Continuous s ∧
      (∀ b, Q.proj (s b) = b.1) ∧
      ∃ hs : ∀ b, s b ∈ apm_t95j06_hopf_slice (F := F) (x := x) k,
        ∀ b, apm_t95j06_hopf_phase k ⟨s b, hs b⟩ = 1 := by
  classical
  let S := apm_t95j06_hopf_slice (F := F) (x := x) k
  let U : Set B := Q.proj '' S
  let q : S → U := fun y ↦ ⟨Q.proj y.1, ⟨y.1, y.2, rfl⟩⟩
  have hqcont : Continuous q :=
    (Q.continuous_proj.comp continuous_subtype_val).subtype_mk _
  have hqopen : IsOpenMap q :=
    (Q.open_proj.restrict (apm_t95j06_hopf_slice_isOpen k)).codRestrict _
  have hqsurj : Function.Surjective q := by
    rintro ⟨b, y, hy, hproj⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hproj⟩
  have hquot : Topology.IsQuotientMap q := hqopen.isQuotientMap hqcont hqsurj
  let r : U → S := fun b ↦ Classical.choose (hqsurj b)
  have hr (b : U) : q (r b) = b := Classical.choose_spec (hqsurj b)
  let s : U → apm_t95j06_hopf_component F x :=
    fun b ↦ apm_t95j06_hopf_normalize Q k (r b)
  have hscomp : s ∘ q = apm_t95j06_hopf_normalize Q k := by
    funext y
    apply apm_t95j06_hopf_normalize_eq_of_proj_eq
    exact congrArg Subtype.val (hr (q y))
  have hscont : Continuous s := by
    apply hquot.continuous_iff.mpr
    rw [hscomp]
    exact apm_t95j06_hopf_normalize_continuous Q k
  have hsproj (b : U) : Q.proj (s b) = b.1 := by
    change Q.proj (Q.act (_, (r b).1)) = b.1
    rw [Q.invariant]
    exact congrArg Subtype.val (hr b)
  have hsS (b : U) : s b ∈ S :=
    apm_t95j06_hopf_slice_invariant Q k _ (r b).1 (r b).2
  refine ⟨s, hscont, hsproj, hsS, ?_⟩
  intro b
  exact apm_t95j06_hopf_normalize_phase Q k (r b)

/-- **Remaining sub-leaf, explicit Hopf charts (estimated 300--550 lines).**
In words: every scalar-orbit quotient core has fibre-preserving,
Circle-equivariant local product charts obtained by choosing a nonzero
coordinate and normalizing its phase.

Why true: for `k : Fin 3`, on `z_k ≠ 0` use the phase
`z_k / |z_k| : Circle`; multiplying by its inverse places `z` in the slice
where coordinate `k` is positive real.  The inverse multiplies the slice
point by the Circle coordinate.  `Complex.continuous_abs`, continuity of
division away from zero, and compact-to-Hausdorff continuity of the quotient
chart prove the homeomorphism.  A norm-one vector has a nonzero coordinate,
so these charts cover.  Equivariance is the identity
`phase(g • z) = g * phase(z)`. -/
theorem apm_t95j06_hopf_slices_component_principalBundle_aux_localTrivial
    (F : Set apm_t95j06_S5) (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hinv : apm_t95j06_IsCircleInvariant F) (x : F)
    (B : Type) (tB : TopologicalSpace B)
    (Q : @apm_t95j06_hopf_slices_component_principalBundle_aux_Core F x B tB) :
    ∀ b, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ φ : {y : {y : F // y ∈ connectedComponent x} // Q.proj y ∈ U} ≃ₜ
          U × Circle,
        (∀ y, ((φ y).1 : B) = Q.proj y.1) ∧
        ∀ g y, (φ ⟨Q.act (g, y.1), by rw [Q.invariant]; exact y.2⟩).2 =
          g * (φ y).2 := by
  intro b
  obtain ⟨y, hy⟩ := Q.surjective_proj b
  obtain ⟨k, hyk⟩ := apm_t95j06_hopf_exists_coordinate_ne_zero y
  let S := apm_t95j06_hopf_slice (F := F) (x := x) k
  let U : Set B := Q.proj '' S
  have hUopen : IsOpen U := by
    exact Q.open_proj _ (apm_t95j06_hopf_slice_isOpen k)
  have hbU : b ∈ U := ⟨y, hyk, hy⟩
  obtain ⟨s, hscont, hsproj, hsS, hsphase⟩ :=
    apm_t95j06_hopf_normalized_section Q k
  have inS : ∀ z : {z : apm_t95j06_hopf_component F x // Q.proj z ∈ U},
      z.1 ∈ S := by
    intro z
    obtain ⟨w, hwS, hwproj⟩ := z.2
    obtain ⟨g, hg⟩ := Q.orbit_fiber w z.1 hwproj
    rw [← hg]
    exact apm_t95j06_hopf_slice_invariant Q k g w hwS
  let toFun : {z : apm_t95j06_hopf_component F x // Q.proj z ∈ U} →
      U × Circle := fun z =>
    (⟨Q.proj z.1, z.2⟩, apm_t95j06_hopf_phase k ⟨z.1, inS z⟩)
  let invFun : U × Circle →
      {z : apm_t95j06_hopf_component F x // Q.proj z ∈ U} := fun p =>
    ⟨Q.act (p.2, s p.1), by rw [Q.invariant, hsproj]; exact p.1.2⟩
  have leftInv : Function.LeftInverse invFun toFun := by
    intro z
    obtain ⟨g, hg⟩ := Q.orbit_fiber (s ⟨Q.proj z.1, z.2⟩) z.1
      (hsproj ⟨Q.proj z.1, z.2⟩)
    have hphase : apm_t95j06_hopf_phase k ⟨z.1, inS z⟩ = g := by
      have he := apm_t95j06_hopf_phase_act Q k g
        ⟨s ⟨Q.proj z.1, z.2⟩, hsS ⟨Q.proj z.1, z.2⟩⟩
      rw [hsphase] at he
      simp only [mul_one] at he
      rw [← he]
      congr 1
      exact Subtype.ext hg.symm
    apply Subtype.ext
    dsimp only [invFun, toFun]
    rw [hphase, hg]
  have rightInv : Function.RightInverse invFun toFun := by
    rintro ⟨u, g⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp only [toFun, invFun]
      rw [Q.invariant, hsproj]
    · dsimp only [toFun, invFun]
      have he := apm_t95j06_hopf_phase_act Q k g ⟨s u, hsS u⟩
      rw [hsphase] at he
      simpa using he
  have toCont : Continuous toFun := by
    apply Continuous.prodMk
    · exact (Q.continuous_proj.comp continuous_subtype_val).subtype_mk _
    · apply (apm_t95j06_hopf_phase_continuous k).comp
      exact continuous_subtype_val.subtype_mk _
  have invCont : Continuous invFun := by
    apply Continuous.subtype_mk
    · apply Q.continuous_act.comp
      exact continuous_snd.prodMk (hscont.comp continuous_fst)
  let φ : {z : apm_t95j06_hopf_component F x // Q.proj z ∈ U} ≃ₜ
      U × Circle := Homeomorph.mk (Equiv.mk toFun invFun leftInv rightInv) toCont invCont
  refine ⟨U, hUopen, hbU, φ, ?_, ?_⟩
  · intro z
    rfl
  · intro g z
    have hgz : Q.proj (Q.act (g, z.1)) ∈ U := by
      rw [Q.invariant]
      exact z.2
    let gz : {y : apm_t95j06_hopf_component F x // Q.proj y ∈ U} :=
      ⟨Q.act (g, z.1), hgz⟩
    change apm_t95j06_hopf_phase k
        ⟨Q.act (g, z.1), inS gz⟩ =
      g * apm_t95j06_hopf_phase k ⟨z.1, inS z⟩
    exact apm_t95j06_hopf_phase_act Q k g ⟨z.1, inS z⟩

theorem apm_t95j06_hopf_slices_component_principalBundle
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hinv : apm_t95j06_IsCircleInvariant F) :
    ∀ x : F, ∃ (B : Type) (tB : TopologicalSpace B),
      @CompactSpace B tB ∧ @ConnectedSpace B tB ∧ @T2Space B tB ∧
      @SecondCountableTopology B tB ∧
      Nonempty (@apm_t95j06_PrincipalCircleBundle
        {y : F // y ∈ connectedComponent x} B inferInstance tB) := by
  intro x
  obtain ⟨B, tB, hc, hconn, h2, hsc, ⟨Q⟩⟩ :=
    apm_t95j06_hopf_slices_component_principalBundle_aux_core F hF hinv x
  refine ⟨B, tB, hc, hconn, h2, hsc, ⟨{
    proj := Q.proj
    act := Q.act
    continuous_proj := Q.continuous_proj
    continuous_act := Q.continuous_act
    one_act := Q.one_act
    mul_act := Q.mul_act
    free := Q.free
    invariant := Q.invariant
    orbit_fiber := Q.orbit_fiber
    surjective_proj := Q.surjective_proj
    local_trivial :=
      apm_t95j06_hopf_slices_component_principalBundle_aux_localTrivial
        F hF hinv x B tB Q }⟩⟩

/-! ### Split of LIBRARY 3(a): cancellation of the circle factor -/

/-- Local Euclidean-plane charts, stated in the same elementary `Homeomorph`
form as `apm_t95j06_IsLocallyRealLine`. -/
def apm_t95j06_IsLocallyEuclideanPlane
    (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set apm_t95j06_E2, IsOpen V ∧ Nonempty (U ≃ₜ V)

/-- **Sub-leaf F1 (estimated 120--200 lines).**  In words: every connected
component of the surface encoded by `hF`, with its subtype topology, is locally
homeomorphic to the Euclidean plane.

Proof sketch: unpack the `ChartedSpace` and `IsManifold` witnesses in `hF`;
use a manifold chart at the underlying point, restrict its source to the
connected-component subtype, and apply the standard open-subtype chart
restriction (`IsOpenEmbedding.isManifold` / manifold chart source openness).
The component is closed, not generally open, so the proof must use local
connectedness of Euclidean chart domains to shrink to the component; it may
not simply claim that an arbitrary closed subtype of a manifold is a
manifold.  `ConstructionTargets.SurfaceClassification` supplies planar chart
and finite surface infrastructure but no component-transfer theorem.

Truth checks: the empty surface is vacuous because there is no `x`; a singleton
and a zero-dimensional component cannot satisfy the frozen two-manifold
instance; disconnected surfaces work component-by-component. -/
theorem apm_t95j06_surface_component_locallyEuclideanPlane
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (x : F) :
    apm_t95j06_IsLocallyEuclideanPlane
      {y : F // y ∈ connectedComponent x} := by
  rcases hF.2 with ⟨charts, hman, _⟩
  letI : ChartedSpace apm_t95j06_E2 F := charts
  letI : IsManifold apm_t95j06_I2 (⊤ : ℕ∞) F := hman
  letI : LocallyConnectedSpace F :=
    ChartedSpace.locallyConnectedSpace apm_t95j06_E2 F
  have hcomponent : IsOpen (connectedComponent x) :=
    isOpen_connectedComponent
  intro y
  let inclusion : {z : F // z ∈ connectedComponent x} → F := Subtype.val
  letI : Nonempty {z : F // z ∈ connectedComponent x} := ⟨y⟩
  have hinclusion : Topology.IsOpenEmbedding inclusion :=
    hcomponent.isOpenEmbedding_subtypeVal
  let e : OpenPartialHomeomorph
      {z : F // z ∈ connectedComponent x} apm_t95j06_E2 :=
    (hinclusion.toOpenPartialHomeomorph inclusion).trans
      (chartAt apm_t95j06_E2 y.1)
  refine ⟨e.source, e.open_source, ?_, e.target, e.open_target,
    ⟨e.toHomeomorphSourceTarget⟩⟩
  change y ∈ e.source
  simp [e, inclusion]

/-- An open subspace of a locally Euclidean plane is locally Euclidean.

This is true by intersecting each planar chart domain with the open subspace;
the restricted chart has open image because both the original chart domain
and the subspace are open.  Estimated proof size: 45--80 lines. -/
theorem apm_t95j06_bundleCharts_product_locallyEuclideanPlane_aux_openSubtype
    (X : Type*) [TopologicalSpace X]
    (hX : apm_t95j06_IsLocallyEuclideanPlane X)
    (W : Set X) (hW : IsOpen W) :
    apm_t95j06_IsLocallyEuclideanPlane W := by
  intro w
  obtain ⟨U, hU, hwU, V, hV, ⟨c⟩⟩ := hX w.1
  let U' : Set W := Subtype.val ⁻¹' U
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  let g : U' → U := fun w' => ⟨w'.1.1, w'.2⟩
  have hg : Topology.IsOpenEmbedding g := by
    have h1 : Topology.IsOpenEmbedding ((Subtype.val : U → X) ∘ g) :=
      (hW.isOpenEmbedding_subtypeVal).comp hU'.isOpenEmbedding_subtypeVal
    exact Topology.IsOpenEmbedding.of_comp g hU.isOpenEmbedding_subtypeVal h1
  have hF : Topology.IsOpenEmbedding ((Subtype.val : V → apm_t95j06_E2) ∘ c ∘ g) :=
    hV.isOpenEmbedding_subtypeVal.comp (c.isOpenEmbedding.comp hg)
  exact ⟨U', hU', hwU, _, hF.isOpen_range, ⟨hF.isEmbedding.toHomeomorph⟩⟩

/-- Local Euclidean-planeness is invariant under homeomorphism.

This is true by taking the image of each open chart domain under the
homeomorphism and composing the inverse homeomorphism with the original
chart.  Estimated proof size: 25--45 lines. -/
theorem apm_t95j06_bundleCharts_product_locallyEuclideanPlane_aux_homeomorph
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hX : apm_t95j06_IsLocallyEuclideanPlane X) :
    apm_t95j06_IsLocallyEuclideanPlane Y := by
  intro y
  obtain ⟨U, hU, hyU, V, hV, ⟨c⟩⟩ := hX (e.symm y)
  refine ⟨e '' U, e.isOpen_image.mpr hU, ⟨e.symm y, hyU, ?_⟩,
    V, hV, ?_⟩
  · simp
  · refine ⟨(e.symm.subtype fun z ↦ ?_).trans c⟩
    simp only [Set.mem_image]
    exact ⟨fun ⟨x, hx, hxy⟩ ↦ by simpa [← hxy] using hx,
      fun hz ↦ ⟨e.symm z, hz, by simp⟩⟩

/-- **Sub-leaf F2 (estimated 100--180 lines).**  In words: a fibre-preserving
local trivialization of a principal circle bundle identifies a neighbourhood
`U × Circle` of each base fibre with an open part of the locally planar total
space, so that product is itself locally planar.

Proof sketch: take `U, φ` from `P.local_trivial b`; continuity of `P.proj`
makes `{x | P.proj x ∈ U}` open.  Restrict the supplied local-plane charts to
that open subtype and transport them across `φ`.  The relevant Mathlib tools
are `IsOpen.preimage`, `Homeomorph.isOpen_preimage`, subtype homeomorphisms,
and `Homeomorph.trans`.

Truth checks: surjectivity makes the fibre over `b` nonempty; a constant
projection cannot satisfy both local triviality and free transitive circle
fibres except in the genuine product case; no compactness of `B` is used. -/
theorem apm_t95j06_bundleCharts_product_locallyEuclideanPlane
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (hX : apm_t95j06_IsLocallyEuclideanPlane X) :
    ∀ b : B, ∃ U : Set B, @IsOpen B tB U ∧ b ∈ U ∧
      apm_t95j06_IsLocallyEuclideanPlane (U × Circle) := by
  intro b
  obtain ⟨U, hU, hbU, φ, hφ⟩ := P.local_trivial b
  let W : Set X := P.proj ⁻¹' U
  have hW : IsOpen W := hU.preimage P.continuous_proj
  have hplaneW : apm_t95j06_IsLocallyEuclideanPlane W :=
    apm_t95j06_bundleCharts_product_locallyEuclideanPlane_aux_openSubtype
      X hX W hW
  refine ⟨U, hU, hbU, ?_⟩
  exact
    apm_t95j06_bundleCharts_product_locallyEuclideanPlane_aux_homeomorph
      W (U × Circle) φ hplaneW

/-! ### Split of F3: planar localization, separation, and arc recognition -/

/-- Local planar charts on a fixed real arc product.  Unlike the conclusion of
F3, this predicate does not assert interval charts on the base. -/
def apm_t95j06_HasPlanarArcProducts
    (B : Type*) [TopologicalSpace B] : Prop :=
  ∀ b : B, ∃ W : Set B, IsOpen W ∧ b ∈ W ∧
    ∃ V : Set apm_t95j06_E2, IsOpen V ∧
      Nonempty ((W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)

/-- The separation certificate used by the classical arc theorem: every point
has a compact connected neighbourhood with exactly two non-cut points, neither
of which is the point itself.  (Without `a ≠ b`, `c ≠ b` the certificate holds
on `[0,1]` at the endpoint `0` with `K = [0,1]`, and F3d would be false.) -/
def apm_t95j06_HasTwoEndpointContinuumNeighborhoods
    (B : Type*) [TopologicalSpace B] : Prop :=
  ∀ b : B, ∃ K : Set B,
    IsCompact K ∧ IsConnected K ∧ b ∈ interior K ∧
    ∃ a c : K, a ≠ c ∧ (a : B) ≠ b ∧ (c : B) ≠ b ∧
      Nonempty (LocallyConnectedSpace K) ∧
      IsPreconnected ({a}ᶜ : Set K) ∧
      IsPreconnected ({c}ᶜ : Set K) ∧
      ∀ y : K, y ≠ a → y ≠ c → ¬ IsPreconnected ({y}ᶜ : Set K)

/-- The disk-projection step of Q, independent of crosscut separation: every
product chart has a compact connected base neighbourhood contained in its
base domain. Take a sufficiently small closed disk in the planar target and
project its inverse image. The open disk projects to an open neighbourhood,
so the centre lies in the interior of the compact image. -/
lemma apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_aux_disk_projection
    (B : Type) (tB : TopologicalSpace B)
    (b : B) (W : Set B) (hW : @IsOpen B tB W) (hbW : b ∈ W)
    (V : Set apm_t95j06_E2) (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V) :
    ∃ K : Set B, K ⊆ W ∧ IsCompact K ∧ IsConnected K ∧ b ∈ interior K := by
  let z : W × Set.Ioo (-1 : ℝ) 1 := ⟨⟨b, hbW⟩, ⟨0, by norm_num⟩⟩
  let p : V := e z
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV p.1 p.2
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hD : Metric.closedBall p.1 r ⊆ V := by
    intro u hu
    apply hεV
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hu) (by dsimp [r]; linarith)
  let D := Metric.closedBall p.1 r
  letI : CompactSpace D := (isCompact_iff_compactSpace).mp (isCompact_closedBall p.1 r)
  letI : ConnectedSpace D := Subtype.connectedSpace (Metric.isConnected_closedBall hr.le)
  let g : V → B := fun v ↦ (e.symm v).1.1
  have hg : Continuous g :=
    continuous_subtype_val.comp (continuous_fst.comp e.symm.continuous)
  have hgopen : IsOpenMap g :=
    hW.isOpenMap_subtype_val.comp (isOpenMap_fst.comp e.symm.isOpenMap)
  let f : D → B := fun u ↦ g ⟨u.1, hD u.2⟩
  have hf : Continuous f := hg.comp (continuous_subtype_val.subtype_mk _)
  let K : Set B := Set.range f
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact (e.symm ⟨u.1, hD u.2⟩).1.2
  · exact isCompact_range hf
  · exact isConnected_range hf
  · let O : Set V := {v | v.1 ∈ Metric.ball p.1 r}
    have hO : IsOpen O := Metric.isOpen_ball.preimage continuous_subtype_val
    have hOK : g '' O ⊆ K := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨⟨v.1, Metric.ball_subset_closedBall hv⟩, rfl⟩
    apply (interior_maximal hOK (hgopen O hO))
    refine ⟨p, ?_, ?_⟩
    · exact Metric.mem_ball_self hr
    · change (e.symm (e z)).1.1 = b
      simp [z]

/-- The closed unit interval used for topological loop erasure. -/
abbrev apm_t95j06_LoopEraseInterval := Set.Icc (0 : ℝ) 1

/-- A closed subset of the path parameter interval is admissible when it
contains both endpoints and every complementary gap has equal path values at
its two endpoints. -/
def apm_t95j06_LoopEraseAdmissible
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X)
    (F : Set apm_t95j06_LoopEraseInterval) : Prop :=
  IsClosed F ∧
    (⟨0, by norm_num⟩ : apm_t95j06_LoopEraseInterval) ∈ F ∧
    (⟨1, by norm_num⟩ : apm_t95j06_LoopEraseInterval) ∈ F ∧
    ∀ s t, s ∈ F → t ∈ F → s < t →
      Set.Ioo s t ∩ F = ∅ → p s = p t

/-- The full parameter interval is admissible: it is closed and has no
complementary gaps. -/
lemma apm_t95j06_loopEraseAdmissible_univ
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X) :
    apm_t95j06_LoopEraseAdmissible p Set.univ := by
  refine ⟨isClosed_univ, Set.mem_univ _, Set.mem_univ _, ?_⟩
  intro s t _ _ hst hgap
  exfalso
  have hst' : s.1 < t.1 := hst
  let m : ℝ := (s.1 + t.1) / 2
  have hsm : s.1 < m := by dsimp [m]; linarith
  have hmt : m < t.1 := by dsimp [m]; linarith
  have hm0 : 0 ≤ m := le_trans s.2.1 hsm.le
  have hm1 : m ≤ 1 := le_trans hmt.le t.2.2
  have hm : (⟨m, hm0, hm1⟩ : apm_t95j06_LoopEraseInterval) ∈
      Set.Ioo s t ∩ (Set.univ : Set apm_t95j06_LoopEraseInterval) :=
    ⟨⟨hsm, hmt⟩, Set.mem_univ _⟩
  rw [hgap] at hm
  exact hm

/-- The intersection of a nonempty family of admissible sets is closed and
retains both endpoints. These are the formal, immediate parts of descending
chain closure; preservation of the gap equation is the remaining limiting
argument. -/
lemma apm_t95j06_loopEraseAdmissible_iInter_basic
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X)
    (c : Set (Set apm_t95j06_LoopEraseInterval))
    (hc : c.Nonempty)
    (hadm : ∀ F ∈ c, apm_t95j06_LoopEraseAdmissible p F) :
    IsClosed (⋂ F ∈ c, F) ∧
      (⟨0, by norm_num⟩ : apm_t95j06_LoopEraseInterval) ∈ ⋂ F ∈ c, F ∧
      (⟨1, by norm_num⟩ : apm_t95j06_LoopEraseInterval) ∈ ⋂ F ∈ c, F := by
  refine ⟨isClosed_iInter (fun F => isClosed_iInter (fun hF => (hadm F hF).1)), ?_, ?_⟩
  · simp only [Set.mem_iInter]
    intro F hF
    exact (hadm F hF).2.1
  · simp only [Set.mem_iInter]
    intro F hF
    exact (hadm F hF).2.2.1

/-- **Loop erasure, chain step.**  The intersection of a nonempty chain of
admissible sets satisfies the gap equation.  If it failed on a gap `(s,t)`,
separate `p s` and `p t` by open sets and shrink to a margin `d`; the compact
middle part `[s+d, t-d]` misses the intersection, hence misses one member `F`
of the chain, and the largest point of `F` below `t-d` and the least point of
`F` above `s+d` bound a gap of `F` whose ends lie in the two open sets. -/
lemma apm_t95j06_loopEraseAdmissible_chain_gap
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    (c : Set (Set apm_t95j06_LoopEraseInterval)) (hc : c.Nonempty)
    (hchain : IsChain (· ⊆ ·) c)
    (hadm : ∀ F ∈ c, apm_t95j06_LoopEraseAdmissible p F)
    (s t : apm_t95j06_LoopEraseInterval) (hs : s ∈ ⋂₀ c) (ht : t ∈ ⋂₀ c)
    (hst : s < t) (hgap : Set.Ioo s t ∩ ⋂₀ c = ∅) : p s = p t := by
  classical
  by_contra hne
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := t2_separation hne
  obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.mp (hu.preimage hp) s hsu
  obtain ⟨ε', hε', hεv⟩ := Metric.isOpen_iff.mp (hv.preimage hp) t htv
  have hst' : s.1 < t.1 := hst
  set d : ℝ := min (min ε ε') ((t.1 - s.1) / 3) with hd
  have hd0 : 0 < d := lt_min (lt_min hε hε') (by linarith)
  have hdε : d ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hdε' : d ≤ ε' := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ (t.1 - s.1) / 3 := min_le_right _ _
  let K : Set apm_t95j06_LoopEraseInterval := {z | s.1 + d ≤ z.1 ∧ z.1 ≤ t.1 - d}
  have hKc : IsClosed K :=
    (isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)
  have hKF : K ∩ ⋂ F : c, (F : Set apm_t95j06_LoopEraseInterval) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hzK hz
    have hz' : z ∈ Set.Ioo s t ∩ ⋂₀ c := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show s.1 < z.1
        linarith [hzK.1]
      · show z.1 < t.1
        linarith [hzK.2]
      · intro F hF
        exact hz ⟨F, hF⟩
    rw [hgap] at hz'
    exact hz'
  haveI : Nonempty c := hc.to_subtype
  have hdir : Directed (· ⊇ ·) (fun F : c => (F : Set apm_t95j06_LoopEraseInterval)) := by
    intro F₁ F₂
    rcases eq_or_ne (F₁ : Set apm_t95j06_LoopEraseInterval) F₂ with h | h
    · exact ⟨F₁, le_rfl, show (F₁ : Set apm_t95j06_LoopEraseInterval) ⊆ F₂ from h ▸ subset_rfl⟩
    · rcases hchain F₁.2 F₂.2 h with h12 | h21
      · exact ⟨F₁, le_rfl, h12⟩
      · exact ⟨F₂, h21, le_rfl⟩
  obtain ⟨⟨F, hFc⟩, hFK⟩ := hKc.isCompact.elim_directed_family_closed _
    (fun F : c => (hadm F.1 F.2).1) hKF hdir
  have hFK' : ∀ z ∈ F, z ∉ K := fun z hzF hzK => by
    have : z ∈ K ∩ F := ⟨hzK, hzF⟩
    simp only at hFK
    rw [hFK] at this
    exact this
  have hFadm := hadm F hFc
  have hsF : s ∈ F := hs F hFc
  have htF : t ∈ F := ht F hFc
  -- greatest point of `F` in `[s, t-d]`
  let L : Set apm_t95j06_LoopEraseInterval := F ∩ {z | s ≤ z ∧ z.1 ≤ t.1 - d}
  have hLc : IsClosed L := hFadm.1.inter
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const))
  obtain ⟨s', hs'L, hs'max⟩ := hLc.isCompact.exists_isGreatest
    ⟨s, hsF, le_rfl, by linarith⟩
  let R : Set apm_t95j06_LoopEraseInterval := F ∩ {z | s.1 + d ≤ z.1 ∧ z ≤ t}
  have hRc : IsClosed R := hFadm.1.inter
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const))
  obtain ⟨t', ht'R, ht'min⟩ := hRc.isCompact.exists_isLeast
    ⟨t, htF, by linarith, le_rfl⟩
  have hs'lt : s'.1 < s.1 + d := by
    by_contra h
    exact hFK' s' hs'L.1 ⟨not_lt.mp h, hs'L.2.2⟩
  have ht'gt : t.1 - d < t'.1 := by
    by_contra h
    exact hFK' t' ht'R.1 ⟨ht'R.2.1, not_lt.mp h⟩
  have hs't' : s' < t' := by
    show s'.1 < t'.1
    linarith [ht'R.2.1]
  have hgap' : Set.Ioo s' t' ∩ F = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨hz1, hz2⟩ hzF
    by_cases hzt : z.1 ≤ t.1 - d
    · have hzL : z ∈ L := ⟨hzF, le_trans hs'L.2.1 hz1.le, hzt⟩
      exact absurd (hs'max hzL) (not_le.mpr hz1)
    · have hzR : z ∈ R := by
        refine ⟨hzF, ?_, le_trans hz2.le ht'R.2.2⟩
        have : t.1 - d ≥ s.1 + d := by linarith
        linarith [not_le.mp hzt]
      exact absurd (ht'min hzR) (not_le.mpr hz2)
  have hpeq := hFadm.2.2.2 s' t' hs'L.1 ht'R.1 hs't' hgap'
  have hs'u : p s' ∈ u := by
    apply hεu
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have : s.1 ≤ s'.1 := hs'L.2.1
    constructor <;> linarith
  have ht'v : p t' ∈ v := by
    apply hεv
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have : t'.1 ≤ t.1 := ht'R.2.2
    constructor <;> linarith
  exact Set.disjoint_left.1 huv hs'u (hpeq ▸ ht'v)

/-- **Loop erasure, Zorn.**  A minimal admissible set exists. -/
lemma apm_t95j06_loopEraseAdmissible_exists_minimal
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p) :
    ∃ F, Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F := by
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty
    {F | apm_t95j06_LoopEraseAdmissible p F} (by
      intro c hcS hchain hcne
      refine ⟨⋂₀ c, ?_, fun F hF => Set.sInter_subset_of_mem hF⟩
      refine ⟨isClosed_sInter (fun F hF => (hcS hF).1),
        fun F hF => (hcS hF).2.1, fun F hF => (hcS hF).2.2.1, ?_⟩
      intro s t hs ht hst hgap
      exact apm_t95j06_loopEraseAdmissible_chain_gap p hp c hcne hchain
        (fun F hF => hcS hF) s t hs ht hst hgap)
    Set.univ (by
      refine ⟨isClosed_univ, Set.mem_univ _, Set.mem_univ _, ?_⟩
      intro s t _ _ hst hgap
      exfalso
      have hst' : s.1 < t.1 := hst
      have hm0 : 0 ≤ (s.1 + t.1) / 2 := by linarith [s.2.1]
      have hm1 : (s.1 + t.1) / 2 ≤ 1 := by linarith [t.2.2]
      have hm : (⟨(s.1 + t.1) / 2, hm0, hm1⟩ : apm_t95j06_LoopEraseInterval) ∈
          Set.Ioo s t ∩ Set.univ := by
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · show s.1 < (s.1 + t.1) / 2
          linarith
        · show (s.1 + t.1) / 2 < t.1
          linarith
      rw [hgap] at hm
      exact hm)
  exact ⟨m, hm⟩

/-- **Loop erasure, minimality.**  In a minimal admissible set, two points with
the same path value bound a gap. -/
lemma apm_t95j06_loopEraseAdmissible_minimal_gap
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    {s t : apm_t95j06_LoopEraseInterval} (hs : s ∈ F) (ht : t ∈ F) (hst : s < t)
    (hpst : p s = p t) : Set.Ioo s t ∩ F = ∅ := by
  classical
  let F' := F \ Set.Ioo s t
  have hF'adm : apm_t95j06_LoopEraseAdmissible p F' := by
    refine ⟨hF.prop.1.sdiff isOpen_Ioo, ⟨hF.prop.2.1, ?_⟩, ⟨hF.prop.2.2.1, ?_⟩, ?_⟩
    · rintro ⟨h0, -⟩
      exact absurd h0 (not_lt.mpr (show (0 : ℝ) ≤ s.1 from s.2.1))
    · rintro ⟨-, h1⟩
      exact absurd h1 (not_lt.mpr (show t.1 ≤ (1 : ℝ) from t.2.2))
    intro a b ha hb hab hgab
    by_cases hF0 : Set.Ioo a b ∩ F = ∅
    · exact hF.prop.2.2.2 a b ha.1 hb.1 hab hF0
    · obtain ⟨z, ⟨hza, hzb⟩, hzF⟩ := Set.nonempty_iff_ne_empty.mpr hF0
      have hzI : z ∈ Set.Ioo s t := by
        by_contra h
        have : z ∈ Set.Ioo a b ∩ F' := ⟨⟨hza, hzb⟩, hzF, h⟩
        rw [hgab] at this
        exact this
      have has : a ≤ s := by
        by_contra h
        push_neg at h
        have hta : t ≤ a := by
          by_contra h'
          exact ha.2 ⟨h, not_le.mp h'⟩
        exact absurd (hzI.2.trans_le hta) (not_lt.mpr hza.le)
      have htb : t ≤ b := by
        by_contra h
        push_neg at h
        have hbs : b ≤ s := by
          by_contra h'
          exact hb.2 ⟨not_le.mp h', h⟩
        exact absurd (hbs.trans_lt hzI.1) (not_lt.mpr hzb.le)
      have has' : a = s := by
        rcases has.lt_or_eq with h | h
        · exfalso
          have : s ∈ Set.Ioo a b ∩ F' :=
            ⟨⟨h, hst.trans_le htb⟩, hs, fun h' => lt_irrefl s h'.1⟩
          rw [hgab] at this
          exact this
        · exact h
      have htb' : b = t := by
        rcases htb.lt_or_eq with h | h
        · exfalso
          have : t ∈ Set.Ioo a b ∩ F' :=
            ⟨⟨has.trans_lt hst, h⟩, ht, fun h' => lt_irrefl t h'.2⟩
          rw [hgab] at this
          exact this
        · exact h.symm
      rw [has', htb']
      exact hpst
  have hsub : F ⊆ F' := hF.2 hF'adm Set.diff_subset
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hzF
  exact (hsub hzF).2 hz

/-- The image of an admissible parameter set under its path. -/
abbrev apm_t95j06_LoopEraseImage
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X)
    (F : Set apm_t95j06_LoopEraseInterval) := p '' F

/-- The parameters in `F` mapping to a specified point of the erased image. -/
def apm_t95j06_loopEraseFiber
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X)
    (F : Set apm_t95j06_LoopEraseInterval)
    (a : apm_t95j06_LoopEraseImage p F) :
    Set apm_t95j06_LoopEraseInterval := F ∩ p ⁻¹' {a.1}

/-- A loop-erasure fibre is compact. -/
lemma apm_t95j06_loopEraseFiber_compact
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    (a : apm_t95j06_LoopEraseImage p F) :
    IsCompact (apm_t95j06_loopEraseFiber p F a) := by
  apply IsClosed.isCompact
  exact hF.prop.1.inter (isClosed_singleton.preimage hp)

/-- A loop-erasure fibre is nonempty. -/
lemma apm_t95j06_loopEraseFiber_nonempty
    {X : Type} [TopologicalSpace X]
    (p : apm_t95j06_LoopEraseInterval → X)
    (F : Set apm_t95j06_LoopEraseInterval)
    (a : apm_t95j06_LoopEraseImage p F) :
    (apm_t95j06_loopEraseFiber p F a).Nonempty := by
  obtain ⟨s, hsF, hps⟩ := a.2
  exact ⟨s, hsF, by simpa [hps]⟩

/-- The first parameter of a point in the erased image. -/
noncomputable def apm_t95j06_loopEraseLo
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    (a : apm_t95j06_LoopEraseImage p F) : apm_t95j06_LoopEraseInterval :=
  Classical.choose ((apm_t95j06_loopEraseFiber_compact p hp hF a).exists_isLeast
    (apm_t95j06_loopEraseFiber_nonempty p F a))

lemma apm_t95j06_loopEraseLo_isLeast
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    (a : apm_t95j06_LoopEraseImage p F) :
    IsLeast (apm_t95j06_loopEraseFiber p F a)
      (apm_t95j06_loopEraseLo p hp hF a) :=
  Classical.choose_spec ((apm_t95j06_loopEraseFiber_compact p hp hF a).exists_isLeast
    (apm_t95j06_loopEraseFiber_nonempty p F a))

/-- Apart from its least parameter, a minimal loop-erasure fibre is
subsingleton. Equivalently, every fibre has at most two points. -/
lemma apm_t95j06_loopEraseFiber_sdiff_lo_subsingleton
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    (a : apm_t95j06_LoopEraseImage p F) :
    (apm_t95j06_loopEraseFiber p F a \
      {apm_t95j06_loopEraseLo p hp hF a}).Subsingleton := by
  intro s hs t ht
  by_cases hst : s = t
  · exact hst
  have ordered {u v : apm_t95j06_LoopEraseInterval}
      (hu : u ∈ apm_t95j06_loopEraseFiber p F a \
        {apm_t95j06_loopEraseLo p hp hF a})
      (hv : v ∈ apm_t95j06_loopEraseFiber p F a \
        {apm_t95j06_loopEraseLo p hp hF a}) (huv : u < v) : False := by
    have hlo := apm_t95j06_loopEraseLo_isLeast p hp hF a
    have hlou : apm_t95j06_loopEraseLo p hp hF a < u :=
      lt_of_le_of_ne (hlo.2 hu.1) (by
        intro h
        apply hu.2
        simpa [h])
    have hlav : apm_t95j06_loopEraseLo p hp hF a < v := hlou.trans huv
    have hgap := apm_t95j06_loopEraseAdmissible_minimal_gap p hF
      hlo.1.1 hv.1.1 hlav (by exact hlo.1.2.trans hv.1.2.symm)
    have huint : u ∈ Set.Ioo (apm_t95j06_loopEraseLo p hp hF a) v ∩ F :=
      ⟨⟨hlou, huv⟩, hu.1.1⟩
    rw [hgap] at huint
    exact huint
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · exact False.elim (ordered hs ht hlt)
  · exact False.elim (ordered ht hs hgt)

/-- The least parameter of an erased-image point maps back to that point. -/
lemma apm_t95j06_loopEraseLo_value
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    (a : apm_t95j06_LoopEraseImage p F) :
    p (apm_t95j06_loopEraseLo p hp hF a) = a.1 := by
  exact (apm_t95j06_loopEraseLo_isLeast p hp hF a).1.2

/-- Least parameters distinguish points of the erased image. -/
lemma apm_t95j06_loopEraseLo_injective
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F) :
    Function.Injective (apm_t95j06_loopEraseLo p hp hF) := by
  intro a b hab
  apply Subtype.ext
  rw [← apm_t95j06_loopEraseLo_value p hp hF a,
    ← apm_t95j06_loopEraseLo_value p hp hF b, hab]

/-- The linear order on the erased image, lifted from first occurrence along
the path. This is deliberately a definition rather than a global instance. -/
noncomputable def apm_t95j06_loopEraseLinearOrder
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F) :
    LinearOrder (apm_t95j06_LoopEraseImage p F) :=
  LinearOrder.lift' (apm_t95j06_loopEraseLo p hp hF)
    (apm_t95j06_loopEraseLo_injective p hp hF)

/-- Along the retained parameter set, path values are monotone for the order
lifted from their least parameters. -/
lemma apm_t95j06_loopErase_monotone
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    {s t : apm_t95j06_LoopEraseInterval} (hs : s ∈ F) (ht : t ∈ F)
    (hst : s ≤ t) :
    (apm_t95j06_loopEraseLinearOrder p hp hF).le ⟨p s, ⟨s, hs, rfl⟩⟩
      ⟨p t, ⟨t, ht, rfl⟩⟩ := by
  let a : apm_t95j06_LoopEraseImage p F := ⟨p s, ⟨s, hs, rfl⟩⟩
  let b : apm_t95j06_LoopEraseImage p F := ⟨p t, ⟨t, ht, rfl⟩⟩
  change apm_t95j06_loopEraseLo p hp hF a ≤
    apm_t95j06_loopEraseLo p hp hF b
  by_contra hle
  have hba : apm_t95j06_loopEraseLo p hp hF b <
      apm_t95j06_loopEraseLo p hp hF a := lt_of_not_ge hle
  have hloA := apm_t95j06_loopEraseLo_isLeast p hp hF a
  have hloB := apm_t95j06_loopEraseLo_isLeast p hp hF b
  have hloAs : apm_t95j06_loopEraseLo p hp hF a ≤ s := by
    apply hloA.2
    exact ⟨hs, by simp [a]⟩
  have hne : p s ≠ p t := by
    intro heq
    have hab : a = b := Subtype.ext heq
    have hlab : apm_t95j06_loopEraseLo p hp hF a =
        apm_t95j06_loopEraseLo p hp hF b := by rw [hab]
    exact (ne_of_lt hba) hlab.symm
  have hloAt : apm_t95j06_loopEraseLo p hp hF a < t := by
    apply lt_of_le_of_ne (hloAs.trans hst)
    intro heq
    apply hne
    have hva : p (apm_t95j06_loopEraseLo p hp hF a) = p s := by
      simpa [a] using apm_t95j06_loopEraseLo_value p hp hF a
    rw [← hva, heq]
  have hgap := apm_t95j06_loopEraseAdmissible_minimal_gap p hF
    hloB.1.1 ht (hba.trans hloAt)
    (by exact (apm_t95j06_loopEraseLo_value p hp hF b).trans rfl)
  have hinside : apm_t95j06_loopEraseLo p hp hF a ∈
      Set.Ioo (apm_t95j06_loopEraseLo p hp hF b) t ∩ F :=
    ⟨⟨hba, hloAt⟩, hloA.1.1⟩
  rw [hgap] at hinside
  exact hinside

/-- A compact Hausdorff topology on a linear order is its order topology as
soon as the non-strict order relation is closed.  The closed relation makes
both strict rays open, so the given topology is finer than the order topology;
compact-to-Hausdorff applied to the identity gives the reverse comparison. -/
lemma apm_t95j06_orderTopology_of_compact_closed_le
    (L : Type*) [LinearOrder L] [TopologicalSpace L] [CompactSpace L]
    [T2Space L]
    (hleClosed : IsClosed {q : L × L | q.1 ≤ q.2}) : OrderTopology L := by
  have hIoi : ∀ a : L, IsOpen (Set.Ioi a) := by
    intro a
    have hc : IsClosed {x : L | x ≤ a} := by
      have hp : {x : L | x ≤ a} =
          (fun x : L => (x, a)) ⁻¹' {q : L × L | q.1 ≤ q.2} := by
        ext x
        rfl
      rw [hp]
      exact hleClosed.preimage (continuous_id.prodMk continuous_const)
    have heq : Set.Ioi a = {x : L | x ≤ a}ᶜ := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact ⟨not_le_of_gt, lt_of_not_ge⟩
    rw [heq]
    exact hc.isOpen_compl
  have hIio : ∀ a : L, IsOpen (Set.Iio a) := by
    intro a
    have hc : IsClosed {x : L | a ≤ x} := by
      have hp : {x : L | a ≤ x} =
          (fun x : L => (a, x)) ⁻¹' {q : L × L | q.1 ≤ q.2} := by
        ext x
        rfl
      rw [hp]
      exact hleClosed.preimage (continuous_const.prodMk continuous_id)
    have heq : Set.Iio a = {x : L | a ≤ x}ᶜ := by
      ext x
      simp only [Set.mem_Iio, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact ⟨not_le_of_gt, lt_of_not_ge⟩
    rw [heq]
    exact hc.isOpen_compl
  have hle : (‹TopologicalSpace L›) ≤ Preorder.topology L := by
    apply le_generateFrom
    rintro s ⟨a, rfl | rfl⟩
    · exact hIoi a
    · exact hIio a
  have hT2 : @T2Space L (Preorder.topology L) := by
    letI : TopologicalSpace L := Preorder.topology L
    haveI : OrderTopology L := ⟨rfl⟩
    infer_instance
  have hcont : @Continuous L L _ (Preorder.topology L) id :=
    continuous_id_of_le hle
  have heq : (‹TopologicalSpace L›) = Preorder.topology L := by
    apply le_antisymm hle
    intro U hU
    have hc : IsCompact Uᶜ := hU.isClosed_compl.isCompact
    have himg : @IsCompact L (Preorder.topology L) (id '' Uᶜ) :=
      @IsCompact.image L L _ (Preorder.topology L) Uᶜ id hc hcont
    rw [Set.image_id] at himg
    have hcl : @IsClosed L (Preorder.topology L) Uᶜ :=
      @IsCompact.isClosed L (Preorder.topology L) hT2 _ himg
    have hU' : @IsOpen L (Preorder.topology L) Uᶜᶜ :=
      (@isOpen_compl_iff L Uᶜ (Preorder.topology L)).mpr hcl
    simpa using hU'
  exact ⟨heq⟩

/-- Between two distinct ordered image values lies a third. Take the last
parameter of the first fibre and the first parameter of the second fibre.
Monotonicity puts them in strict order. Admissibility forces a retained
parameter between them, whose value is strictly intermediate by extremality
of these two fibre parameters. -/
lemma apm_t95j06_loopEraseLo_exists_between
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F)
    (a b : apm_t95j06_LoopEraseImage p F)
    (hab : apm_t95j06_loopEraseLo p hp hF a < apm_t95j06_loopEraseLo p hp hF b) :
    ∃ c : apm_t95j06_LoopEraseImage p F,
      apm_t95j06_loopEraseLo p hp hF a < apm_t95j06_loopEraseLo p hp hF c ∧
      apm_t95j06_loopEraseLo p hp hF c < apm_t95j06_loopEraseLo p hp hF b := by
  letI := apm_t95j06_loopEraseLinearOrder p hp hF
  change a < b at hab
  change ∃ c, a < c ∧ c < b
  obtain ⟨u, hu⟩ := (apm_t95j06_loopEraseFiber_compact p hp hF a).exists_isGreatest
    (apm_t95j06_loopEraseFiber_nonempty p F a)
  let t := apm_t95j06_loopEraseLo p hp hF b
  have ht := apm_t95j06_loopEraseLo_isLeast p hp hF b
  have huF : u ∈ F := hu.1.1
  have htF : t ∈ F := ht.1.1
  have hua : (⟨p u, ⟨u, huF, rfl⟩⟩ : apm_t95j06_LoopEraseImage p F) = a :=
    Subtype.ext hu.1.2
  have htb : (⟨p t, ⟨t, htF, rfl⟩⟩ : apm_t95j06_LoopEraseImage p F) = b :=
    Subtype.ext ht.1.2
  have hut : u < t := by
    by_contra h
    have hba := apm_t95j06_loopErase_monotone p hp hF htF huF (le_of_not_gt h)
    rw [htb, hua] at hba
    exact (not_le_of_gt hab) hba
  have hgap : (Set.Ioo u t ∩ F).Nonempty := by
    by_contra h
    have heq := hF.prop.2.2.2 u t huF htF hut (Set.not_nonempty_iff_eq_empty.mp h)
    have hab' : a = b := Subtype.ext (hu.1.2.symm.trans (heq.trans ht.1.2))
    exact (ne_of_lt hab) hab'
  obtain ⟨r, hr, hrF⟩ := hgap
  let c : apm_t95j06_LoopEraseImage p F := ⟨p r, ⟨r, hrF, rfl⟩⟩
  have hac : a ≤ c := by
    have h := apm_t95j06_loopErase_monotone p hp hF huF hrF hr.1.le
    rwa [hua] at h
  have hcb : c ≤ b := by
    have h := apm_t95j06_loopErase_monotone p hp hF hrF htF hr.2.le
    rwa [htb] at h
  refine ⟨c, lt_of_le_of_ne hac ?_, lt_of_le_of_ne hcb ?_⟩
  · intro heq
    have hrA : r ∈ apm_t95j06_loopEraseFiber p F a :=
      ⟨hrF, (congrArg Subtype.val heq).symm⟩
    exact (not_le_of_gt hr.1) (hu.2 hrA)
  · intro heq
    have hrB : r ∈ apm_t95j06_loopEraseFiber p F b :=
      ⟨hrF, congrArg Subtype.val heq⟩
    exact (not_le_of_gt hr.2) (ht.2 hrB)

/-- The first-occurrence order on the loop-erased image is densely ordered.
This is an explicit theorem, so it introduces no competing global instance. -/
lemma apm_t95j06_loopErase_denselyOrdered
    {X : Type} [TopologicalSpace X] [T2Space X]
    (p : apm_t95j06_LoopEraseInterval → X) (hp : Continuous p)
    {F : Set apm_t95j06_LoopEraseInterval}
    (hF : Minimal (fun F => apm_t95j06_LoopEraseAdmissible p F) F) :
    letI := apm_t95j06_loopEraseLinearOrder p hp hF
    DenselyOrdered (apm_t95j06_LoopEraseImage p F) := by
  letI := apm_t95j06_loopEraseLinearOrder p hp hF
  exact ⟨fun a b hab => apm_t95j06_loopEraseLo_exists_between p hp hF a b hab⟩

/-- Euclidean invariance of domain, with all library premises discharged. -/
lemma apm_t95j06_Q_aux_invariance_domain
    {U : Set apm_t95j06_E2} (hU : IsOpen U) {f : U → apm_t95j06_E2}
    (hf : Continuous f) (hi : Function.Injective f) : IsOpenMap f := by
  apply ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_open
    2 (fun hf' hi' => ?_) hU hf hi
  apply ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_interior
    2 (fun hg => ?_) hf' hi'
  exact ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_brouwer
    2 ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_noRetraction hg

/-- Cartesian coordinates for the Euclidean plane. -/
noncomputable def apm_t95j06_Q_aux_plane_prod : apm_t95j06_E2 ≃ₜ ℝ × ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans Homeomorph.finTwoArrow

/-- Invariance of domain with Cartesian source coordinates. -/
lemma apm_t95j06_Q_aux_invariance_domain_prod_source
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : U → apm_t95j06_E2}
    (hf : Continuous f) (hi : Function.Injective f) : IsOpenMap f := by
  let e := apm_t95j06_Q_aux_plane_prod.symm.image U
  have h := apm_t95j06_Q_aux_invariance_domain
    (apm_t95j06_Q_aux_plane_prod.symm.isOpenMap U hU)
    (hf.comp e.symm.continuous) (hi.comp e.symm.injective)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h.comp e.isOpenMap

/-- Invariance of domain with Cartesian target coordinates. -/
lemma apm_t95j06_Q_aux_invariance_domain_prod_target
    {U : Set apm_t95j06_E2} (hU : IsOpen U) {f : U → ℝ × ℝ}
    (hf : Continuous f) (hi : Function.Injective f) : IsOpenMap f := by
  let e := apm_t95j06_Q_aux_plane_prod
  have h := apm_t95j06_Q_aux_invariance_domain hU
    (e.symm.continuous.comp hf) (e.symm.injective.comp hi)
  simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using e.isOpenMap.comp h

/-- Invariance of domain in Cartesian coordinates on both planes. -/
lemma apm_t95j06_Q_aux_invariance_domain_prod
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : U → ℝ × ℝ}
    (hf : Continuous f) (hi : Function.Injective f) : IsOpenMap f := by
  let e := apm_t95j06_Q_aux_plane_prod
  have h := apm_t95j06_Q_aux_invariance_domain_prod_source hU
    (e.symm.continuous.comp hf) (e.symm.injective.comp hi)
  simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using e.isOpenMap.comp h

/-- Invariance of domain for any source already openly embedded in the plane. -/
lemma apm_t95j06_Q_aux_open_coordinate
    {X : Type*} [TopologicalSpace X] {j : X → apm_t95j06_E2}
    (hj : Topology.IsOpenEmbedding j) {f : X → ℝ × ℝ}
    (hf : Continuous f) (hi : Function.Injective f) : IsOpenMap f := by
  let e := hj.isEmbedding.toHomeomorph
  have h := apm_t95j06_Q_aux_invariance_domain_prod_target hj.isOpen_range
    (hf.comp e.symm.continuous) (hi.comp e.symm.injective)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h.comp e.isOpenMap

/-- An injective real coordinate on an open part of the base has open image.
Apply planar invariance of domain to that coordinate paired with the vertical
coordinate in the given product chart, then project the open image to ℝ. -/
lemma apm_t95j06_Q_aux_base_coordinate_open
    {B : Type*} [TopologicalSpace B] {W U : Set B}
    {V : Set apm_t95j06_E2} (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)
    (hU : IsOpen U) (hUW : U ⊆ W)
    {f : U → ℝ} (hf : Continuous f) (hi : Function.Injective f) :
    IsOpen (Set.range f) := by
  let T : Set (W × Set.Ioo (-1 : ℝ) 1) := {x | x.1.val ∈ U}
  have hT : IsOpen T := hU.preimage (continuous_subtype_val.comp continuous_fst)
  let j : T → apm_t95j06_E2 := fun x => (e x.val).val
  have hj : Topology.IsOpenEmbedding j :=
    hV.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hT.isOpenEmbedding_subtypeVal)
  let F : T → ℝ × ℝ := fun x => (f ⟨x.val.1.val, x.property⟩, x.val.2.val)
  have hF : Continuous F := by
    apply Continuous.prodMk
    · exact hf.comp ((continuous_subtype_val.comp
        (continuous_fst.comp continuous_subtype_val)).subtype_mk _)
    · exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hFi : Function.Injective F := by
    intro x y h
    have hfirst := hi (congrArg Prod.fst h)
    have hsecond := congrArg Prod.snd h
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : U => z.val) hfirst)
    · exact Subtype.ext hsecond
  have hopen := (apm_t95j06_Q_aux_open_coordinate hj hF hFi).isOpen_range
  have hproj : Prod.fst '' Set.range F = Set.range f := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      let t : T := ⟨(⟨x.val, hUW x.property⟩, ⟨0, by norm_num⟩), x.property⟩
      exact ⟨F t, ⟨t, rfl⟩, rfl⟩
  rw [← hproj]
  exact isOpenMap_fst _ hopen

/-- There are no isolated points in the base of a planar interval product. -/
lemma apm_t95j06_Q_aux_no_isolated
    {B : Type*} [TopologicalSpace B] {W : Set B}
    {V : Set apm_t95j06_E2} (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)
    (b : B) (hb : b ∈ W) : ¬ IsOpen ({b} : Set B) := by
  intro hsingle
  let f : ({b} : Set B) → ℝ := fun _ => 0
  have hi : Function.Injective f := by
    intro x y _
    exact Subtype.ext (x.property.trans y.property.symm)
  have hopen := apm_t95j06_Q_aux_base_coordinate_open hV e hsingle
    (Set.singleton_subset_iff.mpr hb) (f := f) continuous_const hi
  have hr : Set.range f = {0} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; rfl
    · intro hz; exact ⟨⟨b, rfl⟩, hz.symm⟩
  rw [hr] at hopen
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 rfl
  have he : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have := hball he
  change ε / 2 = 0 at this
  linarith

/-- The interior of an embedded base arc is ambient-open: its product with
the vertical interval is an injectively parametrized open planar rectangle. -/
lemma apm_t95j06_Q_aux_arc_interior_open
    {B : Type*} [TopologicalSpace B] {W : Set B} (hW : IsOpen W)
    {V : Set apm_t95j06_E2} (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)
    (a : C(Set.Icc (0 : ℝ) 1, B)) (hi : Function.Injective a)
    (haW : Set.range a ⊆ W) :
    IsOpen (a '' {t : Set.Icc (0 : ℝ) 1 | 0 < t.val ∧ t.val < 1}) := by
  let T := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1
  let P : T → W × Set.Ioo (-1 : ℝ) 1 := fun x =>
    (⟨a ⟨x.val.1, x.property.1.1.le, x.property.1.2.le⟩, haW ⟨_, rfl⟩⟩,
      ⟨x.val.2, x.property.2⟩)
  let F : T → apm_t95j06_E2 := fun x => (e (P x)).val
  have hF : Continuous F := by
    apply continuous_subtype_val.comp
    apply e.continuous.comp
    dsimp [P]
    fun_prop
  have hFi : Function.Injective F := by
    intro x y hxy
    have hh := e.injective (Subtype.ext hxy)
    have hx : a ⟨x.val.1, x.property.1.1.le, x.property.1.2.le⟩ =
        a ⟨y.val.1, y.property.1.1.le, y.property.1.2.le⟩ :=
      congrArg (fun z : W × Set.Ioo (-1 : ℝ) 1 => z.1.val) hh
    have hy := congrArg (fun z : W × Set.Ioo (-1 : ℝ) 1 => z.2.val) hh
    exact Subtype.ext (Prod.ext (congrArg Subtype.val (hi hx)) hy)
  have hopen := (apm_t95j06_Q_aux_invariance_domain_prod_source
    (isOpen_Ioo.prod isOpen_Ioo) hF hFi).isOpen_range
  let g : V → B := fun v => (e.symm v).1.val
  have hg : IsOpenMap g := hW.isOpenMap_subtype_val.comp (isOpenMap_fst.comp e.symm.isOpenMap)
  have heq : g '' {v : V | v.val ∈ Set.range F} =
      a '' {t : Set.Icc (0 : ℝ) 1 | 0 < t.val ∧ t.val < 1} := by
    ext z
    constructor
    · rintro ⟨v, ⟨x, hx⟩, rfl⟩
      have he : e.symm v = P x := by
        apply e.injective
        simpa only [Homeomorph.apply_symm_apply] using (Subtype.ext hx.symm : v = e (P x))
      refine ⟨⟨x.val.1, x.property.1.1.le, x.property.1.2.le⟩, x.property.1, ?_⟩
      simp [g, he, P]
    · rintro ⟨t, ht, rfl⟩
      let x : T := ⟨(t.val, 0), ht, by norm_num⟩
      refine ⟨e (P x), ⟨x, rfl⟩, ?_⟩
      simp [g, P, x]
  rw [← heq]
  exact hg _ (hopen.preimage continuous_subtype_val)

/-- An open real subset of [0,1] contains neither endpoint. -/
lemma apm_t95j06_Q_aux_open_interval_endpoints
    {S : Set ℝ} (hS : IsOpen S) (hsub : S ⊆ Set.Icc 0 1) :
    (0 : ℝ) ∉ S ∧ (1 : ℝ) ∉ S := by
  constructor
  · intro h0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS 0 h0
    have hm : -ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (by linarith)]
      linarith
    have h := (hsub (hball hm)).1
    linarith
  · intro h1
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS 1 h1
    have hm : 1 + ε / 2 ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    have h := (hsub (hball hm)).2
    linarith

/-- Neither endpoint of an embedded base arc is interior to its closed image.
The inverse arc parameter on the interior would otherwise have an open image
in ℝ containing an endpoint of [0,1]. -/
lemma apm_t95j06_Q_aux_arc_endpoints_not_interior
    {B : Type*} [TopologicalSpace B] [T2Space B] {W : Set B}
    {V : Set apm_t95j06_E2} (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)
    (a : C(Set.Icc (0 : ℝ) 1, B)) (hi : Function.Injective a)
    (haW : Set.range a ⊆ W) :
    a ⟨0, by norm_num⟩ ∉ interior (Set.range a) ∧
      a ⟨1, by norm_num⟩ ∉ interior (Set.range a) := by
  let A := (a.continuous.isClosedEmbedding hi).isEmbedding.toHomeomorph
  let U := interior (Set.range a)
  let f : U → ℝ := fun x => (A.symm ⟨x.val, interior_subset x.property⟩).val
  have hf : Continuous f := continuous_subtype_val.comp
    (A.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hfi : Function.Injective f := by
    intro x y h
    have hh := A.symm.injective (Subtype.ext h)
    exact Subtype.ext (congrArg (fun z : Set.range a => z.val) hh)
  have hopen := apm_t95j06_Q_aux_base_coordinate_open hV e isOpen_interior
    (interior_subset.trans haW) hf hfi
  have hbound : Set.range f ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro _ ⟨x, rfl⟩
    exact (A.symm ⟨x.val, interior_subset x.property⟩).property
  have hend := apm_t95j06_Q_aux_open_interval_endpoints hopen hbound
  have hparam : ∀ t : Set.Icc (0 : ℝ) 1, ∀ ht : a t ∈ U,
      f ⟨a t, ht⟩ = t.val := by
    intro t ht
    change (A.symm (A t)).val = t.val
    rw [Homeomorph.symm_apply_apply]
  constructor
  · intro h
    exact hend.1 ⟨⟨_, h⟩, hparam _ h⟩
  · intro h
    exact hend.2 ⟨⟨_, h⟩, hparam _ h⟩

/-- An arc which starts on an embedded arc and ends off it cannot return to
the first arc when its interior is open in the ambient space and it avoids the
other endpoint.  This is the connectedness argument used after a crosscut. -/
lemma apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_aux_arc_intersection
    {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (α β : Set.Icc (0 : ℝ) 1 → Y) (hαc : Continuous α) (hβc : Continuous β)
    (hαi : Function.Injective α) (hβi : Function.Injective β)
    (b q r : Y)
    (hα0 : α ⟨0, by norm_num⟩ = b) (hα1 : α ⟨1, by norm_num⟩ = q)
    (hβ0 : β ⟨0, by norm_num⟩ = b) (hβ1 : β ⟨1, by norm_num⟩ = r)
    (hopen : IsOpen (Set.range α \ {b, q}))
    (hq : q ∉ Set.range β) (hr : r ∉ Set.range α) :
    Set.range β ∩ Set.range α = {b} := by
  let i0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let i1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hαcompact : IsCompact (Set.range α) := isCompact_range hαc
  have hD : Set.range β \ {b} = β '' Set.Ioc i0 i1 := by
    ext y
    constructor
    · rintro ⟨⟨t, rfl⟩, hne⟩
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · have : t ≠ i0 := by
          intro ht
          apply hne
          rw [ht]
          simpa [i0] using hβ0
        exact lt_of_le_of_ne t.2.1 (Ne.symm this)
      · exact t.2.2
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      intro htb
      have : β t = β i0 := by rw [hβ0]; exact htb
      exact (ne_of_gt ht.1) (Subtype.ext (congrArg Subtype.val (hβi this)))
  have hpre : IsPreconnected (Set.range β \ {b}) := by
    rw [hD]
    exact isPreconnected_Ioc.image β hβc.continuousOn
  have hcover : Set.range β \ {b} ⊆
      (Set.range α \ {b, q}) ∪ (Set.range α)ᶜ := by
    rintro y ⟨hyβ, hyb⟩
    by_cases hyα : y ∈ Set.range α
    · left
      refine ⟨hyα, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h
      rcases h with h | h
      · exact hyb h
      · exact hq (h ▸ hyβ)
    · exact Or.inr hyα
  have hsub : Set.range β \ {b} ⊆ (Set.range α)ᶜ := by
    apply hpre.subset_right_of_subset_union hopen hαcompact.isClosed.isOpen_compl
      (disjoint_compl_right.mono (fun _ h ↦ h.1) (fun _ h ↦ h)) hcover
    refine ⟨r, ⟨⟨i1, by simpa [i1] using hβ1⟩, ?_⟩, hr⟩
    intro hrb
    apply hr
    rw [hrb]
    exact ⟨i0, by simpa [i0] using hα0⟩
  ext y
  constructor
  · rintro ⟨hyβ, hyα⟩
    have : y = b := by
      by_contra hyb
      exact hsub ⟨hyβ, hyb⟩ hyα
    simpa [this]
  · intro hy
    have hyb : y = b := by simpa using hy
    subst y
    constructor
    · exact ⟨i0, by simpa [i0, hβ0]⟩
    · exact ⟨i0, by simpa [i0, hα0]⟩

/-- Loop erasure in metrizable Hausdorff spaces: a path between distinct
points contains an injectively parametrized arc with the same endpoints. -/
def apm_t95j06_ArcFromPath : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X]
    [TopologicalSpace.MetrizableSpace X] (x y : X), x ≠ y →
    ∀ p : Path x y, ∃ a : C(Set.Icc (0 : ℝ) 1, X),
      Function.Injective a ∧ a ⟨0, by norm_num⟩ = x ∧
      a ⟨1, by norm_num⟩ = y ∧ Set.range a ⊆ Set.range p

/-- Every open base neighborhood inside a planar product chart contains a
compact path-connected neighborhood. Project a sufficiently small closed disk
inside the part of the chart lying over the prescribed neighborhood. -/
lemma apm_t95j06_Q_aux_pathConnected_neighborhood
    {B : Type*} [TopologicalSpace B] {W : Set B} (hW : IsOpen W)
    {V : Set apm_t95j06_E2} (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)
    (b : B) {U : Set B} (hU : IsOpen U) (hUW : U ⊆ W) (hb : b ∈ U) :
    ∃ P : Set B, P ⊆ U ∧ IsCompact P ∧ IsPathConnected P ∧ b ∈ interior P := by
  let z : W × Set.Ioo (-1 : ℝ) 1 := ⟨⟨b, hUW hb⟩, ⟨0, by norm_num⟩⟩
  let p : V := e z
  let g : V → B := fun v ↦ (e.symm v).1.1
  have hg : Continuous g :=
    continuous_subtype_val.comp (continuous_fst.comp e.symm.continuous)
  have hgopen : IsOpenMap g :=
    hW.isOpenMap_subtype_val.comp (isOpenMap_fst.comp e.symm.isOpenMap)
  let S : Set apm_t95j06_E2 := Subtype.val '' (g ⁻¹' U)
  have hS : IsOpen S := hV.isOpenMap_subtype_val _ (hU.preimage hg)
  have hp : g p = b := by simp [g, p, z]
  have hpS : p.val ∈ S := ⟨p, by simpa [hp], rfl⟩
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hS p.val hpS
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hDS : Metric.closedBall p.val r ⊆ S := by
    intro u hu
    apply hεS
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hu) (by dsimp [r]; linarith)
  have hD : Metric.closedBall p.val r ⊆ V := by
    intro u hu
    obtain ⟨v, _, hv⟩ := hDS hu
    exact hv ▸ v.property
  let D := Metric.closedBall p.val r
  letI : CompactSpace D := (isCompact_iff_compactSpace).mp (isCompact_closedBall p.val r)
  letI : PathConnectedSpace D :=
    (isPathConnected_iff_pathConnectedSpace).mp ((convex_closedBall p.val r).isPathConnected ⟨p.val, Metric.mem_closedBall_self hr.le⟩)
  let f : D → B := fun u ↦ g ⟨u.val, hD u.property⟩
  have hf : Continuous f := hg.comp (continuous_subtype_val.subtype_mk _)
  refine ⟨Set.range f, ?_, isCompact_range hf, isPathConnected_range hf, ?_⟩
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, hv, heq⟩ := hDS u.property
    have hv' : v = ⟨u.val, hD u.property⟩ := Subtype.ext heq
    simpa only [hv'] using hv
  · let O : Set V := {v | v.val ∈ Metric.ball p.val r}
    have hO : IsOpen O := Metric.isOpen_ball.preimage continuous_subtype_val
    have hOP : g '' O ⊆ Set.range f := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨⟨v.val, Metric.ball_subset_closedBall hv⟩, rfl⟩
    apply interior_maximal hOP (hgopen O hO)
    exact ⟨p, Metric.mem_ball_self hr, hp⟩

/-- Under loop erasure, any two distinct points of a path-connected subset
are endpoints of an arc contained in that subset. -/
lemma apm_t95j06_Q_aux_arc_in_subset
    (harc : apm_t95j06_ArcFromPath)
    {B : Type} [TopologicalSpace B] [T2Space B]
    [TopologicalSpace.MetrizableSpace B]
    {P : Set B} (hP : IsPathConnected P) {b q : B}
    (hb : b ∈ P) (hq : q ∈ P) (hbq : b ≠ q) :
    ∃ a : C(Set.Icc (0 : ℝ) 1, B), Function.Injective a ∧
      a ⟨0, by norm_num⟩ = b ∧ a ⟨1, by norm_num⟩ = q ∧ Set.range a ⊆ P := by
  letI : PathConnectedSpace P := isPathConnected_iff_pathConnectedSpace.mp hP
  obtain ⟨a, hi, h0, h1, _⟩ := harc P ⟨b, hb⟩ ⟨q, hq⟩
    (fun h => hbq (congrArg Subtype.val h)) (PathConnectedSpace.somePath _ _)
  refine ⟨⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩, ?_, ?_, ?_, ?_⟩
  · intro s t h
    exact hi (Subtype.ext h)
  · exact congrArg Subtype.val h0
  · exact congrArg Subtype.val h1
  · rintro _ ⟨t, rfl⟩
    exact (a t).property

/-- An arc starting at one endpoint of another arc, avoiding its other
endpoint and ending outside it, cannot enter its open interior. The punctured
second arc is preconnected, while the first arc's interior and complement
form a disjoint open cover of it. -/
lemma apm_t95j06_Q_aux_arc_intersection
    {B : Type*} [TopologicalSpace B] [T2Space B]
    (a d : C(Set.Icc (0 : ℝ) 1, B)) (ha : Function.Injective a)
    (hd : Function.Injective d)
    (hopen : IsOpen (a '' {t : Set.Icc (0 : ℝ) 1 | 0 < t.val ∧ t.val < 1}))
    (h0 : a ⟨0, by norm_num⟩ = d ⟨0, by norm_num⟩)
    (hq : a ⟨1, by norm_num⟩ ∉ Set.range d)
    (hr : d ⟨1, by norm_num⟩ ∉ Set.range a) :
    Set.range a ∩ Set.range d = {a ⟨0, by norm_num⟩} := by
  let A := a '' {t : Set.Icc (0 : ℝ) 1 | 0 < t.val ∧ t.val < 1}
  let S := d '' Set.Ioc (0 : Set.Icc (0 : ℝ) 1) 1
  have hclosed : IsClosed (Set.range a) := (isCompact_range a.continuous).isClosed
  have hS : _root_.IsPreconnected S :=
    isPreconnected_Ioc.image d d.continuous.continuousOn
  have hcover : S ⊆ A ∪ (Set.range a)ᶜ := by
    rintro x ⟨t, ht, rfl⟩
    by_cases hx : d t ∈ Set.range a
    · obtain ⟨u, hu⟩ := hx
      apply Or.inl
      refine ⟨u, ⟨?_, ?_⟩, hu⟩
      · have hne : u.val ≠ 0 := by
          intro he
          have he' : u = ⟨0, by norm_num⟩ := Subtype.ext he
          have ht' : t = 0 := hd (by simpa only [he', h0] using hu.symm)
          exact (ne_of_gt ht.1) ht'
        exact lt_of_le_of_ne u.property.1 (Ne.symm hne)
      · have hne : u.val ≠ 1 := by
          intro he
          have he' : u = ⟨1, by norm_num⟩ := Subtype.ext he
          exact hq ⟨t, by simpa only [he'] using hu.symm⟩
        exact lt_of_le_of_ne u.property.2 hne
    · exact Or.inr hx
  have hdis : Disjoint A (Set.range a)ᶜ := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, _, rfl⟩ hx
    exact hx ⟨t, rfl⟩
  have hright : (S ∩ (Set.range a)ᶜ).Nonempty := by
    refine ⟨d ⟨1, by norm_num⟩, ?_, hr⟩
    exact ⟨1, by constructor <;> norm_num, rfl⟩
  have hout : S ⊆ (Set.range a)ᶜ :=
    hS.subset_right_of_subset_union hopen hclosed.isOpen_compl hdis hcover hright
  apply Set.Subset.antisymm
  · rintro x ⟨hx, t, rfl⟩
    by_cases ht : t.val = 0
    · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
      simpa only [Set.mem_singleton_iff, ht'] using h0.symm
    · exact False.elim (hout ⟨t, ⟨(show (0 : ℝ) < t.val from lt_of_le_of_ne t.property.1 (Ne.symm ht)), t.property.2⟩,
        rfl⟩ hx)
  · rintro x rfl
    exact ⟨⟨0, rfl⟩, ⟨0, h0.symm⟩⟩

/-- Loop erasure and planar product charts give two arcs leaving a base
point in different directions, with no other point in common. -/
lemma apm_t95j06_Q_aux_two_arcs
    (harc : apm_t95j06_ArcFromPath)
    {B : Type} [TopologicalSpace B] [T2Space B]
    [TopologicalSpace.MetrizableSpace B]
    {W : Set B} (hW : IsOpen W) {V : Set apm_t95j06_E2} (hV : IsOpen V)
    (e : (W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V) (b : B) (hb : b ∈ W) :
    ∃ q r : B, q ≠ b ∧ r ≠ b ∧ q ≠ r ∧
      ∃ a d : C(Set.Icc (0 : ℝ) 1, B),
        Function.Injective a ∧ Function.Injective d ∧
        a ⟨0, by norm_num⟩ = b ∧ a ⟨1, by norm_num⟩ = q ∧
        d ⟨0, by norm_num⟩ = b ∧ d ⟨1, by norm_num⟩ = r ∧
        Set.range a ⊆ W ∧ Set.range d ⊆ W ∧
        Set.range a ∩ Set.range d = {b} := by
  obtain ⟨P, hPW, _, hP, hbP⟩ :=
    apm_t95j06_Q_aux_pathConnected_neighborhood hW hV e b hW Set.Subset.rfl hb
  have hq : ∃ q ∈ P, q ≠ b := by
    by_contra! hn
    have he : interior P = {b} := by
      apply Set.Subset.antisymm
      · intro x hx
        exact hn x (interior_subset hx)
      · simpa only [Set.singleton_subset_iff] using hbP
    exact apm_t95j06_Q_aux_no_isolated hV e b hb (he ▸ isOpen_interior)
  obtain ⟨q, hqP, hqb⟩ := hq
  obtain ⟨a, hai, ha0, ha1, haP⟩ :=
    apm_t95j06_Q_aux_arc_in_subset harc hP (interior_subset hbP) hqP hqb.symm
  have haW := haP.trans hPW
  obtain ⟨P', hP'U, _, hP', hbP'⟩ :=
    apm_t95j06_Q_aux_pathConnected_neighborhood hW hV e b (U := W \ {q})
      (hW.inter isClosed_singleton.isOpen_compl) Set.diff_subset ⟨hb, hqb.symm⟩
  have hr : ∃ r ∈ P', r ∉ Set.range a := by
    by_contra! hn
    have hbA : b ∈ interior (Set.range a) := interior_mono hn hbP'
    exact (apm_t95j06_Q_aux_arc_endpoints_not_interior hV e a hai haW).1
      (ha0.symm ▸ hbA)
  obtain ⟨r, hrP, hrA⟩ := hr
  have hrb : r ≠ b := by
    intro h
    exact hrA ⟨0, by simpa only [h] using ha0⟩
  have hqr : q ≠ r := by
    intro h
    exact (hP'U hrP).2 (by simpa only [Set.mem_singleton_iff] using h.symm)
  obtain ⟨d, hdi, hd0, hd1, hdP⟩ :=
    apm_t95j06_Q_aux_arc_in_subset harc hP' (interior_subset hbP') hrP hrb.symm
  have hdW : Set.range d ⊆ W := hdP.trans (hP'U.trans Set.diff_subset)
  have hqD : a ⟨1, by norm_num⟩ ∉ Set.range d := by
    rw [ha1]
    intro h
    exact (hP'U (hdP h)).2 rfl
  have hrD : d ⟨1, by norm_num⟩ ∉ Set.range a := by simpa only [hd1] using hrA
  refine ⟨q, r, hqb, hrb, hqr, a, d, hai, hdi, ha0, ha1, hd0, hd1, haW, hdW, ?_⟩
  simpa only [ha0] using apm_t95j06_Q_aux_arc_intersection a d hai hdi
    (apm_t95j06_Q_aux_arc_interior_open hW hV e a hai haW)
    (ha0.trans hd0.symm) hqD hrD

/-- Concatenating two injective paths that meet only at the junction point
gives an injective path. -/
lemma apm_t95j06_Q_aux_path_trans_injective {Y : Type} [TopologicalSpace Y]
    {x y z : Y} (γ₁ : Path x y) (γ₂ : Path y z)
    (h₁ : Function.Injective γ₁) (h₂ : Function.Injective γ₂)
    (hmeet : Set.range γ₁ ∩ Set.range γ₂ ⊆ {y}) :
    Function.Injective (γ₁.trans γ₂) := by
  have mixed : ∀ s t : unitInterval, (s : ℝ) ≤ 1 / 2 → ¬ (t : ℝ) ≤ 1 / 2 →
      (γ₁.trans γ₂) s ≠ (γ₁.trans γ₂) t := by
    intro s t hs ht he
    rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at he
    have hy : γ₂ ⟨2 * t - 1, _⟩ ∈ ({y} : Set Y) := hmeet ⟨⟨_, he⟩, ⟨_, rfl⟩⟩
    have h0 : γ₂ ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ =
        γ₂ 0 := by rw [Path.source]; exact hy
    have := congrArg Subtype.val (h₂ h0)
    simp at this
    linarith [not_le.1 ht]
  intro s t he
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · have he' := he
    rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_pos ht] at he'
    have := congrArg Subtype.val (h₁ he')
    exact Subtype.ext (by simp at this; linarith)
  · exact absurd he (mixed s t hs ht)
  · exact absurd he.symm (mixed t s ht hs)
  · have he' := he
    rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_neg ht] at he'
    have := congrArg Subtype.val (h₂ he')
    exact Subtype.ext (by simp at this; linarith)

/-- **Q-design helper 9.**  Two injective arcs from `b`, to `q` and to `r`,
meeting only at `b`, paste to one injective arc from `r` through `b` (at the
parameter `1/2`) to `q` whose range is the union of their ranges. -/
lemma apm_t95j06_Q_aux_paste_arcs {Y : Type} [TopologicalSpace Y]
    (α β : C(Set.Icc (0 : ℝ) 1, Y)) (hαi : Function.Injective α)
    (hβi : Function.Injective β) (b q r : Y)
    (hα0 : α ⟨0, by norm_num⟩ = b) (hα1 : α ⟨1, by norm_num⟩ = q)
    (hβ0 : β ⟨0, by norm_num⟩ = b) (hβ1 : β ⟨1, by norm_num⟩ = r)
    (hmeet : Set.range α ∩ Set.range β = {b}) :
    ∃ η : C(Set.Icc (0 : ℝ) 1, Y), Function.Injective η ∧
      η ⟨0, by norm_num⟩ = r ∧ η ⟨1, by norm_num⟩ = q ∧
      η ⟨1 / 2, by norm_num⟩ = b ∧ Set.range η = Set.range α ∪ Set.range β := by
  let pα : Path b q := ⟨α, hα0, hα1⟩
  let pβ : Path b r := ⟨β, hβ0, hβ1⟩
  have hβs : Function.Injective pβ.symm := by
    intro s t h
    simp only [Path.symm_apply] at h
    exact unitInterval.symm_inj.mp (hβi h)
  have hrα : Set.range pα = Set.range α := rfl
  have hrβ : Set.range pβ.symm = Set.range β := Path.symm_range pβ
  have hinj := apm_t95j06_Q_aux_path_trans_injective pβ.symm pα hβs hαi
    (by rw [hrβ, hrα, Set.inter_comm, hmeet])
  refine ⟨(pβ.symm.trans pα).toContinuousMap, hinj, ?_, ?_, ?_, ?_⟩
  · exact (pβ.symm.trans pα).source
  · exact (pβ.symm.trans pα).target
  · change (pβ.symm.trans pα) ⟨1 / 2, _⟩ = b
    rw [Path.trans_apply, dif_pos (by norm_num)]
    have : (⟨2 * (1 / 2 : ℝ), by norm_num⟩ : unitInterval) = 1 := Subtype.ext (by norm_num)
    rw [this, Path.target]
  · change Set.range (pβ.symm.trans pα) = _
    rw [Path.trans_range, hrβ, hrα, Set.union_comm]

/-- The range of an embedded closed interval has exactly its two endpoints as
non-cut points.  This is the purely one-dimensional final step in the planar
crosscut construction: compactness, connectedness, and local connectedness
are transported through the interval-to-range homeomorphism, while deleting
an interior parameter leaves the two nonempty open halves. -/
lemma apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_aux_interval_range
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (η : Set.Icc (0 : ℝ) 1 → Y) (hηc : Continuous η)
    (hηi : Function.Injective η) :
    let K := Set.range η
    let b : Y := η ⟨1 / 2, by norm_num⟩
    IsCompact K ∧ IsConnected K ∧
      ∃ a c : K, a ≠ c ∧ (a : Y) ≠ b ∧ (c : Y) ≠ b ∧
        Nonempty (LocallyConnectedSpace K) ∧
        IsPreconnected ({a}ᶜ : Set K) ∧
        IsPreconnected ({c}ᶜ : Set K) ∧
        ∀ y : K, y ≠ a → y ≠ c → ¬ IsPreconnected ({y}ᶜ : Set K) := by
  dsimp only
  let I := Set.Icc (0 : ℝ) 1
  let i0 : I := ⟨0, by change (0 : ℝ) ∈ Set.Icc 0 1; norm_num⟩
  let i1 : I := ⟨1, by change (1 : ℝ) ∈ Set.Icc 0 1; norm_num⟩
  let im : I := ⟨1 / 2, by change (1 / 2 : ℝ) ∈ Set.Icc 0 1; norm_num⟩
  let K := Set.range η
  let A : I ≃ₜ K := (hηc.isClosedEmbedding hηi).isEmbedding.toHomeomorph
  have hAval (t : I) : (A t : Y) = η t := rfl
  have hcompact : IsCompact K := isCompact_range hηc
  have hconnected : IsConnected K := isConnected_range hηc
  letI : LocPathConnectedSpace I := convex_Icc (0 : ℝ) 1 |>.locPathConnectedSpace
  letI : LocallyConnectedSpace K := A.symm.locallyConnectedSpace
  have hlocal : Nonempty (LocallyConnectedSpace K) := ⟨inferInstance⟩
  let a : K := A i0
  let c : K := A i1
  have hac : a ≠ c := by
    intro h
    have := A.injective h
    norm_num [i0, i1] at this
  have hab : (a : Y) ≠ η im := by
    intro h
    have heq : η i0 = η im := by simpa [a, hAval] using h
    have heq' := congrArg Subtype.val (hηi heq)
    norm_num [i0, im] at heq'
  have hcb : (c : Y) ≠ η im := by
    intro h
    have heq : η i1 = η im := by simpa [c, hAval] using h
    have heq' := congrArg Subtype.val (hηi heq)
    norm_num [i1, im] at heq'
  have hpre0 : _root_.IsPreconnected ({i0}ᶜ : Set I) := by
    have heq : ({i0}ᶜ : Set I) = Set.Ioc i0 i1 := by
      ext t
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ioc]
      constructor
      · intro ht
        exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht), t.2.2⟩
      · exact fun ht h => (ne_of_gt ht.1) h
    rw [heq]
    exact isPreconnected_Ioc
  have hpre1 : _root_.IsPreconnected ({i1}ᶜ : Set I) := by
    have heq : ({i1}ᶜ : Set I) = Set.Ico i0 i1 := by
      ext t
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Ico]
      constructor
      · intro ht
        exact ⟨t.2.1, lt_of_le_of_ne t.2.2 ht⟩
      · exact fun ht h => (ne_of_gt ht.2) h.symm
    rw [heq]
    exact isPreconnected_Ico
  have htransport (t : I) (ht : _root_.IsPreconnected ({t}ᶜ : Set I)) :
      _root_.IsPreconnected ({A t}ᶜ : Set K) := by
    have heq : A '' ({t}ᶜ : Set I) = ({A t}ᶜ : Set K) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩ h
        exact hw (A.injective h)
      · intro hz
        refine ⟨A.symm z, ?_, A.apply_symm_apply z⟩
        intro h
        apply hz
        rw [Set.mem_singleton_iff, ← h, A.apply_symm_apply]
    rw [← heq, A.isPreconnected_image]
    exact ht
  refine ⟨hcompact, hconnected, a, c, hac, hab, hcb, hlocal,
    htransport i0 hpre0, htransport i1 hpre1, ?_⟩
  intro y hya hyc hpre
  let t : I := A.symm y
  have ht0 : t ≠ i0 := by
    intro h
    apply hya
    calc y = A t := (A.apply_symm_apply y).symm
      _ = A i0 := congrArg A h
  have ht1 : t ≠ i1 := by
    intro h
    apply hyc
    calc y = A t := (A.apply_symm_apply y).symm
      _ = A i1 := congrArg A h
  have htpos : 0 < t.1 := lt_of_le_of_ne t.2.1 (by
    intro h; apply ht0; exact Subtype.ext h.symm)
  have htlt : t.1 < 1 := lt_of_le_of_ne t.2.2 (by
    intro h; apply ht1; exact Subtype.ext h)
  have hpull : _root_.IsPreconnected ({t}ᶜ : Set I) := by
    have heq : A ⁻¹' ({y}ᶜ : Set K) = ({t}ᶜ : Set I) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hzy hzt
        apply hzy
        subst z
        dsimp [t]
        exact A.apply_symm_apply y
      · intro hzt hzy
        apply hzt
        apply A.injective
        rw [hzy, A.apply_symm_apply]
    rw [← heq, A.isPreconnected_preimage]
    exact hpre
  let U : Set I := {z | z.1 < t.1}
  let V : Set I := {z | t.1 < z.1}
  have hU : IsOpen U := isOpen_Iio.preimage continuous_subtype_val
  have hV : IsOpen V := isOpen_Ioi.preimage continuous_subtype_val
  have hcover : ({t}ᶜ : Set I) ⊆ U ∪ V := by
    intro z hz
    rcases lt_trichotomy z.1 t.1 with h | h | h
    · exact Or.inl h
    · exact (hz (Subtype.ext h)).elim
    · exact Or.inr h
  obtain ⟨z, hz, hzu, hzv⟩ := hpull U V hU hV hcover
    ⟨i0, by
      constructor
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht0.symm
      · exact htpos⟩
    ⟨i1, by
      constructor
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht1.symm
      · exact htlt⟩
  change z.1 < t.1 at hzu
  change t.1 < z.1 at hzv
  exact (not_lt_of_ge (le_of_lt hzv)) hzu

/-- **Arc from a path (loop erasure).**  In a metrizable Hausdorff space a
path between distinct points contains an injective arc with the same
endpoints.  Standard (e.g. Willard, *General Topology*, 31.5); here it is
being proved by topological loop erasure: a minimal admissible closed set of
parameters (`_loopEraseAdmissible_exists_minimal`), the induced order on its
image, and the classification `completeSeparableLinearOrder_homeomorph_Icc`.
Estimated 250--400 further lines. -/
theorem apm_t95j06_arcFromPath : apm_t95j06_ArcFromPath := by
  sorry

/-- **Q from arc extraction.**  Given loop erasure, two arcs from `b` inside
the chart neighbourhood meet only at `b` (helper 8); pasted, they give an arc
`η` through `b = η (1/2)` (helper 9), whose open interior contains `b`
(helper 5), and whose range has exactly two non-cut points (helper 10). -/
lemma apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_of_arcFromPath
    (harc : apm_t95j06_ArcFromPath)
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB)
    (hm : Nonempty (@TopologicalSpace.MetrizableSpace B tB))
    (b : B) (W : Set B) (hW : @IsOpen B tB W) (hbW : b ∈ W)
    (V : Set apm_t95j06_E2) (hV : IsOpen V)
    (hchart : Nonempty ((W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)) :
    ∃ K : Set B,
      @IsCompact B tB K ∧ @IsConnected B tB K ∧ b ∈ @interior B tB K ∧
      ∃ a c : K, a ≠ c ∧ (a : B) ≠ b ∧ (c : B) ≠ b ∧
        Nonempty (LocallyConnectedSpace K) ∧
        IsPreconnected ({a}ᶜ : Set K) ∧
        IsPreconnected ({c}ᶜ : Set K) ∧
        ∀ y : K, y ≠ a → y ≠ c → ¬ IsPreconnected ({y}ᶜ : Set K) := by
  letI := tB
  haveI := h2
  haveI : TopologicalSpace.MetrizableSpace B := hm.some
  obtain ⟨e⟩ := hchart
  obtain ⟨q, r, _hqb, _hrb, _hqr, a, d, hai, hdi, ha0, ha1, hd0, hd1, haW, hdW, hmeet⟩ :=
    apm_t95j06_Q_aux_two_arcs harc hW hV e b hbW
  obtain ⟨η, hηi, _hη0, _hη1, hηm, hηr⟩ :=
    apm_t95j06_Q_aux_paste_arcs a d hai hdi b q r ha0 ha1 hd0 hd1 hmeet
  have hηW : Set.range η ⊆ W := by
    rw [hηr]; exact Set.union_subset haW hdW
  have hopen := apm_t95j06_Q_aux_arc_interior_open hW hV e η hηi hηW
  have H := apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_aux_interval_range
    η η.continuous hηi
  dsimp only at H
  rw [hηm] at H
  obtain ⟨hK1, hK2, rest⟩ := H
  refine ⟨Set.range η, hK1, hK2, ?_, rest⟩
  rw [mem_interior]
  refine ⟨_, Set.image_subset_range _ _, hopen, ⟨⟨1 / 2, by norm_num⟩, ?_, hηm⟩⟩
  constructor <;> norm_num

/-- **Q, a two-endpoint arc neighbourhood from a planar product chart.**
One product chart around `b × 0` yields the required compact continuum in the
base: an embedded arc through `b`.  The proof (Q-design, codex-11) uses the
sorry-free invariance of domain instead of Jordan or crosscut separation:
arcs extracted from paths in small path-connected projected neighbourhoods
(`apm_t95j06_arcFromPath`), two of them meeting only at `b`, pasted into one
arc whose interior is open in `B`.  Its range has exactly two non-cut points.

At an endpoint of `[0,1]` no such product chart exists; a tripod contradicts
the two-endpoint conclusion; a Cantor factor lacks local connectedness/planarity;
and a circle passes because the construction is local. -/
theorem apm_t95j06_planarCrosscut_productChart_twoEndpoint_at
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB)
    (hlc : Nonempty (@LocallyCompactSpace B tB))
    (hm : Nonempty (@TopologicalSpace.MetrizableSpace B tB))
    (hconn : Nonempty (@LocallyConnectedSpace B tB))
    (b : B) (W : Set B) (hW : @IsOpen B tB W) (hbW : b ∈ W)
    (V : Set apm_t95j06_E2) (hV : IsOpen V)
    (hchart : Nonempty ((W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V)) :
    ∃ K : Set B,
      @IsCompact B tB K ∧ @IsConnected B tB K ∧ b ∈ @interior B tB K ∧
      ∃ a c : K, a ≠ c ∧ (a : B) ≠ b ∧ (c : B) ≠ b ∧
        Nonempty (LocallyConnectedSpace K) ∧
        IsPreconnected ({a}ᶜ : Set K) ∧
        IsPreconnected ({c}ᶜ : Set K) ∧
        ∀ y : K, y ≠ a → y ≠ c → ¬ IsPreconnected ({y}ᶜ : Set K) := by
  exact apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_of_arcFromPath
    apm_t95j06_arcFromPath B tB h2 hm b W hW hbW V hV hchart

/-- **Sub-leaf F3c — gating leaf (LIBRARY, estimated 300--400 lines).**
In words: planar arc-product neighbourhoods have arbitrarily local compact
continua with precisely two non-cut points.

Proof sketch: choose a small closed disk around `(b,0)` in the planar chart,
use local connectedness to take the component meeting the zero slice, and
project that component to the base.  A vertical crosscut through a base point
extends to a Jordan curve in the disk.  The Jordan separation theorem gives
the two sides and rules out both a third branch and a non-cut interior point.
Shrink once more so the projected continuum is a neighbourhood of `b`.
The planar input is the sorry-free `Reeken.jordanCurveTheorem`; Mathlib tools
are `IsCompact.image`, `IsConnected.image`, component maximality, and compact
sets being closed in a Hausdorff space.

Truth checks: a tripod fails because its branch produces three complementary
pieces; a Cantor factor fails local connectedness and cannot satisfy the planar
arc-product hypothesis; a discrete factor has a one-dimensional product.
This leaf contains all Jordan-strength work and gates the split. -/
theorem apm_t95j06_planarArcProducts_twoEndpointContinua
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB)
    (hplanar : @apm_t95j06_HasPlanarArcProducts B tB)
    (hlc : Nonempty (@LocallyCompactSpace B tB))
    (hm : Nonempty (@TopologicalSpace.MetrizableSpace B tB))
    (hconn : Nonempty (@LocallyConnectedSpace B tB)) :
    @apm_t95j06_HasTwoEndpointContinuumNeighborhoods B tB := by
  intro b
  obtain ⟨W, hW, hbW, V, hV, hchart⟩ := hplanar b
  exact apm_t95j06_planarCrosscut_productChart_twoEndpoint_at
    B tB h2 hlc hm hconn b W hW hbW V hV hchart

/- **Sub-leaf F3a (LIBRARY, estimated 180--300 lines).**  In words: local
Euclidean charts on `U × Circle` shrink around `(b,1)` to planar charts on a
product of a base neighbourhood with the fixed real arc `(-1,1)`.

Proof sketch: use `isLocalHomeomorph_circleExp` at zero to identify a circle
arc with a real interval.  A product-topology basis rectangle lies inside the
chosen Euclidean chart source; restrict the chart with `Homeomorph.setCongr`
and compose with the product of the circle-arc homeomorphism.  The fixed
linear rescaling sends the resulting interval to `Set.Ioo (-1) 1`.

Truth checks: no global logarithm on `Circle` is asserted.  The empty base is
vacuous; at a discrete base point the requested open planar target cannot
exist, so dimension zero is not smuggled through this statement. -/
open Set in
/-- A fixed open arc about `1 : Circle` is homeomorphic to `(-1,1)`.

Why true: `Circle.exp` is a local homeomorphism at `0`.  Shrink its source to
an open interval on which it is injective, then use an orientation-preserving
affine rescaling of that interval to `(-1,1)`.  This is only a local logarithm,
not a global one.  Estimated size: 35--65 lines. -/
theorem apm_t95j06_circle_openArc_one :
    ∃ A : Set Circle, IsOpen A ∧ (1 : Circle) ∈ A ∧
      Nonempty (A ≃ₜ Set.Ioo (-1 : ℝ) 1) := by
  have hπ := Real.pi_pos
  let A : Set Circle := {z | (z : ℂ) ∈ Complex.slitPlane}
  have hA : IsOpen A := Complex.isOpen_slitPlane.preimage continuous_subtype_val
  have hargexp : ∀ t : Set.Ioo (-1 : ℝ) 1, Complex.arg (Circle.exp (Real.pi * t.1)) = Real.pi * t.1 := by
    intro t
    rw [Circle.coe_exp, Complex.exp_mul_I]
    apply Complex.arg_cos_add_sin_mul_I
    constructor
    · nlinarith [t.2.1]
    · nlinarith [t.2.2]
  have hmemA : ∀ t : Set.Ioo (-1 : ℝ) 1, Circle.exp (Real.pi * t.1) ∈ A := by
    intro t
    show ((Circle.exp (Real.pi * t.1) : Circle) : ℂ) ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff_arg, hargexp]
    refine ⟨?_, Circle.coe_ne_zero _⟩
    intro h
    have : t.1 = 1 := by
      have := mul_left_cancel₀ hπ.ne' (h.trans (mul_one Real.pi).symm)
      exact this
    exact (ne_of_lt t.2.2) this
  have hargIoo : ∀ z : A, Complex.arg (z.1 : ℂ) / Real.pi ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro z
    have hz := (Complex.mem_slitPlane_iff_arg.mp z.2)
    obtain ⟨h1, h2⟩ := Complex.arg_mem_Ioc (z.1 : ℂ)
    have h2' : Complex.arg (z.1 : ℂ) < Real.pi := lt_of_le_of_ne h2 hz.1
    constructor
    · rw [lt_div_iff₀ hπ]; linarith
    · rw [div_lt_iff₀ hπ]; linarith
  refine ⟨A, hA, ?_, ⟨?_⟩⟩
  · show ((1 : Circle) : ℂ) ∈ Complex.slitPlane
    simp [Complex.one_mem_slitPlane]
  · exact
    { toFun := fun z => ⟨Complex.arg (z.1 : ℂ) / Real.pi, hargIoo z⟩
      invFun := fun t => ⟨Circle.exp (Real.pi * t.1), hmemA t⟩
      left_inv := by
        intro z
        apply Subtype.ext
        simp only
        rw [mul_div_cancel₀ _ hπ.ne']
        exact Circle.exp_arg z.1
      right_inv := by
        intro t
        apply Subtype.ext
        simp only
        rw [hargexp, mul_div_cancel_left₀ _ hπ.ne']
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.div_const
        rw [continuous_iff_continuousAt]
        intro z
        have h1 : ContinuousAt (fun w : A => ((w.1 : Circle) : ℂ)) z :=
          (continuous_subtype_val.comp continuous_subtype_val).continuousAt
        exact ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg z.2) h1
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val) }

open Set in
/-- A planar chart on `U × Circle` contains a basic rectangle `W × A` about
`(b,1)`, for any prescribed open neighbourhood `A` of `1`.

Why true: choose a planar chart at `(b,1)`, use the product-topology basis to
find `W₀ × A₀` inside its source, and replace the circle factor by `A₀ ∩ A`.
Restricting the chart to this open subtype gives a homeomorphism onto its open
image, exactly as in the earlier `aux_openSubtype` proof.  Estimated size:
90--150 lines. -/
theorem apm_t95j06_circleProducts_basicRectangle
    (B : Type) (tB : TopologicalSpace B)
    (hprod : ∀ b : B, ∃ U : Set B, @IsOpen B tB U ∧ b ∈ U ∧
      apm_t95j06_IsLocallyEuclideanPlane (U × Circle))
    (A : Set Circle) (hA : IsOpen A) (h1A : (1 : Circle) ∈ A) :
    ∀ b : B, ∃ W : Set B, IsOpen W ∧ b ∈ W ∧
      ∃ A' : Set Circle, IsOpen A' ∧ (1 : Circle) ∈ A' ∧ A' ⊆ A ∧
        ∃ V : Set apm_t95j06_E2, IsOpen V ∧
          Nonempty ((W × A') ≃ₜ V) := by
  intro b
  obtain ⟨U, hU, hbU, hloc⟩ := hprod b
  obtain ⟨C, hC, hpC, V, hV, ⟨c⟩⟩ := hloc (⟨b, hbU⟩, 1)
  obtain ⟨u, a, hu, ha, hbu, h1a, huaC⟩ := isOpen_prod_iff.mp hC ⟨b, hbU⟩ 1 hpC
  let ι : u → B := fun x => x.1.1
  have hι : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hWo : IsOpen (range ι) := by
    have : range ι = Subtype.val '' u := by
      ext y; constructor
      · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    rw [this]; exact hU.isOpenMap_subtype_val _ hu
  let A' : Set Circle := a ∩ A
  have hk : ∀ x : u × A', ((x.1 : U), (x.2 : Circle)) ∈ C :=
    fun x => huaC ⟨x.1.2, x.2.2.1⟩
  let k : u × A' → C := fun x => ⟨((x.1 : U), (x.2 : Circle)), hk x⟩
  have hkemb : Topology.IsEmbedding k := by
    rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff]
    exact Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.subtypeVal
  have hko : IsOpen (range k) := by
    have : range k = Subtype.val ⁻¹' (u ×ˢ A') := by
      ext z; constructor
      · rintro ⟨x, rfl⟩; exact ⟨x.1.2, x.2.2⟩
      · intro hz; exact ⟨(⟨z.1.1, hz.1⟩, ⟨z.1.2, hz.2⟩), rfl⟩
    rw [this]; exact (hu.prod (ha.inter hA)).preimage continuous_subtype_val
  let G : u × A' → apm_t95j06_E2 := fun x => (c (k x) : apm_t95j06_E2)
  have hG : Topology.IsEmbedding G :=
    Topology.IsEmbedding.subtypeVal.comp (c.isEmbedding.comp hkemb)
  have hGo : IsOpen (range G) := by
    have : range G = Subtype.val '' (c '' range k) := by
      rw [← range_comp, ← range_comp]; rfl
    rw [this]; exact hV.isOpenMap_subtype_val _ (c.isOpenMap _ hko)
  refine ⟨range ι, hWo, ⟨⟨⟨b, hbU⟩, hbu⟩, rfl⟩, A', ha.inter hA, ⟨h1a, h1A⟩,
    inter_subset_right, range G, hGo, ⟨?_⟩⟩
  exact (Homeomorph.prodCongr hι.toHomeomorph.symm (Homeomorph.refl A')).trans hG.toHomeomorph

open Set in
/-- A planar rectangle with circle factor an open subarc can be normalized to
the fixed interval `(-1,1)`.

Why true: transport the subarc through a local logarithm `A ≃ₜ (-1,1)`, choose
a smaller real open interval about the image of `1`, and affinely rescale it.
Restrict the planar chart to the corresponding open product subtype; its image
is open by `IsOpenEmbedding.isOpen_range`.  Estimated size: 55--95 lines. -/
theorem apm_t95j06_planarRectangle_normalizeArc
    (W : Type*) [TopologicalSpace W]
    (A A' : Set Circle) (hA' : IsOpen A') (h1A' : (1 : Circle) ∈ A')
    (hA'A : A' ⊆ A) (a : A ≃ₜ Set.Ioo (-1 : ℝ) 1)
    (V : Set apm_t95j06_E2) (hV : IsOpen V)
    (c : (W × A') ≃ₜ V) :
    ∃ V' : Set apm_t95j06_E2, IsOpen V' ∧
      Nonempty ((W × Set.Ioo (-1 : ℝ) 1) ≃ₜ V') := by
  -- the set of coordinates whose point lies in A'
  have hS : IsOpen {s : Set.Ioo (-1 : ℝ) 1 | ((a.symm s : A) : Circle) ∈ A'} :=
    hA'.preimage (continuous_subtype_val.comp a.symm.continuous)
  obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.mp hS
  set x0 : ℝ := (a ⟨1, hA'A h1A'⟩ : ℝ) with hx0
  have hx0I : x0 ∈ Ioo (-1 : ℝ) 1 := (a ⟨1, hA'A h1A'⟩).2
  have hx0O : x0 ∈ O := by
    have : (a ⟨1, hA'A h1A'⟩) ∈ {s : Set.Ioo (-1 : ℝ) 1 | ((a.symm s : A) : Circle) ∈ A'} := by
      simp [h1A']
    rw [← hOS] at this; exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hO.inter isOpen_Ioo) x0 ⟨hx0O, hx0I⟩
  set p := x0 - ε / 2
  set q := x0 + ε / 2
  have hpq : p < q := by simp only [p, q]; linarith
  have hsub' : Ioo p q ⊆ O ∩ Ioo (-1 : ℝ) 1 := by
    intro t ht; apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    simp only [p, q] at ht; constructor <;> linarith [ht.1, ht.2]
  have hsub : Ioo p q ⊆ Ioo (-1 : ℝ) 1 := fun t ht => (hsub' ht).2
  have hmem : ∀ t : Ioo p q, ((a.symm ⟨t.1, hsub t.2⟩ : A) : Circle) ∈ A' := by
    intro t
    have : (⟨t.1, hsub t.2⟩ : Set.Ioo (-1 : ℝ) 1) ∈ Subtype.val ⁻¹' O := (hsub' t.2).1
    rw [hOS] at this; exact this
  let g : Ioo p q → A' := fun t => ⟨(a.symm ⟨t.1, hsub t.2⟩ : Circle), hmem t⟩
  have hg : Topology.IsEmbedding g := by
    rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff]
    have : (Subtype.val ∘ g) = Subtype.val ∘ a.symm ∘ Set.inclusion hsub := rfl
    rw [this]
    exact Topology.IsEmbedding.subtypeVal.comp
      (a.symm.isEmbedding.comp (Topology.IsEmbedding.inclusion hsub))
  let ψ : A' → Set.Ioo (-1 : ℝ) 1 := fun z => a ⟨z.1, hA'A z.2⟩
  have hψ : Continuous ψ :=
    a.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hrg : range g = ψ ⁻¹' (Subtype.val ⁻¹' Ioo p q) := by
    ext z; constructor
    · rintro ⟨t, rfl⟩
      simp only [mem_preimage, ψ, g]
      have : (⟨((a.symm ⟨t.1, hsub t.2⟩ : A) : Circle), hA'A (hmem t)⟩ : A) =
          a.symm ⟨t.1, hsub t.2⟩ := rfl
      rw [this, Homeomorph.apply_symm_apply]; exact t.2
    · intro hz
      refine ⟨⟨(ψ z).1, hz⟩, ?_⟩
      apply Subtype.ext
      simp only [g, ψ]
      rw [Subtype.coe_eta, Homeomorph.symm_apply_apply]
  have hrgo : IsOpen (range g) := by
    rw [hrg]; exact (isOpen_Ioo.preimage continuous_subtype_val).preimage hψ
  let F : W × Ioo p q → apm_t95j06_E2 := fun x => (c (x.1, g x.2) : apm_t95j06_E2)
  have hF : Topology.IsEmbedding F :=
    Topology.IsEmbedding.subtypeVal.comp
      (c.isEmbedding.comp (Topology.IsEmbedding.id.prodMap hg))
  have hFo : IsOpen (range F) := by
    have : range F = Subtype.val '' (c '' (univ ×ˢ range g)) := by
      ext y; constructor
      · rintro ⟨⟨w, t⟩, rfl⟩
        exact ⟨c (w, g t), ⟨(w, g t), ⟨trivial, t, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨⟨w, z⟩, ⟨-, t, rfl⟩, rfl⟩, rfl⟩
        exact ⟨(w, t), rfl⟩
    rw [this]
    exact hV.isOpenMap_subtype_val _ (c.isOpenMap _ (isOpen_univ.prod hrgo))
  have hs : 0 < (q - p) / 2 := by linarith
  let aff : ℝ ≃ₜ ℝ := affineHomeomorph ((q - p) / 2) ((p + q) / 2) hs.ne'
  have himage : aff '' Ioo (-1 : ℝ) 1 = Ioo p q := by
    dsimp [aff]
    rw [affineHomeomorph_image_Ioo _ _ _ _ hs]
    congr 1 <;> ring
  let I : Ioo (-1 : ℝ) 1 ≃ₜ Ioo p q :=
    (aff.image (Ioo (-1 : ℝ) 1)).trans (Homeomorph.setCongr himage)
  exact ⟨range F, hFo, ⟨(Homeomorph.prodCongr (Homeomorph.refl W) I).trans hF.toHomeomorph⟩⟩

/-- Local Euclidean charts on `U × Circle` shrink around `(b,1)` to planar
charts on a product with the fixed real arc `(-1,1)`. -/
theorem apm_t95j06_circleProducts_localizeToPlanarArc
    (B : Type) (tB : TopologicalSpace B)
    (hprod : ∀ b : B, ∃ U : Set B, @IsOpen B tB U ∧ b ∈ U ∧
      apm_t95j06_IsLocallyEuclideanPlane (U × Circle)) :
    @apm_t95j06_HasPlanarArcProducts B tB := by
  obtain ⟨A, hA, h1A, ⟨a⟩⟩ := apm_t95j06_circle_openArc_one
  intro b
  obtain ⟨W, hW, hbW, A', hA', h1A', hA'A, V, hV, ⟨c⟩⟩ :=
    apm_t95j06_circleProducts_basicRectangle B tB hprod A hA h1A b
  obtain ⟨V', hV', hc'⟩ :=
    apm_t95j06_planarRectangle_normalizeArc W A A' hA' h1A' hA'A a V hV c
  exact ⟨W, hW, hbW, V', hV', hc'⟩

/-- **Sub-leaf F3b (LIBRARY, estimated 180--300 lines).**  In words: a
Hausdorff second-countable base with planar real-arc products is locally
compact, metrizable, and locally connected.

Proof sketch: the zero slice is a closed retract of each product chart.
Compact planar neighbourhoods project to compact base neighbourhoods.
Connected open planar neighbourhoods project under the open product
projection to a connected-neighbourhood basis.  Local compact Hausdorff gives
regularity, and Mathlib's
`metrizableSpace_of_t3_secondCountable` (Urysohn metrization) gives the metric.

Truth checks: Hausdorffness excludes the doubled line; second countability
excludes long-line variants; Cantor and tripod factors survive some regularity
conclusions but are not claimed to be intervals here. -/
theorem apm_t95j06_planarArcProducts_factor_regular
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB) (hsc : @SecondCountableTopology B tB)
    (hplanar : @apm_t95j06_HasPlanarArcProducts B tB) :
    Nonempty (@LocallyCompactSpace B tB) ∧
      Nonempty (@TopologicalSpace.MetrizableSpace B tB) ∧
      Nonempty (@LocallyConnectedSpace B tB) := by
  letI : TopologicalSpace B := tB
  letI : T2Space B := h2
  letI : SecondCountableTopology B := hsc
  let J : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hJ : IsOpen J := isOpen_Ioo
  letI : Nonempty J := ⟨⟨0, by norm_num [J]⟩⟩
  have factor_instances (W : Set B) (V : Set apm_t95j06_E2)
      (hV : IsOpen V) (e : (W × J) ≃ₜ V) :
      Nonempty (LocallyCompactSpace W) ∧ Nonempty (LocallyConnectedSpace W) := by
    letI : LocallyCompactSpace V := hV.locallyCompactSpace
    letI : LocallyConnectedSpace V := hV.locallyConnectedSpace
    letI : LocallyCompactSpace (W × J) :=
      e.locallyCompactSpace_iff.mpr inferInstance
    letI : LocallyConnectedSpace (W × J) := e.locallyConnectedSpace
    have hq : IsOpenQuotientMap (Prod.fst : W × J → W) :=
      ⟨Prod.fst_surjective, continuous_fst, isOpenMap_fst⟩
    letI : WeaklyLocallyCompactSpace W := hq.weaklyLocallyCompactSpace
    letI : LocallyCompactSpace W := inferInstance
    have hconn : LocallyConnectedSpace W := by
      rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
      intro w U hU
      let z : W × J := (w, ⟨0, by norm_num [J]⟩)
      have hpre : Prod.fst ⁻¹' U ∈ nhds z := continuousAt_fst hU
      obtain ⟨A, hAU, hAopen, hzA, hAconn⟩ :=
        locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
          (inferInstance : LocallyConnectedSpace (W × J)) z _ hpre
      refine ⟨Prod.fst '' A, ?_, hq.isOpenMap A hAopen,
        ⟨z, hzA, rfl⟩, hAconn.image _ continuous_fst.continuousOn⟩
      rintro _ ⟨a, ha, rfl⟩
      exact hAU ha
    exact ⟨⟨inferInstance⟩, ⟨hconn⟩⟩
  have local_factors (b : B) :
      ∃ W : Set B, IsOpen W ∧ b ∈ W ∧
        Nonempty (LocallyCompactSpace W) ∧ Nonempty (LocallyConnectedSpace W) := by
    obtain ⟨W, hW, hbW, V, hV, ⟨e⟩⟩ := hplanar b
    obtain ⟨hc, hconn⟩ := factor_instances W V hV e
    exact ⟨W, hW, hbW, hc, hconn⟩
  have hwlc : WeaklyLocallyCompactSpace B := by
    constructor
    intro b
    obtain ⟨W, hW, hbW, ⟨hcW⟩, _⟩ := local_factors b
    letI : LocallyCompactSpace W := hcW
    obtain ⟨K, hKcompact, hKnhds⟩ :=
      exists_compact_mem_nhds (⟨b, hbW⟩ : W)
    refine ⟨Subtype.val '' K, hKcompact.image continuous_subtype_val, ?_⟩
    exact hW.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hKnhds
  letI : WeaklyLocallyCompactSpace B := hwlc
  letI : LocallyCompactSpace B := inferInstance
  have hconnected : LocallyConnectedSpace B := by
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro b U hU
    obtain ⟨W, hW, hbW, _, ⟨hconnW⟩⟩ := local_factors b
    letI : LocallyConnectedSpace W := hconnW
    have hpre : Subtype.val ⁻¹' U ∈ nhds (⟨b, hbW⟩ : W) :=
      continuousAt_subtype_val hU
    obtain ⟨A, hAU, hAopen, hbA, hAconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp hconnW
        (⟨b, hbW⟩ : W) _ hpre
    refine ⟨Subtype.val '' A, ?_,
      hW.isOpenEmbedding_subtypeVal.isOpenMap A hAopen,
      ⟨⟨b, hbW⟩, hbA, rfl⟩,
      hAconn.image _ continuous_subtype_val.continuousOn⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hAU ha
  letI : LocallyConnectedSpace B := hconnected
  letI : RegularSpace B := inferInstance
  letI : T3Space B := inferInstance
  letI : TopologicalSpace.MetrizableSpace B :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable B
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/- **Moore--Whyburn arc-recognition theorem (LIBRARY, estimated 180--300
lines).** A nondegenerate compact connected locally connected metrizable
continuum whose only non-cut points are `a` and `c` is an arc, with those
points as its endpoints.

This is true by ordering the remaining points according to which component
of a puncture contains `a`.  Local connectedness makes this a dense order
whose order topology is the given topology; compactness supplies order
completeness, and metrizability supplies separability.  The resulting compact
separable linear continuum is order-isomorphic, hence homeomorphic, to the
unit interval. -/
/- **Moore cut-point order (estimated 120--200 lines).** The separation
relation defined by the component of `K \\ {y}` containing `a` equips `K`
with a complete dense linear order, with endpoints `a,c`, whose order topology
is the original topology.

This is true because each non-endpoint puncture has exactly two components:
local connectedness makes those components open, giving totality and the
order-topology comparison; connectedness gives density, and compactness gives
suprema and infima. -/
/-- A certificate that `K \\ {y}` has exactly two connected components,
labelled by the endpoints they contain. -/
structure apm_t95j06_PunctureSplit
    (K : Type*) [TopologicalSpace K] (a c y : K) where
  sideA : Set K
  sideC : Set K
  sideA_open : IsOpen sideA
  sideC_open : IsOpen sideC
  sideA_preconnected : IsPreconnected sideA
  sideC_preconnected : IsPreconnected sideC
  a_mem : a ∈ sideA
  c_mem : c ∈ sideC
  disjoint : Disjoint sideA sideC
  cover : sideA ∪ sideC = ({y}ᶜ : Set K)
  maximal : ∀ S : Set K, S.Nonempty → IsPreconnected S →
    S ⊆ ({y}ᶜ : Set K) → S ⊆ sideA ∨ S ⊆ sideC

/- **C1, puncture structure (estimated 55--90 lines).** Every non-endpoint
puncture has exactly two open connected components, one containing `a` and
the other containing `c`.

This is true because the puncture is disconnected by `hcut`; local
connectedness makes its connected components open.  If there were a third
component, or if `a,c` lay in the same component, adjoining either of the
other endpoint punctures would contradict the assumed connectedness of those
two punctures. -/
/-- The connected component of an endpoint in a non-endpoint puncture is
open, connected, contained in the puncture, and maximal among connected
subsets of the puncture containing that endpoint. -/
lemma apm_t95j06_puncture_endpointComponent
    (K : Type*) [TopologicalSpace K] [T1Space K] [LocallyConnectedSpace K]
    (a y : K) (hay : a ≠ y) :
    ∃ A : Set K,
      IsOpen A ∧ IsPreconnected A ∧ a ∈ A ∧ A ⊆ ({y}ᶜ : Set K) ∧
      ∀ S : Set K, IsPreconnected S → a ∈ S →
        S ⊆ ({y}ᶜ : Set K) → S ⊆ A := by
  let F : Set K := ({y}ᶜ : Set K)
  let A := connectedComponentIn F a
  have haF : a ∈ F := by
    simpa [F, Set.mem_compl_iff, Set.mem_singleton_iff] using hay
  refine ⟨A, ?_, isPreconnected_connectedComponentIn,
    mem_connectedComponentIn haF, connectedComponentIn_subset F a, ?_⟩
  · exact (isClosed_singleton.isOpen_compl.connectedComponentIn)
  · intro S hS haS hSF
    exact hS.subset_connectedComponentIn haS hSF

/-- Both distinguished endpoints therefore have canonical open maximal
components in every non-endpoint puncture. -/
lemma apm_t95j06_puncture_endpointComponents
    (K : Type*) [TopologicalSpace K] [T1Space K] [LocallyConnectedSpace K]
    (a c y : K) (hya : y ≠ a) (hyc : y ≠ c) :
    (∃ A : Set K,
      IsOpen A ∧ IsPreconnected A ∧ a ∈ A ∧ A ⊆ ({y}ᶜ : Set K)) ∧
    ∃ C : Set K,
      IsOpen C ∧ IsPreconnected C ∧ c ∈ C ∧ C ⊆ ({y}ᶜ : Set K) := by
  obtain ⟨A, hAo, hAc, haA, hAF, _⟩ :=
    apm_t95j06_puncture_endpointComponent K a y hya.symm
  obtain ⟨C, hCo, hCc, hcC, hCF, _⟩ :=
    apm_t95j06_puncture_endpointComponent K c y hyc.symm
  exact ⟨⟨A, hAo, hAc, haA, hAF⟩, ⟨C, hCo, hCc, hcC, hCF⟩⟩

/- **Endpoint in every puncture branch (estimated 45--75 lines).** Every
connected component of a non-endpoint puncture contains `a` or `c`.

This is true for a compact locally connected continuum because each component
of the complement of a cut point contains a non-cut point of the original
continuum: otherwise a nested basis of connected open neighbourhoods in that
branch, together with compactness, produces an additional non-cut point.
Here the hypotheses say that the only non-cut points are `a` and `c`. -/
/-- A side of a puncture separation becomes a closed connected subcontinuum
after adjoining the puncture.  This is the elementary boundary-bumping step:
the other side is exactly its open complement, and any separation after
adjoining the puncture would extend, by adding the other puncture side to the
piece containing the puncture, to a separation of the whole space. -/
lemma apm_t95j06_cutSide_adjoin_puncture
    (X : Type*) [TopologicalSpace X]
    (hX : IsConnected (Set.univ : Set X)) (p : X) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hcover : U ∪ V = ({p}ᶜ : Set X))
    (hUne : U.Nonempty) (hVne : V.Nonempty) :
    IsClosed (U ∪ {p}) ∧ IsPreconnected (U ∪ {p}) := by
  have hpU : p ∉ U := by
    intro hp
    have : p ∈ ({p}ᶜ : Set X) := hcover ▸ Or.inl hp
    exact this (Set.mem_singleton p)
  have hpV : p ∉ V := by
    intro hp
    have : p ∈ ({p}ᶜ : Set X) := hcover ▸ Or.inr hp
    exact this (Set.mem_singleton p)
  have hcompl : (U ∪ {p})ᶜ = V := by
    ext x
    constructor
    · intro hx
      have hxp : x ≠ p := by
        intro h
        exact hx (Or.inr (Set.mem_singleton_iff.mpr h))
      have hxpunct : x ∈ ({p}ᶜ : Set X) := by simpa
      rw [← hcover] at hxpunct
      exact hxpunct.resolve_left (fun hxU => hx (Or.inl hxU))
    · intro hxV hx
      rcases hx with hxU | hxp
      · exact Set.disjoint_left.1 hUV hxU hxV
      · exact hpV (Set.mem_singleton_iff.mp hxp ▸ hxV)
  have hclosed : IsClosed (U ∪ {p}) := isOpen_compl_iff.mp (hcompl.symm ▸ hV)
  refine ⟨hclosed, isPreconnected_iff_subset_of_disjoint.mpr ?_⟩
  intro P Q hP hQ hK hPQ
  by_contra hne
  push_neg at hne
  obtain ⟨hnotP, hnotQ⟩ := hne
  have hpK : p ∈ U ∪ {p} := Or.inr (Set.mem_singleton p)
  rcases hK hpK with hpP | hpQ
  · have hpnotQ : p ∉ Q := by
      intro hpQ'
      have : p ∈ (U ∪ {p}) ∩ (P ∩ Q) := ⟨hpK, hpP, hpQ'⟩
      rw [hPQ] at this
      exact this.elim
    let S : Set X := (U ∪ {p}) ∩ Q
    have hSeq : S = U ∩ Q := by
      ext x
      constructor
      · rintro ⟨hxU | hxp, hxQ⟩
        · exact ⟨hxU, hxQ⟩
        · exact False.elim (hpnotQ (Set.mem_singleton_iff.mp hxp ▸ hxQ))
      · rintro ⟨hxU, hxQ⟩
        exact ⟨Or.inl hxU, hxQ⟩
    have hSopen : IsOpen S := hSeq ▸ hU.inter hQ
    have hSclosed : IsClosed S := by
      have : S = (U ∪ {p}) \ P := by
        ext x
        constructor
        · rintro ⟨hxK, hxQ⟩
          exact ⟨hxK, fun hxP => by
            have : x ∈ (U ∪ {p}) ∩ (P ∩ Q) := ⟨hxK, hxP, hxQ⟩
            rw [hPQ] at this
            exact this.elim⟩
        · rintro ⟨hxK, hxnotP⟩
          rcases hK hxK with hxP | hxQ
          · exact False.elim (hxnotP hxP)
          · exact ⟨hxK, hxQ⟩
      rw [this]
      exact hclosed.sdiff hP
    have hSne : S.Nonempty := by
      obtain ⟨x, hxK, hxnotP⟩ := Set.not_subset.mp hnotP
      rcases hK hxK with hxP | hxQ
      · exact False.elim (hxnotP hxP)
      · exact ⟨x, hxK, hxQ⟩
    letI : PreconnectedSpace X := preconnectedSpace_iff_univ.mpr hX.isPreconnected
    have hSuniv : S = Set.univ := (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ hSne
    exact hpnotQ (by have := hSuniv.symm ▸ Set.mem_univ p; exact this.2)
  · have hpnotP : p ∉ P := by
      intro hpP'
      have : p ∈ (U ∪ {p}) ∩ (P ∩ Q) := ⟨hpK, hpP', hpQ⟩
      rw [hPQ] at this
      exact this.elim
    let S : Set X := (U ∪ {p}) ∩ P
    have hSeq : S = U ∩ P := by
      ext x
      constructor
      · rintro ⟨hxU | hxp, hxP⟩
        · exact ⟨hxU, hxP⟩
        · exact False.elim (hpnotP (Set.mem_singleton_iff.mp hxp ▸ hxP))
      · rintro ⟨hxU, hxP⟩
        exact ⟨Or.inl hxU, hxP⟩
    have hSopen : IsOpen S := hSeq ▸ hU.inter hP
    have hSclosed : IsClosed S := by
      have : S = (U ∪ {p}) \ Q := by
        ext x
        constructor
        · rintro ⟨hxK, hxP⟩
          exact ⟨hxK, fun hxQ => by
            have : x ∈ (U ∪ {p}) ∩ (P ∩ Q) := ⟨hxK, hxP, hxQ⟩
            rw [hPQ] at this
            exact this.elim⟩
        · rintro ⟨hxK, hxnotQ⟩
          rcases hK hxK with hxP | hxQ
          · exact ⟨hxK, hxP⟩
          · exact False.elim (hxnotQ hxQ)
      rw [this]
      exact hclosed.sdiff hQ
    have hSne : S.Nonempty := by
      obtain ⟨x, hxK, hxnotQ⟩ := Set.not_subset.mp hnotQ
      rcases hK hxK with hxP | hxQ
      · exact ⟨x, hxK, hxP⟩
      · exact False.elim (hxnotQ hxQ)
    letI : PreconnectedSpace X := preconnectedSpace_iff_univ.mpr hX.isPreconnected
    have hSuniv : S = Set.univ := (show IsClopen S from ⟨hSclosed, hSopen⟩).eq_univ hSne
    exact hpnotP (by have := hSuniv.symm ▸ Set.mem_univ p; exact this.2)

/-- A chosen separation of a cut-point complement, labelled so that `p` lies
on the coside. -/
structure apm_t95j06_CutSideData
    (X : Type*) [TopologicalSpace X] (r p : X) where
  side : Set X
  coside : Set X
  side_open : IsOpen side
  coside_open : IsOpen coside
  side_nonempty : side.Nonempty
  p_mem_coside : p ∈ coside
  disjoint : Disjoint side coside
  cover : side ∪ coside = ({r}ᶜ : Set X)

/-- A cut point and a distinct reference point admit an endpoint-labelled
open separation. -/
lemma apm_t95j06_CutSideData.exists
    (X : Type*) [TopologicalSpace X] [T1Space X] (r p : X)
    (hcut : ¬ IsPreconnected ({r}ᶜ : Set X)) (hpr : p ≠ r) :
    Nonempty (apm_t95j06_CutSideData X r p) := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint] at hcut
  push_neg at hcut
  obtain ⟨u, v, hu, hv, hcover, hinter, hnu, hnv⟩ := hcut
  let P : Set X := ({r}ᶜ : Set X)
  let U : Set X := P ∩ u
  let V : Set X := P ∩ v
  have hPo : IsOpen P := isClosed_singleton.isOpen_compl
  have hUo : IsOpen U := hPo.inter hu
  have hVo : IsOpen V := hPo.inter hv
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    have he : x ∈ (∅ : Set X) := hinter ▸ ⟨hxU.1, hxU.2, hxV.2⟩
    exact he.elim
  have hUVcover : U ∪ V = P := by
    apply Set.Subset.antisymm
    · exact Set.union_subset Set.inter_subset_left Set.inter_subset_left
    · intro x hxP
      rcases hcover hxP with hxu | hxv
      · exact Or.inl ⟨hxP, hxu⟩
      · exact Or.inr ⟨hxP, hxv⟩
  have hUne : U.Nonempty := by
    obtain ⟨x, hxP, hxnotv⟩ := Set.not_subset.mp hnv
    rcases hcover hxP with hxu | hxv
    · exact ⟨x, hxP, hxu⟩
    · exact False.elim (hxnotv hxv)
  have hVne : V.Nonempty := by
    obtain ⟨x, hxP, hxnotu⟩ := Set.not_subset.mp hnu
    rcases hcover hxP with hxu | hxv
    · exact False.elim (hxnotu hxu)
    · exact ⟨x, hxP, hxv⟩
  have hpP : p ∈ P := by simpa [P]
  rcases hUVcover.symm.subset hpP with hpU | hpV
  · exact ⟨{
      side := V, coside := U, side_open := hVo, coside_open := hUo,
      side_nonempty := hVne, p_mem_coside := hpU,
      disjoint := hUV.symm, cover := by simpa [P, Set.union_comm] using hUVcover }⟩
  · exact ⟨{
      side := U, coside := V, side_open := hUo, coside_open := hVo,
      side_nonempty := hUne, p_mem_coside := hpV,
      disjoint := hUV, cover := by simpa [P] using hUVcover }⟩

/-- The canonical labelled cut-side data. -/
noncomputable def apm_t95j06_cutSideData
    (X : Type*) [TopologicalSpace X] [T1Space X] (r p : X)
    (hcut : ¬ IsPreconnected ({r}ᶜ : Set X)) (hpr : p ≠ r) :
    apm_t95j06_CutSideData X r p :=
  Classical.choice (apm_t95j06_CutSideData.exists X r p hcut hpr)

/-- **H3, nesting of cut sides.**  If `r'` lies on the side of `r` away from
`p`, then the side of `r'` away from `p`, with `r'` adjoined, lies inside the
side of `r` and misses `r`.  The coside of `r` with `r` adjoined is
preconnected, contains `p` and misses `r'`, so it lies in the coside of `r'`;
then the side of `r'` with `r'` adjoined is preconnected, misses `r` and meets
the side of `r` at `r'`. -/
lemma apm_t95j06_CutSideData.nested
    {X : Type*} [TopologicalSpace X]
    (hX : IsConnected (Set.univ : Set X)) {r r' p : X}
    (D : apm_t95j06_CutSideData X r p) (D' : apm_t95j06_CutSideData X r' p)
    (hr' : r' ∈ D.side) :
    D'.side ∪ {r'} ⊆ D.side ∧ r ∉ D'.side ∪ {r'} := by
  have hpD : p ∉ D.side := fun h => Set.disjoint_left.1 D.disjoint h D.p_mem_coside
  have hpD' : p ∉ D'.side := fun h => Set.disjoint_left.1 D'.disjoint h D'.p_mem_coside
  have hrr' : r' ≠ r := by
    have : r' ∈ ({r}ᶜ : Set X) := D.cover ▸ Or.inl hr'
    simpa using this
  -- the coside of `r`, with `r`, lies in the coside of `r'`
  have hpre1 : IsPreconnected (D.coside ∪ {r}) :=
    (apm_t95j06_cutSide_adjoin_puncture X hX r D.coside D.side D.coside_open D.side_open
      D.disjoint.symm (by rw [Set.union_comm]; exact D.cover)
      ⟨p, D.p_mem_coside⟩ D.side_nonempty).2
  have hsub1 : D.coside ∪ {r} ⊆ D'.side ∪ D'.coside := by
    rw [D'.cover]
    rintro x (hx | hx)
    · intro hxr
      rw [Set.mem_singleton_iff] at hxr
      subst hxr
      exact Set.disjoint_left.1 D.disjoint hr' hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa using hrr'.symm
  have hco : D.coside ∪ {r} ⊆ D'.coside := by
    rcases hpre1.subset_or_subset D'.side_open D'.coside_open D'.disjoint hsub1 with h | h
    · exact absurd (h (Or.inl D.p_mem_coside)) hpD'
    · exact h
  have hrco : r ∈ D'.coside := hco (Or.inr rfl)
  have hrside : r ∉ D'.side := fun h => Set.disjoint_left.1 D'.disjoint h hrco
  have hnot : r ∉ D'.side ∪ {r'} := by
    rintro (h | h)
    · exact hrside h
    · exact hrr' (Set.mem_singleton_iff.mp h).symm
  refine ⟨?_, hnot⟩
  have hpre2 : IsPreconnected (D'.side ∪ {r'}) :=
    (apm_t95j06_cutSide_adjoin_puncture X hX r' D'.side D'.coside D'.side_open D'.coside_open
      D'.disjoint D'.cover D'.side_nonempty ⟨p, D'.p_mem_coside⟩).2
  have hsub2 : D'.side ∪ {r'} ⊆ D.side ∪ D.coside := by
    rw [D.cover]
    intro x hx hxr
    rw [Set.mem_singleton_iff] at hxr
    subst hxr
    exact hnot hx
  rcases hpre2.subset_or_subset D.side_open D.coside_open D.disjoint hsub2 with h | h
  · exact h
  · exact absurd (h (Or.inr rfl)) (fun h' => Set.disjoint_left.1 D.disjoint hr' h')

/-- **One-sided boundary bumping (estimated 250--450 lines; LIBRARY).**  Each
nonempty side of a separation of a punctured compact Hausdorff continuum
contains a point whose removal does not disconnect the ambient continuum.

Proof sketch: assuming every point of `A` is a cut point, choose at each such
point the cut side avoiding a fixed point of `B`.  The nesting lemma obtained
from `apm_t95j06_cutSide_adjoin_puncture` orders the resulting compact
subcontinua strictly by reverse inclusion.  A maximal chain has nonempty
intersection by compactness.  A point in that intersection either is already
non-cut, or its avoiding side strictly extends the chain, contradicting
maximality.  Compactness is essential; an open interval side can have an
escaping nested family. -/
theorem apm_t95j06_cutSide_contains_nonCutPoint
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hX : IsConnected (Set.univ : Set X)) (q : X) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = ({q}ᶜ : Set X))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ∃ x ∈ A, IsPreconnected ({x}ᶜ : Set X) := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨p, hpB⟩ := hBne
  have hpA : ∀ r ∈ A, p ≠ r := fun r hr h => Set.disjoint_left.1 hAB hr (h ▸ hpB)
  let D0 : apm_t95j06_CutSideData X q p :=
    { side := A, coside := B, side_open := hA, coside_open := hB, side_nonempty := hAne,
      p_mem_coside := hpB, disjoint := hAB, cover := hcover }
  let D : ∀ r, r ∈ A → apm_t95j06_CutSideData X r p := fun r hr =>
    apm_t95j06_cutSideData X r p (hnone r hr) (hpA r hr)
  let K : ∀ r, r ∈ A → Set X := fun r hr => (D r hr).side ∪ {r}
  have hKA : ∀ r (hr : r ∈ A), K r hr ⊆ A := fun r hr =>
    (apm_t95j06_CutSideData.nested hX D0 (D r hr) hr).1
  have hKclosed : ∀ r (hr : r ∈ A), IsClosed (K r hr) := fun r hr =>
    (apm_t95j06_cutSide_adjoin_puncture X hX r (D r hr).side (D r hr).coside
      (D r hr).side_open (D r hr).coside_open (D r hr).disjoint (D r hr).cover
      (D r hr).side_nonempty ⟨p, (D r hr).p_mem_coside⟩).1
  -- `K x ⊆ K r` whenever `x ∈ K r`
  have hKsub : ∀ r (hr : r ∈ A) x (hx : x ∈ A), x ∈ K r hr → K x hx ⊆ K r hr := by
    intro r hr x hx hxK
    rcases hxK with hxs | hxr
    · exact (apm_t95j06_CutSideData.nested hX (D r hr) (D x hx) hxs).1.trans
        Set.subset_union_left
    · rw [Set.mem_singleton_iff] at hxr
      subst hxr
      exact le_rfl
  let S : Set (Set X) := {L | ∃ r, ∃ hr : r ∈ A, L = K r hr}
  obtain ⟨r0, hr0⟩ := hAne
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty S (by
    intro c hcS hchain hcne
    haveI : Nonempty c := hcne.to_subtype
    have hdir : Directed (· ⊇ ·) (fun L : c => (L : Set X)) := by
      intro L₁ L₂
      rcases eq_or_ne (L₁ : Set X) L₂ with h | h
      · exact ⟨L₁, le_rfl, show (L₁ : Set X) ⊆ L₂ from h ▸ subset_rfl⟩
      · rcases hchain L₁.2 L₂.2 h with h12 | h21
        · exact ⟨L₁, le_rfl, h12⟩
        · exact ⟨L₂, h21, le_rfl⟩
    have hne : ((⋂ L : c, (L : Set X))).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir
      · intro L
        obtain ⟨r, hr, hL⟩ := hcS L.2
        exact ⟨r, hL ▸ Or.inr rfl⟩
      · intro L
        obtain ⟨r, hr, hL⟩ := hcS L.2
        exact hL ▸ (hKclosed r hr).isCompact
      · intro L
        obtain ⟨r, hr, hL⟩ := hcS L.2
        exact hL ▸ hKclosed r hr
    obtain ⟨x, hx⟩ := hne
    rw [Set.mem_iInter] at hx
    obtain ⟨L0, hL0⟩ := hcne
    obtain ⟨r, hr, hL⟩ := hcS hL0
    have hxA : x ∈ A := hKA r hr (hL ▸ hx ⟨L0, hL0⟩)
    refine ⟨K x hxA, ⟨x, hxA, rfl⟩, ?_⟩
    intro L hL'
    obtain ⟨s, hs, rfl⟩ := hcS hL'
    exact hKsub s hs x hxA (hx ⟨_, hL'⟩)) (K r0 hr0) ⟨r0, hr0, rfl⟩
  obtain ⟨r, hr, rfl⟩ := hm.prop
  obtain ⟨y, hy⟩ := (D r hr).side_nonempty
  have hyA : y ∈ A := hKA r hr (Or.inl hy)
  have hnest := apm_t95j06_CutSideData.nested hX (D r hr) (D y hyA) hy
  have hle : K y hyA ⊆ K r hr := hnest.1.trans Set.subset_union_left
  have heq : K r hr ⊆ K y hyA := hm.2 ⟨y, hyA, rfl⟩ hle
  exact hnest.2 (heq (Or.inr rfl))

/-- Every nondegenerate compact connected Hausdorff continuum has two
distinct non-cut points.  This is the one classical continuum-theory input
used below (the boundary-bumping theorem). -/
theorem apm_t95j06_continuum_exists_two_nonCutPoints
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hX : IsConnected (Set.univ : Set X)) [Nontrivial X] :
    ∃ p q : X, p ≠ q ∧
      IsPreconnected ({p}ᶜ : Set X) ∧
      IsPreconnected ({q}ᶜ : Set X) := by
  classical
  by_cases hall : ∀ p : X, IsPreconnected ({p}ᶜ : Set X)
  · obtain ⟨p, q, hpq⟩ := exists_pair_ne X
    exact ⟨p, q, hpq, hall p, hall q⟩
  · push_neg at hall
    obtain ⟨q, hq⟩ := hall
    rw [isPreconnected_iff_subset_of_disjoint] at hq
    push_neg at hq
    obtain ⟨u, v, hu, hv, hcover, hinter, hnu, hnv⟩ := hq
    let P : Set X := ({q}ᶜ : Set X)
    let U : Set X := P ∩ u
    let V : Set X := P ∩ v
    have hPo : IsOpen P := isClosed_singleton.isOpen_compl
    have hUo : IsOpen U := hPo.inter hu
    have hVo : IsOpen V := hPo.inter hv
    have hUV : Disjoint U V := by
      rw [Set.disjoint_left]
      intro x hxU hxV
      have hempty : x ∈ (∅ : Set X) := hinter ▸ ⟨hxU.1, hxU.2, hxV.2⟩
      exact hempty.elim
    have hUVcover : U ∪ V = P := by
      apply Set.Subset.antisymm
      · exact Set.union_subset Set.inter_subset_left Set.inter_subset_left
      · intro x hxP
        rcases hcover hxP with hxu | hxv
        · exact Or.inl ⟨hxP, hxu⟩
        · exact Or.inr ⟨hxP, hxv⟩
    have hUne : U.Nonempty := by
      obtain ⟨x, hxP, hxu⟩ := Set.not_subset.mp hnv
      rcases hcover hxP with hxu' | hxv
      · exact ⟨x, hxP, hxu'⟩
      · exact False.elim (hxu hxv)
    have hVne : V.Nonempty := by
      obtain ⟨x, hxP, hxv⟩ := Set.not_subset.mp hnu
      rcases hcover hxP with hxu | hxv'
      · exact False.elim (hxv hxu)
      · exact ⟨x, hxP, hxv'⟩
    obtain ⟨p, hpU, hp⟩ :=
      apm_t95j06_cutSide_contains_nonCutPoint X hX q U V hUo hVo hUV
        (by simpa [P] using hUVcover) hUne hVne
    obtain ⟨r, hrV, hr⟩ :=
      apm_t95j06_cutSide_contains_nonCutPoint X hX q V U hVo hUo hUV.symm
        (by simpa [P, Set.union_comm] using hUVcover) hVne hUne
    exact ⟨p, r, fun hpr => Set.disjoint_left.1 hUV hpU (hpr ▸ hrV), hp, hr⟩

/-- A puncture component in a connected locally connected space has closure
equal to the component together with the puncture point. -/
lemma apm_t95j06_punctureComponent_closure
    (X : Type*) [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    (hX : IsConnected (Set.univ : Set X)) (p x : X)
    (hx : x ∈ ({p}ᶜ : Set X)) :
    closure (connectedComponentIn ({p}ᶜ : Set X) x) =
      connectedComponentIn ({p}ᶜ : Set X) x ∪ {p} := by
  let F : Set X := ({p}ᶜ : Set X)
  let C : Set X := connectedComponentIn F x
  have hFo : IsOpen F := isClosed_singleton.isOpen_compl
  have hCo : IsOpen C := hFo.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCF : C ⊆ F := connectedComponentIn_subset F x
  have hpC : p ∉ C := fun hp => hCF hp (by simp [F])
  have hclosed : IsClosed (C ∪ {p}) := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hqp : q ∈ F := by
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff] at hq ⊢
      exact fun h => hq (Or.inr h)
    let D : Set X := connectedComponentIn F q
    have hDo : IsOpen D := hFo.connectedComponentIn
    have hqD : q ∈ D := mem_connectedComponentIn hqp
    refine mem_nhds_iff.mpr ⟨D, ?_, hDo, hqD⟩
    intro r hrD hr
    rcases hr with hrC | hrp
    · have hDC : D = C := calc
        D = connectedComponentIn F r := connectedComponentIn_eq hrD
        _ = C := (connectedComponentIn_eq hrC).symm
      have hqC : q ∈ C := hDC ▸ hqD
      exact hq (Or.inl hqC)
    · have hrF : r ∈ F := connectedComponentIn_subset F q hrD
      simpa [F, hrp] using hrF
  apply Set.Subset.antisymm
  · exact closure_minimal (fun q hq => Or.inl hq) hclosed
  · intro q hq
    rcases hq with hq | hq
    · exact subset_closure hq
    · simp only [Set.mem_singleton_iff] at hq
      by_contra hpcl
      have hCclosed : IsClosed C := by
        rw [← closure_eq_iff_isClosed]
        apply Set.Subset.antisymm
        · intro q hqcl
          have hu : q ∈ C ∪ {p} := closure_minimal (fun r hr => Or.inl hr) hclosed hqcl
          exact hu.resolve_right (fun h => hpcl ((h.trans hq.symm) ▸ hqcl))
        · exact subset_closure
      letI : PreconnectedSpace X := ⟨hX.isPreconnected⟩
      have hCuniv : C = Set.univ :=
        (show IsClopen C from ⟨hCclosed, hCo⟩).eq_univ ⟨x, hxC⟩
      have hqC : q ∈ C := by rw [hCuniv]; exact Set.mem_univ q
      exact hpcl (subset_closure hqC)

/-- The complement of a puncture component is connected: all the other
branches meet its closure at the puncture point. -/
lemma apm_t95j06_punctureComponent_compl_preconnected
    (X : Type*) [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    (hX : IsConnected (Set.univ : Set X)) (p x : X)
    (hx : x ∈ ({p}ᶜ : Set X)) :
    IsPreconnected (connectedComponentIn ({p}ᶜ : Set X) x)ᶜ := by
  let F : Set X := ({p}ᶜ : Set X)
  let C : Set X := connectedComponentIn F x
  have hFo : IsOpen F := isClosed_singleton.isOpen_compl
  have hCo : IsOpen C := hFo.connectedComponentIn
  have hpC : p ∉ C := fun hp => (connectedComponentIn_subset F x hp) (by simp [F])
  have hcl : closure C = C ∪ {p} :=
    apm_t95j06_punctureComponent_closure X hX p x hx
  intro u v hu hv huv hune hvne
  by_contra hinter
  obtain ⟨qu, hquC, hqu⟩ := hune
  obtain ⟨qv, hqvC, hqv⟩ := hvne
  have hno : ∀ q, q ∈ Cᶜ → q ∈ u → q ∈ v → False := by
    intro q hqC hqu hqv
    exact hinter ⟨q, hqC, hqu, hqv⟩
  -- A separation of the complement extends to a separation of the whole
  -- space after assigning the component itself to the side containing `p`.
  have hpUV : p ∈ u ∪ v := huv (by simpa [C] using hpC)
  rcases hpUV with hpu | hpv
  · have hqvcl : qv ∉ closure C := by
      rw [hcl]
      rintro (hqv' | hqvp)
      · exact hqvC hqv'
      · exact hno p hpC hpu (hqvp ▸ hqv)
    have hcover : (Set.univ : Set X) ⊆ (u ∪ C) ∪ (v \ closure C) := by
      intro q _
      by_cases hqC : q ∈ C
      · exact Or.inl (Or.inr hqC)
      rcases huv hqC with hqu | hqv
      · exact Or.inl (Or.inl hqu)
      · exact Or.inr ⟨hqv, fun hqcl => by
          rw [hcl] at hqcl
          rcases hqcl with hqinC | hqp
          · exact hqC hqinC
          · exact hno p hpC hpu (hqp ▸ hqv)⟩
    have hd : Disjoint (u ∪ C) (v \ closure C) := by
      rw [Set.disjoint_left]
      rintro q (hqu | hqC) ⟨hqv, hqcl⟩
      · exact hno q (fun hqC => hqcl (subset_closure hqC)) hqu hqv
      · exact hqcl (subset_closure hqC)
    have hi := hX.isPreconnected (u ∪ C) (v \ closure C)
      (hu.union hCo) (hv.inter isClosed_closure.isOpen_compl) hcover
      ⟨qu, Set.mem_univ qu, Or.inl hqu⟩
      ⟨qv, Set.mem_univ qv, ⟨hqv, hqvcl⟩⟩
    obtain ⟨q, _, hq1, hq2⟩ := hi
    exact hd.le_bot ⟨hq1, hq2⟩
  · have hqucl : qu ∉ closure C := by
      rw [hcl]
      rintro (hqu' | hqup)
      · exact hquC hqu'
      · exact hno p hpC (hqup ▸ hqu) hpv
    have hcover : (Set.univ : Set X) ⊆ (u \ closure C) ∪ (v ∪ C) := by
      intro q _
      by_cases hqC : q ∈ C
      · exact Or.inr (Or.inr hqC)
      rcases huv hqC with hqu | hqv
      · exact Or.inl ⟨hqu, fun hqcl => by
          rw [hcl] at hqcl
          rcases hqcl with hqinC | hqp
          · exact hqC hqinC
          · exact hno p hpC (hqp ▸ hqu) hpv⟩
      · exact Or.inr (Or.inl hqv)
    have hd : Disjoint (u \ closure C) (v ∪ C) := by
      rw [Set.disjoint_left]
      rintro q ⟨hqu, hqcl⟩ (hqv | hqC)
      · exact hno q (fun hqC => hqcl (subset_closure hqC)) hqu hqv
      · exact hqcl (subset_closure hqC)
    have hi := hX.isPreconnected (u \ closure C) (v ∪ C)
      (hu.inter isClosed_closure.isOpen_compl) (hv.union hCo) hcover
      ⟨qu, Set.mem_univ qu, ⟨hqu, hqucl⟩⟩
      ⟨qv, Set.mem_univ qv, Or.inl hqv⟩
    obtain ⟨q, _, hq1, hq2⟩ := hi
    exact hd.le_bot ⟨hq1, hq2⟩

/-- Every puncture component of a compact connected locally connected
Hausdorff space contains a non-cut point of the ambient space. -/
theorem apm_t95j06_punctureComponent_contains_globalNonCutPoint
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [LocallyConnectedSpace X]
    (hX : IsConnected (Set.univ : Set X)) (p x : X)
    (hx : x ∈ ({p}ᶜ : Set X)) :
    ∃ z ∈ connectedComponentIn ({p}ᶜ : Set X) x,
      IsPreconnected ({z}ᶜ : Set X) := by
  let C : Set X := connectedComponentIn ({p}ᶜ : Set X) x
  let H : Set X := closure C
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hpC : p ∉ C := fun hp => (connectedComponentIn_subset ({p}ᶜ : Set X) x hp) (by simp)
  have hcl : H = C ∪ {p} := apm_t95j06_punctureComponent_closure X hX p x hx
  have hxH : x ∈ H := subset_closure hxC
  have hpH : p ∈ H := by rw [hcl]; simp
  have hxp : x ≠ p := by simpa using hx
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  letI : CompactSpace H := isClosed_closure.isClosedEmbedding_subtypeVal.compactSpace
  letI : ConnectedSpace H := Subtype.connectedSpace hCconn.closure
  letI : Nontrivial H := ⟨⟨⟨x, hxH⟩, ⟨p, hpH⟩, by simpa using hxp⟩⟩
  obtain ⟨q, r, hqr, hq, hr⟩ :=
    apm_t95j06_continuum_exists_two_nonCutPoints H isConnected_univ
  have choose_noncut : ∀ z : H, z.1 ≠ p → IsPreconnected ({z}ᶜ : Set H) →
      ∃ w ∈ C, IsPreconnected ({w}ᶜ : Set X) := by
    intro z hzp hz
    have hzC : z.1 ∈ C := by
      have hzU : z.1 ∈ C ∪ {p} := hcl ▸ z.2
      exact hzU.resolve_right (by simpa using hzp)
    have himg : IsPreconnected (Subtype.val '' ({z}ᶜ : Set H)) :=
      hz.image _ continuous_subtype_val.continuousOn
    have himgeq : Subtype.val '' ({z}ᶜ : Set H) = H \ {z.1} := by
      ext w
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.2, fun h => ht (Subtype.ext h)⟩
      · rintro ⟨hwH, hwz⟩
        exact ⟨⟨w, hwH⟩, fun h => hwz (congrArg Subtype.val h), rfl⟩
    rw [himgeq] at himg
    have hcomp : IsPreconnected Cᶜ :=
      apm_t95j06_punctureComponent_compl_preconnected X hX p x hx
    have hpimg : p ∈ H \ {z.1} := ⟨hpH, by simpa using hzp.symm⟩
    have hpcomp : p ∈ Cᶜ := hpC
    have hunion : (H \ {z.1}) ∪ Cᶜ = ({z.1}ᶜ : Set X) := by
      ext w
      constructor
      · rintro (⟨_, hwz⟩ | hwC) hw
        · exact hwz (by simpa using hw)
        · exact hwC (hw ▸ hzC)
      · intro hwz
        by_cases hwC : w ∈ C
        · left
          exact ⟨subset_closure hwC, by simpa using hwz⟩
        · exact Or.inr hwC
    refine ⟨z.1, hzC, ?_⟩
    rw [← hunion]
    exact himg.union p hpimg hpcomp hcomp
  by_cases hqp : q.1 = p
  · have hrp : r.1 ≠ p := fun h => hqr (Subtype.ext (hqp.trans h.symm))
    exact choose_noncut r hrp hr
  · exact choose_noncut q hqp hq

theorem apm_t95j06_twoEndpointContinuum_punctureComponent_contains_endpoint
    (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [LocallyConnectedSpace K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (ha : IsPreconnected ({a}ᶜ : Set K))
    (hc : IsPreconnected ({c}ᶜ : Set K))
    (hcut : ∀ y : K, y ≠ a → y ≠ c →
      ¬ IsPreconnected ({y}ᶜ : Set K)) :
    ∀ y : K, y ≠ a → y ≠ c → ∀ z ∈ ({y}ᶜ : Set K),
      a ∈ connectedComponentIn ({y}ᶜ : Set K) z ∨
      c ∈ connectedComponentIn ({y}ᶜ : Set K) z := by
  intro y hya hyc z hz
  obtain ⟨w, hwcomp, hwnoncut⟩ :=
    apm_t95j06_punctureComponent_contains_globalNonCutPoint K hK y z hz
  by_cases hwa : w = a
  · left
    simpa [hwa] using hwcomp
  by_cases hwc : w = c
  · right
    simpa [hwc] using hwcomp
  exact (hcut w hwa hwc hwnoncut).elim

theorem apm_t95j06_twoEndpointContinuum_punctureSplit
    (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [LocallyConnectedSpace K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (ha : IsPreconnected ({a}ᶜ : Set K))
    (hc : IsPreconnected ({c}ᶜ : Set K))
    (hcut : ∀ y : K, y ≠ a → y ≠ c →
      ¬ IsPreconnected ({y}ᶜ : Set K)) :
    ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y) := by
  intro y hya hyc
  let F : Set K := ({y}ᶜ : Set K)
  let A := connectedComponentIn F a
  let C := connectedComponentIn F c
  have haF : a ∈ F := by
    simpa [F, Set.mem_compl_iff, Set.mem_singleton_iff] using hya.symm
  have hcF : c ∈ F := by
    simpa [F, Set.mem_compl_iff, Set.mem_singleton_iff] using hyc.symm
  have hbranches : ∀ z ∈ F,
      a ∈ connectedComponentIn F z ∨ c ∈ connectedComponentIn F z := by
    exact apm_t95j06_twoEndpointContinuum_punctureComponent_contains_endpoint
      K hK a c hac ha hc hcut y hya hyc
  have hcover : A ∪ C = F := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset F a)
        (connectedComponentIn_subset F c)
    · intro z hzF
      have hzz : z ∈ connectedComponentIn F z := mem_connectedComponentIn hzF
      rcases hbranches z hzF with hza | hzc
      · left
        rw [connectedComponentIn_eq hza] at hzz
        exact hzz
      · right
        rw [connectedComponentIn_eq hzc] at hzz
        exact hzz
  have hAC : A ≠ C := by
    intro heq
    apply hcut y hya hyc
    change IsPreconnected F
    rw [← hcover, heq, Set.union_self]
    exact isPreconnected_connectedComponentIn
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro z hzA hzC
    apply hAC
    calc
      A = connectedComponentIn F z := connectedComponentIn_eq hzA
      _ = C := (connectedComponentIn_eq hzC).symm
  refine ⟨{
    sideA := A
    sideC := C
    sideA_open := isClosed_singleton.isOpen_compl.connectedComponentIn
    sideC_open := isClosed_singleton.isOpen_compl.connectedComponentIn
    sideA_preconnected := isPreconnected_connectedComponentIn
    sideC_preconnected := isPreconnected_connectedComponentIn
    a_mem := mem_connectedComponentIn haF
    c_mem := mem_connectedComponentIn hcF
    disjoint := hdisj
    cover := hcover
    maximal := ?_ }⟩
  intro S hSne hSconn hSF
  obtain ⟨z, hzS⟩ := hSne
  have hsub : S ⊆ connectedComponentIn F z :=
    hSconn.subset_connectedComponentIn hzS hSF
  rcases hbranches z (hSF hzS) with hza | hzc
  · left
    rw [connectedComponentIn_eq hza] at hsub
    exact hsub
  · right
    rw [connectedComponentIn_eq hzc] at hsub
    exact hsub

/-- Endpoint-labelled puncture decompositions are unique.  Each connected
side of one decomposition must lie in one side of the other by `maximal`; its
endpoint rules out the incorrectly labelled side.  This is the choice-
independence needed before defining the separation order. -/
lemma apm_t95j06_PunctureSplit_unique
    (K : Type*) [TopologicalSpace K] (a c y : K)
    (p q : apm_t95j06_PunctureSplit K a c y) :
    p.sideA = q.sideA ∧ p.sideC = q.sideC := by
  have subset_compl (r : apm_t95j06_PunctureSplit K a c y) :
      r.sideA ⊆ ({y}ᶜ : Set K) ∧ r.sideC ⊆ ({y}ᶜ : Set K) := by
    constructor
    · intro x hx
      rw [← r.cover]
      exact Or.inl hx
    · intro x hx
      rw [← r.cover]
      exact Or.inr hx
  have sideA_subset (r s : apm_t95j06_PunctureSplit K a c y) :
      r.sideA ⊆ s.sideA := by
    rcases s.maximal r.sideA ⟨a, r.a_mem⟩ r.sideA_preconnected
        (subset_compl r).1 with h | h
    · exact h
    · exact False.elim ((Set.disjoint_left.1 s.disjoint) s.a_mem (h r.a_mem))
  have sideC_subset (r s : apm_t95j06_PunctureSplit K a c y) :
      r.sideC ⊆ s.sideC := by
    rcases s.maximal r.sideC ⟨c, r.c_mem⟩ r.sideC_preconnected
        (subset_compl r).2 with h | h
    · exact False.elim ((Set.disjoint_left.1 s.disjoint) (h r.c_mem) s.c_mem)
    · exact h
  exact ⟨Set.Subset.antisymm (sideA_subset p q) (sideA_subset q p),
    Set.Subset.antisymm (sideC_subset p q) (sideC_subset q p)⟩

/-- The canonical endpoint-labelled split at an interior point.  Uniqueness
below shows that none of the order constructions depend on this choice. -/
noncomputable def apm_t95j06_PunctureSplit.choice
    (K : Type*) [TopologicalSpace K] (a c : K)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y))
    (y : K) (hya : y ≠ a) (hyc : y ≠ c) :
    apm_t95j06_PunctureSplit K a c y :=
  Classical.choice (hsplit y hya hyc)

/-- The canonical split agrees side-for-side with every supplied split. -/
lemma apm_t95j06_PunctureSplit.choice_sides
    (K : Type*) [TopologicalSpace K] (a c : K)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y))
    (y : K) (hya : y ≠ a) (hyc : y ≠ c)
    (s : apm_t95j06_PunctureSplit K a c y) :
    (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideA = s.sideA ∧
      (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideC = s.sideC :=
  apm_t95j06_PunctureSplit_unique K a c y _ s

/-- Every point other than the puncture lies in exactly one canonical side.
This supplies total case analysis for the separation relation; the puncture
itself lies in neither side. -/
lemma apm_t95j06_PunctureSplit.choice_partition
    (K : Type*) [TopologicalSpace K] (a c : K)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y))
    (y : K) (hya : y ≠ a) (hyc : y ≠ c) (x : K) :
    x ≠ y ↔
      (x ∈ (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideA ∨
       x ∈ (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideC) := by
  let s := apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc
  change x ∈ ({y}ᶜ : Set K) ↔ x ∈ s.sideA ∨ x ∈ s.sideC
  rw [← s.cover]
  exact Set.mem_union _ _ _

/-- Membership in the two canonical sides is mutually exclusive. -/
lemma apm_t95j06_PunctureSplit.choice_not_both
    (K : Type*) [TopologicalSpace K] (a c : K)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y))
    (y : K) (hya : y ≠ a) (hyc : y ≠ c) (x : K)
    (hx : x ∈ (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideA) :
    x ∉ (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideC := by
  exact Set.disjoint_left.1
    (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).disjoint hx

/-- Canonical `a`-sides are nested in the separation direction.  This is the
key transitivity lemma for the cut-point order. -/
lemma apm_t95j06_PunctureSplit.sideA_nested
    (K : Type*) [TopologicalSpace K]
    (hK : IsConnected (Set.univ : Set K)) (a c x y : K)
    (sx : apm_t95j06_PunctureSplit K a c x)
    (sy : apm_t95j06_PunctureSplit K a c y)
    (hxy : x ≠ y) (hx : x ∈ sy.sideA) : sx.sideA ⊆ sy.sideA := by
  have side_subset_compl {z : K} (s : apm_t95j06_PunctureSplit K a c z)
      (A : Set K) (hA : A = s.sideA ∨ A = s.sideC) : A ⊆ ({z}ᶜ : Set K) := by
    rw [← s.cover]
    rcases hA with rfl | rfl
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  by_cases hyA : y ∈ sx.sideA
  · have hxC_yC : sx.sideC ⊆ sy.sideC := by
      have havoid : sx.sideC ⊆ ({y}ᶜ : Set K) := by
        intro z hz hzy
        subst z
        exact (Set.disjoint_left.1 sx.disjoint hyA hz)
      rcases sy.maximal sx.sideC ⟨c, sx.c_mem⟩ sx.sideC_preconnected havoid with h | h
      · exact False.elim (Set.disjoint_left.1 sy.disjoint (h sx.c_mem) sy.c_mem)
      · exact h
    have hyC_xC : sy.sideC ⊆ sx.sideC := by
      have havoid : sy.sideC ⊆ ({x}ᶜ : Set K) := by
        intro z hz hzx
        subst z
        exact (Set.disjoint_left.1 sy.disjoint hx hz)
      rcases sx.maximal sy.sideC ⟨c, sy.c_mem⟩ sy.sideC_preconnected havoid with h | h
      · exact False.elim (Set.disjoint_left.1 sx.disjoint (h sy.c_mem) sx.c_mem)
      · exact h
    have hC : sx.sideC = sy.sideC := Set.Subset.antisymm hxC_yC hyC_xC
    letI : ConnectedSpace K := connectedSpace_iff_univ.mpr hK
    have hfront : (frontier sx.sideC).Nonempty := by
      rw [nonempty_frontier_iff]
      refine ⟨⟨c, sx.c_mem⟩, ?_⟩
      intro hU
      have haC : a ∈ sx.sideC := hU.symm ▸ Set.mem_univ a
      exact Set.disjoint_left.1 sx.disjoint sx.a_mem haC
    have hfx : frontier sx.sideC ⊆ ({x} : Set K) := by
      intro z hz
      by_contra hzx
      have hzcompl : z ∈ ({x}ᶜ : Set K) := by simpa
      rw [← sx.cover] at hzcompl
      rcases hzcompl with hzA | hzC
      · exact (Set.disjoint_left.1
          (sx.disjoint.symm.frontier_left sx.sideA_open) hz hzA)
      · exact (Set.disjoint_left.1
          (Set.disjoint_iff_inter_eq_empty.mpr sx.sideC_open.inter_frontier_eq) hzC hz)
    have hfy : frontier sx.sideC ⊆ ({y} : Set K) := by
      rw [hC]
      intro z hz
      by_contra hzy
      have hzcompl : z ∈ ({y}ᶜ : Set K) := by simpa
      rw [← sy.cover] at hzcompl
      rcases hzcompl with hzA | hzC
      · exact (Set.disjoint_left.1
          (sy.disjoint.symm.frontier_left sy.sideA_open) hz hzA)
      · exact (Set.disjoint_left.1
          (Set.disjoint_iff_inter_eq_empty.mpr sy.sideC_open.inter_frontier_eq) hzC hz)
    obtain ⟨z, hz⟩ := hfront
    have hzx : z = x := Set.mem_singleton_iff.mp (hfx hz)
    have hzy : z = y := Set.mem_singleton_iff.mp (hfy hz)
    exact False.elim (hxy (hzx.symm.trans hzy))
  · have havoid : sx.sideA ⊆ ({y}ᶜ : Set K) := by
      intro z hz hzy
      subst z
      exact hyA hz
    rcases sy.maximal sx.sideA ⟨a, sx.a_mem⟩ sx.sideA_preconnected havoid with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.1 sy.disjoint sy.a_mem (h sx.a_mem))

/-- The endpoint-aware strict separation relation.  At an interior right
endpoint it is membership in its canonical `a`-side; `a` has no predecessors
and every point other than `c` precedes `c`. -/
noncomputable def apm_t95j06_PunctureSplit.sepLT
    (K : Type*) [TopologicalSpace K] (a c : K)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y)) (x y : K) : Prop :=
  by
    classical
    exact if hya : y = a then False
      else if hyc : y = c then x ≠ c
      else x ∈ (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).sideA

/-- No point precedes itself in the separation relation. -/
lemma apm_t95j06_PunctureSplit.sepLT_irrefl
    (K : Type*) [TopologicalSpace K] (a c : K)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y)) (x : K) :
    ¬ apm_t95j06_PunctureSplit.sepLT K a c hsplit x x := by
  by_cases hxa : x = a
  · simp [apm_t95j06_PunctureSplit.sepLT, hxa]
  by_cases hxc : x = c
  · simp [apm_t95j06_PunctureSplit.sepLT, hxa, hxc]
  simp only [apm_t95j06_PunctureSplit.sepLT, hxa, hxc, dite_false]
  intro hx
  let s := apm_t95j06_PunctureSplit.choice K a c hsplit x hxa hxc
  have hxcompl : x ∈ ({x}ᶜ : Set K) := by
    rw [← s.cover]
    exact Or.inl hx
  exact hxcompl (Set.mem_singleton x)

/-- The distinguished endpoint `a` is strictly below every other point. -/
lemma apm_t95j06_PunctureSplit.sepLT_a
    (K : Type*) [TopologicalSpace K] (a c : K) (hac : a ≠ c)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y)) (y : K) (hya : y ≠ a) :
    apm_t95j06_PunctureSplit.sepLT K a c hsplit a y := by
  by_cases hyc : y = c
  · simp [apm_t95j06_PunctureSplit.sepLT, hya, hyc, hac, hac.symm]
  · simp only [apm_t95j06_PunctureSplit.sepLT, hya, hyc, dite_false]
    exact (apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc).a_mem

/-- Every point other than `c` is strictly below the distinguished endpoint
`c`. -/
lemma apm_t95j06_PunctureSplit.sepLT_c
    (K : Type*) [TopologicalSpace K] (a c : K) (hac : a ≠ c)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y)) (x : K) (hxc : x ≠ c) :
    apm_t95j06_PunctureSplit.sepLT K a c hsplit x c := by
  simp [apm_t95j06_PunctureSplit.sepLT, hac, hac.symm, hxc]

/-- **C2a, separation-order algebra and completion (estimated 220--380
lines; LIBRARY).**  The endpoint-labelled puncture sides define a unique
complete linear order: for an interior `y`, `x < y` exactly when `x` lies on
the `a`-side of the puncture at `y`, and `a,c` are its endpoints.

Proof sketch: define the strict relation using a chosen split, with explicit
endpoint clauses.  `apm_t95j06_PunctureSplit_unique` makes it independent of
the choice.  Maximality of connected sides proves nesting, hence transitivity
and totality; the cover and disjointness prove asymmetry.  Suprema are limits
of nested closed upper/lower sides, whose finite intersection property is
realized by compactness.  The empty and universal cuts give `a` and `c`.

Truth checks: compactness is needed for completeness (an open interval has
the same local separation order but missing suprema), and endpoint clauses
are needed because `hsplit` deliberately supplies no split at `a` or `c`. -/
theorem apm_t95j06_twoEndpointContinuum_orderOfPunctureSplit_aux_order
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y)) :
    ∃ o : CompleteLinearOrder K,
      a = o.bot ∧ c = o.top ∧
      ∀ (x y : K) (hya : y ≠ a) (hyc : y ≠ c)
        (s : apm_t95j06_PunctureSplit K a c y),
        @LT.lt K o.toLinearOrder.toLT x y ↔ x ∈ s.sideA := by
  classical
  letI : ConnectedSpace K := connectedSpace_iff_univ.mpr hK
  let lt : K → K → Prop := apm_t95j06_PunctureSplit.sepLT K a c hsplit
  let S := fun (y : K) (hya : y ≠ a) (hyc : y ≠ c) =>
    apm_t95j06_PunctureSplit.choice K a c hsplit y hya hyc
  have hlt_int : ∀ x y (hya : y ≠ a) (hyc : y ≠ c),
      lt x y ↔ x ∈ (S y hya hyc).sideA := by
    intro x y hya hyc
    simp only [lt, S, apm_t95j06_PunctureSplit.sepLT, hya, hyc, dite_false]
  have hlt_a : ∀ x, ¬ lt x a := by
    intro x; simp [lt, apm_t95j06_PunctureSplit.sepLT]
  have hlt_c : ∀ x, lt x c ↔ x ≠ c := by
    intro x; simp [lt, apm_t95j06_PunctureSplit.sepLT, hac.symm]
  have hnotself : ∀ y (s : apm_t95j06_PunctureSplit K a c y), y ∉ s.sideA := by
    intro y s hy
    have : y ∈ ({y}ᶜ : Set K) := by rw [← s.cover]; exact Or.inl hy
    exact this (Set.mem_singleton y)
  have hcA : ∀ y (s : apm_t95j06_PunctureSplit K a c y), c ∉ s.sideA :=
    fun y s h => Set.disjoint_left.1 s.disjoint h s.c_mem
  have hclA : ∀ y (s : apm_t95j06_PunctureSplit K a c y),
      closure s.sideA ⊆ insert y s.sideA := by
    intro y s z hz
    by_contra hzn
    simp only [Set.mem_insert_iff, not_or] at hzn
    have hzcompl : z ∈ ({y}ᶜ : Set K) := hzn.1
    rw [← s.cover] at hzcompl
    rcases hzcompl with h | h
    · exact hzn.2 h
    · exact Set.disjoint_left.1 (s.disjoint.symm.closure_right s.sideC_open) h hz
  have hyclA : ∀ y (s : apm_t95j06_PunctureSplit K a c y), y ∈ closure s.sideA := by
    intro y s
    by_contra hy
    have hcl : closure s.sideA ⊆ s.sideA := fun z hz => by
      rcases hclA y s hz with h | h
      · exact absurd (h ▸ hz) hy
      · exact h
    have hclo : IsClopen s.sideA := ⟨closure_subset_iff_isClosed.mp hcl, s.sideA_open⟩
    rcases isClopen_iff.mp hclo with h | h
    · have := s.a_mem; rw [h] at this; exact this
    · have hc' : c ∈ s.sideA := h ▸ Set.mem_univ c
      exact hcA y s hc'
  have htri_int : ∀ x y (hxa : x ≠ a) (hxc : x ≠ c) (hya : y ≠ a) (hyc : y ≠ c),
      x ≠ y → x ∈ (S y hya hyc).sideA ∨ y ∈ (S x hxa hxc).sideA := by
    intro x y hxa hxc hya hyc hxy
    by_contra hn
    push_neg at hn
    obtain ⟨hx, hy⟩ := hn
    have havoid : (S x hxa hxc).sideA ⊆ ({y}ᶜ : Set K) := by
      intro z hz hzy
      rw [Set.mem_singleton_iff] at hzy
      rw [hzy] at hz
      exact hy hz
    rcases (S y hya hyc).maximal _ ⟨a, (S x hxa hxc).a_mem⟩
        (S x hxa hxc).sideA_preconnected havoid with h | h
    · have hxcl := closure_mono h (hyclA x (S x hxa hxc))
      rcases hclA y _ hxcl with h' | h'
      · exact hxy h'
      · exact hx h'
    · exact Set.disjoint_left.1 (S y hya hyc).disjoint (S y hya hyc).a_mem
        (h (S x hxa hxc).a_mem)
  have hirr : ∀ x, ¬ lt x x := apm_t95j06_PunctureSplit.sepLT_irrefl K a c hsplit
  have htrans : ∀ x y z, lt x y → lt y z → lt x z := by
    intro x y z hxy hyz
    by_cases hya : y = a
    · subst y; exact absurd hxy (hlt_a x)
    by_cases hyc : y = c
    · subst y
      by_cases hza : z = a
      · subst z; exact absurd hyz (hlt_a _)
      by_cases hzc : z = c
      · subst z; exact absurd hyz (hirr _)
      exact absurd ((hlt_int _ z hza hzc).mp hyz) (hcA z _)
    have hxA := (hlt_int x y hya hyc).mp hxy
    by_cases hza : z = a
    · subst z; exact absurd hyz (hlt_a y)
    by_cases hzc : z = c
    · subst z
      exact (hlt_c x).mpr (fun h => hcA y _ (h ▸ hxA))
    have hyA := (hlt_int y z hza hzc).mp hyz
    have hyz' : y ≠ z := fun h => hnotself z _ (h ▸ hyA)
    exact (hlt_int x z hza hzc).mpr
      (apm_t95j06_PunctureSplit.sideA_nested K hK a c y z _ _ hyz' hyA hxA)
  have htri : ∀ x y, lt x y ∨ x = y ∨ lt y x := by
    intro x y
    by_cases hxy : x = y
    · exact Or.inr (Or.inl hxy)
    by_cases hya : y = a
    · subst y; exact Or.inr (Or.inr (apm_t95j06_PunctureSplit.sepLT_a K a c hac hsplit x hxy))
    by_cases hxa : x = a
    · subst x; exact Or.inl (apm_t95j06_PunctureSplit.sepLT_a K a c hac hsplit y hya)
    by_cases hyc : y = c
    · subst y; exact Or.inl ((hlt_c x).mpr hxy)
    by_cases hxc : x = c
    · subst x; exact Or.inr (Or.inr ((hlt_c y).mpr hyc))
    rcases htri_int x y hxa hxc hya hyc hxy with h | h
    · exact Or.inl ((hlt_int x y hya hyc).mpr h)
    · exact Or.inr (Or.inr ((hlt_int y x hxa hxc).mpr h))
  haveI hsto : IsStrictTotalOrder K lt :=
    { trichotomous := fun x y h1 h2 => by
        rcases htri x y with h | h | h
        · exact absurd h h1
        · exact h
        · exact absurd h h2
      irrefl := hirr
      trans := htrans }
  letI lo : LinearOrder K := linearOrderOfSTO lt
  have hlt_iff : ∀ x y : K, x < y ↔ lt x y := fun x y => Iff.rfl
  have hle_c : ∀ x : K, x ≤ c := by
    intro x; by_cases hxc : x = c
    · exact le_of_eq hxc
    · exact le_of_lt ((hlt_iff x c).mpr ((hlt_c x).mpr hxc))
  have ha_le : ∀ x : K, a ≤ x := by
    intro x; by_cases hxa : x = a
    · exact le_of_eq hxa.symm
    · exact le_of_lt ((hlt_iff a x).mpr
        (apm_t95j06_PunctureSplit.sepLT_a K a c hac hsplit x hxa))
  have hIci : ∀ y : K, IsClosed (Set.Ici y) := by
    intro y
    rw [← isOpen_compl_iff, Set.compl_Ici]
    by_cases hya : y = a
    · subst y
      have : Set.Iio a = ∅ := Set.eq_empty_of_forall_notMem
        (fun x hx => hlt_a x ((hlt_iff x a).mp hx))
      rw [this]; exact isOpen_empty
    by_cases hyc : y = c
    · subst y
      have : Set.Iio c = ({c}ᶜ : Set K) := by
        ext x; simp only [Set.mem_Iio, Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [hlt_iff]; exact hlt_c x
      rw [this]; exact isOpen_compl_singleton
    have : Set.Iio y = (S y hya hyc).sideA := by
      ext x; rw [Set.mem_Iio, hlt_iff]; exact hlt_int x y hya hyc
    rw [this]; exact (S y hya hyc).sideA_open
  have hIic : ∀ y : K, IsClosed (Set.Iic y) := by
    intro y
    rw [← isOpen_compl_iff, Set.compl_Iic]
    by_cases hya : y = a
    · subst y
      have : Set.Ioi a = ({a}ᶜ : Set K) := by
        ext x; simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff]
        constructor
        · intro h e; rw [e] at h; exact lt_irrefl _ h
        · intro h; exact (hlt_iff a x).mpr
            (apm_t95j06_PunctureSplit.sepLT_a K a c hac hsplit x h)
      rw [this]; exact isOpen_compl_singleton
    by_cases hyc : y = c
    · subst y
      have : Set.Ioi c = ∅ := Set.eq_empty_of_forall_notMem
        (fun x hx => not_lt_of_ge (hle_c x) hx)
      rw [this]; exact isOpen_empty
    have : Set.Ioi y = (S y hya hyc).sideC := by
      ext x; rw [Set.mem_Ioi]
      constructor
      · intro h
        have hxy : x ≠ y := (ne_of_lt h).symm
        have hx : x ∈ ({y}ᶜ : Set K) := hxy
        rw [← (S y hya hyc).cover] at hx
        rcases hx with hx | hx
        · exact absurd ((hlt_iff x y).mpr ((hlt_int x y hya hyc).mpr hx)) (not_lt_of_gt h)
        · exact hx
      · intro hx
        rcases lt_trichotomy x y with h | h | h
        · exact absurd hx (Set.disjoint_left.1 (S y hya hyc).disjoint
            ((hlt_int x y hya hyc).mp ((hlt_iff x y).mp h)))
        · subst h
          have : x ∈ ({x}ᶜ : Set K) := by rw [← (S x hya hyc).cover]; exact Or.inr hx
          exact absurd (Set.mem_singleton x) this
        · exact h
    rw [this]; exact (S y hya hyc).sideC_open
  haveI : ClosedIicTopology K := ⟨hIic⟩
  have hlub : ∀ s : Set K, ∃ m, IsLUB s m := by
    intro s
    have hub : upperBounds s = ⋂ x ∈ s, Set.Ici x := by
      ext z; simp [upperBounds]
    have hcl : IsClosed (upperBounds s) := by
      rw [hub]; exact isClosed_biInter (fun x _ => hIci x)
    obtain ⟨m, hm⟩ := hcl.isCompact.exists_isLeast ⟨c, fun x _ => hle_c x⟩
    exact ⟨m, hm⟩
  letI bo : BoundedOrder K :=
    { top := c, le_top := hle_c, bot := a, bot_le := ha_le }
  letI cl : CompleteLattice K :=
    { (inferInstance : Lattice K), bo with
      sSup := fun s => Classical.choose (hlub s)
      isLUB_sSup := fun s => Classical.choose_spec (hlub s)
      sInf := fun s => Classical.choose (hlub (lowerBounds s))
      isGLB_sInf := fun s =>
        ⟨fun x hx => (Classical.choose_spec (hlub (lowerBounds s))).2 (fun y hy => hy hx),
          fun y hy => (Classical.choose_spec (hlub (lowerBounds s))).1 hy⟩ }
  let o : CompleteLinearOrder K :=
    { __ := lo, __ := cl, __ := LinearOrder.toBiheytingAlgebra K }
  refine ⟨o, rfl, rfl, ?_⟩
  intro x y hya hyc s
  change lt x y ↔ x ∈ s.sideA
  rw [hlt_int x y hya hyc,
    (apm_t95j06_PunctureSplit.choice_sides K a c hsplit y hya hyc s).1]

/-- For an interior point, the strict initial order ray is exactly its
labelled `a`-side. -/
lemma apm_t95j06_orderOfPunctureSplit_Iio_eq_sideA_aux
    (K : Type*) [TopologicalSpace K]
    (a c : K) (o : CompleteLinearOrder K)
    (horder : ∀ (x y : K) (hya : y ≠ a) (hyc : y ≠ c)
      (s : apm_t95j06_PunctureSplit K a c y),
      @LT.lt K o.toLinearOrder.toLT x y ↔ x ∈ s.sideA)
    (y : K) (hya : y ≠ a) (hyc : y ≠ c)
    (p : apm_t95j06_PunctureSplit K a c y) :
    @Set.Iio K o.toLinearOrder.toPreorder y = p.sideA := by
  ext x
  exact horder x y hya hyc p

/-- For an interior point, the strict final order ray is exactly its labelled
`c`-side. -/
lemma apm_t95j06_orderOfPunctureSplit_Ioi_eq_sideC_aux
    (K : Type*) [TopologicalSpace K]
    (a c : K) (o : CompleteLinearOrder K)
    (horder : ∀ (x y : K) (hya : y ≠ a) (hyc : y ≠ c)
      (s : apm_t95j06_PunctureSplit K a c y),
      @LT.lt K o.toLinearOrder.toLT x y ↔ x ∈ s.sideA)
    (y : K) (hya : y ≠ a) (hyc : y ≠ c)
    (p : apm_t95j06_PunctureSplit K a c y) :
    @Set.Ioi K o.toLinearOrder.toPreorder y = p.sideC := by
  ext x
  constructor
  · intro hyx
    have hxy : x ≠ y := hyx.ne.symm
    have hxpunct : x ∈ ({y}ᶜ : Set K) := by simpa
    rw [← p.cover] at hxpunct
    rcases hxpunct with hxA | hxC
    · exact (hyx.asymm (horder x y hya hyc p |>.mpr hxA)).elim
    · exact hxC
  · intro hxC
    have hxy : x ≠ y := by
      intro h
      subst x
      have : y ∈ ({y}ᶜ : Set K) := p.cover ▸ Set.mem_union_right _ hxC
      exact this rfl
    rcases lt_or_gt_of_ne hxy with hxy' | hyx
    · have hxA := (horder x y hya hyc p).mp hxy'
      exact (Set.disjoint_left.1 p.disjoint hxA hxC).elim
    · exact hyx

/-- **C2b, topology and density of the separation order (estimated 140--240
lines; LIBRARY).**  Any complete order realizing the puncture-side relation
has the supplied topology as its order topology and is densely ordered.

Proof sketch: the strict initial and final rays at every interior point are
the open sets `sideA` and `sideC`; endpoint rays are empty or complements of
closed singletons.  Thus order-open rays generate no topology beyond the
given one.  Conversely, the two open puncture sides separate a point from
each closed order ray, yielding the reverse topology inclusion.  If `x < y`
had no intermediate point, the two corresponding rays would disconnect the
connected space `K`; hence the order is dense.

Truth checks: connectedness is essential for density (a finite ordered
compactum is a counterexample), and openness of both labelled sides is
essential for the topology comparison. -/
theorem apm_t95j06_twoEndpointContinuum_orderOfPunctureSplit_aux_topology
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y))
    (o : CompleteLinearOrder K) (ha : a = o.bot) (hc : c = o.top)
    (horder : ∀ (x y : K) (hya : y ≠ a) (hyc : y ≠ c)
      (s : apm_t95j06_PunctureSplit K a c y),
      @LT.lt K o.toLinearOrder.toLT x y ↔ x ∈ s.sideA) :
    @OrderTopology K inferInstance o.toLinearOrder.toPreorder ∧
      @DenselyOrdered K o.toLinearOrder.toLT := by
  letI : CompleteLinearOrder K := o
  have hIio : ∀ y : K, IsOpen (Set.Iio y) := by
    intro y
    by_cases hya : y = a
    · have : Set.Iio y = ∅ := by
        rw [hya, ha]; exact Set.Iio_eq_empty_iff.mpr isMin_bot
      rw [this]; exact isOpen_empty
    by_cases hyc : y = c
    · have : Set.Iio y = {y}ᶜ := by
        ext x; rw [hyc, hc]
        simp only [Set.mem_Iio, Set.mem_compl_iff, Set.mem_singleton_iff]
        exact lt_top_iff_ne_top
      rw [this]; exact isOpen_compl_singleton
    obtain ⟨p⟩ := hsplit y hya hyc
    rw [apm_t95j06_orderOfPunctureSplit_Iio_eq_sideA_aux K a c o horder y hya hyc p]
    exact p.sideA_open
  have hIoi : ∀ y : K, IsOpen (Set.Ioi y) := by
    intro y
    by_cases hya : y = a
    · have : Set.Ioi y = {y}ᶜ := by
        ext x; rw [hya, ha]
        simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff]
        exact bot_lt_iff_ne_bot
      rw [this]; exact isOpen_compl_singleton
    by_cases hyc : y = c
    · have : Set.Ioi y = ∅ := by
        rw [hyc, hc]; exact Set.Ioi_eq_empty_iff.mpr isMax_top
      rw [this]; exact isOpen_empty
    obtain ⟨p⟩ := hsplit y hya hyc
    rw [apm_t95j06_orderOfPunctureSplit_Ioi_eq_sideC_aux K a c o horder y hya hyc p]
    exact p.sideC_open
  have hle : (‹TopologicalSpace K›) ≤ Preorder.topology K := by
    apply le_generateFrom
    rintro s ⟨y, rfl | rfl⟩
    · exact hIoi y
    · exact hIio y
  have hT2 : @T2Space K (Preorder.topology K) := by
    letI := Preorder.topology K
    haveI : OrderTopology K := ⟨rfl⟩
    infer_instance
  have hcont : @Continuous K K _ (Preorder.topology K) id := continuous_id_of_le hle
  have heq : (‹TopologicalSpace K›) = Preorder.topology K := by
    apply le_antisymm hle
    intro U hU
    have hc : IsCompact Uᶜ := hU.isClosed_compl.isCompact
    have himg : @IsCompact K (Preorder.topology K) (id '' Uᶜ) :=
      @IsCompact.image K K _ (Preorder.topology K) Uᶜ id hc hcont
    rw [Set.image_id] at himg
    have hcl : @IsClosed K (Preorder.topology K) Uᶜ :=
      @IsCompact.isClosed K (Preorder.topology K) hT2 _ himg
    have hU' : @IsOpen K (Preorder.topology K) Uᶜᶜ :=
      (@isOpen_compl_iff K Uᶜ (Preorder.topology K)).mpr hcl
    simpa using hU'
  haveI hOT : OrderTopology K := ⟨heq⟩
  haveI : ConnectedSpace K := connectedSpace_iff_univ.mpr hK
  refine ⟨hOT, ⟨fun x y hxy => ?_⟩⟩
  by_contra hno
  push_neg at hno
  have hS : Set.Iio y = Set.Iic x := by
    ext z
    simp only [Set.mem_Iio, Set.mem_Iic]
    constructor
    · intro hz
      by_contra hzx
      push_neg at hzx
      exact absurd hz (not_lt.mpr (hno z hzx))
    · intro hz; exact lt_of_le_of_lt hz hxy
  have hclopen : IsClopen (Set.Iio y) := by
    refine ⟨?_, hIio y⟩
    rw [hS]; exact isClosed_Iic
  rcases isClopen_iff.mp hclopen with h | h
  · have : x ∈ Set.Iio y := hxy
    rw [h] at this; exact this
  · have : y ∈ Set.Iio y := by rw [h]; trivial
    exact lt_irrefl y this

/-- **C2, order construction (estimated 65--110 lines).** Given the labelled
two-component decomposition of every non-endpoint puncture, separation from
`a` defines a complete dense linear order with endpoints `a,c`, and its order
topology is the supplied topology.

This is true by defining `x < y` when `x = a`, or when `x` belongs to the
`a`-component of `K \\ {y}`.  Component nesting proves transitivity and
totality; connectedness gives density; openness of the two sides identifies
the order topology; compactness supplies all suprema and infima. -/
theorem apm_t95j06_twoEndpointContinuum_orderOfPunctureSplit
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (hsplit : ∀ y : K, y ≠ a → y ≠ c →
      Nonempty (apm_t95j06_PunctureSplit K a c y)) :
    ∃ o : CompleteLinearOrder K,
      let _ := o
      @OrderTopology K inferInstance o.toLinearOrder.toPreorder ∧
      @DenselyOrdered K o.toLinearOrder.toLT ∧
      a = o.bot ∧ c = o.top := by
  obtain ⟨o, ha, hc, horder⟩ :=
    apm_t95j06_twoEndpointContinuum_orderOfPunctureSplit_aux_order
      K hK a c hac hsplit
  obtain ⟨hot, hdense⟩ :=
    apm_t95j06_twoEndpointContinuum_orderOfPunctureSplit_aux_topology
      K hK a c hac hsplit o ha hc horder
  exact ⟨o, hot, hdense, ha, hc⟩

/-- Compact metrizable spaces are separable. -/
lemma apm_t95j06_compactMetrizable_separable_order
    (K : Type*) [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] :
    Nonempty (TopologicalSpace.SeparableSpace K) := by
  letI : UniformSpace K :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity K
  letI : PseudoMetricSpace K :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric K
  have hs : TopologicalSpace.IsSeparable (Set.univ : Set K) :=
    isCompact_univ.isSeparable
  exact ⟨TopologicalSpace.isSeparable_univ_iff.mp hs⟩

theorem apm_t95j06_twoEndpointContinuum_cutPointOrder
    (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [TopologicalSpace.MetrizableSpace K]
    [LocallyConnectedSpace K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (ha : IsPreconnected ({a}ᶜ : Set K))
    (hc : IsPreconnected ({c}ᶜ : Set K))
    (hcut : ∀ y : K, y ≠ a → y ≠ c →
      ¬ IsPreconnected ({y}ᶜ : Set K)) :
    ∃ o : CompleteLinearOrder K,
      let _ := o
      @OrderTopology K inferInstance o.toLinearOrder.toPreorder ∧
      @DenselyOrdered K o.toLinearOrder.toLT ∧
      Nonempty (TopologicalSpace.SeparableSpace K) ∧
      a = o.bot ∧ c = o.top := by
  have hsplit := apm_t95j06_twoEndpointContinuum_punctureSplit
    K hK a c hac ha hc hcut
  obtain ⟨o, hot, hdense, ha0, hc1⟩ :=
    apm_t95j06_twoEndpointContinuum_orderOfPunctureSplit
      K hK a c hac hsplit
  exact ⟨o, hot, hdense,
    apm_t95j06_compactMetrizable_separable_order K, ha0, hc1⟩

/-- A dense subset recovers every point as the supremum of its members below
that point.  This is the cut-recovery fact used in both inverse laws of the
Dedekind extension. -/
lemma apm_t95j06_sSup_dense_Iic_aux
    (L : Type*) [TopologicalSpace L] [CompleteLinearOrder L]
    [OrderTopology L] [DenselyOrdered L]
    (s : Set L) (hs : Dense s) (x : L) :
    sSup ((fun q : s ↦ q.1) '' {q : s | q.1 ≤ x}) = x := by
  let A : Set L := (fun q : s ↦ q.1) '' {q : s | q.1 ≤ x}
  apply le_antisymm
  · apply sSup_le
    rintro y ⟨q, hq, rfl⟩
    exact hq
  · by_contra h
    have hlt : sSup A < x := lt_of_not_ge h
    obtain ⟨q, hqs, hsupq, hqx⟩ := hs.exists_between hlt
    have hqA : q ∈ A := ⟨⟨q, hqs⟩, hqx.le, rfl⟩
    exact (not_lt_of_ge (le_sSup hqA)) hsupq

/-- **Dedekind extension of a dense-suborder isomorphism (estimated 70--110
lines).** Let `s` and `t` be dense subsets of complete dense linear orders,
neither containing either endpoint.  An order isomorphism `s ≃o t` extends
uniquely to an endpoint-preserving order isomorphism of the ambient orders.

For `x`, define the extension as the supremum of the images of members of
`s ∩ Iic x`.  Density makes this strictly monotone; completeness supplies the
supremum; applying the symmetric infimum construction to `e.symm` proves
surjectivity and the inverse laws.  Endpoint avoidance ensures the two extreme
values are exactly bottom and top.  A finite or non-dense subset is a genuine
counterexample, while allowing endpoints breaks the no-endpoint suborder used
by Cantor back-and-forth. -/
lemma apm_t95j06_denseOrderIso_extend_complete_aux
    (L M : Type*) [TopologicalSpace L] [CompleteLinearOrder L]
    [OrderTopology L] [DenselyOrdered L] [Nontrivial L]
    [TopologicalSpace M] [CompleteLinearOrder M]
    [OrderTopology M] [DenselyOrdered M] [Nontrivial M]
    (s : Set L) (t : Set M) (hs : Dense s) (ht : Dense t)
    (hsbot : (⊥ : L) ∉ s) (hstop : (⊤ : L) ∉ s)
    (htbot : (⊥ : M) ∉ t) (httop : (⊤ : M) ∉ t)
    (e : s ≃o t) :
    ∃ E : L ≃o M, E ⊥ = ⊥ ∧ E ⊤ = ⊤ := by
  let Fset (x : L) : Set M :=
    (fun q : s ↦ (e q).1) '' {q : s | q.1 ≤ x}
  let Gset (y : M) : Set L :=
    (fun q : t ↦ (e.symm q).1) '' {q : t | q.1 ≤ y}
  let F (x : L) : M := sSup (Fset x)
  let G (y : M) : L := sSup (Gset y)
  have hF_lower (x : L) (q : s) (hq : q.1 ≤ x) : (e q).1 ≤ F x := by
    exact le_sSup ⟨q, hq, rfl⟩
  have hF_upper (x : L) (q : s) (hxq : x < q.1) : F x ≤ (e q).1 := by
    apply sSup_le
    rintro _ ⟨p, hp, rfl⟩
    exact (e.le_iff_le.mpr (hp.trans hxq.le))
  have hG_lower (y : M) (q : t) (hq : q.1 ≤ y) : (e.symm q).1 ≤ G y := by
    exact le_sSup ⟨q, hq, rfl⟩
  have hG_upper (y : M) (q : t) (hyq : y < q.1) : G y ≤ (e.symm q).1 := by
    apply sSup_le
    rintro _ ⟨p, hp, rfl⟩
    exact (e.symm.le_iff_le.mpr (hp.trans hyq.le))
  have hGF (x : L) : G (F x) = x := by
    apply le_antisymm
    · by_contra h
      have hxG : x < G (F x) := lt_of_not_ge h
      obtain ⟨q, hqs, hxq, hqG⟩ := hs.exists_between hxG
      obtain ⟨z, hzG, hqz⟩ := lt_sSup_iff.mp hqG
      obtain ⟨p, hpF, rfl⟩ := hzG
      have heqp : (e (⟨q, hqs⟩ : s)).1 < p.1 := by
        have hsub : (⟨q, hqs⟩ : s) < e.symm p := hqz
        simpa using (e.lt_iff_lt.mpr hsub)
      exact (not_lt_of_ge (hF_upper x ⟨q, hqs⟩ hxq)) (heqp.trans_le hpF)
    · calc
        x = sSup ((fun q : s ↦ q.1) '' {q : s | q.1 ≤ x}) :=
          (apm_t95j06_sSup_dense_Iic_aux L s hs x).symm
        _ ≤ G (F x) := by
          apply sSup_le
          rintro _ ⟨q, hqx, rfl⟩
          simpa using hG_lower (F x) (e q) (hF_lower x q hqx)
  have hFG (y : M) : F (G y) = y := by
    apply le_antisymm
    · by_contra h
      have hyF : y < F (G y) := lt_of_not_ge h
      obtain ⟨q, hqt, hyq, hqF⟩ := ht.exists_between hyF
      obtain ⟨z, hzF, hqz⟩ := lt_sSup_iff.mp hqF
      obtain ⟨p, hpG, rfl⟩ := hzF
      have heqp : (e.symm (⟨q, hqt⟩ : t)).1 < p.1 := by
        have hsub : (⟨q, hqt⟩ : t) < e p := hqz
        simpa using (e.symm.lt_iff_lt.mpr hsub)
      exact (not_lt_of_ge (hG_upper y ⟨q, hqt⟩ hyq)) (heqp.trans_le hpG)
    · calc
        y = sSup ((fun q : t ↦ q.1) '' {q : t | q.1 ≤ y}) :=
          (apm_t95j06_sSup_dense_Iic_aux M t ht y).symm
        _ ≤ F (G y) := by
          apply sSup_le
          rintro _ ⟨q, hqy, rfl⟩
          simpa using hF_lower (G y) (e.symm q) (hG_lower y q hqy)
  have hFstrict : StrictMono F := by
    intro x y hxy
    obtain ⟨q, hqs, hxq, hqy⟩ := hs.exists_between hxy
    obtain ⟨r, hrs, hxr, hrq⟩ := hs.exists_between hxq
    have herq : (e (⟨r, hrs⟩ : s)).1 < (e (⟨q, hqs⟩ : s)).1 := by
      apply e.lt_iff_lt.mpr
      exact hrq
    exact (hF_upper x ⟨r, hrs⟩ hxr).trans_lt
      (herq.trans_le (hF_lower y ⟨q, hqs⟩ hqy.le))
  let E : L ≃o M :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      map_rel_iff' := hFstrict.le_iff_le }
  exact ⟨E, E.map_bot, E.map_top⟩

/-- **Compact separable linear-continuum classification (estimated 70--120
lines).** Every nontrivial second-countable complete dense linear order with
its order topology is endpoint-preservingly homeomorphic to the unit interval.

This is true by choosing a countable dense subset, identifying it with a dense
subset of the rationals in `(0,1)`, and extending the order isomorphism by
Dedekind completeness.  Order isomorphisms between order-topological spaces
are homeomorphisms. -/
theorem apm_t95j06_completeSeparableLinearOrder_homeomorph_Icc
    (L : Type*) [TopologicalSpace L] [CompleteLinearOrder L]
    [OrderTopology L] [DenselyOrdered L] [TopologicalSpace.SeparableSpace L]
    [Nontrivial L] :
    ∃ e : L ≃ₜ Set.Icc (0 : ℝ) 1,
      e ⊥ = ⟨0, by norm_num⟩ ∧ e ⊤ = ⟨1, by norm_num⟩ := by
  let I := Set.Icc (0 : ℝ) 1
  obtain ⟨s, hsc, hsd, hsbot', hstop'⟩ :=
    exists_countable_dense_no_bot_top L
  obtain ⟨t, htc, htd, htbot', httop'⟩ :=
    exists_countable_dense_no_bot_top I
  have hsbot : (⊥ : L) ∉ s := hsbot' ⊥ isBot_bot
  have hstop : (⊤ : L) ∉ s := hstop' ⊤ isTop_top
  have htbot : (⊥ : I) ∉ t := htbot' ⊥ isBot_bot
  have httop : (⊤ : I) ∉ t := httop' ⊤ isTop_top
  letI : Countable s := hsc
  letI : Countable t := htc
  letI : Nonempty s := hsd.nonempty.to_subtype
  letI : Nonempty t := htd.nonempty.to_subtype
  letI : DenselyOrdered s :=
    ⟨fun a b hab ↦ by
      obtain ⟨c, hcs, hac, hcb⟩ := hsd.exists_between hab
      exact ⟨⟨c, hcs⟩, hac, hcb⟩⟩
  letI : DenselyOrdered t :=
    ⟨fun a b hab ↦ by
      obtain ⟨c, hct, hac, hcb⟩ := htd.exists_between hab
      exact ⟨⟨c, hct⟩, hac, hcb⟩⟩
  letI : NoMinOrder s :=
    ⟨fun a ↦ by
      have hba : (⊥ : L) < a.1 := bot_lt_iff_ne_bot.mpr (fun h ↦ hsbot (h ▸ a.2))
      obtain ⟨c, hcs, _, hca⟩ := hsd.exists_between hba
      exact ⟨⟨c, hcs⟩, hca⟩⟩
  letI : NoMaxOrder s :=
    ⟨fun a ↦ by
      have hat : a.1 < (⊤ : L) := lt_top_iff_ne_top.mpr (fun h ↦ hstop (h ▸ a.2))
      obtain ⟨c, hcs, hac, _⟩ := hsd.exists_between hat
      exact ⟨⟨c, hcs⟩, hac⟩⟩
  letI : NoMinOrder t :=
    ⟨fun a ↦ by
      have hba : (⊥ : I) < a.1 := bot_lt_iff_ne_bot.mpr (fun h ↦ htbot (h ▸ a.2))
      obtain ⟨c, hct, _, hca⟩ := htd.exists_between hba
      exact ⟨⟨c, hct⟩, hca⟩⟩
  letI : NoMaxOrder t :=
    ⟨fun a ↦ by
      have hat : a.1 < (⊤ : I) := lt_top_iff_ne_top.mpr (fun h ↦ httop (h ▸ a.2))
      obtain ⟨c, hct, hac, _⟩ := htd.exists_between hat
      exact ⟨⟨c, hct⟩, hac⟩⟩
  obtain ⟨e⟩ := Order.iso_of_countable_dense (α := s) (β := t)
  obtain ⟨E, hEbot, hEtop⟩ :=
    apm_t95j06_denseOrderIso_extend_complete_aux L I s t hsd htd
      hsbot hstop htbot httop e
  refine ⟨E.toHomeomorph, ?_, ?_⟩
  · change E ⊥ = _
    rw [hEbot]
    apply Subtype.ext
    simp [I]
  · change E ⊤ = _
    rw [hEtop]
    apply Subtype.ext
    simp [I]

theorem apm_t95j06_twoEndpointContinuum_homeomorph_Icc
    (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [TopologicalSpace.MetrizableSpace K]
    [LocallyConnectedSpace K]
    (hK : IsConnected (Set.univ : Set K)) (a c : K) (hac : a ≠ c)
    (ha : IsPreconnected ({a}ᶜ : Set K))
    (hc : IsPreconnected ({c}ᶜ : Set K))
    (hcut : ∀ y : K, y ≠ a → y ≠ c →
      ¬ IsPreconnected ({y}ᶜ : Set K)) :
    ∃ e : K ≃ₜ Set.Icc (0 : ℝ) 1,
      e a = ⟨0, by norm_num⟩ ∧ e c = ⟨1, by norm_num⟩ := by
  obtain ⟨o, hot, hdense, hsep, ha0, hc1⟩ :=
    apm_t95j06_twoEndpointContinuum_cutPointOrder K hK a c hac ha hc hcut
  letI : CompleteLinearOrder K := o
  letI : OrderTopology K := hot
  letI : DenselyOrdered K := hdense
  letI : TopologicalSpace.SeparableSpace K := hsep.some
  letI : Nontrivial K := ⟨⟨a, c, hac⟩⟩
  obtain ⟨e, he0, he1⟩ :=
    apm_t95j06_completeSeparableLinearOrder_homeomorph_Icc K
  exact ⟨e, ha0.symm ▸ he0, hc1.symm ▸ he1⟩

/-- **Sub-leaf F3d (LIBRARY, estimated 220--380 lines).**  In words: a
locally connected metrizable Hausdorff space with a neighbourhood basis of
compact continua having exactly two non-cut points has real interval charts.

Proof sketch: apply the Moore--Whyburn arc characterization to each continuum:
a nondegenerate locally connected metric continuum with exactly two non-cut
points is homeomorphic to `[0,1]`.  Since `b` lies in its interior, shrink the
closed-interval homeomorphism to an open subinterval about `b`.  Mathlib
supplies restriction and interior transport for homeomorphisms but currently
has no Moore--Whyburn theorem.

Truth checks: a circle fails because every puncture remains connected; a
tripod has three non-cut endpoints; a Cantor set is not connected or locally
connected; a singleton is excluded by `a ≠ c`. -/
theorem apm_t95j06_twoEndpointContinua_locallyRealLine
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB)
    (hm : Nonempty (@TopologicalSpace.MetrizableSpace B tB))
    (hcert : @apm_t95j06_HasTwoEndpointContinuumNeighborhoods B tB) :
    @apm_t95j06_IsLocallyRealLine B tB := by
  letI : T2Space B := h2
  letI : TopologicalSpace.MetrizableSpace B := hm.some
  intro b
  obtain ⟨K, hKcompact, hKconn, hbint, a, c, hac, hab, hcb,
    hlc, ha, hc, hcut⟩ := hcert b
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : T2Space K := inferInstance
  letI : TopologicalSpace.MetrizableSpace K := inferInstance
  letI : LocallyConnectedSpace K := hlc.some
  letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKconn
  have hKuniv : IsConnected (Set.univ : Set K) := isConnected_univ
  obtain ⟨e, hea, hec⟩ :=
    apm_t95j06_twoEndpointContinuum_homeomorph_Icc K hKuniv a c hac ha hc hcut
  let W : Set B := interior K \ ({(a : B), (c : B)} : Set B)
  have hWopen : IsOpen W := isOpen_interior.sdiff
    (isClosed_singleton.union isClosed_singleton)
  have hbW : b ∈ W := ⟨hbint, by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hab.symm, hcb.symm⟩⟩
  let g : W → K := fun z => ⟨z.1, interior_subset z.2.1⟩
  have hgemb : Topology.IsEmbedding g := by
    have hgcont : Continuous g := by
      dsimp only [g]
      fun_prop
    apply Topology.IsEmbedding.of_comp (f := g)
      (g := (Subtype.val : K → B)) hgcont continuous_subtype_val
    simpa [g, Function.comp_def] using
      (Topology.IsEmbedding.subtypeVal (p := fun z : B => z ∈ W))
  have hgrange : Set.range g = Subtype.val ⁻¹' W := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z.1, hz⟩, Subtype.ext rfl⟩
  have hgopen : Topology.IsOpenEmbedding g :=
    ⟨hgemb, by rw [hgrange]; exact hWopen.preimage continuous_subtype_val⟩
  let f : W → ℝ := fun z => (e (g z) : ℝ)
  have hfemb : Topology.IsEmbedding f := by
    exact Topology.IsEmbedding.subtypeVal.comp (e.isEmbedding.comp hgemb)
  have hegrange : IsOpen (e '' Set.range g) :=
    e.isOpen_image.mpr hgopen.isOpen_range
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hegrange
  have hfrange : Set.range f = O ∩ Set.Ioo (0 : ℝ) 1 := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      have hzimg : e (g z) ∈ e '' Set.range g :=
        ⟨g z, ⟨z, rfl⟩, rfl⟩
      have hzO : (e (g z) : ℝ) ∈ O := by
        have := congrArg (fun A : Set (Set.Icc (0 : ℝ) 1) => e (g z) ∈ A) hOeq
        simpa using this.mpr hzimg
      refine ⟨hzO, ?_⟩
      have hnea : g z ≠ a := by
        intro h
        exact z.2.2 (by left; exact congrArg Subtype.val h)
      have hnec : g z ≠ c := by
        intro h
        exact z.2.2 (by right; exact congrArg Subtype.val h)
      constructor
      · exact lt_of_le_of_ne (e (g z)).2.1 (by
          intro hzero
          apply hnea
          apply e.injective
          rw [hea]
          exact Subtype.ext hzero.symm)
      · exact lt_of_le_of_ne (e (g z)).2.2 (by
          intro hone
          apply hnec
          apply e.injective
          rw [hec]
          exact Subtype.ext hone)
    · rintro ⟨hrO, hrIoo⟩
      have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hrIoo.1.le, hrIoo.2.le⟩
      let q : Set.Icc (0 : ℝ) 1 := ⟨r, hrIcc⟩
      have hqimg : q ∈ e '' Set.range g := by
        have := congrArg (fun A : Set (Set.Icc (0 : ℝ) 1) => q ∈ A) hOeq
        apply this.mp
        exact hrO
      obtain ⟨z, ⟨w, hw⟩, hz⟩ := hqimg
      subst z
      refine ⟨w, ?_⟩
      exact congrArg Subtype.val hz
  have hfopen : Topology.IsOpenEmbedding f :=
    ⟨hfemb, by rw [hfrange]; exact hOopen.inter isOpen_Ioo⟩
  refine ⟨W, hWopen, hbW, Set.range f, hfopen.isOpen_range, ?_⟩
  exact ⟨hfopen.isEmbedding.toHomeomorph⟩

/-- Assembly of F3 from planar localization, factor regularity, Jordan
separation, and the arc characterization. -/
theorem apm_t95j06_circleFactor_locallyRealLine
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB) (hsc : @SecondCountableTopology B tB)
    (hprod : ∀ b : B, ∃ U : Set B, @IsOpen B tB U ∧ b ∈ U ∧
      apm_t95j06_IsLocallyEuclideanPlane (U × Circle)) :
    @apm_t95j06_IsLocallyRealLine B tB := by
  have hplanar := apm_t95j06_circleProducts_localizeToPlanarArc B tB hprod
  obtain ⟨hlc, hm, hconn⟩ :=
    apm_t95j06_planarArcProducts_factor_regular B tB h2 hsc hplanar
  have hcert := apm_t95j06_planarArcProducts_twoEndpointContinua
    B tB h2 hplanar hlc hm hconn
  exact apm_t95j06_twoEndpointContinua_locallyRealLine B tB h2 hm hcert

/-- Assembly of the original manifold-factor leaf from the three independent
sub-leaves above. -/
theorem apm_t95j06_principalBundle_base_locallyRealLine
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (x : F) (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB) (hsc : @SecondCountableTopology B tB)
    (P : @apm_t95j06_PrincipalCircleBundle
      {y : F // y ∈ connectedComponent x} B inferInstance tB) :
    @apm_t95j06_IsLocallyRealLine B tB := by
  have hplane := apm_t95j06_surface_component_locallyEuclideanPlane F hF x
  have hproducts := apm_t95j06_bundleCharts_product_locallyEuclideanPlane
    {y : F // y ∈ connectedComponent x} B tB P hplane
  exact apm_t95j06_circleFactor_locallyRealLine B tB h2 hsc hproducts

/-- A compact space covered by real-line charts is second countable.

In words: compactness reduces the chart cover to finitely many charts, and
each chart is second countable because it is homeomorphic to an open subtype
of `ℝ`.  This is the countability input needed by the end-classification route
for puncture connectedness. -/
lemma apm_t95j06_compact_locallyRealLine_secondCountable_aux
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) :
    @SecondCountableTopology B tB := by
  choose U hUopen hb V hVopen he using hloc
  let e (b : B) : U b ≃ₜ V b := Classical.choice (he b)
  have hcover : (Set.univ : Set B) ⊆ ⋃ b, U b := by
    intro b hbuniv
    exact Set.mem_iUnion.mpr ⟨b, hb b⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  let I := {b : B // b ∈ s}
  let W : I → Set B := fun i ↦ U i.1
  letI : Countable I := Finite.to_countable
  letI (i : I) : SecondCountableTopology (V i.1) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI (i : I) : SecondCountableTopology (W i) :=
    (e i.1).secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := W)
  · intro i
    exact hUopen i.1
  · apply Set.eq_univ_of_univ_subset
    intro b hbuniv
    have hbmem := hs hbuniv
    simp only [Set.mem_iUnion] at hbmem ⊢
    obtain ⟨i, hi⟩ := hbmem
    obtain ⟨his, hbUi⟩ := hi
    exact ⟨⟨i, his⟩, hbUi⟩
/-- An open subspace of a space locally homeomorphic to the real line is again
locally homeomorphic to the real line. -/
theorem apm_t95j06_puncture_inherits_oneManifold_aux_openSubtype
    (B : Type*) [TopologicalSpace B]
    (hloc : apm_t95j06_IsLocallyRealLine B)
    (W : Set B) (hW : IsOpen W) :
    apm_t95j06_IsLocallyRealLine W := by
  intro w
  obtain ⟨U, hU, hwU, V, hV, ⟨c⟩⟩ := hloc w.1
  let U' : Set W := Subtype.val ⁻¹' U
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  let g : U' → U := fun w' => ⟨w'.1.1, w'.2⟩
  have hg : Topology.IsOpenEmbedding g := by
    have h1 : Topology.IsOpenEmbedding ((Subtype.val : U → B) ∘ g) :=
      (hW.isOpenEmbedding_subtypeVal).comp hU'.isOpenEmbedding_subtypeVal
    exact Topology.IsOpenEmbedding.of_comp g hU.isOpenEmbedding_subtypeVal h1
  have hF : Topology.IsOpenEmbedding ((Subtype.val : V → ℝ) ∘ c ∘ g) :=
    hV.isOpenEmbedding_subtypeVal.comp (c.isOpenEmbedding.comp hg)
  exact ⟨U', hU', hwU, _, hF.isOpen_range,
    ⟨hF.isEmbedding.toHomeomorph⟩⟩

/-- The puncture inherits Hausdorffness, second countability, and local real
charts (estimated 60--100 lines). Subtype instances give the first two;
restrict each chart to the open complement of `b` for the third. -/
theorem apm_t95j06_puncture_inherits_oneManifold
    (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB) (hsc : @SecondCountableTopology B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) (b : B) :
    @T2Space {x : B // x ≠ b} inferInstance ∧
      @SecondCountableTopology {x : B // x ≠ b} inferInstance ∧
      @apm_t95j06_IsLocallyRealLine {x : B // x ≠ b} inferInstance := by
  letI : TopologicalSpace B := tB
  letI : T2Space B := h2
  letI : SecondCountableTopology B := hsc
  let W : Set B := {x | x ≠ b}
  have hW : IsOpen W := by
    simpa only [Set.mem_setOf_eq] using (isClosed_singleton : IsClosed ({b} : Set B)).isOpen_compl
  refine ⟨inferInstance, ?_,
    apm_t95j06_puncture_inherits_oneManifold_aux_openSubtype B hloc W hW⟩
  exact @TopologicalSpace.secondCountableTopology_induced W B tB hsc Subtype.val

/-- The puncture is noncompact (estimated 80--140 lines). If compact it would
be closed in the Hausdorff ambient space; it is also open. A real-line chart
provides a second point, so connectedness forbids this nontrivial clopen set.
The endpoint counterexample `[0,1]` fails the local-real-line hypothesis. -/
theorem apm_t95j06_puncture_noncompact
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (hconn : @ConnectedSpace B tB)
    (h2 : @T2Space B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) (b : B) :
    @NoncompactSpace {x : B // x ≠ b} inferInstance := by
  letI : ConnectedSpace B := hconn
  letI : T2Space B := h2
  constructor
  intro hcompact
  have hp : IsCompact ({x : B | x ≠ b} : Set B) := by
    have hi := hcompact.image (continuous_subtype_val :
      Continuous (Subtype.val : {x : B // x ≠ b} → B))
    simpa using hi
  have hopen : IsOpen ({x : B | x ≠ b} : Set B) := isClosed_singleton.isOpen_compl
  obtain ⟨U, hU, hb, V, hV, ⟨e⟩⟩ := hloc b
  let v : V := e ⟨b, hb⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV v.1 v.2
  have hw : v.1 + ε / 2 ∈ V := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have : 0 < ε / 2 := half_pos hε
    rw [show v.1 + ε / 2 - v.1 = ε / 2 by ring, abs_of_pos this]
    linarith
  let w : V := ⟨v.1 + ε / 2, hw⟩
  have hne : (e.symm w).1 ≠ b := by
    intro heq
    have heq' : e.symm w = (⟨b, hb⟩ : U) := Subtype.ext heq
    have heq'' := congrArg (fun u : U ↦ (e u).1) heq'
    simp only [e.apply_symm_apply] at heq''
    change v.1 + ε / 2 = v.1 at heq''
    linarith
  have hall : ({x : B | x ≠ b} : Set B) = Set.univ :=
    (show IsClopen ({x : B | x ≠ b} : Set B) from ⟨hp.isClosed, hopen⟩).eq_univ
      ⟨(e.symm w).1, hne⟩
  have : b ∈ ({x : B | x ≠ b} : Set B) := hall ▸ Set.mem_univ b
  exact this rfl

/-- A second-countable Hausdorff space locally modelled on `ℝ` has a countable
compact cover (estimated 60--100 lines).  Local charts give local compactness;
`sigmaCompactSpace_of_locallyCompact_secondCountable` and
`SigmaCompactSpace_iff_exists_compact_covering` then give the cover.  This is
strictly only the exhaustion input: it makes no classification conclusion. -/
theorem apm_t95j06_locallyRealLine_compact_cover
    (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (hloc : apm_t95j06_IsLocallyRealLine X) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ (⋃ n, K n) = Set.univ := by
  letI : WeaklyLocallyCompactSpace X :=
    { exists_compact_mem_nhds := by
        intro x
        obtain ⟨U, hU, hxU, V, hV, ⟨e⟩⟩ := hloc x
        letI : LocallyCompactSpace V := hV.locallyCompactSpace
        letI : LocallyCompactSpace U :=
          e.locallyCompactSpace_iff.mpr inferInstance
        obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (⟨x, hxU⟩ : U)
        refine ⟨Subtype.val '' C, hCc.image continuous_subtype_val, ?_⟩
        exact hU.isOpenMap_subtype_val.image_mem_nhds hC }
  letI : LocallyCompactSpace X := inferInstance
  letI : SigmaCompactSpace X := inferInstance
  exact SigmaCompactSpace.exists_compact_covering

open Set in
/-- A real-line chart can be shrunk to a relatively compact open interval
chart around its marked point (estimated 70--120 lines).  In coordinates,
choose a bounded open interval whose closed interval lies inside the original
open target, restrict the homeomorphism, and use compactness of the closed
interval plus Hausdorffness to control the ambient closure.  The resulting
bounded interval is homeomorphic to `ℝ`.  This is purely local and makes no
claim about joining charts or classifying the ambient space. -/
theorem apm_t95j06_locallyRealLine_relativelyCompact_chart
    (X : Type) [TopologicalSpace X] [T2Space X]
    (hloc : apm_t95j06_IsLocallyRealLine X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) ∧
      Nonempty (U ≃ₜ ℝ) := by
  obtain ⟨U, hU, hx, V, hV, ⟨e⟩⟩ := hloc x
  set r : ℝ := (e ⟨x, hx⟩ : ℝ) with hr
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV r (e ⟨x, hx⟩).2
  set δ := ε / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hIcc : Icc (r - δ) (r + δ) ⊆ V := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  -- the embedding of the closed interval
  let gK : Icc (r - δ) (r + δ) → X := fun t => (e.symm ⟨t.1, hIcc t.2⟩ : X)
  have hgK : Continuous gK := by
    apply continuous_subtype_val.comp
    apply e.symm.continuous.comp
    exact (continuous_subtype_val).subtype_mk _
  let g : Ioo (r - δ) (r + δ) → X := fun t => (e.symm ⟨t.1, hIcc (Ioo_subset_Icc_self t.2)⟩ : X)
  have hg : Topology.IsEmbedding g := by
    have h1 : Topology.IsEmbedding (fun t : Ioo (r - δ) (r + δ) =>
        (⟨t.1, hIcc (Ioo_subset_Icc_self t.2)⟩ : V)) :=
      Topology.IsEmbedding.inclusion (fun _ ht => hIcc (Ioo_subset_Icc_self ht))
    exact Topology.IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp h1)
  have hgopen : IsOpen (range g) := by
    have h1 : IsOpen (range (fun t : Ioo (r - δ) (r + δ) =>
        (⟨t.1, hIcc (Ioo_subset_Icc_self t.2)⟩ : V))) := by
      have : range (fun t : Ioo (r - δ) (r + δ) =>
          (⟨t.1, hIcc (Ioo_subset_Icc_self t.2)⟩ : V)) = Subtype.val ⁻¹' Ioo (r - δ) (r + δ) := by
        ext v; constructor
        · rintro ⟨t, rfl⟩; exact t.2
        · intro hv; exact ⟨⟨v.1, hv⟩, rfl⟩
      rw [this]; exact isOpen_Ioo.preimage continuous_subtype_val
    have h2 : range g = Subtype.val '' (e.symm '' range (fun t : Ioo (r - δ) (r + δ) =>
        (⟨t.1, hIcc (Ioo_subset_Icc_self t.2)⟩ : V))) := by
      rw [← range_comp, ← range_comp]; rfl
    rw [h2]
    exact hU.isOpenMap_subtype_val _ (e.symm.isOpenMap _ h1)
  refine ⟨range g, hgopen, ?_, ?_, ?_⟩
  · refine ⟨⟨r, by linarith, by linarith⟩, ?_⟩
    simp [g, hr]
  · have hC : IsCompact (range gK) := isCompact_range hgK
    refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨t.1, Ioo_subset_Icc_self t.2⟩, rfl⟩
  · have hrδ : r - δ < r + δ := by linarith
    have hs : 0 < ((r + δ) - (r - δ)) / 2 := by linarith
    let a : ℝ ≃ₜ ℝ := affineHomeomorph (((r + δ) - (r - δ)) / 2) (((r - δ) + (r + δ)) / 2) hs.ne'
    have himage : a '' Ioo (-1 : ℝ) 1 = Ioo (r - δ) (r + δ) := by
      dsimp [a]
      rw [affineHomeomorph_image_Ioo _ _ _ _ hs]
      congr 1 <;> ring
    let I : Ioo (r - δ) (r + δ) ≃ₜ ℝ :=
      ((a.image (Ioo (-1 : ℝ) 1)).trans (Homeomorph.setCongr himage)).symm.trans
        (orderIsoIooNegOneOne ℝ).toHomeomorph.symm
    exact ⟨hg.toHomeomorph.symm.trans I⟩

/- **LIBRARY, finite interval-chart chain (estimated 140--220 lines).**
In a connected noncompact Hausdorff one-manifold, a finite collection of
relatively compact interval charts is contained in one relatively compact
interval chart.  Add charts along a shortest overlap chain from the current
union: the order topology on overlapping real intervals gives only two ends;
Hausdorffness rules out branching and noncompactness rules out the final two
ends closing into a circle.  This lemma begins with the finite chart family
already chosen, so it contains no compactness/subcover argument and is
strictly the finite one-dimensional gluing step. -/
/-- The nerve of a connected open cover is connected: a finite set of members
of the cover can be enlarged to a finite family whose union is connected.
Here every member is connected because it is homeomorphic to `ℝ`.  This is a
cover/finite-graph lemma, independent of compact closures and of the
one-dimensional no-branching argument.  Estimated size: 45--70 lines. -/
theorem apm_t95j06_finite_intervalCharts_connected_enlargement
    (X : Type) [TopologicalSpace X] [ConnectedSpace X]
    (A : X → Set X) (hAopen : ∀ x, IsOpen (A x))
    (hxA : ∀ x, x ∈ A x) (hAreal : ∀ x, Nonempty (A x ≃ₜ ℝ))
    (s : Finset X) :
    ∃ t : Finset X, s ⊆ t ∧ IsConnected (⋃ x ∈ t, A x) := by
  classical
  let S : Finset X → Set X := fun t => ⋃ x ∈ t, A x
  have hAconn (x : X) : IsConnected (A x) := by
    obtain ⟨e⟩ := hAreal x
    rw [isConnected_iff_connectedSpace]
    exact connectedSpace_iff_univ.mpr <| by
      rw [← e.isConnected_image]
      simpa using (isConnected_univ : _root_.IsConnected (Set.univ : Set ℝ))
  let P : X → X → Prop := fun x y =>
    ∃ t : Finset X, x ∈ S t ∧ y ∈ S t ∧ IsConnected (S t)
  have hPlocal (x : X) : ∀ᶠ y in nhds x, P x y := by
    filter_upwards [hAopen x |>.mem_nhds (hxA x)] with y hy
    refine ⟨{x}, ?_, ?_, ?_⟩ <;> simp only [S, Finset.mem_singleton,
      Set.iUnion_iUnion_eq_left]
    · exact hxA x
    · exact hy
    · exact hAconn x
  have hPtrans : IsTrans X P := by
    constructor
    intro x y z hxy hyz
    obtain ⟨t, hxt, hyt, ht⟩ := hxy
    obtain ⟨u, hyu, hzu, hu⟩ := hyz
    have hSunion : S (t ∪ u) = S t ∪ S u := by
      ext q
      simp only [S, Set.mem_iUnion, Finset.mem_union, Set.mem_union]
      constructor
      · rintro ⟨a, ⟨ha | ha, hqa⟩⟩
        · exact Or.inl ⟨a, ha, hqa⟩
        · exact Or.inr ⟨a, ha, hqa⟩
      · rintro (⟨a, ha, hqa⟩ | ⟨a, ha, hqa⟩)
        · exact ⟨a, Or.inl ha, hqa⟩
        · exact ⟨a, Or.inr ha, hqa⟩
    refine ⟨t ∪ u, ?_, ?_, ?_⟩
    · rw [hSunion]; exact Or.inl hxt
    · rw [hSunion]; exact Or.inr hzu
    · rw [hSunion]
      exact ht.union ⟨y, hyt, hyu⟩ hu
  have hPsymm : Symmetric P := by
    intro x y hxy
    obtain ⟨t, hxt, hyt, ht⟩ := hxy
    exact ⟨t, hyt, hxt, ht⟩
  have hP (x y : X) : P x y :=
    PreconnectedSpace.induction₂ P hPlocal hPtrans hPsymm x y
  let x₀ : X := Classical.choice inferInstance
  have aggregate : ∀ r : Finset X,
      ∃ t : Finset X, r ⊆ t ∧ x₀ ∈ S t ∧ IsConnected (S t) := by
    intro r
    induction r using Finset.induction_on with
    | empty =>
        obtain ⟨t, hx₀t, _, ht⟩ := hP x₀ x₀
        exact ⟨t, by simp, hx₀t, ht⟩
    | @insert a r har ih =>
        obtain ⟨t, hrt, hx₀t, ht⟩ := ih
        obtain ⟨u, hx₀u, hau, hu⟩ := hP x₀ a
        have hSunion : S (t ∪ u) = S t ∪ S u := by
          ext q
          simp only [S, Set.mem_iUnion, Finset.mem_union, Set.mem_union]
          constructor
          · rintro ⟨b, ⟨hb | hb, hqb⟩⟩
            · exact Or.inl ⟨b, hb, hqb⟩
            · exact Or.inr ⟨b, hb, hqb⟩
          · rintro (⟨b, hb, hqb⟩ | ⟨b, hb, hqb⟩)
            · exact ⟨b, Or.inl hb, hqb⟩
            · exact ⟨b, Or.inr hb, hqb⟩
        have hvconn : IsConnected (S (t ∪ u)) := by
          rw [hSunion]
          exact ht.union ⟨x₀, hx₀t, hx₀u⟩ hu
        have hSw : S (insert a (t ∪ u)) = A a ∪ S (t ∪ u) := by
          ext q
          simp only [S, Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
          constructor
          · rintro ⟨b, ⟨rfl | hb, hqb⟩⟩
            · exact Or.inl hqb
            · exact Or.inr ⟨b, hb, hqb⟩
          · rintro (hqa | ⟨b, hb, hqb⟩)
            · exact ⟨a, Or.inl rfl, hqa⟩
            · exact ⟨b, Or.inr hb, hqb⟩
        refine ⟨insert a (t ∪ u), ?_, ?_, ?_⟩
        · intro q hq
          rw [Finset.mem_insert] at hq ⊢
          rcases hq with rfl | hq
          · exact Or.inl rfl
          · exact Or.inr (Finset.mem_union_left u (hrt hq))
        · rw [hSw]
          exact Or.inr (by rw [hSunion]; exact Or.inl hx₀t)
        · rw [hSw]
          apply (hAconn a).union
          · refine ⟨a, hxA a, ?_⟩
            rw [hSunion]
            exact Or.inr hau
          · exact hvconn
  obtain ⟨t, hst, _, ht⟩ := aggregate s
  exact ⟨t, hst, ht⟩

/- The genuinely one-dimensional gluing core.  A connected finite union of
relatively compact line charts in a noncompact Hausdorff one-manifold sits in
one relatively compact line chart.  The connected-union hypothesis removes
the open-cover nerve construction from the parent theorem; the proof orders
successive overlaps, rules out branching by local real charts, and rules out
closing the two ends using noncompactness.  Estimated size: 110--170 lines. -/
/- Two overlapping open real-line charts in a Hausdorff space have union
homeomorphic to the real line unless their union is compact.

This is the two-chart one-manifold dichotomy.  Transport the overlap through
the two real coordinates.  Its components are open intervals.  Compatible
orders glue to a line unless both pairs of ends are identified; Hausdorffness
excludes every partial/doubled-end identification, and identifying both pairs
produces the compact alternative.  This statement is independent of compact
closures and of the ambient connected/noncompact hypotheses.  Estimated
size: 80--130 lines. -/
/-- The nested-chart case of two-chart gluing: if either real chart contains
the other, their union is the larger chart and is therefore homeomorphic to
the real line. -/
lemma apm_t95j06_two_realCharts_line_of_nested
    (X : Type) [TopologicalSpace X] (U V : Set X)
    (hUreal : Nonempty (U ≃ₜ ℝ)) (hVreal : Nonempty (V ≃ₜ ℝ))
    (hnested : U ⊆ V ∨ V ⊆ U) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ ℝ) := by
  rcases hnested with hUV | hVU
  · obtain ⟨e⟩ := hVreal
    have h : U ∪ V = V := Set.union_eq_right.mpr hUV
    exact ⟨(Homeomorph.setCongr h).trans e⟩
  · obtain ⟨e⟩ := hUreal
    have h : U ∪ V = U := Set.union_eq_left.mpr hVU
    exact ⟨(Homeomorph.setCongr h).trans e⟩

/-- A continuous injective open coordinate transition on a preconnected open
real set is monotone (up to reversal), and its range is again an open
preconnected real set.  Applied to one overlap component, this says that the
transition carries that component homeomorphically onto an open interval. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_monotone
    (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioo a b))
    (hfi : Set.InjOn f (Set.Ioo a b))
    (hfo : IsOpenMap (Set.restrict (Set.Ioo a b) f)) :
    (StrictMonoOn f (Set.Ioo a b) ∨ StrictAntiOn f (Set.Ioo a b)) ∧
      IsOpen (f '' Set.Ioo a b) ∧ _root_.IsPreconnected (f '' Set.Ioo a b) := by
  have hmono := hf.strictMonoOn_of_injOn_Ioo hab hfi
  have hopen : IsOpen (Set.range (Set.restrict (Set.Ioo a b) f)) := by
    simpa only [Set.image_univ] using hfo Set.univ isOpen_univ
  have hrange : Set.range (Set.restrict (Set.Ioo a b) f) = f '' Set.Ioo a b := by
    ext z
    simp only [Set.mem_range, Set.restrict_apply, Set.mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at hopen
  have hpre : _root_.IsPreconnected (f '' Set.Ioo a b) :=
    isPreconnected_Ioo.image f hf
  exact ⟨hmono, hopen, hpre⟩

/-- Hausdorff endpoint engine for two real charts.  If a net in their overlap
has finite limits in both coordinates, the two inverse-chart limit points
coincide.  In particular the first-coordinate limit still represents a point
of the overlap, which contradicts maximality when it is a finite endpoint of
an overlap component. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_end
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ)
    {ι : Type} {l : Filter ι} [l.NeBot]
    (x : ι → U) (y : ι → V)
    (hxy : ∀ᶠ i in l, (x i : X) = (y i : X))
    (β s : ℝ)
    (hφ : Filter.Tendsto (fun i => φ (x i)) l (nhds β))
    (hψ : Filter.Tendsto (fun i => ψ (y i)) l (nhds s)) :
    β ∈ φ '' (Subtype.val ⁻¹' V) := by
  have hxφ : Filter.Tendsto (fun i => (x i : X)) l
      (nhds ((φ.symm β : U) : X)) := by
    have h := φ.symm.continuous.continuousAt.tendsto.comp hφ
    have hh := continuous_subtype_val.continuousAt.tendsto.comp h
    convert hh using 1
    ext i
    exact congrArg Subtype.val (φ.symm_apply_apply (x i)).symm
  have hxψ : Filter.Tendsto (fun i => (x i : X)) l
      (nhds ((ψ.symm s : V) : X)) := by
    have h := ψ.symm.continuous.continuousAt.tendsto.comp hψ
    have hy : Filter.Tendsto (fun i => (y i : X)) l
        (nhds ((ψ.symm s : V) : X)) := by
      have hh := continuous_subtype_val.continuousAt.tendsto.comp h
      convert hh using 1
      ext i
      exact congrArg Subtype.val (ψ.symm_apply_apply (y i)).symm
    apply hy.congr'
    filter_upwards [hxy] with i hi
    exact hi.symm
  have heq : ((φ.symm β : U) : X) = ((ψ.symm s : V) : X) :=
    tendsto_nhds_unique hxφ hxψ
  refine ⟨φ.symm β, ?_, φ.apply_symm_apply β⟩
  show ((φ.symm β : U) : X) ∈ V
  rw [heq]
  exact (ψ.symm s).property

/-- A finite endpoint missing from the first-coordinate overlap cannot have a
finite transition-coordinate limit along any nontrivial net in the overlap.
This is the Hausdorff end-divergence assertion used in Step 1; monotonicity
then converts failure of every finite limit into unboundedness. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_no_finite_end_limit
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ)
    {ι : Type} {l : Filter ι} [l.NeBot]
    (x : ι → U) (y : ι → V)
    (hxy : ∀ᶠ i in l, (x i : X) = (y i : X))
    (β : ℝ) (hβ : β ∉ φ '' (Subtype.val ⁻¹' V))
    (hφ : Filter.Tendsto (fun i => φ (x i)) l (nhds β)) :
    ∀ s : ℝ, ¬ Filter.Tendsto (fun i => ψ (y i)) l (nhds s) := by
  intro s hψ
  exact hβ (apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_end
    X U V φ ψ x y hxy β s hφ hψ)

/-- Right-ray half of the combinatorial overlap-shape lemma.  If every
component is a left or right ray and one component is a right ray, then the
set is that ray or the union of it with the unique left-ray component.
Distinct rays of the same orientation intersect and hence cannot be distinct
connected components. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_ray_components
    (A : Set ℝ) (hAne : A ≠ Set.univ)
    (hray : ∀ x ∈ A, (∃ a, connectedComponentIn A x = Set.Ioi a) ∨
      ∃ b, connectedComponentIn A x = Set.Iio b)
    (x : ℝ) (hxA : x ∈ A) (a : ℝ)
    (hxa : connectedComponentIn A x = Set.Ioi a) :
    (∃ a, A = Set.Ioi a) ∨
      ∃ a b, a ≤ b ∧ A = Set.Iio a ∪ Set.Ioi b := by
    by_cases hall : A = connectedComponentIn A x
    · exact Or.inl ⟨a, hall.trans hxa⟩
    · obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ∉ connectedComponentIn A x := by
        by_contra h
        push_neg at h
        exact hall (Set.Subset.antisymm h (connectedComponentIn_subset A x))
      rcases hray y hyA with ⟨c, hyc⟩ | ⟨c, hyc⟩
      · let z := max a c + 1
        have hza : z ∈ Set.Ioi a := by
          change a < max a c + 1
          linarith [le_max_left a c]
        have hzc : z ∈ Set.Ioi c := by
          change c < max a c + 1
          linarith [le_max_right a c]
        have hzxa : z ∈ connectedComponentIn A x := hxa.symm ▸ hza
        have hzyc : z ∈ connectedComponentIn A y := hyc.symm ▸ hzc
        have heq := (connectedComponentIn_eq hzxa).trans
          (connectedComponentIn_eq hzyc).symm
        exact (hyx (heq ▸ mem_connectedComponentIn hyA)).elim
      · have hcover : A = Set.Ioi a ∪ Set.Iio c := by
          apply Set.Subset.antisymm
          · intro z hzA
            by_cases hzx : z ∈ connectedComponentIn A x
            · exact Or.inl (hxa ▸ hzx)
            · rcases hray z hzA with ⟨d, hzd⟩ | ⟨d, hzd⟩
              · let w := max a d + 1
                have hwx : w ∈ connectedComponentIn A x := hxa.symm ▸ (by
                  dsimp [w]; linarith [le_max_left a d] : a < w)
                have hwz : w ∈ connectedComponentIn A z := hzd.symm ▸ (by
                  dsimp [w]; linarith [le_max_right a d] : d < w)
                have heq := (connectedComponentIn_eq hwx).trans
                  (connectedComponentIn_eq hwz).symm
                exact (hzx (heq ▸ mem_connectedComponentIn hzA)).elim
              · let w := min c d - 1
                have hwy : w ∈ connectedComponentIn A y := hyc.symm ▸ (by
                  dsimp [w]; linarith [min_le_left c d] : w < c)
                have hwz : w ∈ connectedComponentIn A z := hzd.symm ▸ (by
                  dsimp [w]; linarith [min_le_right c d] : w < d)
                have heq := (connectedComponentIn_eq hwy).trans
                  (connectedComponentIn_eq hwz).symm
                exact Or.inr (hyc ▸ (heq ▸ mem_connectedComponentIn hzA))
          · exact Set.union_subset (hxa ▸ connectedComponentIn_subset A x)
              (hyc ▸ connectedComponentIn_subset A y)
        have hca : c ≤ a := by
          by_contra h
          have hac : a < c := lt_of_not_ge h
          apply hAne
          rw [hcover]
          ext r
          simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_univ, iff_true]
          by_cases har : a < r
          · exact Or.inl har
          · exact Or.inr (lt_of_le_of_lt (le_of_not_gt har) hac)
        exact Or.inr ⟨c, a, hca, by simpa [Set.union_comm] using hcover⟩

/-- Left-ray mirror of `aux_ray_components`: if one component is a left ray,
the set is that ray or its union with the unique right-ray component. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_left_ray_components
    (A : Set ℝ) (hAne : A ≠ Set.univ)
    (hray : ∀ x ∈ A, (∃ a, connectedComponentIn A x = Set.Ioi a) ∨
      ∃ b, connectedComponentIn A x = Set.Iio b)
    (x : ℝ) (hxA : x ∈ A) (b : ℝ)
    (hxb : connectedComponentIn A x = Set.Iio b) :
    (∃ b, A = Set.Iio b) ∨
      ∃ a b, a ≤ b ∧ A = Set.Iio a ∪ Set.Ioi b := by
  by_cases hall : A = connectedComponentIn A x
  · exact Or.inl ⟨b, hall.trans hxb⟩
  · obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ∉ connectedComponentIn A x := by
      by_contra h
      push_neg at h
      exact hall (Set.Subset.antisymm h (connectedComponentIn_subset A x))
    rcases hray y hyA with ⟨c, hyc⟩ | ⟨c, hyc⟩
    · have hcover : A = Set.Iio b ∪ Set.Ioi c := by
        apply Set.Subset.antisymm
        · intro z hzA
          by_cases hzx : z ∈ connectedComponentIn A x
          · exact Or.inl (hxb ▸ hzx)
          · rcases hray z hzA with ⟨d, hzd⟩ | ⟨d, hzd⟩
            · let w := max c d + 1
              have hwy : w ∈ connectedComponentIn A y := hyc.symm ▸ (by
                dsimp [w]; linarith [le_max_left c d] : c < w)
              have hwz : w ∈ connectedComponentIn A z := hzd.symm ▸ (by
                dsimp [w]; linarith [le_max_right c d] : d < w)
              have heq := (connectedComponentIn_eq hwy).trans
                (connectedComponentIn_eq hwz).symm
              exact Or.inr (hyc ▸ (heq ▸ mem_connectedComponentIn hzA))
            · let w := min b d - 1
              have hwx : w ∈ connectedComponentIn A x := hxb.symm ▸ (by
                dsimp [w]; linarith [min_le_left b d] : w < b)
              have hwz : w ∈ connectedComponentIn A z := hzd.symm ▸ (by
                dsimp [w]; linarith [min_le_right b d] : w < d)
              have heq := (connectedComponentIn_eq hwx).trans
                (connectedComponentIn_eq hwz).symm
              exact (hzx (heq ▸ mem_connectedComponentIn hzA)).elim
        · exact Set.union_subset (hxb ▸ connectedComponentIn_subset A x)
            (hyc ▸ connectedComponentIn_subset A y)
      have hbc : b ≤ c := by
        by_contra h
        have hcb : c < b := lt_of_not_ge h
        apply hAne
        rw [hcover]
        ext r
        simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ, iff_true]
        by_cases hrb : r < b
        · exact Or.inl hrb
        · exact Or.inr (lt_of_lt_of_le hcb (le_of_not_gt hrb))
      exact Or.inr ⟨b, c, hbc, hcover⟩
    · let z := min b c - 1
      have hzb : z ∈ Set.Iio b := by
        change min b c - 1 < b
        linarith [min_le_left b c]
      have hzc : z ∈ Set.Iio c := by
        change min b c - 1 < c
        linarith [min_le_right b c]
      have hzxb : z ∈ connectedComponentIn A x := hxb.symm ▸ hzb
      have hzyc : z ∈ connectedComponentIn A y := hyc.symm ▸ hzc
      have heq := (connectedComponentIn_eq hzxb).trans
        (connectedComponentIn_eq hzyc).symm
      exact (hyx (heq ▸ mem_connectedComponentIn hyA)).elim

/-- Combined combinatorial overlap shape: a nonempty proper real set whose
components are rays is one ray or one left ray together with one right ray. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_ray_shape
    (A : Set ℝ) (hA : A.Nonempty) (hAne : A ≠ Set.univ)
    (hray : ∀ x ∈ A, (∃ a, connectedComponentIn A x = Set.Ioi a) ∨
      ∃ b, connectedComponentIn A x = Set.Iio b) :
    (∃ a, A = Set.Ioi a) ∨ (∃ b, A = Set.Iio b) ∨
      ∃ a b, a ≤ b ∧ A = Set.Iio a ∪ Set.Ioi b := by
  obtain ⟨x, hxA⟩ := hA
  rcases hray x hxA with ⟨a, hxa⟩ | ⟨b, hxb⟩
  · rcases apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_ray_components
      A hAne hray x hxA a hxa with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_left_ray_components
      A hAne hray x hxA b hxb with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- An open, nonempty, proper preconnected subset of the real line is an open
bounded interval or a left or right ray.  This is the order-topological first
stage of L3, applied to each open connected component of the chart overlap. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_open_interval_shape
    (S : Set ℝ) (hSopen : IsOpen S) (hSne : S.Nonempty)
    (hSproper : S ≠ Set.univ) (hSconn : _root_.IsPreconnected S) :
    (∃ a b, S = Set.Ioo a b) ∨ (∃ a, S = Set.Ioi a) ∨
      ∃ b, S = Set.Iio b := by
  have hinter : interior S = S := hSopen.interior_eq
  rcases hSconn.mem_intervals with h | h | h | h | h | h | h | h | h | h
  · rw [h, interior_Icc] at hinter
    left; exact ⟨sInf S, sSup S, h.trans hinter.symm⟩
  · rw [h, interior_Ico] at hinter
    left; exact ⟨sInf S, sSup S, h.trans hinter.symm⟩
  · rw [h, interior_Ioc] at hinter
    left; exact ⟨sInf S, sSup S, h.trans hinter.symm⟩
  · left; exact ⟨sInf S, sSup S, h⟩
  · rw [h, interior_Ici] at hinter
    right; left; exact ⟨sInf S, h.trans hinter.symm⟩
  · right; left; exact ⟨sInf S, h⟩
  · rw [h, interior_Iic] at hinter
    right; right; exact ⟨sSup S, h.trans hinter.symm⟩
  · right; right; exact ⟨sSup S, h⟩
  · exact (hSproper h).elim
  · exact (hSne.ne_empty h).elim

/-- The finite endpoints of a bounded connected component of an open subset
of `ℝ` do not belong to the ambient open set.  Otherwise a small closed
interval inside the open set joins the endpoint to an interior point of the
component, contradicting the component's description as `Ioo p q`. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_component_endpoints
    (A : Set ℝ) (hAopen : IsOpen A) (t p q : ℝ) (htA : t ∈ A)
    (hcomp : connectedComponentIn A t = Set.Ioo p q) :
    p ∉ A ∧ q ∉ A := by
  have hpq : p < q := by
    have htcomp : t ∈ connectedComponentIn A t := mem_connectedComponentIn htA
    rw [hcomp] at htcomp
    exact htcomp.1.trans htcomp.2
  constructor
  · intro hpA
    obtain ⟨l, u, ⟨hlp, hpu⟩, hluA⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hAopen.mem_nhds hpA)
    let r := (p + min u q) / 2
    have hpr : p < r := by dsimp [r]; linarith [lt_min hpu hpq]
    have hru : r < u := by dsimp [r]; linarith [min_le_left u q, lt_min hpu hpq]
    have hrq : r < q := by dsimp [r]; linarith [min_le_right u q, lt_min hpu hpq]
    have hI : Set.Icc p r ⊆ A := by
      intro z hz
      exact hluA ⟨hlp.trans_le hz.1, hz.2.trans_lt hru⟩
    have hrcomp : r ∈ connectedComponentIn A t := hcomp.symm ▸ ⟨hpr, hrq⟩
    have heq : connectedComponentIn A r = connectedComponentIn A t :=
      (connectedComponentIn_eq hrcomp).symm
    have hsub : Set.Icc p r ⊆ connectedComponentIn A r :=
      isPreconnected_Icc.subset_connectedComponentIn (Set.right_mem_Icc.mpr hpr.le) hI
    have hpcomp : p ∈ connectedComponentIn A t := heq ▸ hsub (Set.left_mem_Icc.mpr hpr.le)
    exact (hcomp ▸ hpcomp).1.false
  · intro hqA
    obtain ⟨l, u, ⟨hlq, hqu⟩, hluA⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hAopen.mem_nhds hqA)
    let r := (max l p + q) / 2
    have hpr : p < r := by dsimp [r]; linarith [le_max_right l p, max_lt hlq hpq]
    have hrq : r < q := by dsimp [r]; linarith [max_lt hlq hpq]
    have hlr : l < r := by dsimp [r]; linarith [le_max_left l p, max_lt hlq hpq]
    have hI : Set.Icc r q ⊆ A := by
      intro z hz
      exact hluA ⟨hlr.trans_le hz.1, hz.2.trans_lt hqu⟩
    have hrcomp : r ∈ connectedComponentIn A t := hcomp.symm ▸ ⟨hpr, hrq⟩
    have heq : connectedComponentIn A r = connectedComponentIn A t :=
      (connectedComponentIn_eq hrcomp).symm
    have hsub : Set.Icc r q ⊆ connectedComponentIn A r :=
      isPreconnected_Icc.subset_connectedComponentIn (Set.left_mem_Icc.mpr hrq.le) hI
    have hqcomp : q ∈ connectedComponentIn A t := heq ▸ hsub (Set.right_mem_Icc.mpr hrq.le)
    exact (hcomp ▸ hqcomp).2.false

/-- E1: one-sided limits of a strictly monotone function on a bounded open
interval.  For an increasing function the right limit is the supremum and
the left limit is the infimum of the image; for a decreasing function these
are exchanged.  Thus any finite bound on the appropriate side supplies the
finite endpoint limit used by the Hausdorff chart argument. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_monotone_end_limits
    (p q : ℝ) (hpq : p < q) (f : ℝ → ℝ) :
    (StrictMonoOn f (Set.Ioo p q) →
      (BddAbove (f '' Set.Ioo p q) →
        Filter.Tendsto f (nhdsWithin q (Set.Iio q))
          (nhds (sSup (f '' Set.Ioo p q)))) ∧
      (BddBelow (f '' Set.Ioo p q) →
        Filter.Tendsto f (nhdsWithin p (Set.Ioi p))
          (nhds (sInf (f '' Set.Ioo p q))))) ∧
    (StrictAntiOn f (Set.Ioo p q) →
      (BddBelow (f '' Set.Ioo p q) →
        Filter.Tendsto f (nhdsWithin q (Set.Iio q))
          (nhds (sInf (f '' Set.Ioo p q)))) ∧
      (BddAbove (f '' Set.Ioo p q) →
        Filter.Tendsto f (nhdsWithin p (Set.Ioi p))
          (nhds (sSup (f '' Set.Ioo p q))))) := by
  have hne : (Set.Ioo p q).Nonempty := Set.nonempty_Ioo.mpr hpq
  constructor
  · intro hf
    exact ⟨fun hb => hf.monotoneOn.tendsto_nhdsWithin_Ioo_left hne hb,
      fun hb => hf.monotoneOn.tendsto_nhdsWithin_Ioo_right hne hb⟩
  · intro hf
    exact ⟨fun hb => hf.antitoneOn.tendsto_nhdsWithin_Ioo_left hne hb,
      fun hb => hf.antitoneOn.tendsto_nhdsWithin_Ioo_right hne hb⟩

/-- **R1, forward ray endpoint.** A strictly increasing surjection from a
right ray onto a left ray approaches the finite endpoint of the left ray. -/
lemma apm_t95j06_ray_strictMono_surjective_tendsto_leftEndpoint
    (α δ : ℝ) (f : Set.Ioi α → Set.Iio δ)
    (hf : StrictMono f) (hsurj : Function.Surjective f) :
    Filter.Tendsto (fun x => (f x : ℝ)) Filter.atTop (nhdsWithin δ (Set.Iio δ)) := by
  let e₀ : Set.Ioi α ≃ Set.Iio δ :=
    Equiv.ofBijective f ⟨hf.injective, hsurj⟩
  let e : Set.Ioi α ≃o Set.Iio δ :=
    { e₀ with
      map_rel_iff' := fun {x y} => hf.le_iff_le }
  have he : (e : Set.Ioi α → Set.Iio δ) = f := by
    funext x
    rfl
  have ht : Filter.Tendsto f Filter.atTop Filter.atTop := by
    rw [← he]
    exact e.tendsto_atTop
  exact (tendsto_Iio_atTop (a := δ)).mp ht

/-- **R1, inverse ray endpoint.** A strictly increasing surjection from a
left ray onto a right ray diverges to `+∞` at the finite endpoint. -/
lemma apm_t95j06_ray_strictMono_surjective_tendsto_atTop
    (α δ : ℝ) (g : Set.Iio δ → Set.Ioi α)
    (hg : StrictMono g) (hsurj : Function.Surjective g) :
    Filter.Tendsto (fun x => (g x : ℝ)) Filter.atTop Filter.atTop := by
  let e₀ : Set.Iio δ ≃ Set.Ioi α :=
    Equiv.ofBijective g ⟨hg.injective, hsurj⟩
  let e : Set.Iio δ ≃o Set.Ioi α :=
    { e₀ with
      map_rel_iff' := fun {x y} => hg.le_iff_le }
  have he : (e : Set.Iio δ → Set.Ioi α) = g := by
    funext x
    rfl
  have ht : Filter.Tendsto g Filter.atTop Filter.atTop := by
    rw [← he]
    exact e.tendsto_atTop
  apply Filter.tendsto_atTop_atTop.mpr
  intro M
  let M' : Set.Ioi α := ⟨max M (α + 1), lt_of_lt_of_le (lt_add_one α) (le_max_right _ _)⟩
  obtain ⟨a, ha⟩ := Filter.tendsto_atTop_atTop.mp ht M'
  exact ⟨a, fun b hab => (le_max_left M (α + 1)).trans (ha b hab)⟩

/-- **R2, the overlap transition as an order isomorphism.**  If the overlap
is a right ray in the first chart and a left ray in the second, and the chart
transition is increasing, the transition is a strictly increasing continuous
surjection between those rays.  Its forward and inverse endpoint behaviour is
recorded explicitly for the seam construction. -/
lemma apm_t95j06_two_overlapping_realCharts_ray_transition
    (X : Type) [TopologicalSpace X]
    (U V : Set X) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (α δ : ℝ)
    (hA : φ '' (Subtype.val ⁻¹' V) = Set.Ioi α)
    (hB : ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ)
    (hmono : ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
      φ x < φ y → ψ ⟨x, hx⟩ < ψ ⟨y, hy⟩) :
    ∃ (τ : Set.Ioi α → Set.Iio δ) (g : Set.Iio δ → Set.Ioi α),
      StrictMono τ ∧ Function.Surjective τ ∧ Continuous τ ∧
      Function.LeftInverse g τ ∧ Function.RightInverse g τ ∧
      Filter.Tendsto (fun s => (τ s : ℝ)) Filter.atTop (nhdsWithin δ (Set.Iio δ)) ∧
      Filter.Tendsto (fun t => (g t : ℝ)) Filter.atTop Filter.atTop := by
  have hov (s : Set.Ioi α) : ((φ.symm s.1 : U) : X) ∈ V := by
    have hsimg : s.1 ∈ φ '' (Subtype.val ⁻¹' V) := hA.symm ▸ s.2
    obtain ⟨u, huV, hu⟩ := hsimg
    have hueq : u = φ.symm s.1 := by
      apply φ.injective
      rw [hu, φ.apply_symm_apply]
    simpa [hueq] using huV
  let τ₀ (s : Set.Ioi α) : ℝ := ψ ⟨φ.symm s.1, hov s⟩
  have hτmem (s : Set.Ioi α) : τ₀ s ∈ Set.Iio δ := by
    have himg : τ₀ s ∈ ψ '' (Subtype.val ⁻¹' U) := by
      refine ⟨⟨φ.symm s.1, hov s⟩, ?_, rfl⟩
      exact (φ.symm s.1).property
    exact hB ▸ himg
  let τ : Set.Ioi α → Set.Iio δ := fun s => ⟨τ₀ s, hτmem s⟩
  have hτmono : StrictMono τ := by
    intro s t hst
    apply hmono (φ.symm s.1) (φ.symm t.1) (hov s) (hov t)
    simpa only [φ.apply_symm_apply] using hst
  have hτsurj : Function.Surjective τ := by
    intro t
    have htimg : t.1 ∈ ψ '' (Subtype.val ⁻¹' U) := hB.symm ▸ t.2
    obtain ⟨v, hvU, hv⟩ := htimg
    let u : U := ⟨v.1, hvU⟩
    have huV : (u : X) ∈ V := v.property
    have hsimg : φ u ∈ φ '' (Subtype.val ⁻¹' V) := ⟨u, huV, rfl⟩
    have hs' : φ u ∈ Set.Ioi α := hA ▸ hsimg
    have hs : α < φ u := hs'
    let s : Set.Ioi α := ⟨φ u, hs⟩
    refine ⟨s, Subtype.ext ?_⟩
    change ψ ⟨φ.symm (φ u), hov s⟩ = t.1
    have huv : (⟨φ.symm (φ u), hov s⟩ : V) = v := by
      apply Subtype.ext
      simpa [u] using congrArg Subtype.val (φ.symm_apply_apply u)
    rw [huv, hv]
  let e₀ : Set.Ioi α ≃ Set.Iio δ :=
    Equiv.ofBijective τ ⟨hτmono.injective, hτsurj⟩
  let e : Set.Ioi α ≃o Set.Iio δ :=
    { e₀ with map_rel_iff' := fun {x y} => hτmono.le_iff_le }
  have he : (e : Set.Ioi α → Set.Iio δ) = τ := by funext s; rfl
  have hτcont : Continuous τ := by
    rw [← he]
    exact e.toHomeomorph.continuous
  have hfwd := apm_t95j06_ray_strictMono_surjective_tendsto_leftEndpoint
    α δ τ hτmono hτsurj
  have hinvMono : StrictMono e.symm := e.symm.strictMono
  have hinvSurj : Function.Surjective e.symm := e.symm.surjective
  have hinv := apm_t95j06_ray_strictMono_surjective_tendsto_atTop
    α δ e.symm hinvMono hinvSurj
  refine ⟨τ, e.symm, hτmono, hτsurj, hτcont, ?_, ?_, hfwd, hinv⟩
  · intro s
    exact e.symm_apply_apply s
  · intro t
    exact e.apply_symm_apply t

/-- The ray transition together with the equation identifying it with the
actual change of chart.  The earlier transition lemma deliberately exposed
only its order-theoretic properties; the gluing coordinate also needs this
pointwise compatibility. -/
lemma apm_t95j06_two_overlapping_realCharts_ray_transition_linked
    (X : Type) [TopologicalSpace X]
    (U V : Set X) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (α δ : ℝ)
    (hA : φ '' (Subtype.val ⁻¹' V) = Set.Ioi α)
    (hB : ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ)
    (hmono : ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
      φ x < φ y → ψ ⟨x, hx⟩ < ψ ⟨y, hy⟩) :
    ∃ τ : Set.Ioi α → Set.Iio δ,
      StrictMono τ ∧ Function.Surjective τ ∧ Continuous τ ∧
      (∀ (u : U) (hu : (u : X) ∈ V),
        τ ⟨φ u, by
          have himg : φ u ∈ φ '' (Subtype.val ⁻¹' V) := ⟨u, hu, rfl⟩
          exact hA ▸ himg⟩ = ⟨ψ ⟨u, hu⟩, by
            have himg : ψ ⟨u, hu⟩ ∈ ψ '' (Subtype.val ⁻¹' U) :=
              ⟨⟨u, hu⟩, u.property, rfl⟩
            exact hB ▸ himg⟩) := by
  have hov (s : Set.Ioi α) : ((φ.symm s.1 : U) : X) ∈ V := by
    have hsimg : s.1 ∈ φ '' (Subtype.val ⁻¹' V) := hA.symm ▸ s.2
    obtain ⟨u, huV, hu⟩ := hsimg
    have hueq : u = φ.symm s.1 := by
      apply φ.injective
      rw [hu, φ.apply_symm_apply]
    simpa [hueq] using huV
  let τ₀ (s : Set.Ioi α) : ℝ := ψ ⟨φ.symm s.1, hov s⟩
  have hτmem (s : Set.Ioi α) : τ₀ s ∈ Set.Iio δ := by
    have himg : τ₀ s ∈ ψ '' (Subtype.val ⁻¹' U) := by
      refine ⟨⟨φ.symm s.1, hov s⟩, (φ.symm s.1).property, rfl⟩
    exact hB ▸ himg
  let τ : Set.Ioi α → Set.Iio δ := fun s => ⟨τ₀ s, hτmem s⟩
  have hτmono : StrictMono τ := by
    intro s t hst
    apply hmono (φ.symm s.1) (φ.symm t.1) (hov s) (hov t)
    simpa only [φ.apply_symm_apply] using hst
  have hτsurj : Function.Surjective τ := by
    intro t
    have htimg : t.1 ∈ ψ '' (Subtype.val ⁻¹' U) := hB.symm ▸ t.2
    obtain ⟨v, hvU, hv⟩ := htimg
    let u : U := ⟨v.1, hvU⟩
    have hsimg : φ u ∈ φ '' (Subtype.val ⁻¹' V) := ⟨u, v.property, rfl⟩
    let s : Set.Ioi α := ⟨φ u, hA ▸ hsimg⟩
    refine ⟨s, Subtype.ext ?_⟩
    change ψ ⟨φ.symm (φ u), hov s⟩ = t.1
    have huv : (⟨φ.symm (φ u), hov s⟩ : V) = v := by
      apply Subtype.ext
      simpa [u] using congrArg Subtype.val (φ.symm_apply_apply u)
    rw [huv, hv]
  let e₀ : Set.Ioi α ≃ Set.Iio δ :=
    Equiv.ofBijective τ ⟨hτmono.injective, hτsurj⟩
  let e : Set.Ioi α ≃o Set.Iio δ :=
    { e₀ with map_rel_iff' := fun {x y} => hτmono.le_iff_le }
  have he : (e : Set.Ioi α → Set.Iio δ) = τ := by funext s; rfl
  have hτcont : Continuous τ := by
    rw [← he]
    exact e.toHomeomorph.continuous
  refine ⟨τ, hτmono, hτsurj, hτcont, ?_⟩
  intro u hu
  apply Subtype.ext
  change τ₀ _ = ψ ⟨u, hu⟩
  dsimp only [τ₀]
  apply congrArg ψ
  apply Subtype.ext
  simp

/-- **R3a, overlap membership in the second chart.**  Under the left-ray
description of the overlap in `ψ`-coordinates, a point of `V` lies in `U`
exactly when its coordinate is below the seam value `δ`. -/
lemma apm_t95j06_two_overlapping_realCharts_mem_iff_psi_lt
    (X : Type) [TopologicalSpace X] (U V : Set X)
    (ψ : V ≃ₜ ℝ) (δ : ℝ)
    (hB : ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ) (v : V) :
    (v.1 ∈ U ↔ ψ v < δ) := by
  constructor
  · intro hvU
    have himg : ψ v ∈ ψ '' (Subtype.val ⁻¹' U) := ⟨v, hvU, rfl⟩
    have hmem : ψ v ∈ Set.Iio δ := hB ▸ himg
    exact hmem
  · intro hv
    have himg : ψ v ∈ ψ '' (Subtype.val ⁻¹' U) := hB.symm ▸ hv
    obtain ⟨w, hwU, hw⟩ := himg
    have hwv : w = v := ψ.injective hw
    simpa [hwv] using hwU

/-- **R3b, the seam coordinate and its two formulas.**  This packages the
dependent branch on membership in `U`; the preceding lemma identifies that
branch with the numerical test `ψ v < δ`. -/
lemma apm_t95j06_two_overlapping_realCharts_seamCoordinate_formulas
    (X : Type) [TopologicalSpace X] (U V : Set X)
    (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (δ : ℝ)
    (hB : ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ) :
    let G : V → ℝ := fun v =>
      if h : ψ v < δ then Real.arctan (φ ⟨v.1,
        (apm_t95j06_two_overlapping_realCharts_mem_iff_psi_lt
          X U V ψ δ hB v).mpr h⟩)
      else Real.pi / 2 + (ψ v - δ)
    (∀ (v : V) (hv : v.1 ∈ U),
      G v = Real.arctan (φ ⟨v.1, hv⟩)) ∧
    (∀ (v : V), v.1 ∉ U → G v = Real.pi / 2 + (ψ v - δ)) := by
  classical
  dsimp only
  constructor
  · intro v hv
    have hlt := (apm_t95j06_two_overlapping_realCharts_mem_iff_psi_lt
      X U V ψ δ hB v).mp hv
    rw [dif_pos hlt]
  · intro v hv
    have hnlt : ¬ ψ v < δ := fun hlt => hv
      ((apm_t95j06_two_overlapping_realCharts_mem_iff_psi_lt
        X U V ψ δ hB v).mpr hlt)
    rw [dif_neg hnlt]

/-- **Ray gluing from a linked transition.**  Two real charts whose overlap
is a right ray `Ioi α` in the first chart, with an increasing surjective
transition `τ` onto the left ray `Iio δ` of the second, glue to a real line:
the first chart is corrected to `s - α` below `α` and `exp (τ s)` above it,
the second chart is composed with `exp`, and the two agree on the overlap. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_of_transition
    (X : Type) [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (α δ : ℝ)
    (hA : φ '' (Subtype.val ⁻¹' V) = Set.Ioi α)
    (τ : Set.Ioi α → Set.Iio δ) (hτmono : StrictMono τ) (hτsurj : Function.Surjective τ)
    (hlink : ∀ (u : U) (hu : (u : X) ∈ V) (h : α < φ u), (τ ⟨φ u, h⟩ : ℝ) = ψ ⟨u, hu⟩) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ ℝ) := by
  classical
  -- the corrected U-coordinate
  let h : ℝ → ℝ := fun s => if hs : α < s then Real.exp (τ ⟨s, hs⟩) else s - α
  have hmono : StrictMono h := by
    intro s t hst
    by_cases ht : α < t
    · by_cases hs : α < s
      · simp only [h, dif_pos hs, dif_pos ht]
        exact Real.exp_lt_exp.mpr (hτmono (show (⟨s, hs⟩ : Set.Ioi α) < ⟨t, ht⟩ from hst))
      · simp only [h, dif_neg hs, dif_pos ht]
        have := Real.exp_pos ((τ ⟨t, ht⟩ : ℝ))
        linarith [not_lt.mp hs]
    · have hs : ¬ α < s := fun hs => ht (hs.trans hst)
      simp only [h, dif_neg hs, dif_neg ht]
      linarith
  have hlt : ∀ s, h s < Real.exp δ := by
    intro s
    by_cases hs : α < s
    · simp only [h, dif_pos hs]
      exact Real.exp_lt_exp.mpr (τ ⟨s, hs⟩).2
    · simp only [h, dif_neg hs]
      linarith [not_lt.mp hs, Real.exp_pos δ]
  have hsurj : ∀ y, y < Real.exp δ → ∃ s, h s = y := by
    intro y hy
    by_cases hy0 : y ≤ 0
    · refine ⟨y + α, ?_⟩
      have : ¬ α < y + α := by linarith
      simp only [h, dif_neg this]
      ring
    · push_neg at hy0
      have hl : Real.log y < δ := by
        rw [Real.log_lt_iff_lt_exp hy0]; exact hy
      obtain ⟨s, hs⟩ := hτsurj ⟨Real.log y, hl⟩
      refine ⟨s, ?_⟩
      have hs2 : α < (s : ℝ) := s.2
      simp only [h, dif_pos hs2]
      show Real.exp ((τ s : ℝ)) = y
      rw [hs]
      exact Real.exp_log hy0
  let h' : ℝ → Set.Iio (Real.exp δ) := fun s => ⟨h s, hlt s⟩
  have h'mono : StrictMono h' := fun s t hst => hmono hst
  have h'surj : Function.Surjective h' := by
    rintro ⟨y, hy⟩
    obtain ⟨s, hs⟩ := hsurj y hy
    exact ⟨s, Subtype.ext hs⟩
  let hiso : ℝ ≃o Set.Iio (Real.exp δ) := StrictMono.orderIsoOfSurjective h' h'mono h'surj
  have hemb : Topology.IsOpenEmbedding h := by
    have h1 : Topology.IsOpenEmbedding (Subtype.val : Set.Iio (Real.exp δ) → ℝ) :=
      isOpen_Iio.isOpenEmbedding_subtypeVal
    have h2 : Topology.IsOpenEmbedding (hiso : ℝ → Set.Iio (Real.exp δ)) :=
      hiso.toHomeomorph.isOpenEmbedding
    have : h = Subtype.val ∘ (hiso : ℝ → Set.Iio (Real.exp δ)) := rfl
    rw [this]; exact h1.comp h2
  -- the glued map
  let W := {x : X // x ∈ U ∪ V}
  let iU : U → W := fun u => ⟨u.1, Or.inl u.2⟩
  let iV : V → W := fun v => ⟨v.1, Or.inr v.2⟩
  have hWo : IsOpen (U ∪ V) := hU.union hV
  have hiU : Topology.IsOpenEmbedding iU := by
    have hc : Topology.IsOpenEmbedding ((Subtype.val : W → X) ∘ iU) := hU.isOpenEmbedding_subtypeVal
    exact (hWo.isOpenEmbedding_subtypeVal.of_comp_iff _).mp hc
  have hiV : Topology.IsOpenEmbedding iV := by
    have hc : Topology.IsOpenEmbedding ((Subtype.val : W → X) ∘ iV) := hV.isOpenEmbedding_subtypeVal
    exact (hWo.isOpenEmbedding_subtypeVal.of_comp_iff _).mp hc
  let F : W → ℝ := fun x => if hx : x.1 ∈ U then h (φ ⟨x.1, hx⟩) else Real.exp (ψ ⟨x.1,
    x.2.resolve_left hx⟩)
  have hFU : ∀ u : U, F (iU u) = h (φ u) := by
    intro u
    simp only [F, iU, dif_pos u.2]
  have hαV : ∀ (u : U), (u : X) ∈ V → α < φ u := by
    intro u hu
    have : φ u ∈ φ '' (Subtype.val ⁻¹' V) := ⟨u, hu, rfl⟩
    rw [hA] at this; exact this
  have hVα : ∀ (u : U), α < φ u → (u : X) ∈ V := by
    intro u hu
    have : φ u ∈ φ '' (Subtype.val ⁻¹' V) := by rw [hA]; exact hu
    obtain ⟨u', hu', he⟩ := this
    rw [φ.injective he] at hu'; exact hu'
  have hFV : ∀ v : V, F (iV v) = Real.exp (ψ v) := by
    intro v
    by_cases hv : (v : X) ∈ U
    · simp only [F, iV, dif_pos hv]
      have hα := hαV ⟨v, hv⟩ v.2
      simp only [h, dif_pos hα]
      rw [hlink ⟨v, hv⟩ v.2 hα]
    · simp only [F, iV, dif_neg hv]
  have hFUeq : F ∘ iU = h ∘ φ := funext hFU
  have hFVeq : F ∘ iV = Real.exp ∘ ψ := funext hFV
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases x.2 with hx | hx
    · have : ContinuousAt (F ∘ iU) ⟨x.1, hx⟩ := by
        rw [hFUeq]; exact (hemb.continuous.comp φ.continuous).continuousAt
      exact (hiU.continuousAt_iff).mp this
    · have : ContinuousAt (F ∘ iV) ⟨x.1, hx⟩ := by
        rw [hFVeq]; exact (Real.continuous_exp.comp ψ.continuous).continuousAt
      exact (hiV.continuousAt_iff).mp this
  have hopen : IsOpenMap F := by
    intro s hs
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hxs, rfl⟩
    rcases x.2 with hx | hx
    · let T : Set U := iU ⁻¹' s
      have hT : IsOpen T := hs.preimage hiU.continuous
      have hO : IsOpen ((h ∘ φ) '' T) := (hemb.isOpenMap.comp φ.isOpenMap) T hT
      have hsub : (h ∘ φ) '' T ⊆ F '' s := by
        rintro _ ⟨u, hu, rfl⟩; exact ⟨iU u, hu, hFU u⟩
      refine Filter.mem_of_superset (hO.mem_nhds ⟨⟨x.1, hx⟩, hxs, ?_⟩) hsub
      exact (hFU ⟨x.1, hx⟩).symm
    · let T : Set V := iV ⁻¹' s
      have hT : IsOpen T := hs.preimage hiV.continuous
      have hO : IsOpen ((Real.exp ∘ ψ) '' T) :=
        (Real.isOpenEmbedding_exp.isOpenMap.comp ψ.isOpenMap) T hT
      have hsub : (Real.exp ∘ ψ) '' T ⊆ F '' s := by
        rintro _ ⟨v, hv, rfl⟩; exact ⟨iV v, hv, hFV v⟩
      refine Filter.mem_of_superset (hO.mem_nhds ⟨⟨x.1, hx⟩, hxs, ?_⟩) hsub
      exact (hFV ⟨x.1, hx⟩).symm
  have hhpos : ∀ s, s ≤ α → h s ≤ 0 := by
    intro s hs
    simp only [h, dif_neg (not_lt.mpr hs)]; linarith
  have hinj : Function.Injective F := by
    intro x y hxy
    have caseU : ∀ (x y : W) (hx : x.1 ∈ U) (hy : y.1 ∈ U), F x = F y → x = y := by
      intro x y hx hy he
      have := hFU ⟨x.1, hx⟩; have := hFU ⟨y.1, hy⟩
      have he' : h (φ ⟨x.1, hx⟩) = h (φ ⟨y.1, hy⟩) := by
        rw [← hFU, ← hFU]; exact he
      have := congrArg Subtype.val (φ.injective (hmono.injective he'))
      exact Subtype.ext this
    have caseV : ∀ (x y : W) (hx : x.1 ∈ V) (hy : y.1 ∈ V), F x = F y → x = y := by
      intro x y hx hy he
      have he' : Real.exp (ψ ⟨x.1, hx⟩) = Real.exp (ψ ⟨y.1, hy⟩) := by
        rw [← hFV, ← hFV]; exact he
      have := congrArg Subtype.val (ψ.injective (Real.exp_injective he'))
      exact Subtype.ext this
    have caseMix : ∀ (x y : W) (hx : x.1 ∈ U) (hxV : x.1 ∉ V) (hy : y.1 ∈ V), F x ≠ F y := by
      intro x y hx hxV hy he
      have h1 : F x ≤ 0 := by
        have := hFU ⟨x.1, hx⟩
        change F x = _ at this
        rw [this]
        exact hhpos _ (not_lt.mp fun hα => hxV (hVα ⟨x.1, hx⟩ hα))
      have h2 : 0 < F y := by
        have := hFV ⟨y.1, hy⟩
        change F y = _ at this
        rw [this]; exact Real.exp_pos _
      linarith
    by_cases hxU : x.1 ∈ U <;> by_cases hyU : y.1 ∈ U
    · exact caseU x y hxU hyU hxy
    · have hyV := y.2.resolve_left hyU
      by_cases hxV : x.1 ∈ V
      · exact caseV x y hxV hyV hxy
      · exact absurd hxy (caseMix x y hxU hxV hyV)
    · have hxV := x.2.resolve_left hxU
      by_cases hyV : y.1 ∈ V
      · exact caseV x y hxV hyV hxy
      · exact absurd hxy.symm (caseMix y x hyU hyV hxV)
    · exact caseV x y (x.2.resolve_left hxU) (y.2.resolve_left hyU) hxy
  have hsurjF : Function.Surjective F := by
    intro y
    by_cases hy : y < Real.exp δ
    · obtain ⟨s, hs⟩ := hsurj y hy
      exact ⟨iU (φ.symm s), by rw [hFU, φ.apply_symm_apply, hs]⟩
    · have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos δ) (not_lt.mp hy)
      exact ⟨iV (ψ.symm (Real.log y)), by rw [hFV, ψ.apply_symm_apply, Real.exp_log hy0]⟩
  exact ⟨(Equiv.ofBijective F ⟨hinj, hsurjF⟩).toHomeomorphOfContinuousOpen hcont hopen⟩

/-- **Ray gluing.**  Two open real charts whose overlap is a right ray in the
first chart and a left ray in the second, with increasing transition, glue to
a homeomorphism of their union with `ℝ`. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue
    (X : Type) [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (α δ : ℝ)
    (hA : φ '' (Subtype.val ⁻¹' V) = Set.Ioi α)
    (hB : ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ)
    (hmono : ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
      φ x < φ y → ψ ⟨x, hx⟩ < ψ ⟨y, hy⟩) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ ℝ) := by
  obtain ⟨τ, hτmono, hτsurj, -, hlink⟩ :=
    apm_t95j06_two_overlapping_realCharts_ray_transition_linked X U V φ ψ α δ hA hB hmono
  exact apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_of_transition
    X U V hU hV φ ψ α δ hA τ hτmono hτsurj
    (fun u hu _ => congrArg Subtype.val (hlink u hu))

/-- **E2, bounded overlap components.**  If a component of the overlap, in
the first chart, is a bounded interval `Ioo p q`, then the second chart's
coordinates of the overlap cover all of `ℝ`: the transition is strictly
monotone on `Ioo p q`, and a bounded end of its image would give a finite
limit of the second chart at an endpoint `p` or `q` that is not in the
overlap, which `_aux_no_finite_end_limit` forbids. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_bounded_component
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (hV : IsOpen V) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ)
    (t p q : ℝ) (htA : t ∈ φ '' (Subtype.val ⁻¹' V))
    (hcomp : connectedComponentIn (φ '' (Subtype.val ⁻¹' V)) t = Set.Ioo p q) :
    ψ '' (Subtype.val ⁻¹' U) = Set.univ := by
  classical
  set A := φ '' (Subtype.val ⁻¹' V) with hAdef
  have hO : ∀ s ∈ A, ((φ.symm s : U) : X) ∈ V := by
    rintro _ ⟨u, hu, rfl⟩; simpa using hu
  have hAopen : IsOpen A := by
    have : A = (fun s => ((φ.symm s : U) : X)) ⁻¹' V := by
      ext s; constructor
      · intro hs; exact hO s hs
      · intro hs; exact ⟨φ.symm s, hs, by simp⟩
    rw [this]; exact hV.preimage (continuous_subtype_val.comp φ.symm.continuous)
  have hpq : p < q := by
    have h := mem_connectedComponentIn htA
    rw [hcomp] at h; exact h.1.trans h.2
  have hIA : Set.Ioo p q ⊆ A := hcomp ▸ connectedComponentIn_subset A t
  have hends := apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_component_endpoints
    A hAopen t p q htA hcomp
  let τ : ℝ → ℝ := fun s => if h : ((φ.symm s : U) : X) ∈ V then ψ ⟨_, h⟩ else 0
  have hτA : ∀ s (h : ((φ.symm s : U) : X) ∈ V), τ s = ψ ⟨_, h⟩ := by
    intro s h; simp only [τ, dif_pos h]
  have hcontA : ContinuousOn τ A := by
    rw [continuousOn_iff_continuous_restrict]
    have : A.restrict τ = fun s : A => ψ ⟨((φ.symm s.1 : U) : X), hO s.1 s.2⟩ := by
      funext s; exact hτA _ _
    rw [this]
    exact ψ.continuous.comp ((continuous_subtype_val.comp
      (φ.symm.continuous.comp continuous_subtype_val)).subtype_mk _)
  have hcont : ContinuousOn τ (Set.Ioo p q) := hcontA.mono hIA
  have hinj : Set.InjOn τ (Set.Ioo p q) := by
    intro s hs s' hs' he
    rw [hτA s (hO s (hIA hs)), hτA s' (hO s' (hIA hs'))] at he
    have h1 := congrArg Subtype.val (ψ.injective he)
    have h2 : φ.symm s = φ.symm s' := Subtype.ext h1
    simpa using congrArg φ h2
  -- no finite limit at an endpoint not in A
  have hnolim : ∀ (l : Filter ℝ) [Filter.NeBot l] (β : ℝ), β ∉ A → l ≤ nhds β →
      (Set.Ioo p q ∈ l) → ∀ c, ¬ Filter.Tendsto τ l (nhds c) := by
    intro l _ β hβ hlβ hIl c hc
    refine apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_no_finite_end_limit
      X U V φ ψ (l := l) (fun s => φ.symm s) (fun s => ψ.symm (τ s)) ?_ β hβ ?_ c ?_
    · filter_upwards [hIl] with s hs
      rw [hτA s (hO s (hIA hs))]; simp
    · simpa using (Filter.tendsto_id.mono_left hlβ)
    · simpa using hc
  have hmono := hcont.strictMonoOn_of_injOn_Ioo hpq hinj
  have E := apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_monotone_end_limits
    p q hpq τ
  have hnotAbove : ¬ BddAbove (τ '' Set.Ioo p q) := by
    intro hb
    rcases hmono with hm | hm
    · exact hnolim (nhdsWithin q (Set.Iio q)) q hends.2 nhdsWithin_le_nhds (Ioo_mem_nhdsLT hpq) _ ((E.1 hm).1 hb)
    · exact hnolim (nhdsWithin p (Set.Ioi p)) p hends.1 nhdsWithin_le_nhds (Ioo_mem_nhdsGT hpq) _ ((E.2 hm).2 hb)
  have hnotBelow : ¬ BddBelow (τ '' Set.Ioo p q) := by
    intro hb
    rcases hmono with hm | hm
    · exact hnolim (nhdsWithin p (Set.Ioi p)) p hends.1 nhdsWithin_le_nhds (Ioo_mem_nhdsGT hpq) _ ((E.1 hm).2 hb)
    · exact hnolim (nhdsWithin q (Set.Iio q)) q hends.2 nhdsWithin_le_nhds (Ioo_mem_nhdsLT hpq) _ ((E.2 hm).1 hb)
  have hpre : _root_.IsPreconnected (τ '' Set.Ioo p q) := isPreconnected_Ioo.image τ hcont
  have huniv : τ '' Set.Ioo p q = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨_, ⟨a, ha, rfl⟩, hay⟩ := not_bddBelow_iff.mp hnotBelow y
    obtain ⟨_, ⟨b, hb, rfl⟩, hyb⟩ := not_bddAbove_iff.mp hnotAbove y
    exact hpre.Icc_subset ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨hay.le, hyb.le⟩
  apply Set.eq_univ_of_forall
  intro y
  have hy : y ∈ τ '' Set.Ioo p q := huniv ▸ Set.mem_univ y
  obtain ⟨s, hs, rfl⟩ := hy
  refine ⟨⟨_, hO s (hIA hs)⟩, (φ.symm s).2, (hτA s _).symm⟩

/-- **E3, overlap components are rays.**  Each component of the overlap in
the first chart is a right or left ray, unless the overlap is everything in
the first chart or in the second.  A component is open, connected and
nonempty, so it is `ℝ`, a bounded interval or a ray; the bounded case is E2. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_component_ray
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (hV : IsOpen V) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ)
    (t : ℝ) (htA : t ∈ φ '' (Subtype.val ⁻¹' V)) :
    (∃ a, connectedComponentIn (φ '' (Subtype.val ⁻¹' V)) t = Set.Ioi a) ∨
    (∃ b, connectedComponentIn (φ '' (Subtype.val ⁻¹' V)) t = Set.Iio b) ∨
    φ '' (Subtype.val ⁻¹' V) = Set.univ ∨ ψ '' (Subtype.val ⁻¹' U) = Set.univ := by
  set A := φ '' (Subtype.val ⁻¹' V) with hAdef
  have hAopen : IsOpen A := by
    have : A = (fun s => ((φ.symm s : U) : X)) ⁻¹' V := by
      ext s; constructor
      · rintro ⟨u, hu, rfl⟩; simpa using hu
      · intro hs; exact ⟨φ.symm s, hs, by simp⟩
    rw [this]; exact hV.preimage (continuous_subtype_val.comp φ.symm.continuous)
  set C := connectedComponentIn A t with hC
  by_cases hCu : C = Set.univ
  · right; right; left
    exact Set.eq_univ_of_univ_subset (hCu ▸ connectedComponentIn_subset A t)
  rcases apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_open_interval_shape C
      (hAopen.connectedComponentIn) ⟨t, mem_connectedComponentIn htA⟩ hCu
      _root_.isPreconnected_connectedComponentIn with ⟨p, q, h⟩ | h | h
  · right; right; right
    exact apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_bounded_component
      X U V hV φ ψ t p q htA h
  · left; exact h
  · right; left; exact h

/-- Either side of two disjoint nonempty real intervals is bounded on one
side.  This is the order-theoretic boundedness input for the two-ray compact
case: a point of the other transition image is a separating bound. -/
lemma apm_t95j06_disjoint_preconnected_real_sets_oneSided_bounded
    (S T : Set ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (hSconn : _root_.IsPreconnected S) (hdisj : Disjoint S T) :
    BddAbove S ∨ BddBelow S := by
  obtain ⟨t, htT⟩ := hT
  have htS : t ∉ S := by
    intro htS
    exact Set.disjoint_left.1 hdisj htS htT
  by_cases hleft : ∀ s ∈ S, s < t
  · left
    exact ⟨t, fun s hs => (hleft s hs).le⟩
  · right
    push_neg at hleft
    obtain ⟨s₀, hs₀S, hs₀⟩ := hleft
    refine ⟨t, ?_⟩
    intro s hsS
    by_contra hts
    have hst : s < t := lt_of_not_ge hts
    have hts₀ : t ≤ s₀ := by first | exact hs₀ | exact le_of_not_gt hs₀
    exact htS (hSconn.ordConnected.out hsS hs₀S ⟨hst.le, hts₀⟩)

/-- In a two-ray overlap, the transition image of the right ray has a finite
bound on one side.  Its image is an interval, and the disjoint nonempty image
of the left ray supplies the separating bound. -/
lemma apm_t95j06_two_ray_transition_right_image_oneSided_bounded
    (α β : ℝ) (hαβ : α ≤ β) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Iio α ∪ Set.Ioi β))
    (hfi : Set.InjOn f (Set.Iio α ∪ Set.Ioi β)) :
    BddAbove (f '' Set.Ioi β) ∨ BddBelow (f '' Set.Ioi β) := by
  have hright : (f '' Set.Ioi β).Nonempty := by
    refine ⟨f (β + 1), β + 1, Set.mem_Ioi.mpr (by linarith), rfl⟩
  have hleft : (f '' Set.Iio α).Nonempty := by
    refine ⟨f (α - 1), α - 1, Set.mem_Iio.mpr (by linarith), rfl⟩
  have hrightConn : _root_.IsPreconnected (f '' Set.Ioi β) :=
    isPreconnected_Ioi.image f (hf.mono (Set.subset_union_right))
  have hdisj : Disjoint (f '' Set.Ioi β) (f '' Set.Iio α) := by
    apply Set.disjoint_left.2
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxeq : x = y := hfi (Or.inr hx) (Or.inl hy) hxy.symm
    subst y
    exact (not_lt_of_ge hαβ) (lt_trans hx hy)
  exact apm_t95j06_disjoint_preconnected_real_sets_oneSided_bounded
    (f '' Set.Ioi β) (f '' Set.Iio α) hright hleft hrightConn hdisj

/-- Orientation normalization for the four compatible ray-gluing cases.
Opposite rays have increasing transition; equal-direction rays have decreasing
transition. Reflect either chart coordinate as needed, reducing all four cases
to a right ray in the first chart and a left ray in the second, with increasing
transition. This lemma deliberately assumes these compatible cases and does
not assert that the other four combinations are impossible. -/
lemma apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_orientation
    (X : Type) [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (α δ : ℝ)
    (hcases :
      (φ '' (Subtype.val ⁻¹' V) = Set.Ioi α ∧
       ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ ∧
       ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
         φ x < φ y → ψ ⟨x, hx⟩ < ψ ⟨y, hy⟩) ∨
      (φ '' (Subtype.val ⁻¹' V) = Set.Ioi α ∧
       ψ '' (Subtype.val ⁻¹' U) = Set.Ioi δ ∧
       ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
         φ x < φ y → ψ ⟨y, hy⟩ < ψ ⟨x, hx⟩) ∨
      (φ '' (Subtype.val ⁻¹' V) = Set.Iio α ∧
       ψ '' (Subtype.val ⁻¹' U) = Set.Iio δ ∧
       ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
         φ x < φ y → ψ ⟨y, hy⟩ < ψ ⟨x, hx⟩) ∨
      (φ '' (Subtype.val ⁻¹' V) = Set.Iio α ∧
       ψ '' (Subtype.val ⁻¹' U) = Set.Ioi δ ∧
       ∀ x y : U, ∀ hx : (x : X) ∈ V, ∀ hy : (y : X) ∈ V,
         φ x < φ y → ψ ⟨x, hx⟩ < ψ ⟨y, hy⟩)) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ ℝ) := by
  have neg_right : ∀ (T : Type) (f : T → ℝ) (S : Set T) (c : ℝ),
      f '' S = Set.Ioi c → (fun t => -f t) '' S = Set.Iio (-c) := by
    intro T f S c h
    have he : (fun t => -f t) '' S = (fun x : ℝ => -x) '' (f '' S) :=
      (Set.image_image _ _ _).symm
    rw [he, h]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change c < y at hy
      change -y < -c
      exact neg_lt_neg hy
    · intro hx
      refine ⟨-x, ?_, neg_neg x⟩
      change c < -x
      change x < -c at hx
      linarith
  have neg_left : ∀ (T : Type) (f : T → ℝ) (S : Set T) (c : ℝ),
      f '' S = Set.Iio c → (fun t => -f t) '' S = Set.Ioi (-c) := by
    intro T f S c h
    have he : (fun t => -f t) '' S = (fun x : ℝ => -x) '' (f '' S) :=
      (Set.image_image _ _ _).symm
    rw [he, h]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y < c at hy
      change -c < -y
      exact neg_lt_neg hy
    · intro hx
      refine ⟨-x, ?_, neg_neg x⟩
      change -x < c
      change -c < x at hx
      linarith
  rcases hcases with ⟨hA, hB, hm⟩ | ⟨hA, hB, hm⟩ | ⟨hA, hB, hm⟩ | ⟨hA, hB, hm⟩
  · exact apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue
      X U V hU hV φ ψ α δ hA hB hm
  · apply apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue
      X U V hU hV φ (ψ.trans (Homeomorph.neg ℝ)) α (-δ) hA
      (neg_right V ψ _ δ hB)
    intro x y hx hy hxy
    exact neg_lt_neg (hm x y hx hy hxy)
  · apply apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue
      X U V hU hV (φ.trans (Homeomorph.neg ℝ)) ψ (-α) δ
      (neg_left U φ _ α hA) hB
    intro x y hx hy hxy
    exact hm y x hy hx (neg_lt_neg_iff.mp hxy)
  · apply apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue
      X U V hU hV (φ.trans (Homeomorph.neg ℝ)) (ψ.trans (Homeomorph.neg ℝ))
      (-α) (-δ) (neg_left U φ _ α hA) (neg_right V ψ _ δ hB)
    intro x y hx hy hxy
    exact neg_lt_neg (hm y x hy hx (neg_lt_neg_iff.mp hxy))

/-- Two disjoint preconnected real sets, one unbounded below and the other
unbounded above, leave only a bounded complementary gap. -/
lemma apm_t95j06_disjoint_preconnected_compl_bounded
    (S T : Set ℝ) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hSconn : _root_.IsPreconnected S) (hTconn : _root_.IsPreconnected T)
    (hdisj : Disjoint S T) (hSbelow : ¬ BddBelow S)
    (hTabove : ¬ BddAbove T) :
    ∃ c d : ℝ, (S ∪ T)ᶜ ⊆ Set.Icc c d := by
  obtain ⟨s, hsS⟩ := hSne
  obtain ⟨t, htT⟩ := hTne
  refine ⟨s, t, ?_⟩
  intro z hz
  have hzS : z ∉ S := fun h => hz (Or.inl h)
  have hzT : z ∉ T := fun h => hz (Or.inr h)
  have hsz : s < z := by
    by_contra h
    have hzs : z ≤ s := le_of_not_gt h
    obtain ⟨y, hyS, hyz⟩ := not_bddBelow_iff.mp hSbelow z
    have hzmem : z ∈ S :=
      hSconn.Icc_subset hyS hsS ⟨hyz.le, hzs⟩
    exact hzS hzmem
  have hzt : z < t := by
    by_contra h
    have htz : t ≤ z := le_of_not_gt h
    obtain ⟨y, hyT, hzy⟩ := not_bddAbove_iff.mp hTabove z
    have hzmem : z ∈ T :=
      hTconn.Icc_subset htT hyT ⟨htz, hzy.le⟩
    exact hzT hzmem
  exact ⟨hsz.le, hzt.le⟩

/-- Swapped-orientation form of
`apm_t95j06_disjoint_preconnected_compl_bounded`. -/
lemma apm_t95j06_disjoint_preconnected_compl_bounded_swapped
    (S T : Set ℝ) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hSconn : _root_.IsPreconnected S) (hTconn : _root_.IsPreconnected T)
    (hdisj : Disjoint S T) (hSabove : ¬ BddAbove S)
    (hTbelow : ¬ BddBelow T) :
    ∃ c d : ℝ, (S ∪ T)ᶜ ⊆ Set.Icc c d := by
  obtain ⟨c, d, h⟩ := apm_t95j06_disjoint_preconnected_compl_bounded
    T S hTne hSne hTconn hSconn hdisj.symm hTbelow hSabove
  exact ⟨c, d, by simpa [Set.union_comm] using h⟩

/-- A monotone right-ray tail with an upper bound is trapped in a compact
interval after moving one unit away from its finite endpoint. -/
lemma apm_t95j06_strictMono_Ioi_tail_subset_Icc
    (f : ℝ → ℝ) (β : ℝ) (hf : StrictMonoOn f (Set.Ioi β))
    (hb : BddAbove (f '' Set.Ioi β)) :
    f '' Set.Ici (β + 1) ⊆ Set.Icc (f (β + 1)) (sSup (f '' Set.Ioi β)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hb1 : β < β + 1 := by linarith
  have hxray : β < x := lt_of_lt_of_le hb1 hx
  exact ⟨hf.monotoneOn hb1 hxray hx,
    le_csSup hb ⟨x, hxray, rfl⟩⟩

/-- An antitone right-ray tail with a lower bound is trapped in a compact
interval after moving one unit away from its finite endpoint. -/
lemma apm_t95j06_strictAnti_Ioi_tail_subset_Icc
    (f : ℝ → ℝ) (β : ℝ) (hf : StrictAntiOn f (Set.Ioi β))
    (hb : BddBelow (f '' Set.Ioi β)) :
    f '' Set.Ici (β + 1) ⊆ Set.Icc (sInf (f '' Set.Ioi β)) (f (β + 1)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hb1 : β < β + 1 := by linarith
  have hxray : β < x := lt_of_lt_of_le hb1 hx
  exact ⟨csInf_le hb ⟨x, hxray, rfl⟩,
    hf.antitoneOn hb1 hxray hx⟩

/-- A monotone left-ray tail with a lower bound is trapped in a compact
interval after moving one unit away from its finite endpoint. -/
lemma apm_t95j06_strictMono_Iio_tail_subset_Icc
    (f : ℝ → ℝ) (α : ℝ) (hf : StrictMonoOn f (Set.Iio α))
    (hb : BddBelow (f '' Set.Iio α)) :
    f '' Set.Iic (α - 1) ⊆ Set.Icc (sInf (f '' Set.Iio α)) (f (α - 1)) := by
  rintro _ ⟨x, hx, rfl⟩
  have ha1 : α - 1 < α := by linarith
  have hxray : x < α := lt_of_le_of_lt hx ha1
  exact ⟨csInf_le hb ⟨x, hxray, rfl⟩,
    hf.monotoneOn hxray ha1 hx⟩

/-- An antitone left-ray tail with an upper bound is trapped in a compact
interval after moving one unit away from its finite endpoint. -/
lemma apm_t95j06_strictAnti_Iio_tail_subset_Icc
    (f : ℝ → ℝ) (α : ℝ) (hf : StrictAntiOn f (Set.Iio α))
    (hb : BddAbove (f '' Set.Iio α)) :
    f '' Set.Iic (α - 1) ⊆ Set.Icc (f (α - 1)) (sSup (f '' Set.Iio α)) := by
  rintro _ ⟨x, hx, rfl⟩
  have ha1 : α - 1 < α := by linarith
  have hxray : x < α := lt_of_le_of_lt hx ha1
  exact ⟨hf.antitoneOn hxray ha1 hx,
    le_csSup hb ⟨x, hxray, rfl⟩⟩

/-- At the finite endpoint of a right ray, absence of every finite limit
forces an increasing transition to be unbounded below, and a decreasing one
to be unbounded above. -/
lemma apm_t95j06_right_ray_noFiniteLimit_forces_unbounded
    (f : ℝ → ℝ) (β : ℝ)
    (hnolim : ∀ c : ℝ,
      ¬ Filter.Tendsto f (nhdsWithin β (Set.Ioi β)) (nhds c)) :
    (StrictMonoOn f (Set.Ioi β) → ¬ BddBelow (f '' Set.Ioi β)) ∧
    (StrictAntiOn f (Set.Ioi β) → ¬ BddAbove (f '' Set.Ioi β)) := by
  have hβ : β < β + 1 := by linarith
  have hsub : f '' Set.Ioo β (β + 1) ⊆ f '' Set.Ioi β :=
    Set.image_mono Set.Ioo_subset_Ioi_self
  have E := apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_monotone_end_limits
    β (β + 1) hβ f
  constructor
  · intro hm hb
    exact hnolim _ ((E.1 (hm.mono Set.Ioo_subset_Ioi_self)).2 (hb.mono hsub))
  · intro hm hb
    exact hnolim _ ((E.2 (hm.mono Set.Ioo_subset_Ioi_self)).2 (hb.mono hsub))

/-- At the finite endpoint of a left ray, absence of every finite limit
forces an increasing transition to be unbounded above, and a decreasing one
to be unbounded below. -/
lemma apm_t95j06_left_ray_noFiniteLimit_forces_unbounded
    (f : ℝ → ℝ) (α : ℝ)
    (hnolim : ∀ c : ℝ,
      ¬ Filter.Tendsto f (nhdsWithin α (Set.Iio α)) (nhds c)) :
    (StrictMonoOn f (Set.Iio α) → ¬ BddAbove (f '' Set.Iio α)) ∧
    (StrictAntiOn f (Set.Iio α) → ¬ BddBelow (f '' Set.Iio α)) := by
  have hα : α - 1 < α := by linarith
  have hsub : f '' Set.Ioo (α - 1) α ⊆ f '' Set.Iio α :=
    Set.image_mono Set.Ioo_subset_Iio_self
  have E := apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_monotone_end_limits
    (α - 1) α hα f
  constructor
  · intro hm hb
    exact hnolim _ ((E.1 (hm.mono Set.Ioo_subset_Iio_self)).1 (hb.mono hsub))
  · intro hm hb
    exact hnolim _ ((E.2 (hm.mono Set.Ioo_subset_Iio_self)).1 (hb.mono hsub))

/-- A continuous injective function on a right ray is strictly monotone or
strictly antitone there. -/
lemma apm_t95j06_continuousOn_injOn_Ioi_strictMono_or_anti
    (f : ℝ → ℝ) (b : ℝ) (hc : ContinuousOn f (Set.Ioi b))
    (hi : Set.InjOn f (Set.Ioi b)) :
    StrictMonoOn f (Set.Ioi b) ∨ StrictAntiOn f (Set.Ioi b) := by
  let g : ℝ → ℝ := fun t => f (b + Real.exp t)
  have hmem : ∀ t : ℝ, b + Real.exp t ∈ Set.Ioi b := fun t => by
    simp only [Set.mem_Ioi]; linarith [Real.exp_pos t]
  have hgc : Continuous g := hc.comp_continuous (by fun_prop) hmem
  have hgi : Function.Injective g := by
    intro t t' h
    have := hi (hmem t) (hmem t') h
    exact Real.exp_injective (by linarith)
  have hrep : ∀ x ∈ Set.Ioi b, f x = g (Real.log (x - b)) := by
    intro x hx
    have hx' : 0 < x - b := sub_pos.mpr hx
    simp only [g, Real.exp_log hx']; ring_nf
  have hlog : ∀ x ∈ Set.Ioi b, ∀ y ∈ Set.Ioi b, x < y →
      Real.log (x - b) < Real.log (y - b) := by
    intro x hx y hy hxy
    exact Real.log_lt_log (sub_pos.mpr hx) (by linarith)
  rcases hgc.strictMono_of_inj hgi with hg | hg
  · left; intro x hx y hy hxy
    rw [hrep x hx, hrep y hy]; exact hg (hlog x hx y hy hxy)
  · right; intro x hx y hy hxy
    rw [hrep x hx, hrep y hy]; exact hg (hlog x hx y hy hxy)

/-- A continuous injective function on a left ray is strictly monotone or
strictly antitone there. -/
lemma apm_t95j06_continuousOn_injOn_Iio_strictMono_or_anti
    (f : ℝ → ℝ) (a : ℝ) (hc : ContinuousOn f (Set.Iio a))
    (hi : Set.InjOn f (Set.Iio a)) :
    StrictMonoOn f (Set.Iio a) ∨ StrictAntiOn f (Set.Iio a) := by
  have hc' : ContinuousOn (fun s => f (-s)) (Set.Ioi (-a)) :=
    hc.comp continuous_neg.continuousOn (fun s hs => by
      simp only [Set.mem_Ioi, Set.mem_Iio] at hs ⊢; linarith)
  have hi' : Set.InjOn (fun s => f (-s)) (Set.Ioi (-a)) := by
    intro s hs s' hs' h
    have := hi (show -s ∈ Set.Iio a by simp only [Set.mem_Ioi, Set.mem_Iio] at hs ⊢; linarith)
      (show -s' ∈ Set.Iio a by simp only [Set.mem_Ioi, Set.mem_Iio] at hs' ⊢; linarith) h
    linarith
  have hneg : ∀ x ∈ Set.Iio a, -x ∈ Set.Ioi (-a) := fun x hx => by
    simp only [Set.mem_Ioi, Set.mem_Iio] at hx ⊢; linarith
  rcases apm_t95j06_continuousOn_injOn_Ioi_strictMono_or_anti _ (-a) hc' hi' with h | h
  · right; intro x hx y hy hxy
    have := h (hneg y hy) (hneg x hx) (by linarith)
    simpa using this
  · left; intro x hx y hy hxy
    have := h (hneg y hy) (hneg x hx) (by linarith)
    simpa using this

/-- Two disjoint nonempty preconnected real sets cannot both be unbounded
below. -/
lemma apm_t95j06_disjoint_preconnected_not_both_unbounded_below
    (S T : Set ℝ) (hTne : T.Nonempty)
    (hTconn : _root_.IsPreconnected T)
    (hdisj : Disjoint S T) (hS : ¬ BddBelow S) (hT : ¬ BddBelow T) : False := by
  obtain ⟨t0, ht0⟩ := hTne
  obtain ⟨s, hs, hst⟩ := not_bddBelow_iff.mp hS t0
  obtain ⟨t, ht, hts⟩ := not_bddBelow_iff.mp hT s
  exact Set.disjoint_left.mp hdisj hs (hTconn.Icc_subset ht ht0 ⟨hts.le, hst.le⟩)

/-- Two disjoint nonempty preconnected real sets cannot both be unbounded
above. -/
lemma apm_t95j06_disjoint_preconnected_not_both_unbounded_above
    (S T : Set ℝ) (hTne : T.Nonempty)
    (hTconn : _root_.IsPreconnected T)
    (hdisj : Disjoint S T) (hS : ¬ BddAbove S) (hT : ¬ BddAbove T) : False := by
  obtain ⟨t0, ht0⟩ := hTne
  obtain ⟨s, hs, hst⟩ := not_bddAbove_iff.mp hS t0
  obtain ⟨t, ht, hts⟩ := not_bddAbove_iff.mp hT s
  exact Set.disjoint_left.mp hdisj hs (hTconn.Icc_subset ht0 ht ⟨hst.le, hts.le⟩)

/-- The transition function of two real charts, on the overlap in the first
chart: continuous, injective, onto the overlap in the second chart, linked to
the charts, and without finite limit at a point outside the overlap. -/
lemma apm_t95j06_two_overlapping_realCharts_transition_package
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) :
    ∃ f : ℝ → ℝ,
      ContinuousOn f (φ '' (Subtype.val ⁻¹' V)) ∧
      Set.InjOn f (φ '' (Subtype.val ⁻¹' V)) ∧
      f '' (φ '' (Subtype.val ⁻¹' V)) = ψ '' (Subtype.val ⁻¹' U) ∧
      (∀ (u : U) (hu : (u : X) ∈ V), f (φ u) = ψ ⟨u, hu⟩) ∧
      (∀ (s : Set ℝ) (β : ℝ), s ⊆ φ '' (Subtype.val ⁻¹' V) →
        β ∉ φ '' (Subtype.val ⁻¹' V) → (nhdsWithin β s).NeBot →
        ∀ c : ℝ, ¬ Filter.Tendsto f (nhdsWithin β s) (nhds c)) := by
  classical
  set A := φ '' (Subtype.val ⁻¹' V) with hAdef
  have hO : ∀ s ∈ A, ((φ.symm s : U) : X) ∈ V := by
    rintro _ ⟨u, hu, rfl⟩; simpa using hu
  let τ : ℝ → ℝ := fun s => if h : ((φ.symm s : U) : X) ∈ V then ψ ⟨_, h⟩ else 0
  have hτA : ∀ s (h : ((φ.symm s : U) : X) ∈ V), τ s = ψ ⟨_, h⟩ := by
    intro s h; simp only [τ, dif_pos h]
  have hlink : ∀ (u : U) (hu : (u : X) ∈ V), τ (φ u) = ψ ⟨u, hu⟩ := by
    intro u hu
    have h : ((φ.symm (φ u) : U) : X) ∈ V := by simpa using hu
    rw [hτA _ h]; congr 1; ext; simp
  refine ⟨τ, ?_, ?_, ?_, hlink, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : A.restrict τ = fun s : A => ψ ⟨((φ.symm s.1 : U) : X), hO s.1 s.2⟩ := by
      funext s; exact hτA _ _
    rw [this]
    exact ψ.continuous.comp ((continuous_subtype_val.comp
      (φ.symm.continuous.comp continuous_subtype_val)).subtype_mk _)
  · intro s hs s' hs' he
    rw [hτA s (hO s hs), hτA s' (hO s' hs')] at he
    have h1 := congrArg Subtype.val (ψ.injective he)
    have h2 : φ.symm s = φ.symm s' := Subtype.ext h1
    simpa using congrArg φ h2
  · ext t; constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨⟨u, hu⟩, u.2, (hlink u hu).symm⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨φ ⟨v, hv⟩, ⟨⟨v, hv⟩, v.2, rfl⟩, ?_⟩
      rw [hlink ⟨v, hv⟩ v.2]
  · intro s β hsA hβ _ c hc
    refine apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_no_finite_end_limit
      X U V φ ψ (l := nhdsWithin β s) (fun s => φ.symm s) (fun s => ψ.symm (τ s)) ?_ β hβ ?_ c ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [hτA x (hO x (hsA hx))]; simp
    · simpa using (Filter.tendsto_id.mono_left (nhdsWithin_le_nhds (s := s) (a := β)))
    · simpa using hc

/-- **Two-ray overlap gives a compact union.**  If the overlap in the first
chart is the union of two opposite rays, then `U ∪ V` is compact: it is
covered by the first chart over a compact interval and the second chart over
compact intervals containing the tails and the complement of the overlap. -/
lemma apm_t95j06_two_overlapping_realCharts_twoRay_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ) (a b : ℝ) (hab : a ≤ b)
    (hA : φ '' (Subtype.val ⁻¹' V) = Set.Iio a ∪ Set.Ioi b) :
    IsCompact (U ∪ V) := by
  classical
  obtain ⟨f, hfc, hfi, hfB, hlink, hnolim⟩ :=
    apm_t95j06_two_overlapping_realCharts_transition_package X U V φ ψ
  rw [hA] at hfc hfi hfB hnolim
  have hIioA : Set.Iio a ⊆ Set.Iio a ∪ Set.Ioi b := Set.subset_union_left
  have hIoiA : Set.Ioi b ⊆ Set.Iio a ∪ Set.Ioi b := Set.subset_union_right
  have haA : a ∉ Set.Iio a ∪ Set.Ioi b := by
    rintro (h | h)
    · exact lt_irrefl a h
    · exact absurd (lt_of_le_of_lt hab h) (lt_irrefl a)
  have hbA : b ∉ Set.Iio a ∪ Set.Ioi b := by
    rintro (h | h)
    · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl b)
    · exact lt_irrefl b h
  set S := f '' Set.Iio a with hSdef
  set T := f '' Set.Ioi b with hTdef
  have hSne : S.Nonempty := ⟨f (a - 1), a - 1, by simp, rfl⟩
  have hTne : T.Nonempty := ⟨f (b + 1), b + 1, by simp, rfl⟩
  have hSconn : _root_.IsPreconnected S := isPreconnected_Iio.image f (hfc.mono hIioA)
  have hTconn : _root_.IsPreconnected T := isPreconnected_Ioi.image f (hfc.mono hIoiA)
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hfi (hIoiA hy) (hIioA hx) hxy
    rw [this] at hy
    exact absurd (lt_of_lt_of_le (lt_trans hy hx) hab) (lt_irrefl b)
  have hnolimR := apm_t95j06_right_ray_noFiniteLimit_forces_unbounded f b
    (hnolim (Set.Ioi b) b hIoiA hbA inferInstance)
  have hnolimL := apm_t95j06_left_ray_noFiniteLimit_forces_unbounded f a
    (hnolim (Set.Iio a) a hIioA haA inferInstance)
  have hTos := apm_t95j06_disjoint_preconnected_real_sets_oneSided_bounded T S hTne hSne
    hTconn hdisj.symm
  have hSos := apm_t95j06_disjoint_preconnected_real_sets_oneSided_bounded S T hSne hTne
    hSconn hdisj
  -- tails are trapped in compact intervals
  have htailR : ∃ c d : ℝ, f '' Set.Ici (b + 1) ⊆ Set.Icc c d := by
    rcases apm_t95j06_continuousOn_injOn_Ioi_strictMono_or_anti f b (hfc.mono hIoiA)
      (hfi.mono hIoiA) with hm | hm
    · have hba : BddAbove T := hTos.resolve_right (hnolimR.1 hm)
      exact ⟨_, _, apm_t95j06_strictMono_Ioi_tail_subset_Icc f b hm hba⟩
    · have hbb : BddBelow T := hTos.resolve_left (hnolimR.2 hm)
      exact ⟨_, _, apm_t95j06_strictAnti_Ioi_tail_subset_Icc f b hm hbb⟩
  have htailL : ∃ c d : ℝ, f '' Set.Iic (a - 1) ⊆ Set.Icc c d := by
    rcases apm_t95j06_continuousOn_injOn_Iio_strictMono_or_anti f a (hfc.mono hIioA)
      (hfi.mono hIioA) with hm | hm
    · have hbb : BddBelow S := hSos.resolve_left (hnolimL.1 hm)
      exact ⟨_, _, apm_t95j06_strictMono_Iio_tail_subset_Icc f a hm hbb⟩
    · have hba : BddAbove S := hSos.resolve_right (hnolimL.2 hm)
      exact ⟨_, _, apm_t95j06_strictAnti_Iio_tail_subset_Icc f a hm hba⟩
  -- the complement of the overlap in the second chart is bounded
  have hcompl : ∃ c d : ℝ, (S ∪ T)ᶜ ⊆ Set.Icc c d := by
    rcases apm_t95j06_continuousOn_injOn_Ioi_strictMono_or_anti f b (hfc.mono hIoiA)
      (hfi.mono hIoiA) with hR | hR <;>
    rcases apm_t95j06_continuousOn_injOn_Iio_strictMono_or_anti f a (hfc.mono hIioA)
      (hfi.mono hIioA) with hL | hL
    · exact apm_t95j06_disjoint_preconnected_compl_bounded_swapped S T hSne hTne hSconn
        hTconn hdisj (hnolimL.1 hL) (hnolimR.1 hR)
    · exact (apm_t95j06_disjoint_preconnected_not_both_unbounded_below S T hTne hTconn
        hdisj (hnolimL.2 hL) (hnolimR.1 hR)).elim
    · exact (apm_t95j06_disjoint_preconnected_not_both_unbounded_above S T hTne hTconn
        hdisj (hnolimL.1 hL) (hnolimR.2 hR)).elim
    · exact apm_t95j06_disjoint_preconnected_compl_bounded S T hSne hTne hSconn
        hTconn hdisj (hnolimL.2 hL) (hnolimR.2 hR)
  obtain ⟨c1, d1, h1⟩ := htailL
  obtain ⟨c2, d2, h2⟩ := htailR
  obtain ⟨c3, d3, h3⟩ := hcompl
  have hST : S ∪ T = ψ '' (Subtype.val ⁻¹' U) := by
    rw [← hfB, Set.image_union]
  let eU : ℝ → X := fun s => ((φ.symm s : U) : X)
  let eV : ℝ → X := fun s => ((ψ.symm s : V) : X)
  have heU : Continuous eU := continuous_subtype_val.comp φ.symm.continuous
  have heV : Continuous eV := continuous_subtype_val.comp ψ.symm.continuous
  have hK : U ∪ V = eU '' Set.Icc (a - 1) (b + 1) ∪
      eV '' (Set.Icc c1 d1 ∪ Set.Icc c2 d2 ∪ Set.Icc c3 d3) := by
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · set s := φ ⟨x, hx⟩ with hs
        have hxs : eU s = x := by simp [eU, s]
        by_cases hlo : s < a - 1
        · have hsA : s ∈ Set.Iio a ∪ Set.Ioi b := Or.inl (by
            simp only [Set.mem_Iio]; linarith)
          rw [← hA] at hsA
          obtain ⟨u, hu, hus⟩ := hsA
          have hu' : u = ⟨x, hx⟩ := φ.injective hus
          subst hu'
          right
          refine ⟨f s, Or.inl (Or.inl (h1 ⟨s, Set.mem_Iic.mpr hlo.le, rfl⟩)), ?_⟩
          simp only [eV, s, hlink ⟨x, hx⟩ hu, Homeomorph.symm_apply_apply]
        by_cases hhi : b + 1 < s
        · have hsA : s ∈ Set.Iio a ∪ Set.Ioi b := Or.inr (by
            simp only [Set.mem_Ioi]; linarith)
          rw [← hA] at hsA
          obtain ⟨u, hu, hus⟩ := hsA
          have hu' : u = ⟨x, hx⟩ := φ.injective hus
          subst hu'
          right
          refine ⟨f s, Or.inl (Or.inr (h2 ⟨s, Set.mem_Ici.mpr hhi.le, rfl⟩)), ?_⟩
          simp only [eV, s, hlink ⟨x, hx⟩ hu, Homeomorph.symm_apply_apply]
        left
        exact ⟨s, ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩, hxs⟩
      · by_cases hxU : x ∈ U
        · set s := φ ⟨x, hxU⟩ with hs
          by_cases hlo : s < a - 1
          · right
            refine ⟨f s, Or.inl (Or.inl (h1 ⟨s, Set.mem_Iic.mpr hlo.le, rfl⟩)), ?_⟩
            simp only [eV, s, hlink ⟨x, hxU⟩ hx, Homeomorph.symm_apply_apply]
          by_cases hhi : b + 1 < s
          · right
            refine ⟨f s, Or.inl (Or.inr (h2 ⟨s, Set.mem_Ici.mpr hhi.le, rfl⟩)), ?_⟩
            simp only [eV, s, hlink ⟨x, hxU⟩ hx, Homeomorph.symm_apply_apply]
          left
          exact ⟨s, ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩, by simp [eU, s]⟩
        · right
          refine ⟨ψ ⟨x, hx⟩, Or.inr (h3 ?_), by simp [eV]⟩
          rw [hST]
          rintro ⟨v, hv, hvx⟩
          have : v = ⟨x, hx⟩ := ψ.injective hvx
          subst this; exact hxU hv
    · rintro x (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩)
      · exact Or.inl (φ.symm s).2
      · exact Or.inr (ψ.symm s).2
  rw [hK]
  exact (isCompact_Icc.image heU).union
    (((isCompact_Icc.union isCompact_Icc).union isCompact_Icc).image heV)

theorem apm_t95j06_two_overlapping_realCharts_line_or_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUreal : Nonempty (U ≃ₜ ℝ)) (hVreal : Nonempty (V ≃ₜ ℝ))
    (hUV : (U ∩ V).Nonempty) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ ℝ) ∨ IsCompact (U ∪ V) := by
  classical
  obtain ⟨φ⟩ := hUreal
  obtain ⟨ψ⟩ := hVreal
  set A := φ '' (Subtype.val ⁻¹' V) with hAdef
  set B := ψ '' (Subtype.val ⁻¹' U) with hBdef
  have hmemA : ∀ (x : U), (x : X) ∈ V → φ x ∈ A := fun x hx => ⟨x, hx, rfl⟩
  by_cases hAu : A = Set.univ
  · left
    have hsub : U ⊆ V := by
      intro x hx
      obtain ⟨u, hu, hux⟩ : φ ⟨x, hx⟩ ∈ A := hAu ▸ Set.mem_univ _
      have : u = ⟨x, hx⟩ := φ.injective hux
      subst this; exact hu
    exact ⟨(Homeomorph.setCongr (Set.union_eq_right.mpr hsub)).trans ψ⟩
  by_cases hBu : B = Set.univ
  · left
    have hsub : V ⊆ U := by
      intro x hx
      obtain ⟨v, hv, hvx⟩ : ψ ⟨x, hx⟩ ∈ B := hBu ▸ Set.mem_univ _
      have : v = ⟨x, hx⟩ := ψ.injective hvx
      subst this; exact hv
    exact ⟨(Homeomorph.setCongr (Set.union_eq_left.mpr hsub)).trans φ⟩
  obtain ⟨x0, hx0U, hx0V⟩ := hUV
  have hAne : A.Nonempty := ⟨φ ⟨x0, hx0U⟩, ⟨x0, hx0U⟩, hx0V, rfl⟩
  have hBne : B.Nonempty := ⟨ψ ⟨x0, hx0V⟩, ⟨x0, hx0V⟩, hx0U, rfl⟩
  have hrayA : ∀ t ∈ A, (∃ a, connectedComponentIn A t = Set.Ioi a) ∨
      ∃ b, connectedComponentIn A t = Set.Iio b := by
    intro t ht
    rcases apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_component_ray
      X U V hVopen φ ψ t ht with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hAu
    · exact absurd h hBu
  have hrayB : ∀ t ∈ B, (∃ a, connectedComponentIn B t = Set.Ioi a) ∨
      ∃ b, connectedComponentIn B t = Set.Iio b := by
    intro t ht
    rcases apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_component_ray
      X V U hUopen ψ φ t ht with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hBu
    · exact absurd h hAu
  obtain ⟨f, hfc, hfi, hfB, hlink, hnolim⟩ :=
    apm_t95j06_two_overlapping_realCharts_transition_package X U V φ ψ
  rw [← hAdef] at hfc hfi hnolim
  rw [← hAdef, ← hBdef] at hfB
  have hshB := apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_ray_shape
    B hBne hBu hrayB
  rcases apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_ray_shape A hAne hAu hrayA
    with ⟨α, hα⟩ | ⟨α, hα⟩ | ⟨a, b, hab, hAab⟩
  rotate_left 2
  · right
    exact apm_t95j06_two_overlapping_realCharts_twoRay_compact X U V φ ψ a b hab hAab
  all_goals rcases hshB with ⟨δ, hδ⟩ | ⟨δ, hδ⟩ | ⟨c, d, hcd, hBcd⟩
  rotate_left 2
  · right; rw [Set.union_comm]
    exact apm_t95j06_two_overlapping_realCharts_twoRay_compact X V U ψ φ c d hcd hBcd
  rotate_left 2
  · right; rw [Set.union_comm]
    exact apm_t95j06_two_overlapping_realCharts_twoRay_compact X V U ψ φ c d hcd hBcd
  all_goals left
  all_goals rw [hα] at hfc hfi hfB hnolim
  -- A = Ioi α, B = Ioi δ
  · have hnR := apm_t95j06_right_ray_noFiniteLimit_forces_unbounded f α
      (hnolim (Set.Ioi α) α subset_rfl (fun h => lt_irrefl α h) inferInstance)
    rw [hfB, hδ] at hnR
    rcases apm_t95j06_continuousOn_injOn_Ioi_strictMono_or_anti f α hfc hfi with hm | hm
    · exact absurd bddBelow_Ioi (hnR.1 hm)
    · refine apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_orientation
        X U V hUopen hVopen φ ψ α δ (Or.inr (Or.inl ⟨hα, hδ, ?_⟩))
      intro x y hx hy hxy
      rw [← hlink x hx, ← hlink y hy]
      exact hm (hα ▸ hmemA x hx) (hα ▸ hmemA y hy) hxy
  -- A = Ioi α, B = Iio δ
  · have hnR := apm_t95j06_right_ray_noFiniteLimit_forces_unbounded f α
      (hnolim (Set.Ioi α) α subset_rfl (fun h => lt_irrefl α h) inferInstance)
    rw [hfB, hδ] at hnR
    rcases apm_t95j06_continuousOn_injOn_Ioi_strictMono_or_anti f α hfc hfi with hm | hm
    · refine apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_orientation
        X U V hUopen hVopen φ ψ α δ (Or.inl ⟨hα, hδ, ?_⟩)
      intro x y hx hy hxy
      rw [← hlink x hx, ← hlink y hy]
      exact hm (hα ▸ hmemA x hx) (hα ▸ hmemA y hy) hxy
    · exact absurd bddAbove_Iio (hnR.2 hm)
  -- A = Iio α, B = Ioi δ
  · have hnL := apm_t95j06_left_ray_noFiniteLimit_forces_unbounded f α
      (hnolim (Set.Iio α) α subset_rfl (fun h => lt_irrefl α h) inferInstance)
    rw [hfB, hδ] at hnL
    rcases apm_t95j06_continuousOn_injOn_Iio_strictMono_or_anti f α hfc hfi with hm | hm
    · refine apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_orientation
        X U V hUopen hVopen φ ψ α δ (Or.inr (Or.inr (Or.inr ⟨hα, hδ, ?_⟩)))
      intro x y hx hy hxy
      rw [← hlink x hx, ← hlink y hy]
      exact hm (hα ▸ hmemA x hx) (hα ▸ hmemA y hy) hxy
    · exact absurd bddBelow_Ioi (hnL.2 hm)
  -- A = Iio α, B = Iio δ
  · have hnL := apm_t95j06_left_ray_noFiniteLimit_forces_unbounded f α
      (hnolim (Set.Iio α) α subset_rfl (fun h => lt_irrefl α h) inferInstance)
    rw [hfB, hδ] at hnL
    rcases apm_t95j06_continuousOn_injOn_Iio_strictMono_or_anti f α hfc hfi with hm | hm
    · exact absurd bddAbove_Iio (hnL.1 hm)
    · refine apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_orientation
        X U V hUopen hVopen φ ψ α δ (Or.inr (Or.inr (Or.inl ⟨hα, hδ, ?_⟩)))
      intro x y hx hy hxy
      rw [← hlink x hx, ← hlink y hy]
      exact hm (hα ▸ hmemA x hx) (hα ▸ hmemA y hy) hxy

/- Two overlapping relatively compact line charts in a connected noncompact
Hausdorff second-countable one-manifold have a common relatively compact line
chart neighborhood.

This is true because the overlap fixes compatible local orders up to reversal.
Hausdorffness excludes doubled endpoints and local real-line charts exclude
branching.  The only alternative obtained by joining both pairs of ends is a
clopen circle component; connectedness would then make the ambient space
compact, contradicting `NoncompactSpace X`.  Estimated size: 90--150 lines. -/
theorem apm_t95j06_overlapping_intervalCharts_pair_thicken
    (X : Type) [TopologicalSpace X] [ConnectedSpace X] [NoncompactSpace X]
    [T2Space X] [SecondCountableTopology X]
    (hloc : apm_t95j06_IsLocallyRealLine X)
    (U V : Set X) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUcompact : IsCompact (closure U)) (hVcompact : IsCompact (closure V))
    (hUreal : Nonempty (U ≃ₜ ℝ)) (hVreal : Nonempty (V ≃ₜ ℝ))
    (hUV : (U ∩ V).Nonempty) :
    ∃ W : Set X, IsOpen W ∧ U ∪ V ⊆ W ∧ IsCompact (closure W) ∧
      Nonempty (W ≃ₜ ℝ) := by
  have hopen : IsOpen (U ∪ V) := hUopen.union hVopen
  have hclosure : IsCompact (closure (U ∪ V)) := by
    rw [closure_union]
    exact hUcompact.union hVcompact
  rcases apm_t95j06_two_overlapping_realCharts_line_or_compact
      X U V hUopen hVopen hUreal hVreal hUV with hline | hcompact
  · exact ⟨U ∪ V, hopen, fun _ h ↦ h, hclosure, hline⟩
  · have hclosed : IsClosed (U ∪ V) := hcompact.isClosed
    have hnonempty : (U ∪ V).Nonempty :=
      hUV.mono (Set.inter_subset_left.trans Set.subset_union_left)
    have huniv : U ∪ V = Set.univ := (show IsClopen (U ∪ V) from ⟨hclosed, hopen⟩).eq_univ hnonempty
    exact False.elim (hcompact.ne_univ huniv)

/-- The empty and singleton cases of finite chart thickening require no
gluing: for a singleton use its supplied chart, while for the empty family
use any chart (the connected space is nonempty). -/
lemma apm_t95j06_finite_intervalCharts_thicken_card_le_one
    (X : Type) [TopologicalSpace X] [ConnectedSpace X]
    (A : X → Set X) (hAopen : ∀ x, IsOpen (A x))
    (hAcompact : ∀ x, IsCompact (closure (A x)))
    (hAreal : ∀ x, Nonempty (A x ≃ₜ ℝ))
    (t : Finset X) (ht : t.card ≤ 1) :
    ∃ U : Set X, IsOpen U ∧ (⋃ x ∈ t, A x) ⊆ U ∧
      IsCompact (closure U) ∧ Nonempty (U ≃ₜ ℝ) := by
  classical
  by_cases he : t = ∅
  · subst he
    let x : X := Classical.choice (inferInstance : Nonempty X)
    exact ⟨A x, hAopen x, by simp, hAcompact x, hAreal x⟩
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have huniq := Finset.card_le_one.mp ht
    have htx : t = {x} := by
      ext y
      simp only [Finset.mem_singleton]
      exact ⟨fun hy ↦ huniq y hy x hx, fun h ↦ h ▸ hx⟩
    subst htx
    exact ⟨A x, hAopen x, by simp, hAcompact x, hAreal x⟩

theorem apm_t95j06_connected_finite_intervalCharts_thicken
    (X : Type) [TopologicalSpace X] [ConnectedSpace X] [NoncompactSpace X]
    [T2Space X] [SecondCountableTopology X]
    (hloc : apm_t95j06_IsLocallyRealLine X)
    (A : X → Set X)
    (hAopen : ∀ x, IsOpen (A x))
    (hAcompact : ∀ x, IsCompact (closure (A x)))
    (hAreal : ∀ x, Nonempty (A x ≃ₜ ℝ))
    (t : Finset X) (ht : IsConnected (⋃ x ∈ t, A x)) :
    ∃ U : Set X, IsOpen U ∧ (⋃ x ∈ t, A x) ⊆ U ∧
      IsCompact (closure U) ∧ Nonempty (U ≃ₜ ℝ) := by
  classical
  have hne : ∀ x, (A x).Nonempty := fun x => by
    obtain ⟨e⟩ := hAreal x
    exact ⟨(e.symm 0).1, (e.symm 0).2⟩
  obtain ⟨z0, hz0⟩ := ht.nonempty
  obtain ⟨x0, hx0t, -⟩ := Set.mem_iUnion₂.mp hz0
  have key : ∀ n : ℕ, 1 ≤ n → n ≤ t.card → ∃ s : Finset X, s ⊆ t ∧ s.card = n ∧
      ∃ U : Set X, IsOpen U ∧ (⋃ x ∈ s, A x) ⊆ U ∧
        IsCompact (closure U) ∧ Nonempty (U ≃ₜ ℝ) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact ⟨{x0}, by simpa using hx0t, by simp, A x0, hAopen x0, by simp,
          hAcompact x0, hAreal x0⟩
      obtain ⟨s, hst, hsc, U, hUo, hsU, hUc, hUr⟩ := ih hpos (by omega)
      have hlt : s.card < t.card := by omega
      have hsdiff : (t \ s).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
        intro hts
        exact absurd (Finset.card_le_card hts) (by omega)
      obtain ⟨x1, hx1⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨y1, hy1⟩ := hsdiff
      have hPo : IsOpen (⋃ x ∈ s, A x) := isOpen_biUnion fun x _ => hAopen x
      have hQo : IsOpen (⋃ x ∈ t \ s, A x) := isOpen_biUnion fun x _ => hAopen x
      have hcov : (⋃ x ∈ t, A x) ⊆ (⋃ x ∈ s, A x) ∪ (⋃ x ∈ t \ s, A x) := by
        intro z hz
        obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp hz
        by_cases hxs : x ∈ s
        · exact Or.inl (Set.mem_iUnion₂.mpr ⟨x, hxs, hzx⟩)
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hxt, hxs⟩, hzx⟩)
      have hPne : ((⋃ x ∈ t, A x) ∩ (⋃ x ∈ s, A x)).Nonempty := by
        obtain ⟨z, hz⟩ := hne x1
        exact ⟨z, Set.mem_iUnion₂.mpr ⟨x1, hst hx1, hz⟩, Set.mem_iUnion₂.mpr ⟨x1, hx1, hz⟩⟩
      have hQne : ((⋃ x ∈ t, A x) ∩ (⋃ x ∈ t \ s, A x)).Nonempty := by
        obtain ⟨z, hz⟩ := hne y1
        exact ⟨z, Set.mem_iUnion₂.mpr ⟨y1, (Finset.mem_sdiff.mp hy1).1, hz⟩,
          Set.mem_iUnion₂.mpr ⟨y1, hy1, hz⟩⟩
      obtain ⟨z, -, hzP, hzQ⟩ := ht.isPreconnected _ _ hPo hQo hcov hPne hQne
      obtain ⟨y, hyts, hzy⟩ := Set.mem_iUnion₂.mp hzQ
      have hyt := (Finset.mem_sdiff.mp hyts).1
      have hys := (Finset.mem_sdiff.mp hyts).2
      obtain ⟨W, hWo, hUW, hWc, hWr⟩ :=
        apm_t95j06_overlapping_intervalCharts_pair_thicken X hloc U (A y) hUo (hAopen y)
          hUc (hAcompact y) hUr (hAreal y) ⟨z, hsU hzP, hzy⟩
      refine ⟨insert y s, Finset.insert_subset hyt hst, by
        rw [Finset.card_insert_of_notMem hys, hsc], W, hWo, ?_, hWc, hWr⟩
      intro w hw
      obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.mp hw
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact hUW (Or.inr hwx)
      · exact hUW (Or.inl (hsU (Set.mem_iUnion₂.mpr ⟨x, hxs, hwx⟩)))
  have hcard : 1 ≤ t.card := Finset.card_pos.mpr ⟨x0, hx0t⟩
  obtain ⟨s, hst, hsc, U, hUo, hsU, hUc, hUr⟩ := key t.card hcard le_rfl
  have hseq : s = t := Finset.eq_of_subset_of_card_le hst (by omega)
  subst hseq
  exact ⟨U, hUo, hsU, hUc, hUr⟩

theorem apm_t95j06_finite_intervalCharts_thicken
    (X : Type) [TopologicalSpace X] [ConnectedSpace X] [NoncompactSpace X]
    [T2Space X] [SecondCountableTopology X]
    (hloc : apm_t95j06_IsLocallyRealLine X)
    (A : X → Set X)
    (hAopen : ∀ x, IsOpen (A x))
    (hxA : ∀ x, x ∈ A x)
    (hAcompact : ∀ x, IsCompact (closure (A x)))
    (hAreal : ∀ x, Nonempty (A x ≃ₜ ℝ))
    (s : Finset X) :
    ∃ U : Set X, IsOpen U ∧ (⋃ x ∈ s, A x) ⊆ U ∧
      IsCompact (closure U) ∧ Nonempty (U ≃ₜ ℝ) := by
  obtain ⟨t, hst, ht⟩ :=
    apm_t95j06_finite_intervalCharts_connected_enlargement X A hAopen hxA hAreal s
  obtain ⟨U, hU, htU, hcU, hUr⟩ :=
    apm_t95j06_connected_finite_intervalCharts_thicken
      X hloc A hAopen hAcompact hAreal t ht
  refine ⟨U, hU, ?_, hcU, hUr⟩
  intro y hy
  rcases Set.mem_iUnion.mp hy with ⟨x, hy⟩
  rcases Set.mem_iUnion.mp hy with ⟨hx, hy⟩
  apply htU
  apply Set.mem_iUnion_of_mem x
  apply Set.mem_iUnion_of_mem (hst hx)
  exact hy

/-- **LIBRARY, compact-set chart thickening (estimated 180--260 lines).**
In a connected noncompact Hausdorff second-countable one-manifold, every
compact set lies in an open interval chart with compact closure.  Extend the
finitely many local charts meeting the compact set along the unique chart
chain; Hausdorffness prevents branching, connectedness prevents a missed
component, and noncompactness prevents the chain closing into a circle.  The
line with two origins fails Hausdorffness, the long line fails second
countability, a circle fails noncompactness, and two lines fail connectedness.
This is smaller than classification because it only controls one prescribed
compact subset. -/
theorem apm_t95j06_compact_subset_interval_neighborhood
    (X : Type) [TopologicalSpace X] [ConnectedSpace X] [NoncompactSpace X]
    [T2Space X] [SecondCountableTopology X]
    (hloc : apm_t95j06_IsLocallyRealLine X)
    (K : Set X) (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧
      Nonempty (U ≃ₜ ℝ) := by
  classical
  choose A hAopen hxA hAcompact hAreal using
    fun x => apm_t95j06_locallyRealLine_relativelyCompact_chart X hloc x
  have hcover : K ⊆ ⋃ x, A x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨x, hxA x⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover A hAopen hcover
  obtain ⟨U, hUopen, hsU, hUcompact, hUreal⟩ :=
    apm_t95j06_finite_intervalCharts_thicken
      X hloc A hAopen hxA hAcompact hAreal s
  exact ⟨U, hUopen, hs.trans hsU, hUcompact, hUreal⟩

/-- A countable compact cover, together with compact-set interval thickening,
can be reorganized as nested interval domains (estimated 100--160 lines).
Recursively thicken `closure (U n) ∪ K (n+1)`; compactness supplies the next
input and dependent choice supplies the sequence.  This lemma is purely the
exhaustion bookkeeping and assumes the geometric thickening operation. -/
theorem apm_t95j06_nested_interval_exhaustion
    (X : Type) [TopologicalSpace X]
    (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (hcover : (⋃ n, K n) = Set.univ)
    (hthicken : ∀ C : Set X, IsCompact C →
      ∃ U : Set X, IsOpen U ∧ C ⊆ U ∧ IsCompact (closure U) ∧
        Nonempty (U ≃ₜ ℝ)) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧
      (∀ n, closure (U n) ⊆ U (n + 1)) ∧
      (∀ n, Nonempty (U n ≃ₜ ℝ)) ∧ (⋃ n, U n) = Set.univ := by
  classical
  let Good (n : ℕ) (U : Set X) : Prop :=
    IsOpen U ∧ K n ⊆ U ∧ IsCompact (closure U) ∧ Nonempty (U ≃ₜ ℝ)
  obtain ⟨U0, hU0o, hK0U0, hU0c, hU0r⟩ := hthicken (K 0) (hK 0)
  have init : {U : Set X // Good 0 U} :=
    ⟨U0, hU0o, hK0U0, hU0c, hU0r⟩
  let next : ∀ n : ℕ, {U : Set X // Good n U} →
      {V : Set X // Good (n + 1) V} := fun n prev ↦ by
    let C := closure (prev : Set X) ∪ K (n + 1)
    have hC : IsCompact C := prev.property.2.2.1.union (hK (n + 1))
    let V := (hthicken C hC).choose
    have hV := (hthicken C hC).choose_spec
    exact ⟨V, hV.1, (Set.subset_union_right.trans hV.2.1), hV.2.2.1, hV.2.2.2⟩
  have next_nests : ∀ n (prev : {U : Set X // Good n U}),
      closure (prev : Set X) ⊆ (next n prev : Set X) := by
    intro n prev
    dsimp only [next]
    exact Set.subset_union_left.trans
      (hthicken (closure (prev : Set X) ∪ K (n + 1))
        (prev.property.2.2.1.union (hK (n + 1)))).choose_spec.2.1
  let data : ∀ n : ℕ, {U : Set X // Good n U} := fun n ↦
    Nat.rec init (fun n prev ↦ next n prev) n
  let U : ℕ → Set X := fun n ↦ (data n).val
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (data n).property.1
  · intro n
    simpa [U, data] using next_nests n (data n)
  · intro n
    exact (data n).property.2.2.2
  · apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← hcover]
    exact Set.iUnion_mono fun n ↦ (data n).property.2.1

/-- **LIBRARY, coherent interval union (estimated 180--260 lines).**  A
Hausdorff space exhausted by open copies of `ℝ`, each one's closure lying in
the next, is homeomorphic to `ℝ`.  Reparameterize successive interval charts
so they agree on an expanding compact interval, then glue them; the closure
nesting makes the glued map continuous in both directions.  Countability of
the exhaustion excludes the long-line phenomenon, and Hausdorffness excludes
the two-origin gluing.  This is a gluing theorem for an already supplied
exhaustion, not a one-manifold classification. -/
lemma apm_t95j06_increasing_interval_union_mono
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X)
    (hnested : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∀ n, U n ⊆ U (n + 1) := by
  intro n
  exact subset_closure.trans (hnested n)

/-- Every point of the exhausted space lies in some interval domain.  This
is the pointwise form of the union hypothesis used when defining a glued
coordinate function. -/
lemma apm_t95j06_increasing_interval_union_mem
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hcover : (⋃ n, U n) = Set.univ) (x : X) :
    ∃ n, x ∈ U n := by
  have hx : x ∈ ⋃ n, U n := by rw [hcover]; trivial
  simpa only [Set.mem_iUnion] using hx

/-- An increasing exhaustion by open real lines makes the ambient space
connected.  Each stage is connected, consecutive stages meet, and the union
is the whole space. -/
lemma apm_t95j06_increasing_interval_union_connected_aux
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) : ConnectedSpace X := by
  have hconn : ∀ n, IsConnected (U n) := by
    intro n
    obtain ⟨e⟩ := hreal n
    have hsub : _root_.IsConnected (Set.univ : Set (U n)) := by
      rw [← e.isConnected_image]
      simpa using (isConnected_univ : _root_.IsConnected (Set.univ : Set ℝ))
    simpa using hsub.image (Subtype.val : U n → X)
      continuous_subtype_val.continuousOn
  have hmeet : ∀ n, ((U n) ∩ (U (n + 1))).Nonempty := by
    intro n
    obtain ⟨e⟩ := hreal n
    let z : U n := e.symm 0
    exact ⟨z.1, z.2,
      apm_t95j06_increasing_interval_union_mono X U hnested n z.2⟩
  apply connectedSpace_iff_univ.mpr
  rw [← hcover]
  exact _root_.IsConnected.iUnion_of_chain hconn hmeet

/-- A countable open cover by copies of the real line gives a second-countable
ambient topology. -/
lemma apm_t95j06_increasing_interval_union_secondCountable_aux
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) : SecondCountableTopology X := by
  let stageSCT (n : ℕ) : SecondCountableTopology (U n) := by
    obtain ⟨e⟩ := hreal n
    exact e.secondCountableTopology
  letI (n : ℕ) : SecondCountableTopology (U n) := stageSCT n
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hopen hcover

/-- The supplied exhaustion is itself an interval atlas: every point lies in
one of the open real-line stages. -/
lemma apm_t95j06_increasing_interval_union_locallyReal_aux
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) :
    apm_t95j06_IsLocallyRealLine X := by
  intro x
  obtain ⟨n, hxn⟩ :=
    apm_t95j06_increasing_interval_union_mem X U hcover x
  obtain ⟨e⟩ := hreal n
  exact ⟨U n, hopen n, hxn, Set.range e, e.isOpenEmbedding.isOpen_range,
    ⟨e.isEmbedding.toHomeomorph⟩⟩

/-- In arbitrary real coordinates on two nested stages, the coordinate form
of the inclusion is either strictly increasing or strictly decreasing.  This
is the orientation choice used when constructing the compatible global order.
It follows because the subtype inclusion is continuous and injective and a
continuous injective real function is strictly monotone or antitone. -/
lemma apm_t95j06_increasing_interval_union_transition_oriented_aux
    (X : Type) [TopologicalSpace X]
    (U V : Set X) (hUV : U ⊆ V)
    (eU : U ≃ₜ ℝ) (eV : V ≃ₜ ℝ) :
    let j : U → V := fun x => ⟨x.1, hUV x.2⟩
    let g : ℝ → ℝ := fun r => eV (j (eU.symm r))
    StrictMono g ∨ StrictAnti g := by
  dsimp only
  let j : U → V := fun x => ⟨x.1, hUV x.2⟩
  have hjc : Continuous j := Continuous.subtype_mk continuous_subtype_val _
  have hji : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : V => (z : X)) hxy
  let g : ℝ → ℝ := fun r => eV (j (eU.symm r))
  have hgc : Continuous g :=
    eV.continuous.comp (hjc.comp eU.symm.continuous)
  have hgi : Function.Injective g :=
    eV.injective.comp (hji.comp eU.symm.injective)
  exact hgc.strictMono_of_inj hgi

/-- After fixing the orientation of the smaller-stage coordinate, the
larger-stage coordinate can be oriented so that the inclusion is strictly
increasing.  If its arbitrary coordinate is decreasing, postcompose it with
the real negation homeomorphism.  This is the successor step for the
orientation-corrected chart recursion. -/
lemma apm_t95j06_increasing_interval_union_transition_corrected_aux
    (X : Type) [TopologicalSpace X]
    (U V : Set X) (hUV : U ⊆ V)
    (eU : U ≃ₜ ℝ) (eV : V ≃ₜ ℝ) :
    ∃ eV' : V ≃ₜ ℝ,
      let j : U → V := fun x => ⟨x.1, hUV x.2⟩
      StrictMono (fun r : ℝ => eV' (j (eU.symm r))) := by
  rcases apm_t95j06_increasing_interval_union_transition_oriented_aux
      X U V hUV eU eV with hinc | hdec
  · exact ⟨eV, hinc⟩
  · let eV' : V ≃ₜ ℝ := eV.trans (Homeomorph.neg ℝ)
    refine ⟨eV', ?_⟩
    dsimp only
    intro a b hab
    change -eV ⟨(eU.symm a).1, hUV (eU.symm a).2⟩ <
      -eV ⟨(eU.symm b).1, hUV (eU.symm b).2⟩
    exact neg_lt_neg (hdec hab)

/-- Orientation-corrected real coordinates on every stage of the exhaustion.
The successor coordinate is selected by
`transition_corrected_aux`, so all consecutive coordinate inclusions point in
the increasing direction. -/
noncomputable def apm_t95j06_increasing_interval_union_orientedCharts
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ)) :
    (n : ℕ) → U n ≃ₜ ℝ
  | 0 => Classical.choice (hreal 0)
  | n + 1 =>
      Classical.choose
        (apm_t95j06_increasing_interval_union_transition_corrected_aux
          X (U n) (U (n + 1))
          (apm_t95j06_increasing_interval_union_mono X U hnested n)
          (apm_t95j06_increasing_interval_union_orientedCharts
            X U hnested hreal n)
          (Classical.choice (hreal (n + 1))))

/-- Consecutive orientation-corrected charts have a strictly increasing
coordinate transition. -/
lemma apm_t95j06_increasing_interval_union_orientedCharts_step_strictMono
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ)) (n : ℕ) :
    let ψ := apm_t95j06_increasing_interval_union_orientedCharts
      X U hnested hreal
    let j : U n → U (n + 1) := fun x =>
      ⟨x.1, apm_t95j06_increasing_interval_union_mono X U hnested n x.2⟩
    StrictMono (fun r : ℝ => ψ (n + 1) (j ((ψ n).symm r))) := by
  dsimp only
  exact Classical.choose_spec
    (apm_t95j06_increasing_interval_union_transition_corrected_aux
      X (U n) (U (n + 1))
      (apm_t95j06_increasing_interval_union_mono X U hnested n)
      (apm_t95j06_increasing_interval_union_orientedCharts X U hnested hreal n)
      (Classical.choice (hreal (n + 1))))

/-- The local strict orders induced by two consecutive corrected charts agree
on the smaller stage. -/
lemma apm_t95j06_increasing_interval_union_orientedCharts_step_iff
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ)) (n : ℕ) (x y : U n) :
    let ψ := apm_t95j06_increasing_interval_union_orientedCharts
      X U hnested hreal
    ψ n x < ψ n y ↔
      ψ (n + 1)
          ⟨x.1, apm_t95j06_increasing_interval_union_mono X U hnested n x.2⟩ <
        ψ (n + 1)
          ⟨y.1, apm_t95j06_increasing_interval_union_mono X U hnested n y.2⟩ := by
  dsimp only
  let ψ := apm_t95j06_increasing_interval_union_orientedCharts
    X U hnested hreal
  let j : U n → U (n + 1) := fun z =>
    ⟨z.1, apm_t95j06_increasing_interval_union_mono X U hnested n z.2⟩
  have hmono : StrictMono (fun r : ℝ => ψ (n + 1) (j ((ψ n).symm r))) :=
    apm_t95j06_increasing_interval_union_orientedCharts_step_strictMono
      X U hnested hreal n
  have hh :
      ψ (n + 1) (j ((ψ n).symm (ψ n x))) <
          ψ (n + 1) (j ((ψ n).symm (ψ n y))) ↔
        ψ n x < ψ n y := hmono.lt_iff_lt
  simpa [ψ, j] using hh.symm

/-- Earlier stages are contained in every later stage, not only in their
immediate successor. -/
lemma apm_t95j06_increasing_interval_union_mono_of_le
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    {n m : ℕ} (hnm : n ≤ m) : U n ⊆ U m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      exact fun _ hx =>
        apm_t95j06_increasing_interval_union_mono X U hnested (n + k)
          (ih (Nat.le_add_right n k) hx)

/-- The `n`th corrected coordinate, extended by zero away from its stage.
The off-stage value is irrelevant; it lets comparison lemmas be stated on the
ambient type and eliminates iterated subtype transports. -/
noncomputable def apm_t95j06_increasing_interval_union_coordinate
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ)) (n : ℕ) (x : X) : ℝ := by
  classical
  exact if hx : x ∈ U n then
      apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal n ⟨x, hx⟩
    else 0

/-- Corrected coordinate comparisons are independent of the chosen later
stage.  Induction on the gap reduces the successor case to
`orientedCharts_step_iff`; the ambient coordinate wrapper avoids transporting
the same points through a tower of subtype inclusions. -/
lemma apm_t95j06_increasing_interval_union_coordinate_gap_iff
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    {n m : ℕ} (hnm : n ≤ m) {x y : X} (hx : x ∈ U n) (hy : y ∈ U n) :
    apm_t95j06_increasing_interval_union_coordinate X U hnested hreal n x <
        apm_t95j06_increasing_interval_union_coordinate X U hnested hreal n y ↔
      apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m x <
        apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => rfl
  | succ k ih =>
      have hxk : x ∈ U (n + k) :=
        apm_t95j06_increasing_interval_union_mono_of_le X U hnested
          (Nat.le_add_right n k) hx
      have hyk : y ∈ U (n + k) :=
        apm_t95j06_increasing_interval_union_mono_of_le X U hnested
          (Nat.le_add_right n k) hy
      have hxks : x ∈ U (n + k + 1) :=
        apm_t95j06_increasing_interval_union_mono X U hnested (n + k) hxk
      have hyks : y ∈ U (n + k + 1) :=
        apm_t95j06_increasing_interval_union_mono X U hnested (n + k) hyk
      rw [ih (Nat.le_add_right n k)]
      rw [show n + (k + 1) = n + k + 1 by omega]
      simp only [apm_t95j06_increasing_interval_union_coordinate,
        dif_pos hxk, dif_pos hyk, dif_pos hxks, dif_pos hyks]
      change
        apm_t95j06_increasing_interval_union_orientedCharts
              X U hnested hreal (n + k) ⟨x, hxk⟩ <
            apm_t95j06_increasing_interval_union_orientedCharts
              X U hnested hreal (n + k) ⟨y, hyk⟩ ↔
          apm_t95j06_increasing_interval_union_orientedCharts
              X U hnested hreal (n + k + 1) ⟨x, hxks⟩ <
            apm_t95j06_increasing_interval_union_orientedCharts
              X U hnested hreal (n + k + 1) ⟨y, hyks⟩
      exact apm_t95j06_increasing_interval_union_orientedCharts_step_iff
        X U hnested hreal (n + k) ⟨x, hxk⟩ ⟨y, hyk⟩

/-- The least exhaustion stage containing a point. -/
noncomputable def apm_t95j06_increasing_interval_union_stage
    (X : Type) [TopologicalSpace X] (U : ℕ → Set X)
    (hcover : (⋃ n, U n) = Set.univ) (x : X) : ℕ := by
  classical
  exact Nat.find (apm_t95j06_increasing_interval_union_mem X U hcover x)

lemma apm_t95j06_increasing_interval_union_stage_mem
    (X : Type) [TopologicalSpace X] (U : ℕ → Set X)
    (hcover : (⋃ n, U n) = Set.univ) (x : X) :
    x ∈ U (apm_t95j06_increasing_interval_union_stage X U hcover x) := by
  classical
  exact Nat.find_spec (apm_t95j06_increasing_interval_union_mem X U hcover x)

/-- The global strict relation compares two points in the corrected chart of
the larger of their least containing stages. -/
noncomputable def apm_t95j06_increasing_interval_union_lt
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (x y : X) : Prop :=
  let M := max
    (apm_t95j06_increasing_interval_union_stage X U hcover x)
    (apm_t95j06_increasing_interval_union_stage X U hcover y)
  apm_t95j06_increasing_interval_union_coordinate X U hnested hreal M x <
    apm_t95j06_increasing_interval_union_coordinate X U hnested hreal M y

/-- The global comparison can be read in every stage containing both points.
Compare its defining stage and the requested stage through their maximum and
apply coordinate gap-independence twice. -/
lemma apm_t95j06_increasing_interval_union_lt_iff
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) {x y : X} (m : ℕ)
    (hx : x ∈ U m) (hy : y ∈ U m) :
    apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover x y ↔
      apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m x <
        apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m y := by
  let sx := apm_t95j06_increasing_interval_union_stage X U hcover x
  let sy := apm_t95j06_increasing_interval_union_stage X U hcover y
  let M := max sx sy
  let K := max M m
  have hxs : x ∈ U sx :=
    apm_t95j06_increasing_interval_union_stage_mem X U hcover x
  have hys : y ∈ U sy :=
    apm_t95j06_increasing_interval_union_stage_mem X U hcover y
  have hxM : x ∈ U M :=
    apm_t95j06_increasing_interval_union_mono_of_le X U hnested
      (le_max_left sx sy) hxs
  have hyM : y ∈ U M :=
    apm_t95j06_increasing_interval_union_mono_of_le X U hnested
      (le_max_right sx sy) hys
  have hMK := apm_t95j06_increasing_interval_union_coordinate_gap_iff
    X U hnested hreal (le_max_left M m) hxM hyM
  have hmK := apm_t95j06_increasing_interval_union_coordinate_gap_iff
    X U hnested hreal (le_max_right M m) hx hy
  exact hMK.trans hmK.symm

lemma apm_t95j06_increasing_interval_union_lt_irrefl
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (x : X) :
    ¬ apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover x x := by
  simp [apm_t95j06_increasing_interval_union_lt]

lemma apm_t95j06_increasing_interval_union_lt_trans
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) {x y z : X}
    (hxy : apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover x y)
    (hyz : apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover y z) :
    apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover x z := by
  let m := max
    (apm_t95j06_increasing_interval_union_stage X U hcover x)
    (max (apm_t95j06_increasing_interval_union_stage X U hcover y)
      (apm_t95j06_increasing_interval_union_stage X U hcover z))
  have hx : x ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_left _ _) (apm_t95j06_increasing_interval_union_stage_mem X U hcover x)
  have hy : y ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested ((le_max_left _ _).trans (le_max_right _ _))
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover y)
  have hz : z ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested ((le_max_right _ _).trans (le_max_right _ _))
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover z)
  rw [apm_t95j06_increasing_interval_union_lt_iff X U hnested hreal hcover m hx hy] at hxy
  rw [apm_t95j06_increasing_interval_union_lt_iff X U hnested hreal hcover m hy hz] at hyz
  rw [apm_t95j06_increasing_interval_union_lt_iff X U hnested hreal hcover m hx hz]
  exact hxy.trans hyz

lemma apm_t95j06_increasing_interval_union_lt_trichotomous
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (x y : X) :
    apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover x y ∨
      x = y ∨
      apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover y x := by
  let sx := apm_t95j06_increasing_interval_union_stage X U hcover x
  let sy := apm_t95j06_increasing_interval_union_stage X U hcover y
  let M := max sx sy
  have hxM : x ∈ U M := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_left sx sy)
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover x)
  have hyM : y ∈ U M := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_right sx sy)
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover y)
  let c := apm_t95j06_increasing_interval_union_coordinate X U hnested hreal
  rcases lt_trichotomy (c M x) (c M y) with hlt | heq | hgt
  · exact Or.inl hlt
  · right; left
    have heq' :
        apm_t95j06_increasing_interval_union_orientedCharts
            X U hnested hreal M ⟨x, hxM⟩ =
          apm_t95j06_increasing_interval_union_orientedCharts
            X U hnested hreal M ⟨y, hyM⟩ := by
      simpa [c, apm_t95j06_increasing_interval_union_coordinate, hxM, hyM] using heq
    have hsub :=
      (apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal M).injective heq'
    exact congrArg (fun z : U M => (z : X)) hsub
  · exact Or.inr (Or.inr
      ((apm_t95j06_increasing_interval_union_lt_iff
        X U hnested hreal hcover M hyM hxM).2 hgt))

/-- The linear order induced by the compatible corrected stage coordinates. -/
noncomputable def apm_t95j06_increasing_interval_union_linearOrder
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) : LinearOrder X := by
  classical
  let r := apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover
  letI : IsStrictTotalOrder X r := {
    irrefl := apm_t95j06_increasing_interval_union_lt_irrefl
      X U hnested hreal hcover
    trans := @apm_t95j06_increasing_interval_union_lt_trans
      X _ U hnested hreal hcover
    trichotomous := fun a b hab hba => by
      rcases apm_t95j06_increasing_interval_union_lt_trichotomous
          X U hnested hreal hcover a b with h | h | h
      · exact (hab h).elim
      · exact h
      · exact (hba h).elim }
  exact linearOrderOfSTO r

lemma apm_t95j06_increasing_interval_union_linearOrder_lt_iff
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (x y : X) :
    @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
      X U hnested hreal hcover).toLT x y ↔
      apm_t95j06_increasing_interval_union_lt X U hnested hreal hcover x y := by
  rfl

/-- On every exhaustion stage, its corrected coordinate is strictly monotone
for the global linear order. -/
lemma apm_t95j06_increasing_interval_union_coordinate_strictMonoOn
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) :
    @StrictMonoOn X ℝ
      (apm_t95j06_increasing_interval_union_linearOrder
        X U hnested hreal hcover).toPreorder inferInstance
      (apm_t95j06_increasing_interval_union_coordinate
        X U hnested hreal m) (U m) := by
  intro x hx y hy hxy
  have hglobal :
      apm_t95j06_increasing_interval_union_lt
        X U hnested hreal hcover x y :=
    (apm_t95j06_increasing_interval_union_linearOrder_lt_iff
      X U hnested hreal hcover x y).1 hxy
  exact (apm_t95j06_increasing_interval_union_lt_iff
    X U hnested hreal hcover m hx hy).1 hglobal

/-- Every exhaustion stage is convex for the global order: a point strictly
between two points of the stage belongs to the stage. -/
lemma apm_t95j06_increasing_interval_union_stage_orderConvex
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ)
    {x y z : X} (hx : x ∈ U m) (hz : z ∈ U m)
    (hxy : @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
      X U hnested hreal hcover).toLT x y)
    (hyz : @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
      X U hnested hreal hcover).toLT y z) :
    y ∈ U m := by
  let sy := apm_t95j06_increasing_interval_union_stage X U hcover y
  let k := max m sy
  have hmk : m ≤ k := le_max_left _ _
  have hsyk : sy ≤ k := le_max_right _ _
  have hxk : x ∈ U k :=
    apm_t95j06_increasing_interval_union_mono_of_le X U hnested hmk hx
  have hzk : z ∈ U k :=
    apm_t95j06_increasing_interval_union_mono_of_le X U hnested hmk hz
  have hyk : y ∈ U k :=
    apm_t95j06_increasing_interval_union_mono_of_le X U hnested hsyk
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover y)
  let em := Classical.choice (hreal m)
  let psik := apm_t95j06_increasing_interval_union_orientedCharts
    X U hnested hreal k
  let q : ℝ → ℝ := fun r ↦ psik ⟨(em.symm r : X),
    apm_t95j06_increasing_interval_union_mono_of_le X U hnested hmk
      (em.symm r).property⟩
  have hq : Continuous q := by
    exact psik.continuous.comp
      ((continuous_subtype_val.comp em.symm.continuous).subtype_mk _)
  have hpre : _root_.IsPreconnected (Set.range q) := isPreconnected_range hq
  have hcx :
      apm_t95j06_increasing_interval_union_coordinate X U hnested hreal k x ∈
        Set.range q := by
    refine ⟨em ⟨x, hx⟩, ?_⟩
    simp [q, em, psik, apm_t95j06_increasing_interval_union_coordinate, hxk]
  have hcz :
      apm_t95j06_increasing_interval_union_coordinate X U hnested hreal k z ∈
        Set.range q := by
    refine ⟨em ⟨z, hz⟩, ?_⟩
    simp [q, em, psik, apm_t95j06_increasing_interval_union_coordinate, hzk]
  have hcxy := (apm_t95j06_increasing_interval_union_lt_iff
    X U hnested hreal hcover k hxk hyk).1
      ((apm_t95j06_increasing_interval_union_linearOrder_lt_iff
        X U hnested hreal hcover x y).1 hxy)
  have hcyz := (apm_t95j06_increasing_interval_union_lt_iff
    X U hnested hreal hcover k hyk hzk).1
      ((apm_t95j06_increasing_interval_union_linearOrder_lt_iff
        X U hnested hreal hcover y z).1 hyz)
  have hcy :
      apm_t95j06_increasing_interval_union_coordinate X U hnested hreal k y ∈
        Set.range q :=
    hpre.Icc_subset hcx hcz ⟨hcxy.le, hcyz.le⟩
  obtain ⟨r, hr⟩ := hcy
  have heq : (em.symm r : X) = y := by
    have heqsub :
        (⟨(em.symm r : X),
          apm_t95j06_increasing_interval_union_mono_of_le X U hnested hmk
            (em.symm r).property⟩ : U k) = ⟨y, hyk⟩ := by
      apply psik.injective
      simpa [q, psik, apm_t95j06_increasing_interval_union_coordinate, hyk]
        using hr
    exact congrArg Subtype.val heqsub
  rw [← heq]
  exact (em.symm r).property

/-- A point outside a stage lies wholly above it or wholly below it in the
global order. -/
lemma apm_t95j06_increasing_interval_union_outside_stage
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) {x : X}
    (hx : x ∉ U m) :
    (∀ y ∈ U m, @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
      X U hnested hreal hcover).toLT y x) ∨
    (∀ y ∈ U m, @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
      X U hnested hreal hcover).toLT x y) := by
  letI : LinearOrder X :=
    apm_t95j06_increasing_interval_union_linearOrder X U hnested hreal hcover
  let e := Classical.choice (hreal m)
  let y₀ : X := e.symm 0
  have hy₀ : y₀ ∈ U m := (e.symm 0).property
  rcases lt_trichotomy y₀ x with hbelow | heq | habove
  · left
    intro y hy
    rcases lt_trichotomy y x with hyx | hyxeq | hxy
    · exact hyx
    · exact (hx (hyxeq ▸ hy)).elim
    · exact (hx (apm_t95j06_increasing_interval_union_stage_orderConvex
        X U hnested hreal hcover m hy₀ hy hbelow hxy)).elim
  · exact (hx (heq ▸ hy₀)).elim
  · right
    intro y hy
    rcases lt_trichotomy x y with hxy | hxyeq | hyx
    · exact hxy
    · exact (hx (hxyeq ▸ hy)).elim
    · exact (hx (apm_t95j06_increasing_interval_union_stage_orderConvex
        X U hnested hreal hcover m hy hy₀ hyx habove)).elim

lemma apm_t95j06_increasing_interval_union_isOpen_Ioi
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (w : X) :
    IsOpen {z : X | @LT.lt X
      (apm_t95j06_increasing_interval_union_linearOrder
        X U hnested hreal hcover).toLT w z} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hwz
  let sw := apm_t95j06_increasing_interval_union_stage X U hcover w
  let sz := apm_t95j06_increasing_interval_union_stage X U hcover z
  let m := max sw sz
  have hw : w ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_left sw sz)
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover w)
  have hz : z ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_right sw sz)
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover z)
  let c := apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m
  have hc : ContinuousOn c (U m) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : (U m).restrict c = fun x : U m =>
        apm_t95j06_increasing_interval_union_orientedCharts X U hnested hreal m x := by
      funext x
      simp only [Set.restrict_apply, c, apm_t95j06_increasing_interval_union_coordinate,
        dif_pos x.2]
    rw [hrestr]
    exact (apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal m).continuous
  refine ⟨U m ∩ c ⁻¹' Set.Ioi (c w), ?_,
    hc.isOpen_inter_preimage (hopen m) isOpen_Ioi, hz, ?_⟩
  · intro y hy
    exact (apm_t95j06_increasing_interval_union_linearOrder_lt_iff
      X U hnested hreal hcover w y).2
      ((apm_t95j06_increasing_interval_union_lt_iff
        X U hnested hreal hcover m hw hy.1).2 hy.2)
  · exact ((apm_t95j06_increasing_interval_union_lt_iff
      X U hnested hreal hcover m hw hz).1
        ((apm_t95j06_increasing_interval_union_linearOrder_lt_iff
          X U hnested hreal hcover w z).1 hwz))

lemma apm_t95j06_increasing_interval_union_isOpen_Iio
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (w : X) :
    IsOpen {z : X | @LT.lt X
      (apm_t95j06_increasing_interval_union_linearOrder
        X U hnested hreal hcover).toLT z w} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hzw
  let sw := apm_t95j06_increasing_interval_union_stage X U hcover w
  let sz := apm_t95j06_increasing_interval_union_stage X U hcover z
  let m := max sw sz
  have hw : w ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_left sw sz)
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover w)
  have hz : z ∈ U m := apm_t95j06_increasing_interval_union_mono_of_le
    X U hnested (le_max_right sw sz)
      (apm_t95j06_increasing_interval_union_stage_mem X U hcover z)
  let c := apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m
  have hc : ContinuousOn c (U m) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : (U m).restrict c = fun x : U m =>
        apm_t95j06_increasing_interval_union_orientedCharts X U hnested hreal m x := by
      funext x
      simp only [Set.restrict_apply, c, apm_t95j06_increasing_interval_union_coordinate,
        dif_pos x.2]
    rw [hrestr]
    exact (apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal m).continuous
  refine ⟨U m ∩ c ⁻¹' Set.Iio (c w), ?_,
    hc.isOpen_inter_preimage (hopen m) isOpen_Iio, hz, ?_⟩
  · intro y hy
    exact (apm_t95j06_increasing_interval_union_linearOrder_lt_iff
      X U hnested hreal hcover y w).2
      ((apm_t95j06_increasing_interval_union_lt_iff
        X U hnested hreal hcover m hy.1 hw).2 hy.2)
  · exact ((apm_t95j06_increasing_interval_union_lt_iff
      X U hnested hreal hcover m hz hw).1
        ((apm_t95j06_increasing_interval_union_linearOrder_lt_iff
          X U hnested hreal hcover z w).1 hzw))

/-- The `m`th bounded order coordinate: arctangent on the stage, and the
corresponding endpoint value on either component of its complement. -/
noncomputable def apm_t95j06_increasing_interval_union_boundedCoordinate
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) (x : X) : ℝ := by
  classical
  exact if x ∈ U m then
      Real.arctan
        (apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m x)
    else if (∀ y ∈ U m,
        @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
          X U hnested hreal hcover).toLT y x) then
      Real.pi / 2
    else
      -(Real.pi / 2)

/-- The bounded coordinate is monotone for the global order. -/
lemma apm_t95j06_increasing_interval_union_boundedCoordinate_monotone
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) :
    @Monotone X ℝ
      (apm_t95j06_increasing_interval_union_linearOrder
        X U hnested hreal hcover).toPreorder inferInstance
      (apm_t95j06_increasing_interval_union_boundedCoordinate
        X U hnested hreal hcover m) := by
  letI : LinearOrder X :=
    apm_t95j06_increasing_interval_union_linearOrder X U hnested hreal hcover
  have hopposite (a : X)
      (ha : ∀ z ∈ U m, z < a) (hb : ∀ z ∈ U m, a < z) : False := by
    let e := Classical.choice (hreal m)
    exact (ha (e.symm 0) (e.symm 0).property).asymm
      (hb (e.symm 0) (e.symm 0).property)
  intro x y hxy
  by_cases hx : x ∈ U m <;> by_cases hy : y ∈ U m
  · rcases hxy.eq_or_lt with h | h
    · subst y; rfl
    · simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx, hy,
        ↓reduceIte]
      exact (Real.arctan_strictMono
        (apm_t95j06_increasing_interval_union_coordinate_strictMonoOn
          X U hnested hreal hcover m hx hy h)).le
  · rcases apm_t95j06_increasing_interval_union_outside_stage
      X U hnested hreal hcover m hy with habove | hbelow
    · simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx, hy,
        if_false, if_pos habove]
      exact (Real.arctan_lt_pi_div_two _).le
    · exact (not_lt_of_ge hxy (hbelow x hx)).elim
  · rcases apm_t95j06_increasing_interval_union_outside_stage
      X U hnested hreal hcover m hx with habove | hbelow
    · exact (not_lt_of_ge hxy (habove y hy)).elim
    · have hnabove : ¬ ∀ z ∈ U m, z < x := fun ha ↦ hopposite x ha hbelow
      simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx, hy,
        if_false, if_true, if_neg hnabove]
      exact (Real.neg_pi_div_two_lt_arctan _).le
  · rcases apm_t95j06_increasing_interval_union_outside_stage
      X U hnested hreal hcover m hx with hxabove | hxbelow
    · have hyabove : ∀ z ∈ U m, z < y := fun z hz ↦
        (hxabove z hz).trans_le hxy
      simp only [apm_t95j06_increasing_interval_union_boundedCoordinate,
        hx, hy, if_false, if_pos hxabove, if_pos hyabove]
      exact le_rfl
    · rcases apm_t95j06_increasing_interval_union_outside_stage
        X U hnested hreal hcover m hy with hyabove | hybelow
      · have hnxabove : ¬ ∀ z ∈ U m, z < x := fun ha ↦ hopposite x ha hxbelow
        simp only [apm_t95j06_increasing_interval_union_boundedCoordinate,
          hx, hy, if_false, if_neg hnxabove, if_pos hyabove]
        exact neg_le_self (div_nonneg Real.pi_pos.le zero_le_two)
      · have hnxabove : ¬ ∀ z ∈ U m, z < x := fun ha ↦ hopposite x ha hxbelow
        have hnyabove : ¬ ∀ z ∈ U m, z < y := fun ha ↦ hopposite y ha hybelow
        simp only [apm_t95j06_increasing_interval_union_boundedCoordinate,
          hx, hy, if_false, if_neg hnxabove, if_neg hnyabove]
        exact le_rfl

/-- On the stage itself, the bounded coordinate is strictly monotone. -/
lemma apm_t95j06_increasing_interval_union_boundedCoordinate_strictMonoOn
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) :
    @StrictMonoOn X ℝ
      (apm_t95j06_increasing_interval_union_linearOrder
        X U hnested hreal hcover).toPreorder inferInstance
      (apm_t95j06_increasing_interval_union_boundedCoordinate
        X U hnested hreal hcover m) (U m) := by
  intro x hx y hy hxy
  simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx, hy,
    ↓reduceIte]
  exact Real.arctan_strictMono
    (apm_t95j06_increasing_interval_union_coordinate_strictMonoOn
      X U hnested hreal hcover m hx hy hxy)

/-- Every bounded coordinate takes values in `[-π/2, π/2]`. -/
lemma apm_t95j06_increasing_interval_union_boundedCoordinate_mem_Icc
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) (x : X) :
    -(Real.pi / 2) ≤
        apm_t95j06_increasing_interval_union_boundedCoordinate
          X U hnested hreal hcover m x ∧
      apm_t95j06_increasing_interval_union_boundedCoordinate
          X U hnested hreal hcover m x ≤ Real.pi / 2 := by
  by_cases hx : x ∈ U m
  · simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx,
      ↓reduceIte]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,
      (Real.arctan_lt_pi_div_two _).le⟩
  · by_cases hside : ∀ y ∈ U m,
        @LT.lt X (apm_t95j06_increasing_interval_union_linearOrder
          X U hnested hreal hcover).toLT y x
    · simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx,
        if_false, if_pos hside]
      exact ⟨neg_le_self (div_nonneg Real.pi_pos.le zero_le_two), le_rfl⟩
    · simp only [apm_t95j06_increasing_interval_union_boundedCoordinate, hx,
        if_false, if_neg hside]
      exact ⟨le_rfl, neg_le_self (div_nonneg Real.pi_pos.le zero_le_two)⟩

/-- A uniformly bounded, geometrically weighted series of continuous real
functions is continuous. -/
lemma apm_t95j06_continuous_geometric_tsum
    (X : Type*) [TopologicalSpace X] (f : ℕ → X → ℝ)
    (hf : ∀ m, Continuous (f m))
    (hbound : ∀ m x, |f m x| ≤ 2) :
    Continuous (fun x ↦ ∑' m : ℕ, (1 / 2 : ℝ) ^ m * f m x) := by
  apply continuous_tsum
  · intro m
    exact (continuous_const.mul (hf m))
  · exact (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)).mul_left 2
  · intro m x
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hbound m x)
      (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) m)

/-- Geometrically weighted monotone coordinates form a strictly monotone
sum as soon as some coordinate strictly separates every ordered pair. -/
lemma apm_t95j06_strictMono_geometric_tsum
    (X : Type*) [LinearOrder X] (f : ℕ → X → ℝ)
    (hmono : ∀ m, Monotone (f m))
    (hsep : ∀ x y, x < y → ∃ m, f m x < f m y)
    (hbound : ∀ m x, |f m x| ≤ 2) :
    StrictMono (fun x ↦ ∑' m : ℕ, (1 / 2 : ℝ) ^ m * f m x) := by
  intro x y hxy
  obtain ⟨m, hm⟩ := hsep x y hxy
  let g : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n * f n x
  let h : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n * f n y
  have hsummable (z : X) : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * f n z) := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)).mul_left 2)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hbound n z)
      (pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n)
  apply Summable.tsum_lt_tsum (i := m)
  · intro n
    exact mul_le_mul_of_nonneg_left (hmono n hxy.le) (pow_nonneg (by norm_num) _)
  · exact mul_lt_mul_of_pos_left hm (pow_pos (by norm_num) _)
  · exact hsummable x
  · exact hsummable y

/-- Each bounded stage coordinate is continuous in the original topology. -/
lemma apm_t95j06_increasing_interval_union_boundedCoordinate_continuous
    (X : Type) [TopologicalSpace X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) (m : ℕ) :
    Continuous (apm_t95j06_increasing_interval_union_boundedCoordinate
      X U hnested hreal hcover m) := by
  letI : LinearOrder X :=
    apm_t95j06_increasing_interval_union_linearOrder X U hnested hreal hcover
  let c := apm_t95j06_increasing_interval_union_coordinate X U hnested hreal m
  let f := apm_t95j06_increasing_interval_union_boundedCoordinate
    X U hnested hreal hcover m
  have hfmono : Monotone f :=
    apm_t95j06_increasing_interval_union_boundedCoordinate_monotone
      X U hnested hreal hcover m
  have hfbounds (z : X) : -(Real.pi / 2) ≤ f z ∧ f z ≤ Real.pi / 2 :=
    apm_t95j06_increasing_interval_union_boundedCoordinate_mem_Icc
      X U hnested hreal hcover m z
  have hc : ContinuousOn c (U m) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : (U m).restrict c = fun x : U m =>
        apm_t95j06_increasing_interval_union_orientedCharts
          X U hnested hreal m x := by
      funext x
      simp only [Set.restrict_apply, c,
        apm_t95j06_increasing_interval_union_coordinate, dif_pos x.2]
    rw [hrestr]
    exact (apm_t95j06_increasing_interval_union_orientedCharts
      X U hnested hreal m).continuous
  have hfstage : ContinuousOn f (U m) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : (U m).restrict f = fun x : U m => Real.arctan (c x) := by
      funext x
      simp [Set.restrict_apply, f, c,
        apm_t95j06_increasing_interval_union_boundedCoordinate, x.2]
    rw [hrestr]
    exact Real.continuous_arctan.comp
      (continuousOn_iff_continuous_restrict.mp hc)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U m
  · exact hfstage.continuousAt (hopen m |>.mem_nhds hx)
  rcases apm_t95j06_increasing_interval_union_outside_stage
      X U hnested hreal hcover m hx with habove | hbelow
  · have hfx : f x = Real.pi / 2 := by
      simp only [f, apm_t95j06_increasing_interval_union_boundedCoordinate,
        hx, if_false, if_pos habove]
    change Filter.Tendsto f (nhds x) (nhds (f x))
    rw [hfx]
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      let q := max ((a + Real.pi / 2) / 2) 0
      have haq : a < q := by
        have : a < (a + Real.pi / 2) / 2 := by linarith
        exact this.trans_le (le_max_left _ _)
      have hqlo : -(Real.pi / 2) < q := by
        exact (neg_lt_zero.mpr (div_pos Real.pi_pos zero_lt_two)).trans_le
          (le_max_right _ _)
      have hqhi : q < Real.pi / 2 := by
        apply max_lt
        · linarith
        · exact div_pos Real.pi_pos zero_lt_two
      let T := Real.tan q
      let e := apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal m
      let w : X := e.symm T
      have hw : w ∈ U m := (e.symm T).property
      have hcw : c w = T := by
        simp [c, w, T, e, apm_t95j06_increasing_interval_union_coordinate]
      have hfw : f w = q := by
        simp only [f, apm_t95j06_increasing_interval_union_boundedCoordinate,
          hw, if_true]
        change Real.arctan (c w) = q
        rw [hcw]
        dsimp only [T]
        exact Real.arctan_tan hqlo hqhi
      have hwx : w < x := habove w hw
      have hnhds : {z : X | w < z} ∈ nhds x :=
        (apm_t95j06_increasing_interval_union_isOpen_Ioi
          X U hopen hnested hreal hcover w).mem_nhds hwx
      filter_upwards [hnhds] with z hz
      exact haq.trans_le (hfw ▸ hfmono hz.le)
    · intro b hb
      filter_upwards [] with z
      exact (hfbounds z).2.trans_lt hb
  · have hnabove : ¬ ∀ y ∈ U m, y < x := by
      intro ha
      let e := apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal m
      exact (ha (e.symm 0) (e.symm 0).property).asymm
        (hbelow (e.symm 0) (e.symm 0).property)
    have hfx : f x = -(Real.pi / 2) := by
      simp only [f, apm_t95j06_increasing_interval_union_boundedCoordinate,
        hx, if_false, if_neg hnabove]
    change Filter.Tendsto f (nhds x) (nhds (f x))
    rw [hfx]
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [] with z
      exact ha.trans_le (hfbounds z).1
    · intro b hb
      let q := min ((-(Real.pi / 2) + b) / 2) 0
      have hqlo : -(Real.pi / 2) < q := by
        apply lt_min
        · linarith
        · exact neg_lt_zero.mpr (div_pos Real.pi_pos zero_lt_two)
      have hqb : q < b := by
        have : (-(Real.pi / 2) + b) / 2 < b := by linarith
        exact (min_le_left _ _).trans_lt this
      have hqhi : q < Real.pi / 2 :=
        (min_le_right _ _).trans_lt (div_pos Real.pi_pos zero_lt_two)
      let T := Real.tan q
      let e := apm_t95j06_increasing_interval_union_orientedCharts
        X U hnested hreal m
      let w : X := e.symm T
      have hw : w ∈ U m := (e.symm T).property
      have hcw : c w = T := by
        simp [c, w, T, e, apm_t95j06_increasing_interval_union_coordinate]
      have hfw : f w = q := by
        simp only [f, apm_t95j06_increasing_interval_union_boundedCoordinate,
          hw, if_true]
        change Real.arctan (c w) = q
        rw [hcw]
        dsimp only [T]
        exact Real.arctan_tan hqlo hqhi
      have hxw : x < w := hbelow w hw
      have hnhds : {z : X | z < w} ∈ nhds x :=
        (apm_t95j06_increasing_interval_union_isOpen_Iio
          X U hopen hnested hreal hcover w).mem_nhds hxw
      filter_upwards [hnhds] with z hz
      exact (hfmono hz.le).trans_lt (hfw ▸ hqb)

theorem apm_t95j06_increasing_interval_union_homeomorph_real
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) :
    Nonempty (X ≃ₜ ℝ) := by
  haveI : ConnectedSpace X :=
    apm_t95j06_increasing_interval_union_connected_aux X U hnested hreal hcover
  haveI : SecondCountableTopology X :=
    apm_t95j06_increasing_interval_union_secondCountable_aux
      X U hopen hreal hcover
  have hloc : apm_t95j06_IsLocallyRealLine X :=
    apm_t95j06_increasing_interval_union_locallyReal_aux
      X U hopen hreal hcover
  sorry

/-- **LIBRARY, open one-manifold classification (estimated 300--400 lines).**
A connected noncompact Hausdorff second-countable locally-real-line space is
`ℝ`. Extend an oriented chart through a countable locally finite interval
atlas; connectedness gives one chain and noncompactness makes both coordinate
ends unbounded. Second countability excludes the long line, Hausdorffness the
two-origin line, local charts a ray, and noncompactness a circle. -/
theorem apm_t95j06_connected_noncompact_locallyRealLine_homeomorph_real
    (X : Type) (tX : TopologicalSpace X)
    (hconn : @ConnectedSpace X tX) (hnc : @NoncompactSpace X tX)
    (h2 : @T2Space X tX) (hsc : @SecondCountableTopology X tX)
    (hloc : @apm_t95j06_IsLocallyRealLine X tX) :
    Nonempty (@Homeomorph X ℝ tX inferInstance) := by
  letI : TopologicalSpace X := tX
  letI : ConnectedSpace X := hconn
  letI : NoncompactSpace X := hnc
  letI : T2Space X := h2
  letI : SecondCountableTopology X := hsc
  obtain ⟨K, hK, hcover⟩ :=
    apm_t95j06_locallyRealLine_compact_cover X hloc
  have hthicken : ∀ C : Set X, IsCompact C →
      ∃ U : Set X, IsOpen U ∧ C ⊆ U ∧ IsCompact (closure U) ∧
        Nonempty (U ≃ₜ ℝ) := by
    intro C hC
    exact apm_t95j06_compact_subset_interval_neighborhood X hloc C hC
  obtain ⟨U, hopen, hnested, hreal, hUcover⟩ :=
    apm_t95j06_nested_interval_exhaustion X K hK hcover hthicken
  exact apm_t95j06_increasing_interval_union_homeomorph_real
    X U hopen hnested hreal hUcover

/-- Every connected component of a punctured compact connected one-manifold is
an open noncompact one-manifold and hence is homeomorphic to `ℝ`.

Proof sketch (estimated 90--140 lines): the puncture is open and locally
connected, so `connectedComponent x` is open as well as closed in the
puncture.  It inherits Hausdorffness, second countability (from
`apm_t95j06_compact_locallyRealLine_secondCountable_aux`), and real-line
charts (by
`apm_t95j06_puncture_inherits_oneManifold_aux_openSubtype`).  If it were
compact, its image in the Hausdorff ambient space would be closed; it is also
open, so ambient connectedness would make it all of `B`, contradicting the
missing point.  Apply
`apm_t95j06_connected_noncompact_locallyRealLine_homeomorph_real`.

Counterexample checks: disconnected ambient spaces can have compact
components; the long line shows why second countability is used; the doubled
line shows why Hausdorffness is used; a discrete space fails the local
real-line hypothesis. -/
lemma apm_t95j06_puncture_components_homeomorph_real_aux
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (hconn : @ConnectedSpace B tB)
    (h2 : @T2Space B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) (b : B) :
    ∀ x : {y : B // y ≠ b},
      Nonempty ({y : {z : B // z ≠ b} //
        y ∈ connectedComponent x} ≃ₜ ℝ) := by
  letI : TopologicalSpace B := tB
  letI : CompactSpace B := hc
  letI : ConnectedSpace B := hconn
  letI : T2Space B := h2
  letI : SecondCountableTopology B :=
    apm_t95j06_compact_locallyRealLine_secondCountable_aux B tB hc hloc
  have hlocal : LocallyConnectedSpace B := by
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro z N hN
    obtain ⟨U, hU, hzU, V, hV, ⟨e⟩⟩ := hloc z
    letI : LocallyConnectedSpace V := hV.locallyConnectedSpace
    letI : LocallyConnectedSpace U := e.locallyConnectedSpace
    have hNU : Subtype.val ⁻¹' N ∈ nhds (⟨z, hzU⟩ : U) :=
      (continuous_subtype_val.continuousAt.tendsto hN)
    obtain ⟨W, hWN, hWopen, hzW, hWconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
        (inferInstance : LocallyConnectedSpace U) _ _ hNU
    refine ⟨Subtype.val '' W, ?_,
      hU.isOpenEmbedding_subtypeVal.isOpenMap W hWopen,
      ⟨⟨z, hzU⟩, hzW, rfl⟩, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hWN hw
    · exact hWconn.image _ continuous_subtype_val.continuousOn
  letI : LocallyConnectedSpace B := hlocal
  let P := {y : B // y ≠ b}
  letI : SecondCountableTopology P :=
    TopologicalSpace.secondCountableTopology_induced P B Subtype.val
  have hPopen : IsOpen ({y : B | y ≠ b} : Set B) := isClosed_singleton.isOpen_compl
  letI : LocallyConnectedSpace P := hPopen.locallyConnectedSpace
  intro x
  let C := {y : P // y ∈ connectedComponent x}
  letI : SecondCountableTopology C :=
    TopologicalSpace.secondCountableTopology_induced C P Subtype.val
  have hCopen : IsOpen (connectedComponent x) := isOpen_connectedComponent
  letI : ConnectedSpace C :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  letI : NoncompactSpace C := by
    constructor
    intro hcompact
    letI : CompactSpace C := isCompact_univ_iff.mp hcompact
    let f : C → B := fun y ↦ y.1.1
    have hf : Topology.IsOpenEmbedding f :=
      hPopen.isOpenEmbedding_subtypeVal.comp hCopen.isOpenEmbedding_subtypeVal
    have hrangeCompact : IsCompact (Set.range f) := isCompact_range hf.continuous
    have hrangeClopen : IsClopen (Set.range f) :=
      ⟨hrangeCompact.isClosed, hf.isOpen_range⟩
    have hxrange : f ⟨x, mem_connectedComponent⟩ ∈ Set.range f :=
      Set.mem_range_self _
    have hall : Set.range f = Set.univ := hrangeClopen.eq_univ ⟨_, hxrange⟩
    have hb : b ∈ Set.range f := hall.symm ▸ Set.mem_univ b
    obtain ⟨y, hy⟩ := hb
    exact y.1.2 hy
  have hPloc : apm_t95j06_IsLocallyRealLine P :=
    apm_t95j06_puncture_inherits_oneManifold_aux_openSubtype B hloc _ hPopen
  have hCloc : apm_t95j06_IsLocallyRealLine C :=
    apm_t95j06_puncture_inherits_oneManifold_aux_openSubtype P hPloc _ hCopen
  exact apm_t95j06_connected_noncompact_locallyRealLine_homeomorph_real
    C inferInstance inferInstance inferInstance inferInstance inferInstance hCloc

/- The one-chart end argument: if every connected component of the puncture
is a real line, then the puncture has only one component.

Proof sketch (estimated 110--170 lines): a chart about `b` has two connected
half-intervals.  Under a hypothetical separation, choose the puncture
component `C` meeting one half.  Connected-component openness and closedness
show that `C` meets the chart in exactly that half.  The complement of this
half in `C` is compact because it is the part of the closed set `C ∪ {b}`
outside a smaller chart.  Transporting along `C ≃ₜ ℝ`, a connected open
interval with compact complement must be all of `ℝ`; hence `C` is precisely
the half-chart.  Then `C ∪ {b}` is compact, while its chart image is a
half-open interval, contradiction.

Counterexample checks: for an interval an endpoint puncture is connected but
the endpoint has no real-line chart; for a circle the conclusion holds; a
tripod fails the chart hypothesis; the doubled line fails Hausdorffness; the
long circle fails the component-to-`ℝ` premise. -/
/-- **Real-line end obstruction (estimated 15--25 lines).** A preconnected
subset of `ℝ` whose complement is compact is the whole line.

Why true: compactness bounds the complement above and below. If the subset
were bounded on either side as well, a point beyond both bounds would belong
to neither it nor its complement. Thus it is unbounded in both directions,
and order-convexity of preconnected subsets of `ℝ` fills the whole line. -/
lemma apm_t95j06_puncture_connected_of_components_real_aux_realEnds
    (U : Set ℝ) (hU : _root_.IsPreconnected U) (hUc : IsCompact Uᶜ) :
    U = Set.univ := by
  have hub : ¬ BddAbove U := by
    intro hba
    obtain ⟨a, ha⟩ := hba
    obtain ⟨c, hc⟩ := hUc.bddAbove
    let x : ℝ := max a c + 1
    by_cases hx : x ∈ U
    · have hxle := ha hx
      dsimp [x] at hxle
      linarith [le_max_left a c]
    · have hxc : x ∈ Uᶜ := hx
      have hxle := hc hxc
      dsimp [x] at hxle
      linarith [le_max_right a c]
  have hlb : ¬ BddBelow U := by
    intro hbb
    obtain ⟨a, ha⟩ := hbb
    obtain ⟨c, hc⟩ := hUc.bddBelow
    let x : ℝ := min a c - 1
    by_cases hx : x ∈ U
    · have hxle := ha hx
      dsimp [x] at hxle
      linarith [min_le_left a c]
    · have hxc : x ∈ Uᶜ := hx
      have hxle := hc hxc
      dsimp [x] at hxle
      linarith [min_le_right a c]
  exact hU.eq_univ_of_unbounded hlb hub

/-- **Puncture-component accumulation (estimated 35--55 lines).** Every
connected component of a locally connected puncture of a connected `T₁`
space accumulates at the removed point.

Why true: the component is clopen in the puncture. Its image is open in the
ambient space. If the removed point were outside its closure, closedness in
the puncture would make the image ambient-closed as well, contradicting
connectedness. This is only the component/ambient-closure transport fact; it
does not assert that the puncture is connected. -/
lemma apm_t95j06_puncture_connected_of_components_real_aux_component_accumulates
    (B : Type) [TopologicalSpace B] [ConnectedSpace B] [T1Space B]
    (b : B) [LocallyConnectedSpace {y : B // y ≠ b}]
    (x : {y : B // y ≠ b}) :
    b ∈ closure (Subtype.val '' connectedComponent x) := by
  let P := {y : B // y ≠ b}
  let C : Set P := connectedComponent x
  let f : P → B := Subtype.val
  have hPopen : IsOpen ({y : B | y ≠ b} : Set B) := isClosed_singleton.isOpen_compl
  have hCopen : IsOpen C := isOpen_connectedComponent
  have himgOpen : IsOpen (f '' C) :=
    hPopen.isOpenEmbedding_subtypeVal.isOpenMap C hCopen
  by_contra hbcl
  have himgClosed : IsClosed (f '' C) := by
    rw [← closure_eq_iff_isClosed]
    apply Set.Subset.antisymm
    · intro y hy
      have hyb : y ≠ b := by
        intro hyb
        subst y
        exact hbcl hy
      let yp : P := ⟨y, hyb⟩
      have hyp : yp ∈ closure C := by
        have he := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image C
        rw [he]
        exact hy
      have hypC : yp ∈ C := by
        change yp ∈ connectedComponent x
        rw [← (isClosed_connectedComponent (x := x)).closure_eq]
        exact hyp
      exact ⟨yp, hypC, rfl⟩
    · exact subset_closure
  have hne : (f '' C).Nonempty :=
    ⟨x.1, ⟨x, mem_connectedComponent, rfl⟩⟩
  have hall : f '' C = Set.univ :=
    (show IsClopen (f '' C) from ⟨himgClosed, himgOpen⟩).eq_univ hne
  have hbimg : b ∈ f '' C := hall.symm ▸ Set.mem_univ b
  obtain ⟨y, _, hy⟩ := hbimg
  exact y.2 hy

open Topology Set in
/-- Side contradiction for the puncture argument: a closed puncture component
homeomorphic to `ℝ` cannot meet a neighbourhood of the removed point in only
one open half-chart whose end point lies outside it. -/
lemma apm_t95j06_puncture_connected_of_components_real_aux_side (B : Type) [TopologicalSpace B] [CompactSpace B] (b : B)
    (C : Set {y : B // y ≠ b}) (hCcl : IsClosed C)
    (φ : {y : {z : B // z ≠ b} // y ∈ C} ≃ₜ ℝ)
    (W A : Set B) (hW : IsOpen W) (hbW : b ∈ W)
    (hA : _root_.IsPreconnected A) (hAW : A ⊆ W)
    (hAC : A ⊆ Subtype.val '' C) (hCW : Subtype.val '' C ∩ W ⊆ A)
    (a : B) (hab : a ≠ b) (haA : a ∈ closure A) (ha : a ∉ A) : False := by
  let f : {y : {z : B // z ≠ b} // y ∈ C} → B := fun y => y.1.1
  have hf : IsEmbedding f :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hclC : ∀ y ∈ closure (Subtype.val '' C), y ≠ b → y ∈ Subtype.val '' C := by
    intro y hy hyb
    let yp : {z : B // z ≠ b} := ⟨y, hyb⟩
    have hyp : yp ∈ closure C := by
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image C]
      exact hy
    rw [hCcl.closure_eq] at hyp
    exact ⟨yp, hyp, rfl⟩
  have himg : ∀ s : Set {y : {z : B // z ≠ b} // y ∈ C},
      f '' s = Subtype.val '' C ∩ {y | ∃ p ∈ s, f p = y} := by
    intro s; ext y; constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p.1, p.2, rfl⟩, p, hp, rfl⟩
    · rintro ⟨_, p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  let S : Set {y : {z : B // z ≠ b} // y ∈ C} := {y | f y ∉ W}
  have hSimg : f '' S = Subtype.val '' C ∩ Wᶜ := by
    ext y; constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p.1, p.2, rfl⟩, hp⟩
    · rintro ⟨⟨q, hq, rfl⟩, hyW⟩; exact ⟨⟨q, hq⟩, hyW, rfl⟩
  have hScImg : f '' Sᶜ = A := by
    ext y; constructor
    · rintro ⟨p, hp, rfl⟩
      have : f p ∈ W := by simpa [S] using hp
      exact hCW ⟨⟨p.1, p.2, rfl⟩, this⟩
    · intro hy
      obtain ⟨q, hq, rfl⟩ := hAC hy
      exact ⟨⟨q, hq⟩, by simpa [S] using hAW hy, rfl⟩
  have hScl : IsClosed (Subtype.val '' C ∩ Wᶜ) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have h1 := closure_inter_subset_inter_closure _ _ hy
    rw [hW.isClosed_compl.closure_eq] at h1
    have hyb : y ≠ b := fun e => h1.2 (e ▸ hbW)
    exact ⟨hclC y h1.1 hyb, h1.2⟩
  have hScpt : IsCompact S := by
    rw [hf.isCompact_iff, hSimg]; exact hScl.isCompact
  have hScpre : _root_.IsPreconnected Sᶜ := by
    rw [← hf.isInducing.isPreconnected_image, hScImg]; exact hA
  have hT : φ '' Sᶜ = Set.univ := by
    apply apm_t95j06_puncture_connected_of_components_real_aux_realEnds
    · exact hScpre.image _ φ.continuous.continuousOn
    · rw [← φ.image_compl, compl_compl]; exact hScpt.image φ.continuous
  have hSc : Sᶜ = Set.univ := by
    rw [← Set.image_univ_of_surjective φ.surjective] at hT; exact φ.injective.image_injective hT
  have hCA : Subtype.val '' C ⊆ A := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← hScImg]; exact ⟨⟨q, hq⟩, by rw [hSc]; trivial, rfl⟩
  exact ha (hCA (hclC a (closure_mono (hAC.trans subset_rfl) haA) hab))

open Topology Set in
/-- Chart form of puncture connectedness: with a real chart at the removed
point, every component contains both half-charts, so there is one component. -/
lemma apm_t95j06_puncture_connected_of_components_real_aux_chart (B : Type) [TopologicalSpace B] [CompactSpace B] (b : B)
    (U : Set B) (hU : IsOpen U) (hbU : b ∈ U) (V : Set ℝ) (hV : IsOpen V)
    (h : U ≃ₜ V)
    (hcomp : ∀ x : {y : B // y ≠ b},
      Nonempty ({y : {z : B // z ≠ b} // y ∈ connectedComponent x} ≃ₜ ℝ))
    (hacc : ∀ x : {y : B // y ≠ b},
      b ∈ closure (Subtype.val '' connectedComponent x)) :
    ConnectedSpace {y : B // y ≠ b} := by
  classical
  set t₀ : ℝ := (h ⟨b, hbU⟩ : ℝ) with ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV t₀ (h ⟨b, hbU⟩).2
  set d : ℝ := ε / 2 with hd
  have hd0 : 0 < d := by positivity
  have hsub : ∀ t, t₀ - d ≤ t → t ≤ t₀ + d → t ∈ V := fun t h1 h2 =>
    hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  let I : Set ℝ → Set B := fun s => Subtype.val '' (h ⁻¹' (Subtype.val ⁻¹' s))
  have hImem : ∀ s y, y ∈ I s ↔ ∃ hy : y ∈ U, (h ⟨y, hy⟩ : ℝ) ∈ s := by
    intro s y; constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
    · rintro ⟨hy, hs⟩; exact ⟨⟨y, hy⟩, hs, rfl⟩
  have hIopen : ∀ s, IsOpen s → IsOpen (I s) := fun s hs =>
    hU.isOpenEmbedding_subtypeVal.isOpenMap _
      ((hs.preimage continuous_subtype_val).preimage h.continuous)
  have hIpre : ∀ s, _root_.IsPreconnected s → s ⊆ V → _root_.IsPreconnected (I s) := by
    intro s hs hsV
    have h1 : _root_.IsPreconnected (Subtype.val ⁻¹' s : Set V) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.mpr hsV]
      exact hs
    have h2 : h ⁻¹' (Subtype.val ⁻¹' s) = h.symm '' (Subtype.val ⁻¹' s) :=
      by rw [h.image_symm]
    show _root_.IsPreconnected (Subtype.val '' (h ⁻¹' (Subtype.val ⁻¹' s)))
    rw [h2]
    exact (h1.image _ h.symm.continuous.continuousOn).image _
      continuous_subtype_val.continuousOn
  have hcoord_b : ∀ y (hy : y ∈ U), (h ⟨y, hy⟩ : ℝ) = t₀ → y = b := by
    intro y hy he
    have : h ⟨y, hy⟩ = h ⟨b, hbU⟩ := Subtype.ext he
    exact congrArg Subtype.val (h.injective this)
  -- points
  let pt : ∀ t, t ∈ V → B := fun t ht => (h.symm ⟨t, ht⟩).1
  have hptU : ∀ t ht, pt t ht ∈ U := fun t ht => (h.symm ⟨t, ht⟩).2
  have hptc : ∀ t ht, (h ⟨pt t ht, hptU t ht⟩ : ℝ) = t := by
    intro t ht; simp [pt]
  have hptI : ∀ t ht s, pt t ht ∈ I s ↔ t ∈ s := by
    intro t ht s; rw [hImem]; constructor
    · rintro ⟨hy, hs⟩; rwa [hptc t ht] at hs
    · intro hs; exact ⟨hptU t ht, by rwa [hptc t ht]⟩
  -- closure of a half at an end point
  have hclos : ∀ (lo hi e : ℝ), t₀ - d ≤ lo → lo < hi → hi ≤ t₀ + d →
      ∀ (he : e = lo ∨ e = hi) (heV : e ∈ V),
      pt e heV ∈ closure (I (Ioo lo hi)) := by
    intro lo hi e hlo hlohi hhi he heV
    let J := Icc lo hi
    have hJV : ∀ t ∈ J, t ∈ V := fun t ht => hsub t (by linarith [ht.1]) (by linarith [ht.2])
    let g : J → B := fun t => (h.symm ⟨t.1, hJV t.1 t.2⟩).1
    have hg : Continuous g :=
      continuous_subtype_val.comp (h.symm.continuous.comp
        (continuous_subtype_val.subtype_mk _))
    let Q : Set J := {p | p.1 ∈ Ioo lo hi}
    have heJ : e ∈ J := by rcases he with rfl | rfl <;> constructor <;> linarith
    have hp0 : (⟨e, heJ⟩ : J) ∈ closure Q := by
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      have : Subtype.val '' Q = Ioo lo hi := by
        ext t; constructor
        · rintro ⟨p, hp, rfl⟩; exact hp
        · intro ht; exact ⟨⟨t, Ioo_subset_Icc_self ht⟩, ht, rfl⟩
      show e ∈ closure (Subtype.val '' Q)
      rw [this, closure_Ioo hlohi.ne]; exact heJ
    have h1 := image_closure_subset_closure_image hg ⟨_, hp0, rfl⟩
    refine closure_mono ?_ h1
    rintro _ ⟨p, hp, rfl⟩
    exact (hptI p.1 (hJV p.1 p.2) _).mpr hp
  have hm : t₀ - d ∈ V := hsub _ le_rfl (by linarith)
  have hp : t₀ + d ∈ V := hsub _ (by linarith) le_rfl
  let W := I (Ioo (t₀ - d) (t₀ + d))
  let L := I (Ioo (t₀ - d) t₀)
  let R := I (Ioo t₀ (t₀ + d))
  have hWo : IsOpen W := hIopen _ isOpen_Ioo
  have hbW : b ∈ W := (hImem _ _).mpr ⟨hbU, show t₀ ∈ Ioo (t₀ - d) (t₀ + d) from
    ⟨by linarith, by linarith⟩⟩
  have hLsub : Ioo (t₀ - d) t₀ ⊆ V := fun t ht => hsub t ht.1.le (by linarith [ht.2])
  have hRsub : Ioo t₀ (t₀ + d) ⊆ V := fun t ht => hsub t (by linarith [ht.1]) ht.2.le
  have hLpre := hIpre _ isPreconnected_Ioo hLsub
  have hRpre := hIpre _ isPreconnected_Ioo hRsub
  have hLW : L ⊆ W := fun y hy => by
    obtain ⟨hy, hs⟩ := (hImem _ _).mp hy
    exact (hImem _ _).mpr ⟨hy, hs.1, by linarith [hs.2]⟩
  have hRW : R ⊆ W := fun y hy => by
    obtain ⟨hy, hs⟩ := (hImem _ _).mp hy
    exact (hImem _ _).mpr ⟨hy, by linarith [hs.1], hs.2⟩
  have hbL : ∀ y ∈ L, y ≠ b := by
    intro y hy hyb; subst hyb
    obtain ⟨hy, hs⟩ := (hImem _ _).mp hy
    have : (h ⟨y, hy⟩ : ℝ) = t₀ := rfl
    linarith [hs.2]
  have hbR : ∀ y ∈ R, y ≠ b := by
    intro y hy hyb; subst hyb
    obtain ⟨hy, hs⟩ := (hImem _ _).mp hy
    have : (h ⟨y, hy⟩ : ℝ) = t₀ := rfl
    linarith [hs.1]
  have hsplit : ∀ y ∈ W, y ≠ b → y ∈ L ∨ y ∈ R := by
    intro y hy hyb
    obtain ⟨hyU, hs⟩ := (hImem _ _).mp hy
    rcases lt_trichotomy (h ⟨y, hyU⟩ : ℝ) t₀ with hl | he | hg
    · left; exact (hImem _ _).mpr ⟨hyU, hs.1, hl⟩
    · exact absurd (hcoord_b y hyU he) hyb
    · right; exact (hImem _ _).mpr ⟨hyU, hg, hs.2⟩
  let LP : Set {y : B // y ≠ b} := Subtype.val ⁻¹' L
  let RP : Set {y : B // y ≠ b} := Subtype.val ⁻¹' R
  have hLPimg : Subtype.val '' LP = L := by
    ext y; constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hy; exact ⟨⟨y, hbL y hy⟩, hy, rfl⟩
  have hRPimg : Subtype.val '' RP = R := by
    ext y; constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hy; exact ⟨⟨y, hbR y hy⟩, hy, rfl⟩
  have hLPpre : _root_.IsPreconnected LP := by
    have hh := (IsEmbedding.subtypeVal (p := fun y : B => y ≠ b)).isInducing.isPreconnected_image (s := LP)
    rw [hLPimg] at hh; exact hh.mp hLpre
  have hRPpre : _root_.IsPreconnected RP := by
    have hh := (IsEmbedding.subtypeVal (p := fun y : B => y ≠ b)).isInducing.isPreconnected_image (s := RP)
    rw [hRPimg] at hh; exact hh.mp hRpre
  have hdisj : ∀ (S : Set {y : B // y ≠ b}), _root_.IsPreconnected S →
      ∀ x, ¬ S ⊆ connectedComponent x → ∀ q ∈ S, q ∉ connectedComponent x := by
    intro S hS x hn q hq hqx
    apply hn
    have := hS.subset_connectedComponent hq
    rwa [connectedComponent_eq hqx]
  have hamL : pt (t₀ - d) hm ∉ L := fun hh =>
    lt_irrefl _ ((hptI _ hm _).mp hh).1
  have hapR : pt (t₀ + d) hp ∉ R := fun hh =>
    lt_irrefl _ ((hptI _ hp _).mp hh).2
  have hamb : pt (t₀ - d) hm ≠ b := by
    intro e
    have : pt (t₀ - d) hm ∈ W := by rw [e]; exact hbW
    exact lt_irrefl _ ((hptI _ hm _).mp this).1
  have hapb : pt (t₀ + d) hp ≠ b := by
    intro e
    have : pt (t₀ + d) hp ∈ W := by rw [e]; exact hbW
    exact lt_irrefl _ ((hptI _ hp _).mp this).2
  have hLtoR : ∀ x, LP ⊆ connectedComponent x → RP ⊆ connectedComponent x := by
    intro x hL
    by_contra hR
    obtain ⟨φ⟩ := hcomp x
    refine apm_t95j06_puncture_connected_of_components_real_aux_side B b _ isClosed_connectedComponent φ W L hWo hbW hLpre hLW ?_ ?_
      (pt (t₀ - d) hm) hamb ?_ hamL
    · intro y hy; exact ⟨⟨y, hbL y hy⟩, hL hy, rfl⟩
    · rintro _ ⟨⟨q, hq, rfl⟩, hqW⟩
      rcases hsplit q.1 hqW q.2 with h1 | h1
      · exact h1
      · exact absurd hq (hdisj RP hRPpre x hR q h1)
    · exact hclos (t₀ - d) t₀ (t₀ - d) le_rfl (by linarith) (by linarith) (Or.inl rfl) hm
  have hRtoL : ∀ x, RP ⊆ connectedComponent x → LP ⊆ connectedComponent x := by
    intro x hR
    by_contra hL
    obtain ⟨φ⟩ := hcomp x
    refine apm_t95j06_puncture_connected_of_components_real_aux_side B b _ isClosed_connectedComponent φ W R hWo hbW hRpre hRW ?_ ?_
      (pt (t₀ + d) hp) hapb ?_ hapR
    · intro y hy; exact ⟨⟨y, hbR y hy⟩, hR hy, rfl⟩
    · rintro _ ⟨⟨q, hq, rfl⟩, hqW⟩
      rcases hsplit q.1 hqW q.2 with h1 | h1
      · exact absurd hq (hdisj LP hLPpre x hL q h1)
      · exact h1
    · exact hclos t₀ (t₀ + d) (t₀ + d) (by linarith) (by linarith) le_rfl (Or.inr rfl) hp
  have hboth : ∀ x, LP ⊆ connectedComponent x := by
    intro x
    obtain ⟨y, hyW, ⟨q, hq, rfl⟩⟩ := mem_closure_iff.mp (hacc x) W hWo hbW
    rcases hsplit q.1 hyW q.2 with h1 | h1
    · have := hLPpre.subset_connectedComponent (show q ∈ LP from h1)
      rwa [← connectedComponent_eq hq] at this
    · apply hRtoL
      have := hRPpre.subset_connectedComponent (show q ∈ RP from h1)
      rwa [← connectedComponent_eq hq] at this
  have hmid : t₀ - d / 2 ∈ V := hsub _ (by linarith) (by linarith)
  have hzL : pt _ hmid ∈ L := (hptI _ _ _).mpr ⟨by linarith, by linarith⟩
  let z : {y : B // y ≠ b} := ⟨_, hbL _ hzL⟩
  have hz : z ∈ LP := hzL
  refine connectedSpace_iff_connectedComponent.mpr ⟨z, eq_univ_of_forall fun x => ?_⟩
  rw [← connectedComponent_eq (hboth x hz)]
  exact mem_connectedComponent

/-- If every connected component of the puncture is a real line, the
puncture is connected. -/
lemma apm_t95j06_puncture_connected_of_components_real_aux
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (hconn : @ConnectedSpace B tB)
    (h2 : @T2Space B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) (b : B)
    (hcomponents : ∀ x : {y : B // y ≠ b},
      Nonempty ({y : {z : B // z ≠ b} //
        y ∈ connectedComponent x} ≃ₜ ℝ)) :
    @ConnectedSpace {x : B // x ≠ b} inferInstance := by
  letI : TopologicalSpace B := tB
  haveI : CompactSpace B := hc
  haveI : T2Space B := h2
  have hlc : LocallyConnectedSpace B := by
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro x N hN
    obtain ⟨U, hU, hxU, V, hV, ⟨e⟩⟩ := hloc x
    haveI : LocallyConnectedSpace V := hV.locallyConnectedSpace
    have hUlc : LocallyConnectedSpace U := e.isOpenEmbedding.locallyConnectedSpace
    have hpre : Subtype.val ⁻¹' N ∈ nhds (⟨x, hxU⟩ : U) := continuousAt_subtype_val hN
    obtain ⟨A, hAN, hAo, hxA, hAc⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp hUlc _ _ hpre
    refine ⟨Subtype.val '' A, ?_, hU.isOpenEmbedding_subtypeVal.isOpenMap A hAo,
      ⟨_, hxA, rfl⟩, hAc.image _ continuous_subtype_val.continuousOn⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hAN ha
  haveI := hlc
  haveI : LocallyConnectedSpace {y : B // y ≠ b} :=
    (isOpen_compl_singleton (x := b)).locallyConnectedSpace
  obtain ⟨U, hU, hbU, V, hV, ⟨e⟩⟩ := hloc b
  exact apm_t95j06_puncture_connected_of_components_real_aux_chart B b U hU hbU V hV e
    hcomponents
    (fun x => apm_t95j06_puncture_connected_of_components_real_aux_component_accumulates B b x)

/-- **LIBRARY, puncture connectedness (estimated 180--260 lines).** Removing one
point from a compact connected Hausdorff locally-real-line space leaves a
connected space. A punctured chart has two half-intervals; a separation would
separate the original space after a finite compact chart-chain argument. Use
`isPreconnected_iff_connected` and `Homeomorph.isPreconnected_image`.
Compactness excludes `ℝ \ {0}`, local-line charts exclude wedges, and
Hausdorffness excludes the line with two origins. -/
theorem apm_t95j06_puncture_connected
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (hconn : @ConnectedSpace B tB)
    (h2 : @T2Space B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) (b : B) :
    @ConnectedSpace {x : B // x ≠ b} inferInstance := by
  apply apm_t95j06_puncture_connected_of_components_real_aux
    B tB hc hconn h2 hloc b
  exact apm_t95j06_puncture_components_homeomorph_real_aux
    B tB hc hconn h2 hloc b

/-- Adding one point back to a punctured compact Hausdorff space recovers the
original space (estimated 80--120 lines). Apply
`OnePoint.equivOfIsEmbeddingOfRangeEq` to the subtype inclusion, whose range is
the complement of the removed point. -/
theorem apm_t95j06_onePoint_puncture_homeomorph
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (h2 : @T2Space B tB) (b : B) :
    Nonempty (@Homeomorph (OnePoint {x : B // x ≠ b}) B inferInstance tB) :=
  ⟨OnePoint.equivOfIsEmbeddingOfRangeEq b Subtype.val Topology.IsEmbedding.subtypeVal
    (by ext x; simp)⟩

/-- **LIBRARY 3(b), compact one-manifold classification (estimated 900--1800
lines).**  A compact connected Hausdorff second-countable space locally
homeomorphic to the real line is a circle.

Proof route: build a finite oriented interval atlas, extend one chart
successively through overlapping intervals, and use compactness to make the
two ends meet; Hausdorffness makes the resulting continuous bijection a
homeomorphism.  Search found no existing Mathlib or ConstructionTargets
theorem.  The hypotheses exclude the empty space, a compact interval (endpoint
not locally real), the real line (noncompact), and the long circle (not second
countable). -/
theorem apm_t95j06_compact_connected_locallyRealLine_homeomorph_circle
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (hconn : @ConnectedSpace B tB)
    (h2 : @T2Space B tB) (hsc : @SecondCountableTopology B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) :
    Nonempty (@Homeomorph B Circle tB inferInstance) := by
  letI : CompactSpace B := hc
  letI : ConnectedSpace B := hconn
  letI : T2Space B := h2
  letI : SecondCountableTopology B := hsc
  let b : B := Classical.choice (inferInstance : Nonempty B)
  let P := {x : B // x ≠ b}
  letI : ConnectedSpace P :=
    apm_t95j06_puncture_connected B tB hc hconn h2 hloc b
  obtain ⟨hP2, hPsc, hPloc⟩ :=
    apm_t95j06_puncture_inherits_oneManifold B tB h2 hsc hloc b
  letI : T2Space P := hP2
  letI : SecondCountableTopology P := hPsc
  letI : NoncompactSpace P :=
    apm_t95j06_puncture_noncompact B tB hc hconn h2 hloc b
  obtain ⟨eline⟩ :=
    apm_t95j06_connected_noncompact_locallyRealLine_homeomorph_real
      P inferInstance inferInstance inferInstance inferInstance inferInstance hPloc
  obtain ⟨ecompact⟩ :=
    apm_t95j06_onePoint_puncture_homeomorph B tB hc h2 b
  let e₁ : OnePoint ℝ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let L : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
    Complex.orthonormalBasisOneI.repr.symm
  let e₂ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
    Homeomorph.subtype L.toHomeomorph (by
      intro x
      change x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
        L x ∈ Metric.sphere (0 : ℂ) 1
      simp only [Metric.mem_sphere, dist_zero_right, L.norm_map])
  let erealCircle : OnePoint ℝ ≃ₜ Circle := e₁.trans e₂
  exact ⟨ecompact.symm.trans (eline.onePointCongr.trans erealCircle)⟩

/-- An equivariant local trivialization supplies a continuous local section.
The section is the inverse image of the constant group coordinate `1`; the
fibre-preserving clause of `local_trivial` proves that it lies over its input. -/
lemma apm_t95j06_principalCircleBundle_local_section
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (b : B) :
    ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ s : U → X, Continuous s ∧ ∀ u, P.proj (s u) = u := by
  obtain ⟨U, hU, hb, φ, hφproj, hφact⟩ := P.local_trivial b
  let s : U → X := fun u ↦ (φ.symm (u, 1)).1
  refine ⟨U, hU, hb, s, ?_, ?_⟩
  · exact continuous_subtype_val.comp
      (φ.symm.continuous.comp (continuous_id.prodMk continuous_const))
  · intro u
    have hp := hφproj (φ.symm (u, 1))
    have heq : φ (φ.symm (u, 1)) = (u, 1) := φ.apply_symm_apply (u, 1)
    simpa [s] using
      ((congrArg (fun q : U × Circle ↦ (q.1 : B)) heq).symm.trans hp).symm

/-- Pulling the local-section cover back along one traversal of the circle
gives a local continuous lift around every point of the closed interval.

In words: continuity of `t ↦ e⁻¹(exp(2πt))` makes the inverse image of a
local-section domain open, and composing that local section with the traversal
gives the required lift.  This is the local input to the finite-subdivision
pasting argument. -/
lemma apm_t95j06_principalCircleBundle_interval_local_lift_aux
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance)
    (hloc : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ s : U → X, Continuous s ∧ ∀ u, P.proj (s u) = u) :
    let I := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
    let γ : I → B := fun t ↦ e.symm (Circle.exp (2 * Real.pi * t.1))
    ∀ t : I, ∃ W : Set I, IsOpen W ∧ t ∈ W ∧
      ∃ σ : W → X, Continuous σ ∧ ∀ u, P.proj (σ u) = γ u := by
  dsimp only
  let γ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → B := fun t ↦
    e.symm (Circle.exp (2 * Real.pi * t.1))
  have hγ : Continuous γ := by
    exact e.symm.continuous.comp (Circle.exp.continuous.comp (by fun_prop))
  intro t
  obtain ⟨U, hU, htU, s, hscont, hsproj⟩ := hloc (γ t)
  let W : Set {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} := γ ⁻¹' U
  let σ : W → X := fun u ↦ s ⟨γ u.1, u.2⟩
  refine ⟨W, hU.preimage hγ, htU, σ, ?_, ?_⟩
  · exact hscont.comp
      (Continuous.subtype_mk (hγ.comp continuous_subtype_val) (fun u ↦ u.2))
  · intro u
    exact hsproj ⟨γ u.1, u.2⟩

/- Local sections of a principal `Circle` bundle over a circle paste to a
global section.

This is true by compactness of `Circle`: refine the local-section cover to a
finite cyclic cover by arcs.  On each connected overlap, fibre freeness and
transitivity give a continuous `Circle`-valued transition.  Lift that map to
`ℝ` along `Circle.exp`, extend the lift across the next (contractible) arc,
and use its exponential to correct the next section.  Induction pastes around
the finite cyclic cover; the same lift-and-correct step removes the closing
mismatch.  Estimated size: 350--650 lines, principally the finite arc cover,
real lift, and closed-cover pasting infrastructure. -/
/- A finite chain of local sections lifts one traversal of the circle.

In words, compactness of `[0,1]` gives a finite subdivision subordinate to
the inverse images of the local-section domains.  Starting with the first
local section, multiply each subsequent one by a constant circle element so
that adjacent pieces agree at their common endpoint; fibre transitivity gives
the constant and the closed-interval pasting lemma gives continuity.
Estimated size: 180--300 lines. -/
/-- Two continuous maps on adjacent closed real intervals which agree at the
common endpoint paste to a continuous map on their union.  This is the closed
piece pasting step used at every stage of the interval-section induction. -/
lemma apm_t95j06_paste_adjacent_closed_intervals
    {Y : Type*} [TopologicalSpace Y] {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b)
    (f : {x : ℝ // x ∈ Set.Icc a s} → Y)
    (g : {x : ℝ // x ∈ Set.Icc s b} → Y)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f ⟨s, has, le_rfl⟩ = g ⟨s, le_rfl, hsb⟩) :
    ∃ h : {x : ℝ // x ∈ Set.Icc a b} → Y, Continuous h ∧
      (∀ x (hx : x.1 ≤ s), h x = f ⟨x.1, x.2.1, hx⟩) ∧
      (∀ x (hx : s ≤ x.1), h x = g ⟨x.1, hx, x.2.2⟩) := by
  let D := {x : {x : ℝ // x ∈ Set.Icc a b} | x.1 ≤ s}
  let E := {x : {x : ℝ // x ∈ Set.Icc a b} | s ≤ x.1}
  let qf : {x : ℝ // x ∈ Set.Icc a b} → {x : ℝ // x ∈ Set.Icc a s} := fun x ↦
    ⟨min x.1 s, le_min x.2.1 has, min_le_right _ _⟩
  let qg : {x : ℝ // x ∈ Set.Icc a b} → {x : ℝ // x ∈ Set.Icc s b} := fun x ↦
    ⟨max s x.1, le_max_left _ _, max_le hsb x.2.2⟩
  let h : {x : ℝ // x ∈ Set.Icc a b} → Y := fun x ↦
    if x ∈ D then f (qf x) else g (qg x)
  have hD : IsClosed D := isClosed_Iic.preimage continuous_subtype_val
  have hE : IsClosed E := isClosed_Ici.preimage continuous_subtype_val
  have hqf : Continuous qf := Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) _
  have hqg : Continuous qg := Continuous.subtype_mk
    (continuous_const.max continuous_subtype_val) _
  have hfD : ContinuousOn h D := by
    apply (hf.comp hqf).continuousOn.congr
    intro x hx
    simp [h, hx]
  have hgE : ContinuousOn h E := by
    apply (hg.comp hqg).continuousOn.congr
    intro x hx
    by_cases hxs : x ∈ D
    · have heq : x.1 = s := le_antisymm hxs hx
      subst heq
      simpa [h, hxs, qf, qg] using hfg
    · simp [h, hxs]
  have hcont : Continuous h := by
    rw [← continuousOn_univ]
    have hDE : D ∪ E = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      change x.1 ≤ s ∨ s ≤ x.1
      exact le_total x.1 s
    rw [← hDE]
    exact hfD.union_of_isClosed hgE hD hE
  refine ⟨h, hcont, ?_, ?_⟩
  · intro x hx
    have hxD : x ∈ D := hx
    simp [h, hxD, qf, min_eq_left hx]
  · intro x hx
    by_cases hxs : x.1 ≤ s
    · have : x.1 = s := le_antisymm hxs hx
      subst this
      simpa [h, D, qf, qg] using hfg
    · simp [h, D, hxs, qg, max_eq_right hx]

theorem apm_t95j06_principalCircleBundle_interval_section
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance)
    (hloc : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ s : U → X, Continuous s ∧ ∀ u, P.proj (s u) = u) :
    ∃ σ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X,
      Continuous σ ∧ ∀ t,
        P.proj (σ t) = e.symm (Circle.exp (2 * Real.pi * t.1)) := by
  classical
  let pp : ℝ → B := fun t => e.symm (Circle.exp (2 * Real.pi * t))
  have hppc : Continuous pp :=
    e.symm.continuous.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
  let Good : ℝ → Prop := fun r => ∃ σ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) r} → X,
      Continuous σ ∧ ∀ t, P.proj (σ t) = pp t.1
  have hlocal : ∀ m : ℝ, ∃ δ > 0, ∃ τ : Metric.ball m δ → X, Continuous τ ∧
      ∀ t, P.proj (τ t) = pp t.1 := by
    intro m
    obtain ⟨U, hU, hmU, s, hs, hsp⟩ := hloc (pp m)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hppc) m hmU
    refine ⟨δ, hδ, fun t => s ⟨pp t.1, hball t.2⟩, ?_, fun t => hsp _⟩
    exact hs.comp (Continuous.subtype_mk (hppc.comp continuous_subtype_val) _)
  let S : Set ℝ := {r | r ∈ Set.Icc (0 : ℝ) 1 ∧ Good r}
  have h0 : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, zero_le_one⟩, fun _ => Classical.choose (P.surjective_proj (pp 0)),
      continuous_const, fun t => ?_⟩
    have ht : t.1 = 0 := le_antisymm t.2.2 t.2.1
    rw [Classical.choose_spec (P.surjective_proj (pp 0)), ht]
  have hbdd : BddAbove S := ⟨1, fun r hr => hr.1.2⟩
  set m := sSup S with hm
  have hm1 : m ≤ 1 := csSup_le ⟨0, h0⟩ fun r hr => hr.1.2
  have hm0 : 0 ≤ m := le_csSup hbdd h0
  obtain ⟨δ, hδ, τ, hτc, hτp⟩ := hlocal m
  obtain ⟨r, hrS, hrm⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ (show m - δ < m by linarith)
  have hr_le : r ≤ m := le_csSup hbdd hrS
  obtain ⟨⟨hr0, hr1⟩, σ, hσc, hσp⟩ := hrS
  set r' := min (m + δ / 2) 1 with hr'
  have hrr' : r ≤ r' := le_min (by linarith) hr1
  have hball : ∀ t : {x : ℝ // x ∈ Set.Icc r r'}, t.1 ∈ Metric.ball m δ := by
    intro t
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    have h1 := t.2.1; have h2 := t.2.2; have h3 := min_le_left (m + δ / 2) 1
    constructor <;> linarith
  let τ' : {x : ℝ // x ∈ Set.Icc r r'} → X := fun t => τ ⟨t.1, hball t⟩
  have hτ'c : Continuous τ' :=
    hτc.comp (Continuous.subtype_mk continuous_subtype_val _)
  obtain ⟨g, hg⟩ := P.orbit_fiber (τ' ⟨r, le_rfl, hrr'⟩) (σ ⟨r, hr0, le_rfl⟩)
    (by rw [hτp, hσp])
  let τ'' : {x : ℝ // x ∈ Set.Icc r r'} → X := fun t => P.act (g, τ' t)
  have hτ''c : Continuous τ'' :=
    P.continuous_act.comp (continuous_const.prodMk hτ'c)
  obtain ⟨h, hhc, hh1, hh2⟩ :=
    apm_t95j06_paste_adjacent_closed_intervals hr0 hrr' σ τ'' hσc hτ''c hg.symm
  have hgood : Good r' := by
    refine ⟨h, hhc, fun t => ?_⟩
    rcases le_total t.1 r with htr | htr
    · rw [hh1 t htr, hσp]
    · rw [hh2 t htr]
      change P.proj (P.act (g, τ' _)) = _
      rw [P.invariant, hτp]
  have hr'1 : r' = 1 := by
    by_contra hne
    have hlt : r' < 1 := lt_of_le_of_ne (min_le_right _ _) hne
    have heq : r' = m + δ / 2 := by
      rcases min_choice (m + δ / 2) 1 with h' | h'
      · exact h'
      · exact absurd h' (ne_of_lt hlt)
    have hmem : r' ∈ S := ⟨⟨by linarith, hlt.le⟩, hgood⟩
    have := le_csSup hbdd hmem
    linarith
  rw [hr'1] at hgood
  exact hgood

/-- A lifted section along one traversal can be corrected to close up.

The two endpoint values lie in the same fibre, hence differ by some
`h : Circle`.  Choose a path in `Circle` from `1` to `h⁻¹` (for example the
exponential of a linear multiple of `arg h`) and act pointwise by that path.
Invariance preserves the projection, while the action law makes the corrected
endpoints equal.  Estimated size: 45--90 lines. -/
theorem apm_t95j06_principalCircleBundle_close_interval_section
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance)
    (σ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X)
    (hσcont : Continuous σ)
    (hσproj : ∀ t, P.proj (σ t) =
      e.symm (Circle.exp (2 * Real.pi * t.1))) :
    ∃ σ' : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X,
      Continuous σ' ∧
      (∀ t, P.proj (σ' t) = e.symm (Circle.exp (2 * Real.pi * t.1))) ∧
      σ' ⟨0, by simp⟩ = σ' ⟨1, by simp⟩ := by
  let z : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} := ⟨0, by simp⟩
  let o : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} := ⟨1, by simp⟩
  have hbase : P.proj (σ z) = P.proj (σ o) := by
    rw [hσproj, hσproj]
    simp [z, o, Circle.exp_zero, Circle.exp_two_pi]
  obtain ⟨h, hh⟩ := P.orbit_fiber (σ z) (σ o) hbase
  let a : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → Circle := fun t ↦
    Circle.exp (-t.1 * Complex.arg (h : ℂ))
  have hacont : Continuous a := by
    apply continuous_induced_rng.2
    change Continuous (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} ↦
      Complex.exp ((↑(-t.1 * Complex.arg (h : ℂ)) : ℂ) * Complex.I))
    fun_prop
  let σ' : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X := fun t ↦ P.act (a t, σ t)
  refine ⟨σ', P.continuous_act.comp (hacont.prodMk hσcont), ?_, ?_⟩
  · intro t
    rw [show P.proj (σ' t) = P.proj (σ t) by exact P.invariant (a t) (σ t)]
    exact hσproj t
  · change σ' z = σ' o
    have ha0 : a z = 1 := by simp [a, z, Circle.exp_zero]
    have ha1 : a o = h⁻¹ := by
      simp only [a, o]
      rw [neg_one_mul, Circle.exp_neg, Circle.exp_arg]
    rw [show σ' z = σ z by simp [σ', ha0, P.one_act]]
    change σ z = P.act (a o, σ o)
    rw [ha1, ← hh, P.mul_act, inv_mul_cancel, P.one_act]

/-- The standard exponential parametrization of the circle by the closed unit
interval is onto.  This follows by choosing the argument in `[0,2π)` (adding
`2π` to a negative principal argument) and dividing by `2π`.  Estimated proof
size: 20--35 lines. -/
theorem apm_t95j06_principalCircleBundle_descend_interval_section_aux_surjective :
    Function.Surjective
      (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} ↦
        Circle.exp (2 * Real.pi * t.1)) := by
  intro z
  have hπ := Real.pi_pos
  obtain ⟨h1, h2⟩ := Complex.arg_mem_Ioc (z : ℂ)
  by_cases h : 0 ≤ Complex.arg z
  · refine ⟨⟨Complex.arg z / (2 * Real.pi), ?_, ?_⟩, ?_⟩
    · positivity
    · rw [div_le_one (by positivity)]; linarith
    · simp only
      rw [mul_div_cancel₀ _ (by positivity)]
      exact Circle.exp_arg z
  · push_neg at h
    refine ⟨⟨(Complex.arg z + 2 * Real.pi) / (2 * Real.pi), ?_, ?_⟩, ?_⟩
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by positivity)]; linarith
    · simp only
      rw [mul_div_cancel₀ _ (by positivity), Circle.exp_add_two_pi]
      exact Circle.exp_arg z

/-- A continuous closed interval lift is constant on the fibres of the
standard exponential parametrization.  `Circle.exp_eq_exp` says two parameters
differ by an integral multiple of `2π`; parameters in `[0,1]` therefore agree,
except that `0` and `1` may be paired, where the endpoint-closing hypothesis
applies.  Estimated proof size: 35--60 lines. -/
theorem apm_t95j06_principalCircleBundle_descend_interval_section_aux_factorsThrough
    (X : Type*) [TopologicalSpace X]
    (σ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X)
    (hclose : σ ⟨0, by simp⟩ = σ ⟨1, by simp⟩) :
    Function.FactorsThrough σ
      (fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} ↦
        Circle.exp (2 * Real.pi * t.1)) := by
  intro a b hab
  have hπ := Real.pi_pos
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 hab
  have hab' : a.1 = b.1 + m := by
    have : 2 * Real.pi * a.1 = 2 * Real.pi * (b.1 + m) := by rw [hm]; ring
    exact mul_left_cancel₀ (by positivity) this
  obtain ⟨ha0, ha1⟩ := a.2
  obtain ⟨hb0, hb1⟩ := b.2
  have hm1 : (m : ℝ) ≤ 1 := by linarith
  have hm2 : (-1 : ℝ) ≤ m := by linarith
  have hm1' : m ≤ 1 := by exact_mod_cast hm1
  have hm2' : -1 ≤ m := by exact_mod_cast hm2
  interval_cases m
  · have ha : a = ⟨0, by simp⟩ := Subtype.ext (by push_cast at hab'; linarith)
    have hb : b = ⟨1, by simp⟩ := Subtype.ext (by push_cast at hab'; linarith)
    rw [ha, hb, hclose]
  · exact congrArg σ (Subtype.ext (by simpa using hab'))
  · have ha : a = ⟨1, by simp⟩ := Subtype.ext (by push_cast at hab'; linarith)
    have hb : b = ⟨0, by simp⟩ := Subtype.ext (by push_cast at hab'; linarith)
    rw [ha, hb, hclose]

/-- A closed lifted section descends through the exponential quotient.

The map `t ↦ Circle.exp (2πt)` from `[0,1]` is a quotient map onto `Circle`;
its only repeated endpoints are `0` and `1`.  Thus a continuous map with
equal endpoint values descends continuously.  Its projection identity also
descends pointwise.  Estimated size: 60--120 lines. -/
theorem apm_t95j06_principalCircleBundle_descend_interval_section
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance)
    (σ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X)
    (hσcont : Continuous σ)
    (hσproj : ∀ t, P.proj (σ t) =
      e.symm (Circle.exp (2 * Real.pi * t.1)))
    (hclose : σ ⟨0, by simp⟩ = σ ⟨1, by simp⟩) :
    ∃ s : Circle → X, Continuous s ∧ ∀ c, P.proj (s c) = e.symm c := by
  let q : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → Circle :=
    fun t ↦ Circle.exp (2 * Real.pi * t.1)
  have hqcont : Continuous q := by
    exact Circle.exp.continuous.comp
      (continuous_const.mul continuous_subtype_val)
  have hqsurj : Function.Surjective q :=
    apm_t95j06_principalCircleBundle_descend_interval_section_aux_surjective
  let qc : C({t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, Circle) := ⟨q, hqcont⟩
  have hq : Topology.IsQuotientMap qc :=
    IsQuotientMap.of_surjective_continuous hqsurj hqcont
  let σc : C({t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}, X) := ⟨σ, hσcont⟩
  have hfac : Function.FactorsThrough σc qc :=
    apm_t95j06_principalCircleBundle_descend_interval_section_aux_factorsThrough
      X σ hclose
  let sc : C(Circle, X) :=
    hq.lift σc hfac
  refine ⟨sc, sc.continuous, ?_⟩
  intro c
  obtain ⟨t, rfl⟩ := hqsurj c
  rw [show sc (q t) = σ t by
    have ht := ContinuousMap.congr_fun (hq.lift_comp σc hfac) t
    change sc (qc t) = σc t at ht
    simpa [qc, σc] using ht]
  exact hσproj t

/-- Local sections of a principal `Circle` bundle over a circle paste to a
global section by lifting around one traversal, correcting its endpoint
monodromy, and descending the resulting closed lift. -/
theorem apm_t95j06_principalCircleBundle_circle_local_sections_glue
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance)
    (hloc : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ s : U → X, Continuous s ∧ ∀ u, P.proj (s u) = u) :
    ∃ s : B → X, Continuous s ∧ ∀ b, P.proj (s b) = b := by
  obtain ⟨σ, hσcont, hσproj⟩ :=
    apm_t95j06_principalCircleBundle_interval_section X B tB P e hloc
  obtain ⟨σ', hσ'cont, hσ'proj, hclose⟩ :=
    apm_t95j06_principalCircleBundle_close_interval_section
      X B tB P e σ hσcont hσproj
  obtain ⟨s₀, hs₀cont, hs₀proj⟩ :=
    apm_t95j06_principalCircleBundle_descend_interval_section
      X B tB P e σ' hσ'cont hσ'proj hclose
  refine ⟨fun b ↦ s₀ (e b), hs₀cont.comp e.continuous, ?_⟩
  intro b
  rw [hs₀proj, e.symm_apply_apply]

/-- A principal `Circle` bundle over a circle admits a continuous section.

This is true because two closed arcs cover the circle.  Local trivializations
give sections on the arcs; their transition functions on the two overlap
components can be joined inside the path-connected group `Circle`, allowing
one section to be corrected and the two to be pasted.  Estimated size:
450--850 lines (arc parametrizations, transition continuity, and pasting). -/
theorem apm_t95j06_principalCircleBundle_over_circle_section
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance) :
    ∃ s : B → X, Continuous s ∧ ∀ b, P.proj (s b) = b := by
  apply apm_t95j06_principalCircleBundle_circle_local_sections_glue X B tB P e
  exact fun b ↦ apm_t95j06_principalCircleBundle_local_section X B tB P b

/-- The fibre coordinate relative to a continuous section is continuous.

For each `x`, freeness and fibre transitivity give a unique `g` with
`act (g, s (proj x)) = x`.  In every equivariant local trivialization this
`g` is the quotient of the chart's circle coordinate of `x` by that of the
section, hence is continuous; these local assertions cover the base.
Estimated size: 180--320 lines. -/
theorem apm_t95j06_principalCircleBundle_section_coordinate_continuous
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (s : B → X) (hscont : Continuous s) (hs : ∀ b, P.proj (s b) = b) :
    Continuous (fun x : X ↦ Classical.choose (P.orbit_fiber (s (P.proj x)) x (hs _))) := by
  let coord : X → Circle := fun x ↦
    Classical.choose (P.orbit_fiber (s (P.proj x)) x (hs _))
  have hcoord (x : X) : P.act (coord x, s (P.proj x)) = x :=
    Classical.choose_spec (P.orbit_fiber (s (P.proj x)) x (hs _))
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hxU, φ, hφproj, hφact⟩ := P.local_trivial (P.proj x)
  let V : Set X := P.proj ⁻¹' U
  have hV : IsOpen V := hU.preimage P.continuous_proj
  have hxV : x ∈ V := hxU
  let lift : V → {y : X // P.proj y ∈ U} := fun y ↦ ⟨y.1, y.2⟩
  have hlift : Continuous lift :=
    continuous_subtype_val.subtype_mk (fun y ↦ y.2)
  let sectionLift : V → {y : X // P.proj y ∈ U} := fun y ↦
    ⟨s (P.proj y.1), by rw [hs]; exact y.2⟩
  have hsectionLift : Continuous sectionLift := by
    apply Continuous.subtype_mk
    exact hscont.comp (P.continuous_proj.comp continuous_subtype_val)
  let localCoord : V → Circle := fun y ↦
    (φ (lift y)).2 * ((φ (sectionLift y)).2)⁻¹
  have hlocalCoord : Continuous localCoord := by
    exact ((continuous_snd.comp (φ.continuous.comp hlift)).mul
      ((continuous_snd.comp (φ.continuous.comp hsectionLift)).inv))
  have hlocal (y : V) : coord y.1 = localCoord y := by
    have hact := hφact (coord y.1) (sectionLift y)
    have heq :
        (⟨P.act (coord y.1, (sectionLift y).1), by
          rw [P.invariant]
          exact (sectionLift y).2⟩ : {z : X // P.proj z ∈ U}) = lift y := by
      apply Subtype.ext
      exact hcoord y.1
    rw [heq] at hact
    change coord y.1 = (φ (lift y)).2 * ((φ (sectionLift y)).2)⁻¹
    calc
      coord y.1 = (coord y.1 * (φ (sectionLift y)).2) *
          ((φ (sectionLift y)).2)⁻¹ := by simp
      _ = (φ (lift y)).2 * ((φ (sectionLift y)).2)⁻¹ := by rw [← hact]
  have hrestrict : Continuous (V.restrict coord) := by
    rw [show V.restrict coord = localCoord from funext hlocal]
    exact hlocalCoord
  have hwithin : ContinuousWithinAt coord V x :=
    (continuousWithinAt_iff_continuousAt_restrict coord hxV).2
      hrestrict.continuousAt
  exact hwithin.continuousAt (hV.mem_nhds hxV)

/-- **LIBRARY, principal Circle bundles over a circle (estimated 600--1200
lines).**  An equivariantly locally trivial principal Circle bundle whose base
is a circle has total space homeomorphic to `Circle × Circle`.

Proof route: pull back along the supplied base homeomorphism, trivialize over
two arcs, and alter one local section by a path in the connected structure
group `Circle` so the sections agree on the overlap.  The resulting global
section and the free transitive fibre action give the product homeomorphism.
Local triviality alone would be false here (the Klein-bottle circle bundle);
the principal equivariant action in `P` excludes its reflected transition. -/
theorem apm_t95j06_principalCircleBundle_over_circle_trivial
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance) :
    Nonempty (X ≃ₜ Circle × Circle) := by
  obtain ⟨s, hscont, hs⟩ :=
    apm_t95j06_principalCircleBundle_over_circle_section X B tB P e
  let coord : X → Circle := fun x ↦
    Classical.choose (P.orbit_fiber (s (P.proj x)) x (hs _))
  have hcoord (x : X) : P.act (coord x, s (P.proj x)) = x :=
    Classical.choose_spec (P.orbit_fiber (s (P.proj x)) x (hs _))
  have hcoord_cont : Continuous coord :=
    apm_t95j06_principalCircleBundle_section_coordinate_continuous X B tB P s hscont hs
  let f : X → Circle × Circle := fun x ↦ (e (P.proj x), coord x)
  let g : Circle × Circle → X := fun cg ↦ P.act (cg.2, s (e.symm cg.1))
  have hf : Continuous f :=
    (e.continuous.comp P.continuous_proj).prodMk hcoord_cont
  have hg : Continuous g := by
    exact P.continuous_act.comp
      (continuous_snd.prodMk (hscont.comp (e.symm.continuous.comp continuous_fst)))
  refine ⟨Homeomorph.mk
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_ }
    hf hg⟩
  · intro x
    simpa [f, g] using hcoord x
  · intro cg
    rcases cg with ⟨c, k⟩
    apply Prod.ext
    · simp only [f, g]
      rw [P.invariant, hs, e.apply_symm_apply]
    · simp only [f, g]
      have hbase : P.proj (P.act (k, s (e.symm c))) = e.symm c := by
        rw [P.invariant, hs]
      have hchosen := hcoord (P.act (k, s (e.symm c)))
      simp only [hbase] at hchosen
      apply mul_inv_eq_one.mp
      apply P.free (coord (P.act (k, s (e.symm c))) * k⁻¹)
        (P.act (k, s (e.symm c)))
      rw [P.mul_act, mul_assoc, inv_mul_cancel, mul_one, hchosen]

theorem apm_t95J06_bridge_1
    (H : apm_t95j06_S5 × ℝ → apm_t95j06_S5)
    (hH : apm_t95j06_isHopfFlow H)
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hF_invariant : apm_t95j06_IsInvariant H F) :
    apm_t95j06_EveryComponentDiffeomorphicToTorus F := by
  have hinv : apm_t95j06_IsCircleInvariant F := by
    intro z hz g
    refine ⟨H (z, Complex.arg (g : ℂ)), hF_invariant z hz _, ?_⟩
    rw [hH]
    simpa only [show Complex.exp (Complex.I * (Complex.arg (g : ℂ) : ℂ)) = (g : ℂ) by
      rw [show Complex.I * (Complex.arg (g : ℂ) : ℂ) =
          (Complex.arg (g : ℂ) : ℂ) * Complex.I by ring,
        ← Circle.coe_exp, Circle.exp_arg]]
  intro x
  obtain ⟨B, tB, hc, hconn, h2, hsc, ⟨P⟩⟩ :=
    apm_t95j06_hopf_slices_component_principalBundle F hF hinv x
  have hloc := apm_t95j06_principalBundle_base_locallyRealLine
    F hF x B tB h2 hsc P
  obtain ⟨e⟩ := apm_t95j06_compact_connected_locallyRealLine_homeomorph_circle
    B tB hc hconn h2 hsc hloc
  exact apm_t95j06_principalCircleBundle_over_circle_trivial _ B tB P e

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

#print axioms apm_t95j06_planarCrosscut_productChart_twoEndpoint_at_aux_disk_projection







#print axioms apm_t95j06_Q_aux_no_isolated
#print axioms apm_t95j06_Q_aux_arc_interior_open
#print axioms apm_t95j06_Q_aux_arc_endpoints_not_interior

#print axioms apm_t95j06_Q_aux_pathConnected_neighborhood

#print axioms apm_t95j06_Q_aux_arc_in_subset

#print axioms apm_t95j06_Q_aux_arc_intersection

#print axioms apm_t95j06_Q_aux_two_arcs

#print axioms apm_t95j06_two_overlapping_realCharts_line_or_compact_aux_rayGlue_orientation

#print axioms apm_t95j06_loopErase_denselyOrdered

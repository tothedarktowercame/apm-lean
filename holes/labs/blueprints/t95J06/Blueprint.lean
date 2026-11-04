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

/-- The pure planar crosscut statement used by F3c.  An embedded closed arc in
a closed Euclidean disk, meeting the boundary circle precisely in its two
endpoints, cuts the open disk into two nonempty connected open sides, and the
whole arc is in the frontier of both sides. -/
def apm_t95j06_PlanarCrosscutSeparation : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ (A : Set apm_t95j06_E2),
    ∀ (e : Set.Icc (-1 : ℝ) 1 ≃ₜ A),
      A ⊆ Metric.closedBall 0 r →
      A ∩ Metric.sphere 0 r =
        ({(e ⟨-1, by norm_num⟩ : apm_t95j06_E2),
          (e ⟨1, by norm_num⟩ : apm_t95j06_E2)} : Set apm_t95j06_E2) →
      ∃ L R : Set apm_t95j06_E2,
        IsOpen L ∧ IsOpen R ∧ L.Nonempty ∧ R.Nonempty ∧
        IsPreconnected L ∧ IsPreconnected R ∧ Disjoint L R ∧
        Metric.ball 0 r \ A = L ∪ R ∧
        A ⊆ frontier L ∧ A ⊆ frontier R

/-- Pure Jordan-curve separation in the plane: every subset homeomorphic to a
circle has exactly two complementary domains, and the curve is the frontier
of each.  This contains no disk, crosscut, interval arc, or base space. -/
def apm_t95j06_PlanarJordanSeparation : Prop :=
  ∀ (J : Set apm_t95j06_E2), Nonempty (Circle ≃ₜ J) →
    ∃ inside outside : Set apm_t95j06_E2,
      IsOpen inside ∧ IsOpen outside ∧ inside.Nonempty ∧ outside.Nonempty ∧
      IsPreconnected inside ∧ IsPreconnected outside ∧
      Disjoint inside outside ∧ Jᶜ = inside ∪ outside ∧
      J = frontier inside ∧ J = frontier outside

/-- Normalize a nonzero complex number to its direction on the unit circle. -/
noncomputable def apm_t95j06_jordan_complement_separates_aux_normalize :
    C({z : ℂ // z ≠ 0}, Circle) where
  toFun z := ⟨z.val / (‖z.val‖ : ℂ), by
    change z.val / (‖z.val‖ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self]
    exact norm_ne_zero_iff.mpr z.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div
      (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
      (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.property))

/-- The concrete direction loop about a point off the image of a circle map. -/
noncomputable def apm_t95j06_jordan_complement_separates_aux_loop
    (γ : C(Circle, ℂ)) (z : ↥((Set.range γ)ᶜ)) : C(Circle, Circle) :=
  apm_t95j06_jordan_complement_separates_aux_normalize.comp
    ⟨fun t => ⟨γ t - z.val, sub_ne_zero.mpr (fun h => z.property ⟨t, h⟩)⟩,
      (γ.continuous.sub continuous_const).subtype_mk _⟩

/-- Winding is the integral homological degree of the specified direction loop. -/
noncomputable def apm_t95j06_jordan_complement_separates_aux_winding
    (γ : C(Circle, ℂ)) (z : ↥((Set.range γ)ᶜ)) : ℤ :=
  ConstructionTargets.T00J02Closure.circleDegree
    (apm_t95j06_jordan_complement_separates_aux_loop γ z)

/-- Homotopic circle maps have equal integral homological degree. -/
lemma apm_t95j06_jordan_complement_separates_aux_degree_homotopic
    {f g : C(Circle, Circle)} (h : ContinuousMap.Homotopic f g) :
    ConstructionTargets.T00J02Closure.circleDegree f =
      ConstructionTargets.T00J02Closure.circleDegree g := by
  have H := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) h 1
  unfold ConstructionTargets.T00J02Closure.circleDegree
    ConstructionTargets.T00J02Closure.circleHomologyCoordinateMap
  exact congrArg (fun k =>
    (ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫ k ≫
      ConstructionTargets.CircleHomology.circleH1IsoInt.hom) (1 : ℤ)) H

/-- Moving the observation point along a path avoiding the curve gives an
explicit homotopy of direction loops, hence preserves their degree. -/
lemma apm_t95j06_jordan_complement_separates_aux_winding_path
    (γ : C(Circle, ℂ)) {z w : ↥((Set.range γ)ᶜ)} (p : Path z w) :
    apm_t95j06_jordan_complement_separates_aux_winding γ z =
      apm_t95j06_jordan_complement_separates_aux_winding γ w := by
  apply apm_t95j06_jordan_complement_separates_aux_degree_homotopic
  let F : C(unitInterval × Circle, {v : ℂ // v ≠ 0}) :=
    ⟨fun tx => ⟨γ tx.2 - (p tx.1).val,
      sub_ne_zero.mpr (fun h => (p tx.1).property ⟨tx.2, h⟩)⟩,
      ((γ.continuous.comp continuous_snd).sub
        (continuous_subtype_val.comp (p.continuous.comp continuous_fst))).subtype_mk _⟩
  refine ⟨?_⟩
  refine {
    toContinuousMap := apm_t95j06_jordan_complement_separates_aux_normalize.comp F
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro x
    simp [F, apm_t95j06_jordan_complement_separates_aux_loop]
  · intro x
    simp [F, apm_t95j06_jordan_complement_separates_aux_loop]

/-- Winding is locally constant off a compact curve: each open path component
of its complement is contained in one winding fibre. -/
lemma apm_t95j06_jordan_complement_separates_aux_winding_locallyConstant
    (γ : C(Circle, ℂ)) :
    IsLocallyConstant (apm_t95j06_jordan_complement_separates_aux_winding γ) := by
  have ho : IsOpen (Set.range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  letI := ho.locPathConnectedSpace
  intro S
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  refine ⟨pathComponent z, ?_, IsOpen.pathComponent z, ?_⟩
  · intro w hw
    rcases hw with ⟨p⟩
    have he := apm_t95j06_jordan_complement_separates_aux_winding_path γ p
    change apm_t95j06_jordan_complement_separates_aux_winding γ w ∈ S
    rw [← he]
    exact hz
  · exact Joined.refl z

/-- A point beyond a norm bound for the curve has winding zero. The homotopy
contracts the entire curve linearly to zero without meeting that point. -/
lemma apm_t95j06_jordan_complement_separates_aux_far_zero
    (γ : C(Circle, ℂ)) (R : ℝ) (hR : 0 < R)
    (hbound : ∀ t, ‖γ t‖ < R) :
    ∃ z : ↥((Set.range γ)ᶜ),
      apm_t95j06_jordan_complement_separates_aux_winding γ z = 0 := by
  have hfar : (R : ℂ) ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    have := hbound t
    rw [ht, Complex.norm_real, Real.norm_of_nonneg hR.le] at this
    exact (lt_irrefl _ this)
  let z : ↥((Set.range γ)ᶜ) := ⟨(R : ℂ), hfar⟩
  have havoid : ∀ (t : unitInterval) (x : Circle),
      (1 - (t : ℝ)) * γ x - (R : ℂ) ≠ 0 := by
    intro t x he
    have heq := sub_eq_zero.mp he
    have hsmall : ‖(1 - (t : ℝ)) * γ x‖ < R := by
      rw [norm_mul]
      have hn : ‖(1 - (t : ℝ) : ℂ)‖ ≤ 1 := by
        rw [show (1 - (t : ℝ) : ℂ) = ((1 - (t : ℝ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.mpr t.property.2)]
        linarith [t.property.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hn) (hbound x)
    rw [heq, Complex.norm_real, Real.norm_of_nonneg hR.le] at hsmall
    exact (lt_irrefl _ hsmall)
  let F : C(unitInterval × Circle, {v : ℂ // v ≠ 0}) :=
    ⟨fun tx => ⟨(1 - (tx.1 : ℝ)) * γ tx.2 - (R : ℂ), havoid tx.1 tx.2⟩,
      by apply Continuous.subtype_mk; fun_prop⟩
  let v : Circle := apm_t95j06_jordan_complement_separates_aux_normalize
    ⟨-(R : ℂ), neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hR.ne')⟩
  have hh : ContinuousMap.Homotopic
      (apm_t95j06_jordan_complement_separates_aux_loop γ z)
      (ContinuousMap.const Circle v) := by
    refine ⟨?_⟩
    refine {
      toContinuousMap := apm_t95j06_jordan_complement_separates_aux_normalize.comp F
      map_zero_left := ?_
      map_one_left := ?_ }
    · intro x
      simp [F, z, apm_t95j06_jordan_complement_separates_aux_loop]
    · intro x
      simp [F, v]
  refine ⟨z, ?_⟩
  change ConstructionTargets.T00J02Closure.circleDegree _ = 0
  rw [apm_t95j06_jordan_complement_separates_aux_degree_homotopic hh]
  apply ConstructionTargets.T00J02Closure.circleDegree_eq_zero_of_homologyMap_eq_zero
  exact ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_const_eq_zero
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero v

/-- The precise Brouwer obstruction needed by the Borsuk index argument: the
closed planar unit disk does not retract continuously onto its boundary
circle.  This is already proved, sorry-free, by integral sphere homology in
`ConstructionTargets/CollaredConnectedSumHomology.lean:203`; specializing its
dimension parameter to `1` gives the two-dimensional disk. -/
lemma apm_t95j06_jordan_complement_separates_aux_no_disk_retraction :
    ¬ ∃ r : ConstructionTargets.CollaredConnectedSumHomology.Disk 2 1 →
        ConstructionTargets.CollaredConnectedSumHomology.Sphere 2,
      Continuous r ∧ ∀ s,
        r (ConstructionTargets.CollaredConnectedSumHomology.sphereToDisk 2 s) = s := by
  exact ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_noRetraction 1

/-- Borsuk's nonzero-index lemma: an embedded circle has a point at which
its concrete normalized-difference loop has nonzero integral homological degree.
This is true for every topological embedding, without smoothness or polygonality,
by Borsuk's planar non-retraction/index argument. The degree and loop above are
fixed independently of separation; no arbitrary separating function is assumed.
Estimated remaining proof: 200--400 lines of planar non-retraction/index theory. -/
lemma apm_t95j06_jordan_complement_separates_aux_borsuk
    (γ : C(Circle, ℂ)) (hγ : Topology.IsEmbedding γ) :
    ∃ z : ↥((Set.range γ)ᶜ),
      apm_t95j06_jordan_complement_separates_aux_winding γ z ≠ 0 := by
  sorry

/-- The nonzero and zero fibres of the concrete winding separate the complement
of an embedded complex circle. Local constancy gives openness, Borsuk gives a
nonzero fibre, and the explicit far-point contraction gives a zero fibre. -/
lemma apm_t95j06_jordan_complement_separates_aux_complex
    (γ : C(Circle, ℂ)) (hγ : Topology.IsEmbedding γ) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint U V ∧ (Set.range γ)ᶜ = U ∪ V := by
  let w := apm_t95j06_jordan_complement_separates_aux_winding γ
  have hw : IsLocallyConstant w :=
    apm_t95j06_jordan_complement_separates_aux_winding_locallyConstant γ
  have ho : IsOpen (Set.range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  let A : Set ↥((Set.range γ)ᶜ) := {z | w z ≠ 0}
  let B : Set ↥((Set.range γ)ᶜ) := {z | w z = 0}
  have hA : IsOpen A := hw.isClosed_fiber 0 |>.isOpen_compl
  have hB : IsOpen B := hw.isOpen_fiber 0
  obtain ⟨z, hz⟩ := apm_t95j06_jordan_complement_separates_aux_borsuk γ hγ
  obtain ⟨R, hR, hbound⟩ := (isCompact_range γ.continuous).isBounded.exists_pos_norm_lt
  obtain ⟨v, hv⟩ := apm_t95j06_jordan_complement_separates_aux_far_zero γ R hR
    (fun t => hbound (γ t) ⟨t, rfl⟩)
  refine ⟨Subtype.val '' A, Subtype.val '' B,
    ho.isOpenMap_subtype_val A hA, ho.isOpenMap_subtype_val B hB,
    ⟨z.val, z, hz, rfl⟩, ⟨v.val, v, hv, rfl⟩, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have he' : b = a := Subtype.ext he
    subst b
    exact ha hb
  · ext x
    constructor
    · intro hx
      by_cases hh : w ⟨x, hx⟩ = 0
      · exact Or.inr ⟨⟨x, hx⟩, hh, rfl⟩
      · exact Or.inl ⟨⟨x, hx⟩, hh, rfl⟩
    · rintro (⟨a, _, rfl⟩ | ⟨b, _, rfl⟩)
      · exact a.property
      · exact b.property

/-- **J1, existence of two Jordan sides (estimated 100--180 lines).**
The complement of an embedded circle admits a nontrivial separation into two
disjoint nonempty open sets.  A winding-number-one point on one side and a
point sufficiently far from the compact curve on the other give the two
sides; winding is locally constant off the curve.  This claims neither that
the sides are connected nor that their frontiers equal the curve, so it is
strictly weaker than Jordan separation.  Relevant foundations are the circle
winding equivalence in `ConstructionTargets/CircleHurewiczIsomorphism.lean:94`
and winding transport in
`ConstructionTargets/PeriodicCircleHomotopyWinding.lean:88`; neither already
proves this planar complement statement. -/
theorem apm_t95j06_jordan_complement_separates
    (J : Set apm_t95j06_E2) (eJ : Nonempty (Circle ≃ₜ J)) :
    ∃ inside outside : Set apm_t95j06_E2,
      IsOpen inside ∧ IsOpen outside ∧ inside.Nonempty ∧ outside.Nonempty ∧
      Disjoint inside outside ∧ Jᶜ = inside ∪ outside := by
  rcases eJ with ⟨e⟩
  let L : apm_t95j06_E2 ≃ₜ ℂ :=
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph
  let γ : C(Circle, ℂ) := ⟨fun t => L (e t).val,
    L.continuous.comp (continuous_subtype_val.comp e.continuous)⟩
  have hγ : Topology.IsEmbedding γ :=
    L.isEmbedding.comp (Topology.IsEmbedding.subtypeVal.comp e.isEmbedding)
  obtain ⟨U, V, hU, hV, hUn, hVn, hd, hc⟩ :=
    apm_t95j06_jordan_complement_separates_aux_complex γ hγ
  have hr : L ⁻¹' Set.range γ = J := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      have he : (e t).val = x := L.injective ht
      exact he ▸ (e t).property
    · intro hx
      obtain ⟨t, ht⟩ := e.surjective ⟨x, hx⟩
      exact ⟨t, by simp [γ, ht]⟩
  refine ⟨L ⁻¹' U, L ⁻¹' V, hU.preimage L.continuous,
    hV.preimage L.continuous, ?_, ?_, hd.preimage L, ?_⟩
  · obtain ⟨z, hz⟩ := hUn
    exact ⟨L.symm z, by simpa using hz⟩
  · obtain ⟨z, hz⟩ := hVn
    exact ⟨L.symm z, by simpa using hz⟩
  · rw [← Set.preimage_union, ← hc, Set.preimage_compl, hr]

/-- A connected component of an open separated union stays on the side
containing its base point. No planar separation theorem is used. -/
lemma apm_t95j06_jordan_complement_atMostTwo_aux_component_side
    {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hu : IsOpen u) (hv : IsOpen v) (hd : Disjoint u v)
    (hs : s = u ∪ v) {x : X} (hx : x ∈ u) :
    connectedComponentIn s x ⊆ u := by
  have hxs : x ∈ s := hs ▸ Or.inl hx
  have hcover : connectedComponentIn s x ⊆ u ∪ v := by
    rw [← hs]
    exact connectedComponentIn_subset s x
  rcases isPreconnected_connectedComponentIn.subset_or_subset hu hv hd hcover with h | h
  · exact h
  · exact False.elim (Set.disjoint_left.mp hd hx (h (mem_connectedComponentIn hxs)))

/-- Pure topological assembly for J2: if among any three points of a set
some two lie in the same connected component, every nontrivial separation
into two ambient-open sets has connected sides. This isolates the component
counting interface that an H₀/duality computation must supply. It neither
asserts nor assumes a Jordan curve theorem. -/
lemma apm_t95j06_jordan_complement_atMostTwo_aux_of_component_bound
    {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hu : IsOpen u) (hv : IsOpen v) (hun : u.Nonempty) (hvn : v.Nonempty)
    (hd : Disjoint u v) (hs : s = u ∪ v)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s,
      connectedComponentIn s x = connectedComponentIn s y ∨
      connectedComponentIn s x = connectedComponentIn s z ∨
      connectedComponentIn s y = connectedComponentIn s z) :
    IsPreconnected u ∧ IsPreconnected v := by
  have side : ∀ (u v : Set X), IsOpen u → IsOpen v →
      u.Nonempty → v.Nonempty → Disjoint u v → s = u ∪ v → IsPreconnected u := by
    intro u v hu hv _ hvn hd hs
    obtain ⟨z, hz⟩ := hvn
    have hzs : z ∈ s := hs ▸ Or.inr hz
    apply isPreconnected_of_forall_pair
    intro x hx y hy
    have hxs : x ∈ s := hs ▸ Or.inl hx
    have hys : y ∈ s := hs ▸ Or.inl hy
    have cx : connectedComponentIn s x ⊆ u :=
      apm_t95j06_jordan_complement_atMostTwo_aux_component_side hu hv hd hs hx
    have cy : connectedComponentIn s y ⊆ u :=
      apm_t95j06_jordan_complement_atMostTwo_aux_component_side hu hv hd hs hy
    have hxy : connectedComponentIn s x = connectedComponentIn s y := by
      rcases hbound x hxs y hys z hzs with h | h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp hd
          (cx (h ▸ mem_connectedComponentIn hzs)) hz)
      · exact False.elim (Set.disjoint_left.mp hd
          (cy (h ▸ mem_connectedComponentIn hzs)) hz)
    refine ⟨connectedComponentIn s x, cx, mem_connectedComponentIn hxs, ?_,
      isPreconnected_connectedComponentIn⟩
    rw [hxy]
    exact mem_connectedComponentIn hys
  exact ⟨side u v hu hv hun hvn hd hs,
    side v u hv hu hvn hun hd.symm (hs.trans (Set.union_comm _ _))⟩

/-- **J2, no third Jordan side (estimated 120--200 lines).**
Any nontrivial open separation of the complement of an embedded circle has
connected sides.  Equivalently, its complement has at most two connected
components.  Use planar duality/invariance of domain: three components would
give two independent separation classes around a domain homeomorphic to a
circle, contradicting its rank-one winding group.  The hypotheses expose an
already chosen separation, so this leaf does not construct sides or identify
their frontiers. -/
theorem apm_t95j06_jordan_complement_atMostTwo
    (J : Set apm_t95j06_E2) (eJ : Nonempty (Circle ≃ₜ J))
    (inside outside : Set apm_t95j06_E2)
    (hi : IsOpen inside) (ho : IsOpen outside)
    (hin : inside.Nonempty) (hout : outside.Nonempty)
    (hdisj : Disjoint inside outside)
    (hcover : Jᶜ = inside ∪ outside) :
    IsPreconnected inside ∧ IsPreconnected outside := by
  sorry

/- **J3, local two-sidedness of a Jordan curve (estimated 100--170 lines).**
For two connected complementary domains of an embedded circle, every curve
point is approached from both domains, so the curve is exactly each frontier.
Local straightening of an embedded arc gives the two local half-disks; a
connected complementary side cannot switch local sides without crossing the
curve.  This assumes the sides and their connectedness, and proves only the
frontier identification. -/
/-- The complement in the plane of a topologically embedded closed interval is
connected.  This is the classical non-separation theorem for arcs.  It follows
by planar arc straightening (or Alexander duality); Mathlib 4.29 contains no
such theorem.  Estimated proof size: 80--130 lines once planar arc
straightening is available. -/
theorem apm_t95j06_jordan_sides_frontier_aux_arc_nonseparation
    (A : Set apm_t95j06_E2)
    (eA : Nonempty (Set.Icc (0 : ℝ) 1 ≃ₜ A)) :
    IsPreconnected Aᶜ := by
  sorry

/-- A circle homeomorphism has arbitrarily small complementary closed arcs
away from a marked point (estimated 35--60 lines).  Pull an open neighbourhood
of the marked point back to `Circle`, choose a short exponential-coordinate
arc inside it, and parametrize the complementary closed arc by `[0,1]`.
Its image lies in `J`, omits the marked point, and the removed part of `J` lies
in the prescribed neighbourhood.  This is elementary circle parametrization,
with no planar separation content. -/
theorem apm_t95j06_circle_small_complementary_closedArc
    (J : Set apm_t95j06_E2) (e : Circle ≃ₜ J)
    (p : apm_t95j06_E2) (hp : p ∈ J)
    (O : Set apm_t95j06_E2) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ A : Set apm_t95j06_E2,
      Nonempty (Set.Icc (0 : ℝ) 1 ≃ₜ A) ∧ A ⊆ J ∧ p ∉ A ∧ J \ A ⊆ O := by
  classical
  set q : Circle := e.symm ⟨p, hp⟩ with hq
  let g : ℝ → apm_t95j06_E2 := fun θ => (e (q * Circle.exp θ)).1
  have hgc : Continuous g :=
    continuous_subtype_val.comp (e.continuous.comp
      (continuous_const.mul Circle.exp.continuous))
  have hg0 : g 0 = p := by
    simp [g, hq]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hgc) 0
    (by simpa [Set.mem_preimage, hg0] using hpO)
  set ε : ℝ := min δ (Real.pi / 2) with hε
  have hε0 : 0 < ε := lt_min hδ (by positivity)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεpi : ε ≤ Real.pi / 2 := min_le_right _ _
  have hpi := Real.pi_pos
  let L : ℝ := 2 * Real.pi - 2 * ε
  have hL : 0 < L := by simp only [L]; linarith
  let f : Set.Icc (0 : ℝ) 1 → apm_t95j06_E2 := fun t => g (ε + t.1 * L)
  have hfc : Continuous f :=
    hgc.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
  have hθrange : ∀ t : Set.Icc (0 : ℝ) 1, ε ≤ ε + t.1 * L ∧ ε + t.1 * L ≤ 2 * Real.pi - ε := by
    intro t
    have h1 := t.2.1; have h2 := t.2.2
    constructor
    · nlinarith
    · have : t.1 * L ≤ L := by nlinarith
      simp only [L] at this; linarith
  have hfinj : Function.Injective f := by
    intro s t hst
    have h1 : e (q * Circle.exp (ε + s.1 * L)) = e (q * Circle.exp (ε + t.1 * L)) :=
      Subtype.ext hst
    have h2 := mul_left_cancel (e.injective h1)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h2
    have hs := hθrange s; have ht := hθrange t
    have hm0 : m = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        nlinarith
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hgt
        nlinarith
    subst hm0
    simp only [Int.cast_zero, zero_mul, add_zero, add_right_inj] at hm
    exact Subtype.ext (mul_right_cancel₀ hL.ne' hm)
  have hemb := (hfc.isClosedEmbedding hfinj).isEmbedding
  refine ⟨Set.range f, ⟨hemb.toHomeomorph⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (e _).2
  · rintro ⟨t, ht⟩
    have h1 : e (q * Circle.exp (ε + t.1 * L)) = e q := by
      apply Subtype.ext
      simpa [f, g, hq] using ht
    have h2 : Circle.exp (ε + t.1 * L) = Circle.exp 0 := by
      have := e.injective h1
      rw [Circle.exp_zero]
      calc Circle.exp (ε + t.1 * L) = q⁻¹ * (q * Circle.exp (ε + t.1 * L)) := by group
        _ = q⁻¹ * q := by rw [this]
        _ = 1 := inv_mul_cancel q
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h2
    have hs := hθrange t
    rcases lt_trichotomy m 0 with hlt | heq | hgt
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith
    · subst heq; simp at hm; linarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hgt
      nlinarith
  · rintro x ⟨hxJ, hxA⟩
    set w : Circle := q⁻¹ * e.symm ⟨x, hxJ⟩ with hw
    set θ : ℝ := Complex.arg (w : ℂ) with hθ
    have hθw : Circle.exp θ = w := Circle.exp_arg w
    have hθlo : -Real.pi < θ := Complex.neg_pi_lt_arg _
    have hθhi : θ ≤ Real.pi := Complex.arg_le_pi _
    have hgx : ∀ φ : ℝ, Circle.exp φ = w → g φ = x := by
      intro φ hφ
      simp only [g, hφ, hw, mul_inv_cancel_left, Homeomorph.apply_symm_apply]
    by_cases hsmall : |θ| < ε
    · have hmem := hball (show θ ∈ Metric.ball (0 : ℝ) δ by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
      rw [Set.mem_preimage, hgx θ hθw] at hmem
      exact hmem
    · exfalso
      apply hxA
      push_neg at hsmall
      rcases le_or_gt 0 θ with h0 | h0
      · rw [abs_of_nonneg h0] at hsmall
        refine ⟨⟨(θ - ε) / L, div_nonneg (by linarith) hL.le, ?_⟩, ?_⟩
        · rw [div_le_one hL]; simp only [L]; linarith
        · change g (ε + (θ - ε) / L * L) = x
          rw [div_mul_cancel₀ _ hL.ne']
          exact hgx _ (by rw [add_sub_cancel]; exact hθw)
      · rw [abs_of_neg h0] at hsmall
        refine ⟨⟨(θ + 2 * Real.pi - ε) / L, div_nonneg (by linarith) hL.le, ?_⟩, ?_⟩
        · rw [div_le_one hL]; simp only [L]; linarith
        · change g (ε + (θ + 2 * Real.pi - ε) / L * L) = x
          rw [div_mul_cancel₀ _ hL.ne']
          apply hgx
          rw [show ε + (θ + 2 * Real.pi - ε) = θ + (1 : ℤ) * (2 * Real.pi) by push_cast; ring]
          rw [← hθw]
          exact Circle.exp_eq_exp.mpr ⟨1, rfl⟩

/-- Arc non-separation implies local access to each of two connected Jordan
sides.  Remove a small open circle arc about `p`; its complementary closed arc
does not separate the plane, so a connected bridge between the two sides,
avoiding that closed arc, must cross the small arc.  Openness then supplies
points of both sides arbitrarily close to `p`.  This is strictly the local
access step, not a frontier equality.  Estimated proof size: 55--85 lines. -/
theorem apm_t95j06_jordan_sides_frontier_aux_local_access
    (harc : ∀ (A : Set apm_t95j06_E2),
      Nonempty (Set.Icc (0 : ℝ) 1 ≃ₜ A) → IsPreconnected Aᶜ)
    (J : Set apm_t95j06_E2) (eJ : Nonempty (Circle ≃ₜ J))
    (inside outside : Set apm_t95j06_E2)
    (hi : IsOpen inside) (ho : IsOpen outside)
    (hin : inside.Nonempty) (hout : outside.Nonempty)
    (hpi : IsPreconnected inside) (hpo : IsPreconnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : Jᶜ = inside ∪ outside) :
    ∀ p ∈ J, p ∈ closure inside ∧ p ∈ closure outside := by
  intro p hp
  let e := eJ.some
  have side_access (S T : Set apm_t95j06_E2)
      (hSopen : IsOpen S) (hTopen : IsOpen T)
      (hSne : S.Nonempty) (hTne : T.Nonempty)
      (hST : Disjoint S T) (hcov : Jᶜ = S ∪ T) :
      p ∈ closure S := by
    by_contra hpcl
    let O : Set apm_t95j06_E2 := (closure S)ᶜ
    have hO : IsOpen O := isClosed_closure.isOpen_compl
    have hpO : p ∈ O := hpcl
    obtain ⟨A, hAarc, hAJ, hpA, hrem⟩ :=
      apm_t95j06_circle_small_complementary_closedArc J e p hp O hO hpO
    have hAconn := harc A hAarc
    have hSsub : S ⊆ Jᶜ := by rw [hcov]; exact Set.subset_union_left
    have hTsub : T ⊆ Jᶜ := by rw [hcov]; exact Set.subset_union_right
    have hS_Ac : S ⊆ Aᶜ := fun x hx hxa => hSsub hx (hAJ hxa)
    have hT_Ac : T ⊆ Aᶜ := fun x hx hxa => hTsub hx (hAJ hxa)
    have hT_O : T ⊆ O := by
      intro x hx
      intro hxcl
      have hTc : IsClosed Tᶜ := IsOpen.isClosed_compl hTopen
      have hclsub : closure S ⊆ Tᶜ := hTc.closure_subset_iff.2
        (Set.disjoint_left.1 hST)
      exact hclsub hxcl hx
    have hAc_cover : Aᶜ ⊆ S ∪ O := by
      intro x hxA
      by_cases hxJ : x ∈ J
      · exact Or.inr (hrem ⟨hxJ, hxA⟩)
      · have hxJc : x ∈ Jᶜ := hxJ
        rw [hcov] at hxJc
        exact hxJc.imp_right (fun hxT => hT_O hxT)
    have hdis : Aᶜ ∩ (S ∩ O) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, -, hxS, hxO⟩
      exact hxO (subset_closure hxS)
    rcases isPreconnected_iff_subset_of_disjoint.1 hAconn
      S O hSopen hO hAc_cover hdis with hsub | hsub
    · obtain ⟨x, hx⟩ := hTne
      exact (hST.le_bot ⟨hsub (hT_Ac hx), hx⟩)
    · obtain ⟨x, hx⟩ := hSne
      exact (hsub (hS_Ac hx)) (subset_closure hx)
  exact ⟨side_access inside outside hi ho hin hout hdisj hcover,
    side_access outside inside ho hi hout hin hdisj.symm
      (hcover.trans (Set.union_comm _ _))⟩

theorem apm_t95j06_jordan_sides_frontier
    (J : Set apm_t95j06_E2) (eJ : Nonempty (Circle ≃ₜ J))
    (inside outside : Set apm_t95j06_E2)
    (hi : IsOpen inside) (ho : IsOpen outside)
    (hin : inside.Nonempty) (hout : outside.Nonempty)
    (hpi : IsPreconnected inside) (hpo : IsPreconnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : Jᶜ = inside ∪ outside) :
    J = frontier inside ∧ J = frontier outside := by
  have haccess := apm_t95j06_jordan_sides_frontier_aux_local_access
    apm_t95j06_jordan_sides_frontier_aux_arc_nonseparation J eJ inside outside
      hi ho hin hout hpi hpo hdisj hcover
  have hi_sub : inside ⊆ Jᶜ := by
    rw [hcover]
    exact Set.subset_union_left
  have ho_sub : outside ⊆ Jᶜ := by
    rw [hcover]
    exact Set.subset_union_right
  have hfi : J = frontier inside := by
    apply Set.Subset.antisymm
    · intro p hp
      rw [frontier, hi.interior_eq]
      exact ⟨(haccess p hp).1, fun hpin => hi_sub hpin hp⟩
    · intro p hp
      by_contra hpJ
      have hpcompl : p ∈ Jᶜ := hpJ
      rw [hcover] at hpcompl
      rcases hpcompl with hpinside | hpoutside
      · exact hp.2 (mem_interior_iff_mem_nhds.2 (hi.mem_nhds hpinside))
      · have hclosed : IsClosed outsideᶜ := ho.isClosed_compl
        have hsub : inside ⊆ outsideᶜ := Set.disjoint_left.1 hdisj
        have hpcl : p ∈ closure inside := frontier_subset_closure hp
        exact (hclosed.closure_subset_iff.2 hsub hpcl) hpoutside
  have hfo : J = frontier outside := by
    apply Set.Subset.antisymm
    · intro p hp
      rw [frontier, ho.interior_eq]
      exact ⟨(haccess p hp).2, fun hpout => ho_sub hpout hp⟩
    · intro p hp
      by_contra hpJ
      have hpcompl : p ∈ Jᶜ := hpJ
      rw [hcover] at hpcompl
      rcases hpcompl with hpinside | hpoutside
      · have hclosed : IsClosed insideᶜ := hi.isClosed_compl
        have hsub : outside ⊆ insideᶜ := Set.disjoint_right.1 hdisj
        have hpcl : p ∈ closure outside := frontier_subset_closure hp
        exact (hclosed.closure_subset_iff.2 hsub hpcl) hpinside
      · exact hp.2 (mem_interior_iff_mem_nhds.2 (ho.mem_nhds hpoutside))
  exact ⟨hfi, hfo⟩

/-- **LIBRARY, Jordan-curve separation (estimated 250--450 lines).**
This is the classical Jordan curve theorem in its separation form.  A winding
number proof shows that the complement of an embedded circle has one bounded
and one unbounded connected component; invariance of domain and local arc
straightening show that both have the curve as frontier.  Mathlib 4.29 has
connected-component and winding-number APIs, but no theorem combining them;
the searches found only conditional winding results such as
`ConstructionTargets/EmbeddedCirclePreimage.lean:66` and
`ConstructionTargets/DiskBoundedPreimageDuality.lean:26`, neither of which
proves planar separation.  This is strictly more primitive than the crosscut
theorem: it mentions only an embedded circle and its full-plane complement. -/
theorem apm_t95j06_planar_jordan_separation :
    apm_t95j06_PlanarJordanSeparation := by
  intro J eJ
  obtain ⟨inside, outside, hi, ho, hin, hout, hdisj, hcover⟩ :=
    apm_t95j06_jordan_complement_separates J eJ
  obtain ⟨hpi, hpo⟩ := apm_t95j06_jordan_complement_atMostTwo
    J eJ inside outside hi ho hin hout hdisj hcover
  obtain ⟨hfi, hfo⟩ := apm_t95j06_jordan_sides_frontier
    J eJ inside outside hi ho hin hout hpi hpo hdisj hcover
  exact ⟨inside, outside, hi, ho, hin, hout, hpi, hpo,
    hdisj, hcover, hfi, hfo⟩

/-- The exterior of a positive-radius planar closed disk is connected.
It is the continuous image of the unit circle times the radius interval
`(r,∞)` under scalar multiplication. -/
lemma apm_t95j06_planar_crosscut_of_jordan_aux_exterior
    (r : ℝ) (hr : 0 < r) :
    IsConnected ((Metric.closedBall (0 : apm_t95j06_E2) r)ᶜ) := by
  let S := Metric.sphere (0 : apm_t95j06_E2) 1
  let T := Set.Ioi r
  letI : ConnectedSpace S := Subtype.connectedSpace
    (isConnected_sphere (E := apm_t95j06_E2)
      (by simp [← Module.finrank_eq_rank, apm_t95j06_E2]) 0 (by norm_num : (0 : ℝ) ≤ 1))
  letI : ConnectedSpace T := Subtype.connectedSpace isConnected_Ioi
  let f : S × T → apm_t95j06_E2 := fun p ↦ p.2.1 • p.1.1
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)
  have heq : Set.range f = (Metric.closedBall (0 : apm_t95j06_E2) r)ᶜ := by
    ext y
    constructor
    · rintro ⟨⟨a, t⟩, rfl⟩
      have ha : ‖(a : apm_t95j06_E2)‖ = 1 := by
        simpa only [S, Metric.mem_sphere, dist_zero_right] using a.2
      have ht : 0 < t.1 := lt_trans hr t.2
      change ¬ dist (f (a, t)) 0 ≤ r
      simp only [f, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ha, mul_one]
      exact not_le.mpr t.2
    · intro hy
      have hy' : r < ‖y‖ := by simpa only [Set.mem_compl_iff,
        Metric.mem_closedBall, dist_zero_right, not_le] using hy
      have hn : 0 < ‖y‖ := lt_trans hr hy'
      have ha : ‖y‖⁻¹ • y ∈ S := by
        simp [S, Metric.mem_sphere, dist_zero_right, norm_smul,
          abs_of_pos (inv_pos.mpr hn), hn.ne']
      refine ⟨(⟨‖y‖⁻¹ • y, ha⟩, ⟨‖y‖, hy'⟩), ?_⟩
      simp [f, smul_smul, hn.ne']
  rw [← heq]
  exact isConnected_range hf

/-- Jordan domains can be labelled relative to a containing disk. The entire
exterior lies in one domain, and the other domain lies in the open disk.
This uses only connectedness of the disk exterior and the given Jordan
partition; it does not assume the crosscut theorem or an arc-pasting result. -/
lemma apm_t95j06_planar_crosscut_of_jordan_aux_label_domains
    (hJordan : apm_t95j06_PlanarJordanSeparation)
    (r : ℝ) (hr : 0 < r) (J : Set apm_t95j06_E2)
    (he : Nonempty (Circle ≃ₜ J)) (hJ : J ⊆ Metric.closedBall 0 r) :
    ∃ I O : Set apm_t95j06_E2,
      IsOpen I ∧ IsOpen O ∧ I.Nonempty ∧ O.Nonempty ∧
      IsPreconnected I ∧ IsPreconnected O ∧ Disjoint I O ∧
      Jᶜ = I ∪ O ∧ J = frontier I ∧ J = frontier O ∧
      I ⊆ Metric.ball 0 r ∧ (Metric.closedBall 0 r)ᶜ ⊆ O := by
  obtain ⟨L, R, hL, hR, hnL, hnR, hcL, hcR, hd, hcover, hfL, hfR⟩ := hJordan J he
  have hext : (Metric.closedBall (0 : apm_t95j06_E2) r)ᶜ ⊆ L ∪ R := by
    rw [← hcover]
    exact Set.compl_subset_compl.mpr hJ
  have split := (apm_t95j06_planar_crosscut_of_jordan_aux_exterior r hr).isPreconnected.subset_or_subset
    hL hR hd hext
  rcases split with hleft | hright
  · refine ⟨R, L, hR, hL, hnR, hnL, hcR, hcL, hd.symm, ?_, hfR, hfL, ?_, hleft⟩
    · simpa [Set.union_comm] using hcover
    · have hsub : R ⊆ Metric.closedBall 0 r := by
        intro y hy
        by_contra hout
        exact Set.disjoint_left.mp hd (hleft hout) hy
      simpa only [interior_closedBall (0 : apm_t95j06_E2) hr.ne'] using
        interior_maximal hsub hR
  · refine ⟨L, R, hL, hR, hnL, hnR, hcL, hcR, hd, hcover, hfL, hfR, ?_, hright⟩
    have hsub : L ⊆ Metric.closedBall 0 r := by
      intro y hy
      by_contra hout
      exact Set.disjoint_left.mp hd hy (hright hout)
    simpa only [interior_closedBall (0 : apm_t95j06_E2) hr.ne'] using
      interior_maximal hsub hL

/-- Restricting an open set to an open neighbourhood preserves its frontier
at points of that neighbourhood. This is the local frontier step for a crosscut. -/
lemma apm_t95j06_planar_crosscut_of_jordan_aux_frontier_restrict
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) :
    frontier U ∩ V ⊆ frontier (U ∩ V) := by
  intro x hx
  rw [(hU.inter hV).frontier_eq]
  refine ⟨?_, fun h => (hU.frontier_eq ▸ hx.1).2 h.1⟩
  apply mem_closure_iff.mpr
  intro W hW hxW
  have hcl : x ∈ closure U := frontier_subset_closure hx.1
  obtain ⟨y, hyW, hyU⟩ := mem_closure_iff.mp hcl (W ∩ V) (hW.inter hV) ⟨hxW, hx.2⟩
  exact ⟨y, hyW.1, hyU, hyW.2⟩

/-- The interior points of a disk crosscut are nonempty and dense in the
whole arc, including its endpoints. Parameter values strictly between the
endpoints map into the open disk, and their closure is the closed parameter
interval. This uses only the endpoint intersection condition. -/
lemma apm_t95j06_planar_crosscut_of_jordan_aux_arc_density
    (r : ℝ) (A : Set apm_t95j06_E2)
    (e : Set.Icc (-1 : ℝ) 1 ≃ₜ A)
    (hA : A ⊆ Metric.closedBall 0 r)
    (hend : A ∩ Metric.sphere 0 r =
      ({(e ⟨-1, by norm_num⟩ : apm_t95j06_E2),
        (e ⟨1, by norm_num⟩ : apm_t95j06_E2)} : Set apm_t95j06_E2)) :
    (A ∩ Metric.ball 0 r).Nonempty ∧ A ⊆ closure (A ∩ Metric.ball 0 r) := by
  let a : Set.Icc (-1 : ℝ) 1 := ⟨-1, by norm_num⟩
  let b : Set.Icc (-1 : ℝ) 1 := ⟨1, by norm_num⟩
  let f : Set.Icc (-1 : ℝ) 1 → apm_t95j06_E2 := fun t => (e t).val
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hsub : f '' Set.Ioo a b ⊆ A ∩ Metric.ball 0 r := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨(e t).property, ?_⟩
    have hle : dist (f t) 0 ≤ r := hA (e t).property
    apply lt_of_le_of_ne hle
    intro heq
    have hs : f t ∈ A ∩ Metric.sphere 0 r := ⟨(e t).property, heq⟩
    rw [hend] at hs
    rcases Set.mem_insert_iff.mp hs with ha | hb
    · have he : t = a := e.injective (Subtype.ext ha)
      exact (ne_of_gt ht.1) he
    · have he : t = b := e.injective (Subtype.ext (Set.mem_singleton_iff.mp hb))
      exact (ne_of_lt ht.2) he
  constructor
  · have ht : (⟨0, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) ∈ Set.Ioo a b := by
      constructor <;> norm_num [a, b]
    exact ⟨_, hsub ⟨_, ht, rfl⟩⟩
  · intro x hx
    obtain ⟨t, ht⟩ := e.surjective ⟨x, hx⟩
    have htc : t ∈ closure (Set.Ioo a b) := by
      rw [closure_Ioo (show a ≠ b by intro h; have := congrArg Subtype.val h; norm_num [a, b] at this)]
      exact t.property
    have hfc : f t ∈ closure (f '' Set.Ioo a b) :=
      image_closure_subset_closure_image hf ⟨t, htc, rfl⟩
    have hfc' := closure_mono hsub hfc
    simpa [f, ht] using hfc'

/-- One pasted Jordan curve already gives two nonempty open disk sides, with
the entire crosscut in both frontiers. The inner side is connected. The only
conclusion intentionally absent is connectedness of the restricted outer side:
that requires the geometry of the complementary boundary arc. No separation
claim is assumed here beyond the supplied Jordan hypothesis. -/
lemma apm_t95j06_planar_crosscut_of_jordan_aux_one_curve_partition
    (hJordan : apm_t95j06_PlanarJordanSeparation)
    (r : ℝ) (hr : 0 < r) (A B : Set apm_t95j06_E2)
    (hA : A ⊆ Metric.closedBall 0 r) (hB : B ⊆ Metric.sphere 0 r)
    (he : Nonempty (Circle ≃ₜ ↥(A ∪ B)))
    (e : Set.Icc (-1 : ℝ) 1 ≃ₜ A)
    (hend : A ∩ Metric.sphere 0 r =
      ({(e ⟨-1, by norm_num⟩ : apm_t95j06_E2),
        (e ⟨1, by norm_num⟩ : apm_t95j06_E2)} : Set apm_t95j06_E2)) :
    ∃ L R : Set apm_t95j06_E2,
      IsOpen L ∧ IsOpen R ∧ L.Nonempty ∧ R.Nonempty ∧
      IsPreconnected L ∧ Disjoint L R ∧
      Metric.ball 0 r \ A = L ∪ R ∧
      A ⊆ frontier L ∧ A ⊆ frontier R := by
  obtain ⟨hAn, hAdense⟩ :=
    apm_t95j06_planar_crosscut_of_jordan_aux_arc_density r A e hA hend
  have hJ : A ∪ B ⊆ Metric.closedBall 0 r :=
    Set.union_subset hA (hB.trans Metric.sphere_subset_closedBall)
  obtain ⟨I, O, hi, ho, hin, hon, hci, hco, hd, hc, hfi, hfo, hib, hext⟩ :=
    apm_t95j06_planar_crosscut_of_jordan_aux_label_domains hJordan r hr (A ∪ B) he hJ
  have hai : A ⊆ frontier I := fun x hx => hfi ▸ Or.inl hx
  have hao : A ⊆ frontier (O ∩ Metric.ball 0 r) := by
    have hlocal : A ∩ Metric.ball 0 r ⊆ frontier (O ∩ Metric.ball 0 r) := by
      intro x hx
      exact apm_t95j06_planar_crosscut_of_jordan_aux_frontier_restrict ho Metric.isOpen_ball
        ⟨hfo ▸ Or.inl hx.1, hx.2⟩
    exact hAdense.trans (closure_minimal hlocal isClosed_frontier)
  have hrn : (O ∩ Metric.ball 0 r).Nonempty := by
    obtain ⟨x, hx⟩ := hAn
    have hxcl := frontier_subset_closure (hao hx.1)
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, closure_empty] at hxcl
    exact hxcl
  refine ⟨I, O ∩ Metric.ball 0 r, hi, ho.inter Metric.isOpen_ball,
    hin, hrn, hci, hd.mono_right Set.inter_subset_left, ?_, hai, hao⟩
  ext x
  constructor
  · rintro ⟨hxb, hxA⟩
    have hxJ : x ∉ A ∪ B := by
      rintro (ha | hb)
      · exact hxA ha
      · have hs := hB hb
        exact (ne_of_lt hxb) hs
    have hxcover : x ∈ I ∪ O := by rw [← hc]; exact hxJ
    rcases hxcover with hxI | hxO
    · exact Or.inl hxI
    · exact Or.inr ⟨hxO, hxb⟩
  · rintro (hxI | ⟨hxO, hxb⟩)
    · refine ⟨hib hxI, ?_⟩
      intro hxA
      exact (hi.frontier_eq ▸ hai hxA).2 hxI
    · refine ⟨hxb, ?_⟩
      intro hxA
      exact (ho.frontier_eq ▸ (show x ∈ frontier O from hfo ▸ Or.inl hxA)).2 hxO

/-- To distinguish the inner domains of the two pasted curves, it suffices
to exhibit a boundary point of the second domain outside the first curve.
Connectedness puts the second domain on one Jordan side; that boundary point
rules out nesting inside the first inner domain. This is a general domain
comparison lemma and asserts no new planar separation theorem. -/
lemma apm_t95j06_planar_crosscut_of_jordan_aux_domains_disjoint
    {X : Type*} [TopologicalSpace X] {J I O D : Set X}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O)
    (hcover : Jᶜ = I ∪ O) (hfront : J = frontier I)
    (hD : IsPreconnected D) (hsub : D ⊆ Jᶜ)
    (p : X) (hp : p ∈ frontier D) (hpJ : p ∉ J) (hpI : p ∉ I) :
    Disjoint I D := by
  have hcov : D ⊆ I ∪ O := hcover ▸ hsub
  rcases hD.subset_or_subset hI hO hd hcov with hi | ho
  · have hpc : p ∈ closure I := closure_mono hi (frontier_subset_closure hp)
    have hpf : p ∈ frontier I := by
      rw [hI.frontier_eq]
      exact ⟨hpc, hpI⟩
    exact False.elim (hpJ (hfront ▸ hpf))
  · exact hd.mono_right ho

/-- Closing a disk crosscut by either of the two boundary semicircles reduces
the crosscut theorem to Jordan-curve separation (estimated 90--150 lines).
The hypothesis that the arc meets the boundary only at its endpoints makes
both pasted curves embedded.  Apply Jordan separation to the two curves and
intersect their complementary domains with the open disk; the matching sides
are the two connected components of the disk minus the crosscut, and the
Jordan frontier equalities give the required crosscut frontier equalities.
This lemma assumes the complete Jordan separation interface and contains only
explicit circle parametrization, pasting, and set algebra. -/
theorem apm_t95j06_planar_crosscut_of_jordan
    (hJordan : apm_t95j06_PlanarJordanSeparation) :
    apm_t95j06_PlanarCrosscutSeparation := by
  sorry

/-- **LIBRARY P, planar crosscut theorem (estimated 180--280 lines).**
This is the classical crosscut theorem for a disk, a standard consequence of
the Jordan curve theorem: join either boundary subarc to the crosscut, apply
Jordan separation, and identify the two complementary sides.  The endpoint
condition prevents an arc from touching the boundary elsewhere.  This leaf is
entirely about subsets of `apm_t95j06_E2`; it has no base space, chart, or
product hypothesis.  No matching sorry-free result was found in
`ConstructionTargets/`; the unusable Lean-4.33 Reeken theorem is the standard
source to backport only this consequence from. -/
theorem apm_t95j06_planar_crosscut_separation :
    apm_t95j06_PlanarCrosscutSeparation := by
  exact apm_t95j06_planar_crosscut_of_jordan
    apm_t95j06_planar_jordan_separation

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

/-- **LIBRARY Q, projection from planar crosscuts (estimated 180--280 lines).**
Assuming the pure disk-crosscut theorem, one explicit product chart around
`b × 0` yields the required compact continuum in the base.  Choose a small
closed disk in the chart, take the component meeting the zero slice, and
project it to `B`.  Compactness and connectedness pass through the projection;
the two planar sides say exactly that the projected continuum has two non-cut
endpoints and every other point is a cut point.  This is the chart restriction,
component, and projection bookkeeping left after Jordan separation is given.

At an endpoint of `[0,1]` no such product chart exists; a tripod contradicts
the two-side conclusion; a Cantor factor lacks local connectedness/planarity;
and a circle passes because the construction is local. -/
theorem apm_t95j06_planarCrosscut_productChart_twoEndpoint_at
    (hcrosscut : apm_t95j06_PlanarCrosscutSeparation)
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
  sorry

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
    apm_t95j06_planar_crosscut_separation
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

/-- **Endpoint in every puncture branch (estimated 45--75 lines).** Every
connected component of a non-endpoint puncture contains `a` or `c`.

This is true for a compact locally connected continuum because each component
of the complement of a cut point contains a non-cut point of the original
continuum: otherwise a nested basis of connected open neighbourhoods in that
branch, together with compactness, produces an additional non-cut point.
Here the hypotheses say that the only non-cut points are `a` and `c`. -/
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
  sorry

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
  sorry

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

theorem apm_t95j06_two_overlapping_realCharts_line_or_compact
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U V : Set X) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUreal : Nonempty (U ≃ₜ ℝ)) (hVreal : Nonempty (V ≃ₜ ℝ))
    (hUV : (U ∩ V).Nonempty) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ ℝ) ∨ IsCompact (U ∪ V) := by
  sorry

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

#print axioms apm_t95j06_planar_crosscut_of_jordan_aux_exterior
#print axioms apm_t95j06_planar_crosscut_of_jordan_aux_label_domains

#print axioms apm_t95j06_jordan_complement_atMostTwo_aux_of_component_bound

#print axioms apm_t95j06_jordan_complement_separates_aux_winding_locallyConstant
#print axioms apm_t95j06_jordan_complement_separates_aux_far_zero
#print axioms apm_t95j06_jordan_complement_separates

#print axioms apm_t95j06_planar_crosscut_of_jordan_aux_one_curve_partition
#print axioms apm_t95j06_planar_crosscut_of_jordan_aux_domains_disjoint

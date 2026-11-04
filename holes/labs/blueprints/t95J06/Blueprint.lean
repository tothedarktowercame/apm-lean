import Mathlib
import Mathlib.Topology.Bases
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
  sorry

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
  sorry

/-- **Sub-leaf F3a (LIBRARY, estimated 180--300 lines).**  In words: local
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
theorem apm_t95j06_circleProducts_localizeToPlanarArc
    (B : Type) (tB : TopologicalSpace B)
    (hprod : ∀ b : B, ∃ U : Set B, @IsOpen B tB U ∧ b ∈ U ∧
      apm_t95j06_IsLocallyEuclideanPlane (U × Circle)) :
    @apm_t95j06_HasPlanarArcProducts B tB := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The one-chart end argument: if every connected component of the puncture
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
lemma apm_t95j06_puncture_connected_of_components_real_aux
    (B : Type) (tB : TopologicalSpace B)
    (hc : @CompactSpace B tB) (hconn : @ConnectedSpace B tB)
    (h2 : @T2Space B tB)
    (hloc : @apm_t95j06_IsLocallyRealLine B tB) (b : B)
    (hcomponents : ∀ x : {y : B // y ≠ b},
      Nonempty ({y : {z : B // z ≠ b} //
        y ∈ connectedComponent x} ≃ₜ ℝ)) :
    @ConnectedSpace {x : B // x ≠ b} inferInstance := by
  sorry

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
  sorry

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
theorem apm_t95j06_increasing_interval_union_homeomorph_real
    (X : Type) [TopologicalSpace X] [T2Space X]
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n))
    (hnested : ∀ n, closure (U n) ⊆ U (n + 1))
    (hreal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hcover : (⋃ n, U n) = Set.univ) :
    Nonempty (X ≃ₜ ℝ) := by
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
/-- A finite chain of local sections lifts one traversal of the circle.

In words, compactness of `[0,1]` gives a finite subdivision subordinate to
the inverse images of the local-section domains.  Starting with the first
local section, multiply each subsequent one by a constant circle element so
that adjacent pieces agree at their common endpoint; fibre transitivity gives
the constant and the closed-interval pasting lemma gives continuity.
Estimated size: 180--300 lines. -/
theorem apm_t95j06_principalCircleBundle_interval_section
    (X B : Type*) [TopologicalSpace X] (tB : TopologicalSpace B)
    (P : @apm_t95j06_PrincipalCircleBundle X B inferInstance tB)
    (e : @Homeomorph B Circle tB inferInstance)
    (hloc : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ s : U → X, Continuous s ∧ ∀ u, P.proj (s u) = u) :
    ∃ σ : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} → X,
      Continuous σ ∧ ∀ t,
        P.proj (σ t) = e.symm (Circle.exp (2 * Real.pi * t.1)) := by
  sorry

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
  sorry

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

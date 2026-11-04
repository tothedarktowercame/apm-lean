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
theorem apm_t95j06_hopf_slices_component_principalBundle_aux_core
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (hinv : apm_t95j06_IsCircleInvariant F) :
    ∀ x : F, ∃ (B : Type) (tB : TopologicalSpace B),
      @CompactSpace B tB ∧ @ConnectedSpace B tB ∧ @T2Space B tB ∧
      @SecondCountableTopology B tB ∧
      Nonempty (@apm_t95j06_hopf_slices_component_principalBundle_aux_Core
        F x B tB) := by
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
  sorry

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

/-- **LIBRARY 3(a), manifold-factor cancellation (estimated 1800--4000
lines).**  For the Hopf quotient presentation, local products with `Circle`
are surface charts only when the base factor is locally a real line.

This is the classical low-dimensional manifold-factor theorem: a locally
compact, second-countable Hausdorff `B` for which `B × S¹` is locally a
2-manifold is locally a 1-manifold.  One route uses local homology to show that
`B` is a one-dimensional homology manifold, local contractibility from its
retract in a bundle chart, and the classification of one-dimensional ANR
homology manifolds.  The component atlas and bundle charts supply precisely
those hypotheses.  Non-Hausdorff and non-second-countable counterexamples are
excluded explicitly; dimension zero fails because a discrete factor times a
circle is one-dimensional. -/
theorem apm_t95j06_principalBundle_base_locallyRealLine
    (F : Set apm_t95j06_S5)
    (hF : apm_t95j06_IsCompactOrientableSurface F)
    (x : F) (B : Type) (tB : TopologicalSpace B)
    (h2 : @T2Space B tB) (hsc : @SecondCountableTopology B tB)
    (P : @apm_t95j06_PrincipalCircleBundle
      {y : F // y ∈ connectedComponent x} B inferInstance tB) :
    @apm_t95j06_IsLocallyRealLine B tB := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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

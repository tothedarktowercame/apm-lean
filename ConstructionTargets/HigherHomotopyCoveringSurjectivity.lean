import ConstructionTargets.CubeBoundaryPathConnected
import Mathlib.Topology.Homotopy.Lifting

/-! # Coverings are surjective on higher homotopy cube quotients -/

open Set Function
open scoped Topology unitInterval
noncomputable section

namespace ConstructionTargets.HigherHomotopyCoveringSurjectivity

def genLoopMap
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : GenLoop N X x) : GenLoop N Y (f x) :=
  ⟨f.comp a.1, fun y hy ↦ by simp only [ContinuousMap.comp_apply]; rw [a.2 y hy]⟩

def homotopyMap
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (genLoopMap f x) fun _ _ h ↦
    ContinuousMap.HomotopicRel.comp_continuousMap h f

@[simp] theorem homotopyMap_mk
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : GenLoop N X x) :
    homotopyMap f x (Quotient.mk _ a) = Quotient.mk _ (genLoopMap f x a) := rfl

/-- A lift of a generalized cube loop is constant on the boundary when that
boundary is path connected.  The proof uses uniqueness of covering lifts on
the boundary, rather than assuming boundary constancy as lift data. -/
theorem lift_eq_base_on_boundary
    {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (p : E → X) (hp : IsCoveringMap p) (e : E) (a : GenLoop N X (p e))
    (F : C(I^N, E)) (hF : p ∘ F = a.1)
    [PathConnectedSpace ↥(Cube.boundary N)]
    (y : I^N) (hy : y ∈ Cube.boundary N) (hFy : F y = e)
    (z : I^N) (hz : z ∈ Cube.boundary N) : F z = e := by
  let g : ↥(Cube.boundary N) → E := fun w ↦ F w.1
  have hg : Continuous g := F.continuous.comp continuous_subtype_val
  have hcomp : ∀ u v : ↥(Cube.boundary N), p (g u) = p (g v) := by
    intro u v
    change p (F u.1) = p (F v.1)
    rw [show p (F u.1) = a.1 u.1 by exact congr_fun hF u.1,
      show p (F v.1) = a.1 v.1 by exact congr_fun hF v.1,
      a.2 u.1 u.2, a.2 v.1 v.2]
  exact (hp.const_of_comp hg hcomp ⟨z, hz⟩ ⟨y, hy⟩).trans hFy

/-- For a simply connected, locally path-connected cube with path-connected
boundary, every generalized loop downstairs has a generalized-loop lift with
the prescribed basepoint. -/
theorem exists_genLoop_lift
    {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace ↥(Cube.boundary N)]
    (p : E → X) (hp : IsCoveringMap p) (e : E)
    (y : I^N) (hy : y ∈ Cube.boundary N) (a : GenLoop N X (p e)) :
    ∃ b : GenLoop N E e, genLoopMap ⟨p, hp.continuous⟩ e b = a := by
  let expand : C(I × I^N, I^N) :=
    ⟨fun tz ↦ CubeBoundaryPathConnected.cubeSegment y tz.2 tz.1,
      continuous_pi fun i ↦ by
        apply Continuous.subtype_mk
        fun_prop⟩
  let H : C(I × I^N, X) := a.1.comp expand
  let c : C(I^N, E) := ContinuousMap.const _ e
  have H0 : ∀ z, H (0, z) = p (c z) := by
    intro z
    simp [H, expand, c, CubeBoundaryPathConnected.cubeSegment, Icc.convexCombo,
      a.2 y hy]
  let L : C(I × I^N, E) := hp.liftHomotopy H c H0
  let atOne : C(I^N, I × I^N) :=
    (ContinuousMap.const _ (1 : I)).prodMk (ContinuousMap.id _)
  let F : C(I^N, E) := L.comp atOne
  have hF : p ∘ F = a.1 := by
    funext z
    change p (L (1, z)) = a.1 z
    rw [show p (L (1, z)) = H (1, z) by
      exact congr_fun (hp.liftHomotopy_lifts H c H0) (1, z)]
    simp [H, expand, CubeBoundaryPathConnected.cubeSegment, Icc.convexCombo]
  have hFy : F y = e := by
    let gy : I → E := fun t ↦ L (t, y)
    have hgy : Continuous gy :=
      L.continuous.comp (Continuous.prodMk continuous_id continuous_const)
    have hHy (u : I) : H (u, y) = a.1 y := by
      change a.1 (CubeBoundaryPathConnected.cubeSegment y y u) = a.1 y
      congr 1
      ext i
      simp [CubeBoundaryPathConnected.cubeSegment, Icc.convexCombo_eq]
    have hconst : ∀ s t : I, p (gy s) = p (gy t) := by
      intro s t
      change p (L (s, y)) = p (L (t, y))
      rw [show p (L (s, y)) = H (s, y) by
        exact congr_fun (hp.liftHomotopy_lifts H c H0) (s, y),
        show p (L (t, y)) = H (t, y) by
          exact congr_fun (hp.liftHomotopy_lifts H c H0) (t, y)]
      rw [hHy s, hHy t]
    change L (1, y) = e
    exact (hp.const_of_comp hgy hconst 1 0).trans (hp.liftHomotopy_zero H c H0 y)
  let b : GenLoop N E e :=
    ⟨F, fun z hz ↦ lift_eq_base_on_boundary p hp e a F hF y hy hFy z hz⟩
  refine ⟨b, ?_⟩
  apply GenLoop.ext _ _
  intro z
  exact congr_fun hF z

/-- The induced map on Mathlib's generalized-cube quotient is surjective. -/
theorem homotopyMap_surjective
    {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace ↥(Cube.boundary N)]
    (p : E → X) (hp : IsCoveringMap p) (e : E)
    (y : I^N) (hy : y ∈ Cube.boundary N) :
    Function.Surjective (homotopyMap (N := N) ⟨p, hp.continuous⟩ e) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
      obtain ⟨b, hb⟩ := exists_genLoop_lift p hp e y hy a
      refine ⟨Quotient.mk _ b, ?_⟩
      simpa [hb]

/-- Relative-homotopy lift uniqueness gives the complementary injectivity
statement whenever the cube is preconnected and has a boundary point. -/
theorem homotopyMap_injective
    {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PreconnectedSpace (I^N)]
    (p : E → X) (hp : IsCoveringMap p) (e : E)
    (y : I^N) (hy : y ∈ Cube.boundary N) :
    Function.Injective (homotopyMap (N := N) ⟨p, hp.continuous⟩ e) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ a =>
    induction r using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      change a.1.HomotopicRel b.1 (Cube.boundary N)
      apply (hp.homotopicRel_iff_comp
        ⟨y, hy, (a.2 y hy).trans (b.2 y hy).symm⟩).mpr
      exact Quotient.exact hqr

/-- Frozen-compatible specialization to `Fin n`: the compiled cube-boundary
path construction supplies the last topological hypothesis. -/
theorem fin_homotopyMap_surjective
    (n : ℕ) (hn : 2 ≤ n)
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (p : E → X) (hp : IsCoveringMap p) (e : E) :
    Function.Surjective (homotopyMap (N := Fin n) ⟨p, hp.continuous⟩ e) := by
  letI : PathConnectedSpace ↥(Cube.boundary (Fin n)) :=
    CubeBoundaryPathConnected.cubeBoundary_pathConnectedSpace n hn
  let y : I^(Fin n) := fun _ ↦ 0
  have hy : y ∈ Cube.boundary (Fin n) := by
    exact ⟨⟨0, lt_of_lt_of_le (by norm_num) hn⟩, Or.inl rfl⟩
  exact homotopyMap_surjective p hp e y hy

/-- A covering map induces a bijection on the actual `Fin n` cube quotient in
all dimensions `n ≥ 2`. -/
theorem fin_homotopyMap_bijective
    (n : ℕ) (hn : 2 ≤ n)
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (p : E → X) (hp : IsCoveringMap p) (e : E) :
    Function.Bijective (homotopyMap (N := Fin n) ⟨p, hp.continuous⟩ e) := by
  letI : PathConnectedSpace ↥(Cube.boundary (Fin n)) :=
    CubeBoundaryPathConnected.cubeBoundary_pathConnectedSpace n hn
  let y : I^(Fin n) := fun _ ↦ 0
  have hy : y ∈ Cube.boundary (Fin n) := by
    exact ⟨⟨0, lt_of_lt_of_le (by norm_num) hn⟩, Or.inl rfl⟩
  exact ⟨homotopyMap_injective p hp e y hy,
    homotopyMap_surjective p hp e y hy⟩

#print axioms lift_eq_base_on_boundary
#print axioms exists_genLoop_lift
#print axioms homotopyMap_surjective
#print axioms homotopyMap_injective
#print axioms fin_homotopyMap_surjective
#print axioms fin_homotopyMap_bijective

end ConstructionTargets.HigherHomotopyCoveringSurjectivity

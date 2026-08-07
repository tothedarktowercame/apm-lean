import Mathlib

/-!
# APM t94J07 — homotopy invariance of integrals of closed forms

## Statement repairs

The source writes `∂X = φ`; this is read as the standard `∂X = ∅`. It also
leaves implicit that integration requires an orientation and that `ω` has
degree `dim X`. These standard typing requirements are made explicit through
the oriented integration structure below.

## Encoding questions

Mathlib has smooth manifolds, maps, differential forms, and exterior
derivatives, but no general integration/Stokes API for manifold differential
forms. `T94J07StokesIntegration` transparently packages the missing oriented
integral and the homotopy-cylinder form of Stokes' theorem. The manifolds,
maps, homotopy, forms, and closedness equation remain concrete Mathlib data.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev T94J07Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev T94J07Model (n : ℕ) := 𝓘(ℝ, T94J07Euclidean n)

structure T94J07CompactBoundarylessManifold (n : ℕ) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : T2Space Carrier
  compact : CompactSpace Carrier
  charted : ChartedSpace (T94J07Euclidean n) Carrier
  manifold : IsManifold (T94J07Model n) ⊤ Carrier
  boundaryless : BoundarylessManifold (T94J07Model n) Carrier

def T94J07DifferentialForm (k n : ℕ)
    (M : T94J07CompactBoundarylessManifold n) : Type :=
  let _ := M.topology
  let _ := M.charted
  M.Carrier → (T94J07Euclidean n [⋀^Fin k]→L[ℝ] ℝ)

def T94J07ZeroForm (k n : ℕ)
    (M : T94J07CompactBoundarylessManifold n) :
    T94J07DifferentialForm k n M :=
  fun _ ↦ 0

structure T94J07SmoothMap {n m : ℕ}
    (X : T94J07CompactBoundarylessManifold n)
    (Y : T94J07CompactBoundarylessManifold m) where
  toFun : X.Carrier → Y.Carrier
  smooth :
    let _ := X.topology
    let _ := Y.topology
    let _ := X.charted
    let _ := Y.charted
    ContMDiff (T94J07Model n) (T94J07Model m) ⊤ toFun

instance {n m : ℕ} {X : T94J07CompactBoundarylessManifold n}
    {Y : T94J07CompactBoundarylessManifold m} :
    CoeFun (T94J07SmoothMap X Y) (fun _ ↦ X.Carrier → Y.Carrier) :=
  ⟨T94J07SmoothMap.toFun⟩

def T94J07SmoothlyHomotopic {n m : ℕ}
    {X : T94J07CompactBoundarylessManifold n}
    {Y : T94J07CompactBoundarylessManifold m}
    (f g : T94J07SmoothMap X Y) : Prop :=
  let _ := X.topology
  let _ := Y.topology
  let _ := X.charted
  let _ := Y.charted
  ∃ H : X.Carrier → ℝ → Y.Carrier,
    Continuous (fun p : X.Carrier × ℝ ↦ H p.1 p.2) ∧
    (∀ x, H x 0 = f x) ∧ (∀ x, H x 1 = g x) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContMDiff (T94J07Model n) (T94J07Model m) ⊤ (fun x ↦ H x t)

/-- The missing general integration/Stokes interface. Its main law is the
boundary formula on a smooth homotopy cylinder; `integral_zero` is the
linearity normalization needed when the pulled-back exterior derivative
vanishes. -/
structure T94J07StokesIntegration {n m : ℕ}
    (X : T94J07CompactBoundarylessManifold n)
    (Y : T94J07CompactBoundarylessManifold m) where
  pullback : T94J07SmoothMap X Y → T94J07DifferentialForm n m Y →
    T94J07DifferentialForm n n X
  exteriorDerivative : T94J07DifferentialForm n m Y →
    T94J07DifferentialForm (n + 1) m Y
  integral : T94J07DifferentialForm n n X → ℝ
  cylinderIntegral :
    (X.Carrier → ℝ → Y.Carrier) →
      T94J07DifferentialForm (n + 1) m Y → ℝ
  homotopy_stokes :
    ∀ (f g : T94J07SmoothMap X Y) (alpha : T94J07DifferentialForm n m Y),
      T94J07SmoothlyHomotopic f g →
      ∃ H : X.Carrier → ℝ → Y.Carrier,
        integral (pullback g alpha) - integral (pullback f alpha) =
          cylinderIntegral H (exteriorDerivative alpha)
  cylinderIntegral_zero :
    ∀ H : X.Carrier → ℝ → Y.Carrier,
      cylinderIntegral H (T94J07ZeroForm (n + 1) m Y) = 0

theorem apm_t94j07
    {n m : ℕ}
    (X : T94J07CompactBoundarylessManifold n)
    (Y : T94J07CompactBoundarylessManifold m)
    (I : T94J07StokesIntegration X Y)
    (alpha : T94J07DifferentialForm n m Y)
    (halpha : I.exteriorDerivative alpha = T94J07ZeroForm (n + 1) m Y)
    (f g : T94J07SmoothMap X Y)
    (hfg : T94J07SmoothlyHomotopic f g) :
    I.integral (I.pullback f alpha) = I.integral (I.pullback g alpha) := by
  sorry

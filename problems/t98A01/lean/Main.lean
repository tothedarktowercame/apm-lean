import Mathlib
import Mathlib.Analysis.Fourier.AddCircle
import ConstructionTargets.Surfaces

/-!
# APM t98A01 — a five-fold surface cover and a connected sum

The fivefold example is the genuine map `(x,y) ↦ (5x,y)` on
`(ℝ/ℤ)²`.  General closed orientable surfaces and the connected-sum
calculation use the concrete polygon quotients and classification arithmetic
from `ConstructionTargets.Surfaces`.

## Statement repairs

None.

## Encoding questions

Regularity is transitivity of actual deck homeomorphisms on every fiber.
-/

open ConstructionTargets.Surfaces

noncomputable section

abbrev T98A01Torus := UnitAddCircle × UnitAddCircle

def t98A01TorusFiveCover : C(T98A01Torus, T98A01Torus) :=
  ⟨fun p ↦ (5 • p.1, p.2), by fun_prop⟩

def t98A01IsNfoldCover {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B]
    (n : ℕ) (p : E → B) : Prop :=
  IsCoveringMap p ∧ ∀ b : B, Nat.card {e : E // p e = b} = n

def t98A01IsRegularNfoldCover {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B]
    (n : ℕ) (p : E → B) : Prop :=
  t98A01IsNfoldCover n p ∧
    ∀ x y : E, p x = p y →
      ∃ h : E ≃ₜ E, (∀ z : E, p (h z) = p z) ∧ h x = y

def t98A01SumKT : Bool × ℕ := connectedSum false 2 true 1
def t98A01SumKTT : Bool × ℕ :=
  connectedSum t98A01SumKT.1 t98A01SumKT.2 true 1
def t98A01SumKTTP : Bool × ℕ :=
  connectedSum t98A01SumKTT.1 t98A01SumKTT.2 false 1
def t98A01SumKTTPK : Bool × ℕ :=
  connectedSum t98A01SumKTTP.1 t98A01SumKTTP.2 false 2

/-- Classification coordinates of `K # T # T # P # K # T`. -/
def t98A01PrintedSurfaceData : Bool × ℕ :=
  connectedSum t98A01SumKTTPK.1 t98A01SumKTTPK.2 true 1

abbrev T98A01PrintedSurface :=
  Surface t98A01PrintedSurfaceData.1 t98A01PrintedSurfaceData.2

theorem apm_t98a01 :
    t98A01IsRegularNfoldCover 5 t98A01TorusFiveCover ∧
    (∀ (g h : ℕ) (p : Surface true g → Surface true h),
      t98A01IsRegularNfoldCover 5 p →
      Nonempty (Surface true g ≃ₜ Surface true h) →
      eulerCharacteristic true g = 5 * eulerCharacteristic true h ∧
      g = 1 ∧ h = 1) ∧
    t98A01PrintedSurfaceData = (false, 11) ∧
    Nonempty (T98A01PrintedSurface ≃ₜ Surface false 11) ∧
    eulerCharacteristic t98A01PrintedSurfaceData.1
      t98A01PrintedSurfaceData.2 = -9 := by
  sorry

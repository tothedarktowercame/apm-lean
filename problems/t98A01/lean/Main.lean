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

/-- The promoted connected-sum arithmetic computes the printed classification
data without any topological assumptions. -/
lemma t98A01PrintedSurfaceData_eq :
    t98A01PrintedSurfaceData = (false, 11) := by
  decide

lemma t98A01PrintedSurface_homeomorph :
    Nonempty (T98A01PrintedSurface ≃ₜ Surface false 11) := by
  change Nonempty
    (Surface t98A01PrintedSurfaceData.1 t98A01PrintedSurfaceData.2 ≃ₜ
      Surface false 11)
  rw [t98A01PrintedSurfaceData_eq]
  exact ⟨Homeomorph.refl _⟩

lemma t98A01PrintedSurface_eulerCharacteristic :
    eulerCharacteristic t98A01PrintedSurfaceData.1
      t98A01PrintedSurfaceData.2 = -9 := by
  rw [t98A01PrintedSurfaceData_eq]
  norm_num [eulerCharacteristic]

/-- Once homeomorphic orientable presentations are known to have equal genus,
Euler multiplicativity for five sheets forces both genera to be one. -/
lemma t98A01_orientable_genus_arithmetic (g h : ℕ)
    (hgh : g = h)
    (hχ : eulerCharacteristic true g =
      5 * eulerCharacteristic true h) :
    g = 1 ∧ h = 1 := by
  simp [eulerCharacteristic] at hχ
  omega

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
  /-
  CLOSER HOP 2 boundary. The promoted `ConstructionTargets.Surfaces` module
  now makes the connected-sum tail completely computational.
  `t98A01PrintedSurfaceData_eq` computes the classification pair as
  `(false, 11)`, `t98A01PrintedSurface_homeomorph` reduces to the identity
  homeomorphism, and `t98A01PrintedSurface_eulerCharacteristic` computes
  `2 - 11 = -9`. The helper `t98A01_orientable_genus_arithmetic` also proves
  that, once classification supplies `g = h` and cover multiplicativity
  supplies the displayed Euler equation, both genera must equal one.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, `UnitAddCircle`
  multiplication/covering sources, surface-cover siblings, Mathlib's
  `IsCoveringMap`, deck-transformation, and finite-cover APIs found no theorem
  packaging `x ↦ 5 • x` as a five-sheeted regular cover, no fiber-cardinality
  theorem for this map, and no Euler-characteristic multiplicativity or
  classification injectivity theorem for the polygon quotients. The remaining
  bridge is therefore the explicit torus cover/deck action and those two
  surface-topology comparison results; all connected-sum arithmetic is closed.
  -/
  sorry

import Mathlib
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Covering.AddCircle
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

/-- The first-coordinate factor in the displayed torus map is a genuine
quotient covering map by its five-torsion kernel. -/
lemma t98A01_circleFive_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (5 • · : UnitAddCircle → UnitAddCircle)
      (nsmulAddMonoidHom (α := UnitAddCircle) 5).ker := by
  exact AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 5

lemma t98A01_circleFive_isCoveringMap :
    IsCoveringMap (5 • · : UnitAddCircle → UnitAddCircle) :=
  t98A01_circleFive_isAddQuotientCoveringMap.isCoveringMap

lemma t98A01_circleFive_surjective :
    Function.Surjective (5 • · : UnitAddCircle → UnitAddCircle) :=
  t98A01_circleFive_isAddQuotientCoveringMap.surjective

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
  CLOSER HOP 3 boundary. A deeper Mathlib search found the previously missed
  `Topology.Covering.AddCircle` module. The new compiled lemmas
  `t98A01_circleFive_isAddQuotientCoveringMap`,
  `t98A01_circleFive_isCoveringMap`, and
  `t98A01_circleFive_surjective` prove that `x ↦ 5 • x` is genuinely the
  quotient covering by its five-torsion kernel. This supplies not merely a
  local-homeomorphism approximation but the exact orbit-transitivity data
  needed for future deck transformations. This theorem also now wires the
  already-compiled connected-sum data, homeomorphism, and Euler arithmetic
  into the final three frozen conjuncts.

  Renewed consultation of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's
  `Topology.Covering.AddCircle`, quotient-covering, product-homeomorphism,
  kernel/fiber-equivalence, and covering APIs, surface-cover siblings, and git
  history found no product constructor promoting this circle quotient cover
  directly to `IsCoveringMap (x,y ↦ (5x,y))`. The remaining concrete cover
  work is to build product trivializations, identify every torus fiber with
  the five-torsion kernel and prove its `Nat.card` is five, then package kernel
  translations as deck homeomorphisms. Independently, the polygon-surface
  classification-injectivity and Euler-multiplicativity theorems remain absent.
  The frozen statement is unchanged.
  -/
  have hfront :
      t98A01IsRegularNfoldCover 5 t98A01TorusFiveCover ∧
      (∀ (g h : ℕ) (p : Surface true g → Surface true h),
        t98A01IsRegularNfoldCover 5 p →
        Nonempty (Surface true g ≃ₜ Surface true h) →
        eulerCharacteristic true g = 5 * eulerCharacteristic true h ∧
        g = 1 ∧ h = 1) := by
    sorry
  exact ⟨hfront.1, hfront.2, t98A01PrintedSurfaceData_eq,
    t98A01PrintedSurface_homeomorph,
    t98A01PrintedSurface_eulerCharacteristic⟩

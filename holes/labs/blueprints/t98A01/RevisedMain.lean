import Mathlib
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Covering.AddCircle
import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonMoves
import ConstructionTargets.RationalLefschetz

/-!
# APM t98A01 — a five-fold surface cover and a connected sum

(a) The fivefold example is the genuine map `(x,y) ↦ (5x,y)` on `(ℝ/ℤ)²`.
The universal clause says that among the repository's closed orientable
surfaces only the torus admits a regular five-sheeted self-cover.

(b) A surface presented by a polygon word `w` is
`PolygonMoves.PolygonSurface w`: the closed disk with its boundary arcs paired
as `w` prescribes (equal signs glue `t ↔ t`, opposite signs `t ↔ 1 - t`).  For
words with disjoint labels, the connected sum of the surfaces of `w₁` and `w₂`
is the surface of the concatenated word `w₁ ++ w₂`: cutting a disk at a vertex
of each polygon and gluing the boundary circles leaves the single polygon
`w₁w₂` (Massey, *Algebraic Topology: An Introduction*, Ch. 1 §7).  `T`, `P`, `K`
are the words `aba⁻¹b⁻¹`, `aa`, `aba⁻¹b`; the statement certifies each against
the repository's standard models `Surface true 1`, `Surface false 1`,
`Surface false 2`.  The canonical form of `K#T#T#P#K#T` is `Surface false 11`
(eleven crosscaps).  The Euler characteristic is the alternating rank sum of
rational singular homology (`HasEulerCharacteristic`), a homeomorphism
invariant.

## Statement repairs

2026-10-16 (claude-14): part (b) previously computed classification data
with the arithmetic function `connectedSum : Bool → ℕ → Bool → ℕ → Bool × ℕ`
(which encodes `T#P ≅ P#P#P`, the substance of the exercise) and certified the
homeomorphism by `Homeomorph.refl`; χ was the formula `2 - g`.  Part (b) is
replaced by the polygon-word connected sum and the rational-homology Euler
characteristic above.  Part (a) is unchanged.

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

/-- The six summands of `K # T # T # P # K # T`. -/
inductive T98A01Summand
  | K₁ | T₁ | T₂ | P | K₂ | T₃
  deriving DecidableEq

/-- Edge labels: summand `s` uses `(s, false)` (`a`) and `(s, true)` (`b`). -/
abbrev T98A01Edge := T98A01Summand × Bool

/-- `T = a b a⁻¹ b⁻¹`. -/
def t98A01TorusWord (s : T98A01Summand) : List (PolygonMoves.Signed T98A01Edge) :=
  [((s, false), true), ((s, true), true), ((s, false), false), ((s, true), false)]

/-- `P = a a`. -/
def t98A01ProjectiveWord (s : T98A01Summand) : List (PolygonMoves.Signed T98A01Edge) :=
  [((s, false), true), ((s, false), true)]

/-- `K = a b a⁻¹ b`. -/
def t98A01KleinWord (s : T98A01Summand) : List (PolygonMoves.Signed T98A01Edge) :=
  [((s, false), true), ((s, true), true), ((s, false), false), ((s, true), true)]

/-- The word of `K # T # T # P # K # T`. -/
def t98A01SumWord : List (PolygonMoves.Signed T98A01Edge) :=
  t98A01KleinWord .K₁ ++ t98A01TorusWord .T₁ ++ t98A01TorusWord .T₂ ++
    t98A01ProjectiveWord .P ++ t98A01KleinWord .K₂ ++ t98A01TorusWord .T₃

abbrev T98A01SumSurface := PolygonMoves.PolygonSurface t98A01SumWord

theorem apm_t98a01 :
    t98A01IsRegularNfoldCover 5 t98A01TorusFiveCover ∧
    (∀ (g h : ℕ) (p : Surface true g → Surface true h),
      t98A01IsRegularNfoldCover 5 p →
      Nonempty (Surface true g ≃ₜ Surface true h) →
      eulerCharacteristic true g = 5 * eulerCharacteristic true h ∧
      g = 1 ∧ h = 1) ∧
    Nonempty (PolygonMoves.PolygonSurface (t98A01TorusWord .T₁) ≃ₜ Surface true 1) ∧
    Nonempty (PolygonMoves.PolygonSurface (t98A01ProjectiveWord .P) ≃ₜ
      Surface false 1) ∧
    Nonempty (PolygonMoves.PolygonSurface (t98A01KleinWord .K₁) ≃ₜ Surface false 2) ∧
    Nonempty (T98A01SumSurface ≃ₜ Surface false 11) ∧
    ConstructionTargets.RationalLefschetz.HasEulerCharacteristic T98A01SumSurface (-9) := by
  sorry

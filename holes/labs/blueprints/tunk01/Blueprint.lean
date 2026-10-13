import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.PolygonSurfacePiOne

/-! # Blueprint for APM tunk01 -/

open Set

noncomputable section

inductive apm_tunk01_Label
  | a | b | c | d | e | f | g
  deriving DecidableEq

inductive apm_tunk01_SignedLabel
  | pos (x : apm_tunk01_Label)
  | neg (x : apm_tunk01_Label)
  deriving DecidableEq

def apm_tunk01_word : List apm_tunk01_SignedLabel :=
  [.pos .a, .pos .c, .neg .d, .neg .g, .pos .f, .neg .e, .pos .b,
   .neg .c, .neg .d, .neg .g, .neg .e, .pos .f, .pos .a, .pos .b]

def apm_tunk01_vertexClass (i : Fin 14) : Fin 2 :=
  if i.1 = 3 ∨ i.1 = 9 then 1 else 0

def apm_tunk01_SignedLabel.label : apm_tunk01_SignedLabel → apm_tunk01_Label
  | .pos x | .neg x => x

def apm_tunk01_edgeCount (word : List apm_tunk01_SignedLabel) : ℕ :=
  (word.map apm_tunk01_SignedLabel.label).toFinset.card

def apm_tunk01_vertexCount {n m : ℕ} (vertexClass : Fin n → Fin m) : ℕ :=
  (Finset.univ.image vertexClass).card

def apm_tunk01_eulerCharacteristic {n m : ℕ}
    (word : List apm_tunk01_SignedLabel) (vertexClass : Fin n → Fin m) : ℤ :=
  apm_tunk01_vertexCount vertexClass - apm_tunk01_edgeCount word + 1

def apm_tunk01_hasOppositeOrientationPairing
    (word : List apm_tunk01_SignedLabel) : Prop :=
  ∀ x : apm_tunk01_Label,
    word.count (.pos x) = 1 ∧ word.count (.neg x) = 1

abbrev apm_tunk01_Disk := Metric.closedBall (0 : ℂ) 1

def apm_tunk01_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_tunk01_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_tunk01_reverse (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

inductive apm_tunk01_PolygonRel : apm_tunk01_Disk → apm_tunk01_Disk → Prop
  | a (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 0 t) (apm_tunk01_edgePoint 14 12 t)
  | b (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 6 t) (apm_tunk01_edgePoint 14 13 t)
  | c (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 1 t)
      (apm_tunk01_edgePoint 14 7 (apm_tunk01_reverse t))
  | d (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 2 t) (apm_tunk01_edgePoint 14 8 t)
  | e (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 5 t) (apm_tunk01_edgePoint 14 10 t)
  | f (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 4 t) (apm_tunk01_edgePoint 14 11 t)
  | g (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 3 t) (apm_tunk01_edgePoint 14 9 t)

def apm_tunk01_PolygonSurface :=
  Quotient (Relation.EqvGen.setoid apm_tunk01_PolygonRel)

noncomputable instance : TopologicalSpace apm_tunk01_PolygonSurface :=
  TopologicalSpace.coinduced
    (fun x : apm_tunk01_Disk ↦ Quotient.mk _ x) inferInstance

def apm_tunk01_N6Rel (x y : apm_tunk01_Disk) : Prop :=
  ∃ j : ℕ, j < 6 ∧ ∃ t : Set.Icc (0 : ℝ) 1,
    x = apm_tunk01_edgePoint 12 (2 * j) t ∧
    y = apm_tunk01_edgePoint 12 (2 * j + 1) t

def apm_tunk01_N6 :=
  Quotient (Relation.EqvGen.setoid apm_tunk01_N6Rel)

noncomputable instance : TopologicalSpace apm_tunk01_N6 :=
  TopologicalSpace.coinduced
    (fun x : apm_tunk01_Disk ↦ Quotient.mk _ x) inferInstance

lemma apm_tunk01_vertexCount_eq :
    apm_tunk01_vertexCount apm_tunk01_vertexClass = 2 := by
  decide

lemma apm_tunk01_edgeCount_eq :
    apm_tunk01_edgeCount apm_tunk01_word = 7 := by
  decide

lemma apm_tunk01_eulerCharacteristic_eq :
    apm_tunk01_eulerCharacteristic apm_tunk01_word
      apm_tunk01_vertexClass = -4 := by
  decide

lemma apm_tunk01_not_oppositeOrientationPairing :
    ¬apm_tunk01_hasOppositeOrientationPairing apm_tunk01_word := by
  intro h
  have ha := h apm_tunk01_Label.a
  simp [apm_tunk01_word] at ha

/-- LIBRARY: normalize the concrete fourteen-gon presentation to the standard
twelve-gon presentation of the nonorientable genus-six surface. -/
theorem apm_tunk01_polygon_normalization :
    Nonempty (apm_tunk01_PolygonSurface ≃ₜ apm_tunk01_N6) := by
  sorry

/-- The printed polygon is the nonorientable closed surface of genus six. -/
theorem apm_tunk01
    (X : Type*) [TopologicalSpace X]
    (hPresentation : Nonempty (X ≃ₜ apm_tunk01_PolygonSurface)) :
    apm_tunk01_vertexCount apm_tunk01_vertexClass = 2 ∧
    apm_tunk01_edgeCount apm_tunk01_word = 7 ∧
    apm_tunk01_eulerCharacteristic apm_tunk01_word apm_tunk01_vertexClass = -4 ∧
    ¬apm_tunk01_hasOppositeOrientationPairing apm_tunk01_word ∧
    Nonempty (X ≃ₜ apm_tunk01_N6) := by
  rcases hPresentation with ⟨e⟩
  let en : apm_tunk01_PolygonSurface ≃ₜ apm_tunk01_N6 :=
    Classical.choice apm_tunk01_polygon_normalization
  exact ⟨apm_tunk01_vertexCount_eq, apm_tunk01_edgeCount_eq,
    apm_tunk01_eulerCharacteristic_eq,
    apm_tunk01_not_oppositeOrientationPairing,
    ⟨e.trans en⟩⟩

#print axioms apm_tunk01

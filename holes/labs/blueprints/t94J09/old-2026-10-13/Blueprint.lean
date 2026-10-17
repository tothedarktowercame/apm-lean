import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.SingularHomologyConcrete

/-! # Blueprint for APM t94J09 -/

open CategoryTheory Set

noncomputable section

inductive apm_t94J09_Label
  | a | b | c | d | e | f | g
  deriving DecidableEq

inductive apm_t94J09_SignedLabel
  | pos (x : apm_t94J09_Label)
  | neg (x : apm_t94J09_Label)
  deriving DecidableEq

def apm_t94J09_word : List apm_t94J09_SignedLabel :=
  [.pos .a, .pos .c, .neg .d, .neg .g, .pos .f, .neg .e, .pos .b,
   .neg .c, .neg .d, .neg .g, .neg .e, .pos .f, .pos .a, .pos .b]

def apm_t94J09_vertexClass (i : Fin 14) : Fin 2 :=
  if i.1 = 3 ∨ i.1 = 9 then 1 else 0

def apm_t94J09_SignedLabel.label : apm_t94J09_SignedLabel → apm_t94J09_Label
  | .pos x | .neg x => x

def apm_t94J09_edgeCount (word : List apm_t94J09_SignedLabel) : ℕ :=
  (word.map apm_t94J09_SignedLabel.label).toFinset.card

def apm_t94J09_vertexCount {n m : ℕ} (vertexClass : Fin n → Fin m) : ℕ :=
  (Finset.univ.image vertexClass).card

def apm_t94J09_eulerCharacteristic {n m : ℕ}
    (word : List apm_t94J09_SignedLabel)
    (vertexClass : Fin n → Fin m) : ℤ :=
  apm_t94J09_vertexCount vertexClass - apm_t94J09_edgeCount word + 1

def apm_t94J09_hasOppositeOrientationPairing
    (word : List apm_t94J09_SignedLabel) : Prop :=
  ∀ x : apm_t94J09_Label,
    word.count (.pos x) = 1 ∧ word.count (.neg x) = 1

def apm_t94J09_nonorientableGenus (chi : ℤ) : ℤ := 2 - chi

abbrev apm_t94J09_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t94J09_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t94J09_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_t94J09_reverse (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

inductive apm_t94J09_PolygonRel :
    apm_t94J09_Disk → apm_t94J09_Disk → Prop
  | a (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 0 t) (apm_t94J09_edgePoint 14 12 t)
  | b (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 6 t) (apm_t94J09_edgePoint 14 13 t)
  | c (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 1 t)
      (apm_t94J09_edgePoint 14 7 (apm_t94J09_reverse t))
  | d (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 2 t) (apm_t94J09_edgePoint 14 8 t)
  | e (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 5 t) (apm_t94J09_edgePoint 14 10 t)
  | f (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 4 t) (apm_t94J09_edgePoint 14 11 t)
  | g (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 3 t) (apm_t94J09_edgePoint 14 9 t)

def apm_t94J09_PolygonSurface :=
  Quotient (Relation.EqvGen.setoid apm_t94J09_PolygonRel)

noncomputable instance : TopologicalSpace apm_t94J09_PolygonSurface :=
  TopologicalSpace.coinduced
    (fun x : apm_t94J09_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t94J09_N6Rel (x y : apm_t94J09_Disk) : Prop :=
  ∃ j : ℕ, j < 6 ∧ ∃ t : Set.Icc (0 : ℝ) 1,
    x = apm_t94J09_edgePoint 12 (2 * j) t ∧
    y = apm_t94J09_edgePoint 12 (2 * j + 1) t

def apm_t94J09_N6 :=
  Quotient (Relation.EqvGen.setoid apm_t94J09_N6Rel)

noncomputable instance : TopologicalSpace apm_t94J09_N6 :=
  TopologicalSpace.coinduced
    (fun x : apm_t94J09_Disk ↦ Quotient.mk _ x) inferInstance

abbrev apm_t94J09_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t94J09_PolygonSurface))

lemma apm_t94J09_vertexCount_eq :
    apm_t94J09_vertexCount apm_t94J09_vertexClass = 2 := by
  decide

lemma apm_t94J09_edgeCount_eq :
    apm_t94J09_edgeCount apm_t94J09_word = 7 := by
  decide

lemma apm_t94J09_eulerCharacteristic_eq :
    apm_t94J09_eulerCharacteristic apm_t94J09_word
      apm_t94J09_vertexClass = -4 := by
  decide

lemma apm_t94J09_not_oppositeOrientationPairing :
    ¬apm_t94J09_hasOppositeOrientationPairing apm_t94J09_word := by
  intro h
  have ha := h apm_t94J09_Label.a
  simp [apm_t94J09_word] at ha

lemma apm_t94J09_nonorientableGenus_eq :
    apm_t94J09_nonorientableGenus
      (apm_t94J09_eulerCharacteristic apm_t94J09_word
        apm_t94J09_vertexClass) = 6 := by
  decide

/-- LIBRARY: normalize the concrete fourteen-gon presentation to the standard
twelve-gon presentation of the nonorientable genus-six surface. -/
theorem apm_t94J09_polygon_normalization :
    Nonempty (apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6) := by
  sorry

/-- LIBRARY: compute the integral singular homology of the concrete polygon
quotient.  This is independent of choosing a normalization homeomorphism. -/
theorem apm_t94J09_polygon_homology :
    Nonempty (apm_t94J09_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t94J09_H 1 ≅
      ModuleCat.of ℤ ((Fin 5 → ℤ) × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t94J09_H k)) := by
  sorry

theorem apm_t94j09 :
    apm_t94J09_vertexCount apm_t94J09_vertexClass = 2 ∧
    apm_t94J09_edgeCount apm_t94J09_word = 7 ∧
    apm_t94J09_eulerCharacteristic apm_t94J09_word
      apm_t94J09_vertexClass = -4 ∧
    ¬apm_t94J09_hasOppositeOrientationPairing apm_t94J09_word ∧
    apm_t94J09_nonorientableGenus
      (apm_t94J09_eulerCharacteristic apm_t94J09_word
        apm_t94J09_vertexClass) = 6 ∧
    Nonempty (apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6) ∧
    Nonempty (apm_t94J09_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t94J09_H 1 ≅
      ModuleCat.of ℤ ((Fin 5 → ℤ) × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t94J09_H k)) := by
  exact ⟨apm_t94J09_vertexCount_eq, apm_t94J09_edgeCount_eq,
    apm_t94J09_eulerCharacteristic_eq,
    apm_t94J09_not_oppositeOrientationPairing,
    apm_t94J09_nonorientableGenus_eq,
    apm_t94J09_polygon_normalization, apm_t94J09_polygon_homology⟩

#print axioms apm_t94j09

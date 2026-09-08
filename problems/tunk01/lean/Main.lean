import Mathlib

/-!
# APM tunk01: classification of a polygon surface

## Statement repairs

The embedded source solution only refers to duplicate problem `t94J09`.  The
explicitly stipulated two vertex classes give Euler characteristic
`2 - 7 + 1 = -4`; together with a same-orientation edge pair, this classifies
the quotient as the nonorientable genus-six surface.  We therefore reject the
older, self-described untrusted genus-three answer preserved in `t94J09`.

## Encoding questions

Mathlib has no packaged polygon-surface classification theorem.  We model the
given polygon and the standard word `a₁a₁⋯a₆a₆` as actual topological quotients
of the closed disk and state classification as a `Homeomorph` between them.
The finite word, vertex partition, Euler characteristic, and orientability
test remain in the conclusion so that the claimed genus is tied to the printed
combinatorial data.
-/

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

/-- The corners after the two printed `d⁻¹` occurrences form the second class. -/
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

/-- Standard polygon presentation `a₁a₁⋯a₆a₆` of the genus-six surface. -/
def apm_tunk01_N6Rel (x y : apm_tunk01_Disk) : Prop :=
  ∃ j : ℕ, j < 6 ∧ ∃ t : Set.Icc (0 : ℝ) 1,
    x = apm_tunk01_edgePoint 12 (2 * j) t ∧
    y = apm_tunk01_edgePoint 12 (2 * j + 1) t

def apm_tunk01_N6 :=
  Quotient (Relation.EqvGen.setoid apm_tunk01_N6Rel)

noncomputable instance : TopologicalSpace apm_tunk01_N6 :=
  TopologicalSpace.coinduced
    (fun x : apm_tunk01_Disk ↦ Quotient.mk _ x) inferInstance

/-- The printed polygon is the nonorientable closed surface of genus six. -/
theorem apm_tunk01
    (X : Type*) [TopologicalSpace X]
    (hPresentation : Nonempty (X ≃ₜ apm_tunk01_PolygonSurface)) :
    apm_tunk01_vertexCount apm_tunk01_vertexClass = 2 ∧
    apm_tunk01_edgeCount apm_tunk01_word = 7 ∧
    apm_tunk01_eulerCharacteristic apm_tunk01_word apm_tunk01_vertexClass = -4 ∧
    ¬apm_tunk01_hasOppositeOrientationPairing apm_tunk01_word ∧
    Nonempty (X ≃ₜ apm_tunk01_N6) := by
  sorry

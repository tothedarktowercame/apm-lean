import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t94J09

## Statement repairs

The harvested TeX includes an old proposed answer claiming a connected sum of
three projective planes, but explicitly warns that computation is not trusted.
It contradicts the problem's stipulated two vertex classes: the resulting CW
structure has `V = 2`, `E = 7`, `F = 1`, hence Euler characteristic `-4` and
non-orientable genus `6`.  The formal conclusion follows the stated gluing
data and therefore classifies the surface as a sum of six projective planes.

## Encoding questions

The signed word determines an actual quotient of the closed disk by its seven
edge pairings. A second quotient realizes the standard polygon
`a₁a₁⋯a₆a₆` for the nonorientable genus-six surface. The conclusion identifies
these spaces by a homeomorphism and computes integral singular homology of the
source quotient, in addition to retaining the cell-count certificate.
-/

open CategoryTheory Set

noncomputable section

/-- The seven edge labels in the polygon. -/
inductive apm_t94J09_Label
  | a | b | c | d | e | f | g
  deriving DecidableEq

/-- An oriented occurrence of a polygon edge. -/
inductive apm_t94J09_SignedLabel
  | pos (x : apm_t94J09_Label)
  | neg (x : apm_t94J09_Label)
  deriving DecidableEq

/-- The edge word `a c d⁻¹ g⁻¹ f e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ f a b`. -/
def apm_t94J09_word : List apm_t94J09_SignedLabel :=
  [.pos .a, .pos .c, .neg .d, .neg .g, .pos .f, .neg .e, .pos .b,
   .neg .c, .neg .d, .neg .g, .neg .e, .pos .f, .pos .a, .pos .b]

/-- The two exceptional corners are those after positions `3` and `9`. -/
def apm_t94J09_vertexClass (i : Fin 14) : Fin 2 :=
  if i.1 = 3 ∨ i.1 = 9 then 1 else 0

/-- Forget the orientation of an edge occurrence. -/
def apm_t94J09_SignedLabel.label : apm_t94J09_SignedLabel → apm_t94J09_Label
  | .pos x | .neg x => x

/-- Number of distinct edge labels in a polygon word. -/
def apm_t94J09_edgeCount (word : List apm_t94J09_SignedLabel) : ℕ :=
  (word.map apm_t94J09_SignedLabel.label).toFinset.card

/-- Number of vertex classes specified by the corner partition. -/
def apm_t94J09_vertexCount {n m : ℕ} (vertexClass : Fin n → Fin m) : ℕ :=
  (Finset.univ.image vertexClass).card

/-- Euler characteristic of the one-face polygonal CW structure. -/
def apm_t94J09_eulerCharacteristic {n m : ℕ}
    (word : List apm_t94J09_SignedLabel)
    (vertexClass : Fin n → Fin m) : ℤ :=
  apm_t94J09_vertexCount vertexClass - apm_t94J09_edgeCount word + 1

/-- Every label occurs once in each orientation, the orientable pairing test. -/
def apm_t94J09_hasOppositeOrientationPairing
    (word : List apm_t94J09_SignedLabel) : Prop :=
  ∀ x : apm_t94J09_Label,
    word.count (.pos x) = 1 ∧ word.count (.neg x) = 1

/-- The genus forced by Euler characteristic in the nonorientable case. -/
def apm_t94J09_nonorientableGenus (chi : ℤ) : ℤ := 2 - chi

abbrev apm_t94J09_Disk := Metric.closedBall (0 : ℂ) 1

/-- Boundary parameter `t` on edge `j` of an `edgeCount`-gon. -/
def apm_t94J09_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t94J09_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_t94J09_reverse (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- The seven edge pairings specified by the signed fourteen-edge word. -/
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

/-- Standard polygon pairings `a₁a₁⋯a₆a₆` for `N₆`. -/
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
  refine ⟨apm_t94J09_vertexCount_eq, apm_t94J09_edgeCount_eq,
    apm_t94J09_eulerCharacteristic_eq,
    apm_t94J09_not_oppositeOrientationPairing,
    apm_t94J09_nonorientableGenus_eq, ?_⟩
  /-
  CLOSER HOP 1: all five finite classification certificates are now closed by
  the compiled lemmas above.  Kernel reduction computes the two vertex classes,
  seven edge labels, Euler characteristic `-4`, and genus `6`; specializing
  the orientation predicate to label `a` proves directly that the word fails
  the opposite-orientation test.

  Desk research covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, every
  topology sibling mentioning polygon quotients or surface classification,
  Mathlib's singular-homology, quotient, CW-complex, and Mayer--Vietoris
  sources, and git history.  `ConstructionTargets.Surfaces` provides the
  standard nonorientable polygon quotient and Euler arithmetic, but no
  polygon-move theorem or homeomorphism normalizing this fourteen-edge
  `EqvGen` relation to its genus-six relation.  The closest siblings
  (`t97A01`, `t97J02`, `t98A01`, `t99J03`) likewise stop at quotient cocones
  or classification arithmetic.

  The remaining frozen goal is precisely the homeomorphism of the two actual
  quotient spaces followed by singular homology of that quotient.  Mathlib
  has no classification theorem for polygon surfaces, no cellular chain
  complex attached to these quotients, no cellular-to-singular comparison,
  and no singular Mayer--Vietoris sequence (the available named development
  is sheaf cohomology).  Consequently the expected cellular boundary
  calculation `ℤ → ℤ⁷` cannot yet be transported to `apm_t94J09_H`.  The
  frozen statement is unchanged; no axiom or opaque placeholder was added.
  -/
  sorry

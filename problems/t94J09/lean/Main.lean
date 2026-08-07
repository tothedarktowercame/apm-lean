import Mathlib

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

The signed fourteen-edge word and the two vertex classes are concrete below.
Mathlib has a genuine real projective plane but no packaged polygon-edge
adjunction or connected-sum construction for surfaces. Rather than introduce
uninterpreted spaces, the conclusion gives the standard complete classification
certificate for the resulting closed surface: its cell counts, Euler
characteristic, failure of the opposite-orientation pairing criterion, and
therefore its nonorientable genus.
-/

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

theorem apm_t94j09 :
    apm_t94J09_vertexCount apm_t94J09_vertexClass = 2 ∧
    apm_t94J09_edgeCount apm_t94J09_word = 7 ∧
    apm_t94J09_eulerCharacteristic apm_t94J09_word
      apm_t94J09_vertexClass = -4 ∧
    ¬apm_t94J09_hasOppositeOrientationPairing apm_t94J09_word ∧
    apm_t94J09_nonorientableGenus
      (apm_t94J09_eulerCharacteristic apm_t94J09_word
        apm_t94J09_vertexClass) = 6 := by
  sorry

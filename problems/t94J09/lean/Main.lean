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
Mathlib has no packaged polygon-edge adjunction or connected-sum construction
for topological surfaces, so those two genuine spaces are isolated as opaque,
typed constructions and the classification is stated as a homeomorphism.
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

/-- The quotient of the polygon by the specified signed edge and vertex gluings. -/
opaque apm_t94J09_PolygonSurface
    (word : List apm_t94J09_SignedLabel)
    (vertexClass : Fin word.length → Fin 2) : Type

opaque apm_t94J09_polygonTopology
    (word : List apm_t94J09_SignedLabel)
    (vertexClass : Fin word.length → Fin 2) :
    TopologicalSpace (apm_t94J09_PolygonSurface word vertexClass)

noncomputable instance
    (word : List apm_t94J09_SignedLabel)
    (vertexClass : Fin word.length → Fin 2) :
    TopologicalSpace (apm_t94J09_PolygonSurface word vertexClass) :=
  apm_t94J09_polygonTopology word vertexClass

/-- The connected sum of `n` copies of the real projective plane. -/
opaque apm_t94J09_ProjectivePlaneSum (n : ℕ) : Type

opaque apm_t94J09_projectivePlaneSumTopology (n : ℕ) :
    TopologicalSpace (apm_t94J09_ProjectivePlaneSum n)

noncomputable instance (n : ℕ) :
    TopologicalSpace (apm_t94J09_ProjectivePlaneSum n) :=
  apm_t94J09_projectivePlaneSumTopology n

theorem apm_t94j09 :
    Nonempty
      (apm_t94J09_PolygonSurface apm_t94J09_word apm_t94J09_vertexClass ≃ₜ
        apm_t94J09_ProjectivePlaneSum 6) := by
  sorry

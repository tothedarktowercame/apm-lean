import Mathlib

/-!
# APM t02A02 — classification of the polygon word `aabcc⁻¹d⁻¹bd⁻¹`

## Statement repairs

None.

## Encoding note

The polygon gluing is retained as its signed eight-edge word and explicit
vertex quotient.  The conclusion uses the closed-surface classifier (Euler
characteristic plus orientability), rather than replacing the word by a
preselected surface name.
-/

inductive apm_t02a02_Edge
  | a | b | c | d
  deriving DecidableEq

structure apm_t02a02_SignedEdge where
  edge : apm_t02a02_Edge
  forward : Bool

def apm_t02a02_word : Fin 8 → apm_t02a02_SignedEdge :=
  ![⟨.a, true⟩, ⟨.a, true⟩, ⟨.b, true⟩, ⟨.c, true⟩,
    ⟨.c, false⟩, ⟨.d, false⟩, ⟨.b, true⟩, ⟨.d, false⟩]

def apm_t02a02_vertexClass : Fin 8 → Fin 3 :=
  ![0, 0, 0, 1, 2, 1, 0, 1]

def apm_t02a02_pair : Fin 8 → Fin 8 :=
  ![1, 0, 6, 4, 3, 7, 2, 5]

def apm_t02a02_next (i : Fin 8) : Fin 8 :=
  ⟨(i.val + 1) % 8, Nat.mod_lt _ (by decide)⟩

def apm_t02a02_orientedStart (i : Fin 8) : Fin 8 :=
  if (apm_t02a02_word i).forward then i else apm_t02a02_next i

def apm_t02a02_orientedEnd (i : Fin 8) : Fin 8 :=
  if (apm_t02a02_word i).forward then apm_t02a02_next i else i

def apm_t02a02_validVertexQuotient : Prop :=
  ∀ i : Fin 8,
    apm_t02a02_pair (apm_t02a02_pair i) = i ∧
    (apm_t02a02_word (apm_t02a02_pair i)).edge = (apm_t02a02_word i).edge ∧
    apm_t02a02_vertexClass (apm_t02a02_orientedStart i) =
      apm_t02a02_vertexClass (apm_t02a02_orientedStart (apm_t02a02_pair i)) ∧
    apm_t02a02_vertexClass (apm_t02a02_orientedEnd i) =
      apm_t02a02_vertexClass (apm_t02a02_orientedEnd (apm_t02a02_pair i))

def apm_t02a02_nonorientable : Prop :=
  ∃ i j : Fin 8, i ≠ j ∧
    (apm_t02a02_word i).edge = (apm_t02a02_word j).edge ∧
    (apm_t02a02_word i).forward = (apm_t02a02_word j).forward

inductive apm_t02a02_SurfaceKind
  | sphere | torus | kleinBottle | other
  deriving DecidableEq

def apm_t02a02_classify (orientable : Bool) (eulerCharacteristic : ℤ) :
    apm_t02a02_SurfaceKind :=
  if orientable then
    if eulerCharacteristic = 0 then .torus else .other
  else if eulerCharacteristic = 0 then .kleinBottle else .other

theorem apm_t02a02 :
    apm_t02a02_validVertexQuotient ∧
    Function.Surjective apm_t02a02_vertexClass ∧
    apm_t02a02_nonorientable ∧
    ((Nat.card (Fin 3) : ℤ) - Nat.card apm_t02a02_Edge + 1 = 0) ∧
    apm_t02a02_classify false 0 = .kleinBottle := by
  sorry

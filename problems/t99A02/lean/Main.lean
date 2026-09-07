import Mathlib

/-! # APM t99A02: universal covers of two wedges

## Statement repairs

The requested answer is a picture of two Cayley 2-complexes.  Mathlib has
covering maps, but no projective plane, based wedge, CW complex, or Bass--Serre
tree construction with which to state those pictures faithfully.  Those
universal-cover identifications are therefore NOT encoded.  The theorem records
the genuine presentation calculation on which both sketches are based; it does
not introduce an abstract predicate standing for either missing picture.

## Encoding questions

`Fin 2` indexes the two wedge summands.  For the second space, generator `0`
is the circle generator and generator `1` is the projective-plane generator.
-/

namespace APMT99A02

def rp2WedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 0 : FreeGroup (Fin 2)) ^ 2,
   (FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

def circleWedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

end APMT99A02

theorem apm_t99a02 :
    (PresentedGroup.of (rels := APMT99A02.rp2WedgeRp2Relations) 0) ^ 2 = 1 ∧
    (PresentedGroup.of (rels := APMT99A02.rp2WedgeRp2Relations) 1) ^ 2 = 1 ∧
    (PresentedGroup.of (rels := APMT99A02.circleWedgeRp2Relations) 1) ^ 2 = 1 ∧
    Infinite (PresentedGroup APMT99A02.circleWedgeRp2Relations) := by
  sorry

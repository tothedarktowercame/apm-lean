import Mathlib

/-! # APM t99A02: universal covers of two wedges

The original formal statement recorded only defining relators.  This repaired
statement records the two fundamental-group identifications that determine the
Cayley/Bass--Serre pictures requested by the problem.
-/

namespace APMT99A02

def rp2WedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 0 : FreeGroup (Fin 2)) ^ 2,
   (FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

def circleWedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

end APMT99A02

theorem apm_t99a02 :
    Nonempty
      (PresentedGroup APMT99A02.rp2WedgeRp2Relations ≃*
        DihedralGroup 0) ∧
    Nonempty
      (PresentedGroup APMT99A02.circleWedgeRp2Relations ≃*
        Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))) := by
  sorry

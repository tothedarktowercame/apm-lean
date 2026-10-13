import Mathlib

/-! # APM t99A02: universal covers of two wedges

This blueprint proves the repaired statement from two independent presentation
calculations.  They are deliberately exposed as library-scale obligations: the
current Mathlib API gives the universal properties of `PresentedGroup` and
`Monoid.Coprod`, but no ready-made Tietze transformation joining these concrete
presentations.
-/

namespace APMT99A02

def rp2WedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 0 : FreeGroup (Fin 2)) ^ 2,
   (FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

def circleWedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

end APMT99A02

/-- **LIBRARY:** the presentation with two involutory generators is the
infinite dihedral group. -/
theorem t99A02_rp2WedgeRp2_presentedGroup_equiv :
    Nonempty
      (PresentedGroup APMT99A02.rp2WedgeRp2Relations ≃*
        DihedralGroup 0) := by
  sorry

/-- **LIBRARY:** the presentation with one unrestricted generator and one
involutory generator is the indicated free product. -/
theorem t99A02_circleWedgeRp2_presentedGroup_equiv :
    Nonempty
      (PresentedGroup APMT99A02.circleWedgeRp2Relations ≃*
        Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))) := by
  sorry

theorem apm_t99a02 :
    Nonempty
      (PresentedGroup APMT99A02.rp2WedgeRp2Relations ≃*
        DihedralGroup 0) ∧
    Nonempty
      (PresentedGroup APMT99A02.circleWedgeRp2Relations ≃*
        Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))) := by
  exact
    ⟨t99A02_rp2WedgeRp2_presentedGroup_equiv,
      t99A02_circleWedgeRp2_presentedGroup_equiv⟩

#print axioms apm_t99a02

import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PointWedgeVanKampen

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace APMT99A02

def rp2WedgeRp2Point : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

abbrev CircleWedgeProjectivePlane := Wedge (1 : Circle) (surfacePoint false 1)

def circleWedgeRp2Point : CircleWedgeProjectivePlane :=
  quotientMap (1 : Circle) (surfacePoint false 1) (Sum.inl 1)

def rp2WedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 0 : FreeGroup (Fin 2)) ^ 2,
   (FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

def circleWedgeRp2Relations : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 1 : FreeGroup (Fin 2)) ^ 2}

end APMT99A02

/-- **LIBRARY:** polygon-surface pi-one followed by point-wedge van Kampen,
specialized simultaneously to the two concrete wedges. -/
theorem t99A02_wedge_fundamentalGroups_presented :
    Nonempty
      (FundamentalGroup ProjectivePlaneWedge APMT99A02.rp2WedgeRp2Point ≃*
        PresentedGroup APMT99A02.rp2WedgeRp2Relations) ∧
    Nonempty
      (FundamentalGroup APMT99A02.CircleWedgeProjectivePlane
          APMT99A02.circleWedgeRp2Point ≃*
        PresentedGroup APMT99A02.circleWedgeRp2Relations) := by
  sorry

/-- The presentation with two involutory generators is the infinite dihedral
group. -/
theorem t99A02_rp2WedgeRp2_presentedGroup_equiv :
    Nonempty
      (PresentedGroup APMT99A02.rp2WedgeRp2Relations ≃*
        DihedralGroup 0) := by
  sorry

/-- The presentation with one unrestricted generator and one involutory
generator is the indicated free product. -/
theorem t99A02_circleWedgeRp2_presentedGroup_equiv :
    Nonempty
      (PresentedGroup APMT99A02.circleWedgeRp2Relations ≃*
        Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))) := by
  sorry

theorem apm_t99a02 :
    Nonempty
      (FundamentalGroup ProjectivePlaneWedge APMT99A02.rp2WedgeRp2Point ≃*
        DihedralGroup 0) ∧
    Nonempty
      (FundamentalGroup APMT99A02.CircleWedgeProjectivePlane
          APMT99A02.circleWedgeRp2Point ≃*
        Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))) := by
  obtain ⟨⟨hRP⟩, ⟨hCRP⟩⟩ := t99A02_wedge_fundamentalGroups_presented
  obtain ⟨hRPA⟩ := t99A02_rp2WedgeRp2_presentedGroup_equiv
  obtain ⟨hCRPA⟩ := t99A02_circleWedgeRp2_presentedGroup_equiv
  exact ⟨⟨hRP.trans hRPA⟩, ⟨hCRP.trans hCRPA⟩⟩

#print axioms apm_t99a02

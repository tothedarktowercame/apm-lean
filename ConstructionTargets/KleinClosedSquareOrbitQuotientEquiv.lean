import ConstructionTargets.KleinSquareRepresentative
import ConstructionTargets.KleinSquareEqvGenToCases

noncomputable section

namespace ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv

open KleinPlaneActionSquareOrbitClassification
open KleinSquareEqvGenToCases
open KleinSquareRepresentative

abbrev ClosedSquare := {p : ℝ × ℝ // InSquare p}

def orbitSetoid : Setoid (ℝ × ℝ) where
  r := SameOrbit
  iseqv := ⟨sameOrbit_refl, @sameOrbit_symm, @sameOrbit_trans⟩

def closedSquareOrbitSetoid : Setoid ClosedSquare where
  r p q := SameOrbit p.1 q.1
  iseqv := ⟨fun p => sameOrbit_refl p.1,
    fun {_ _} => sameOrbit_symm, fun {_ _ _} => sameOrbit_trans⟩

def closedSquareToOrbitQuotient :
    Quotient closedSquareOrbitSetoid → Quotient orbitSetoid :=
  Quotient.map Subtype.val (fun _ _ h => h)

theorem closedSquareToOrbitQuotient_surjective :
    Function.Surjective closedSquareToOrbitQuotient := by
  intro z
  induction z using Quotient.inductionOn with
  | _ p =>
      obtain ⟨g, h0, h1, h2, h3⟩ := exists_closedSquare_smul p
      let q : ClosedSquare := ⟨g • p, h0, h1, h2, h3⟩
      refine ⟨Quotient.mk _ q, ?_⟩
      apply Quotient.sound
      exact sameOrbit_symm ⟨g, rfl⟩

theorem closedSquareToOrbitQuotient_injective :
    Function.Injective closedSquareToOrbitQuotient := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ p =>
      induction y using Quotient.inductionOn with
      | _ q =>
          apply Quotient.sound
          change (Quotient.mk orbitSetoid p.1) =
            Quotient.mk orbitSetoid q.1 at h
          have hpq : SameOrbit p.1 q.1 :=
            @Quotient.exact (ℝ × ℝ) orbitSetoid p.1 q.1 h
          exact hpq

/-- Every orbit of the explicit Klein plane action has a closed-square
representative, and two such representatives define the same closed-square
orbit exactly when they define the same plane orbit. -/
noncomputable def closedSquareOrbitQuotientEquiv :
    Quotient closedSquareOrbitSetoid ≃ Quotient orbitSetoid :=
  Equiv.ofBijective closedSquareToOrbitQuotient
    ⟨closedSquareToOrbitQuotient_injective,
      closedSquareToOrbitQuotient_surjective⟩

#print axioms closedSquareToOrbitQuotient_surjective
#print axioms closedSquareToOrbitQuotient_injective
#print axioms closedSquareOrbitQuotientEquiv

end ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv

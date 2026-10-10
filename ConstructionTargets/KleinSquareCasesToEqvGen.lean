import ConstructionTargets.KleinSquareBoundaryRelation

namespace KleinSquareCasesToEqvGen

open Set Relation
open KleinPlaneActionSquareOrbitClassification
open KleinSquareEdgeOrientation
open KleinSquareBoundaryRelation

private theorem lr (t : Set.Icc (0 : ℝ) 1) :
    EqvGen SquareRel (0, t.1) (1, t.1) :=
  squareRel_eqvGen (Or.inl ⟨t, rfl, rfl⟩)

private theorem bt (t : Set.Icc (0 : ℝ) 1) :
    EqvGen SquareRel (t.1, 0) (1 - t.1, 1) :=
  squareRel_eqvGen (Or.inr ⟨t, rfl, rfl⟩)

theorem cases_eqvGen {p q : ℝ × ℝ} (hp : InSquare p) (hq : InSquare q)
    (h : Cases p q) : EqvGen SquareRel p q := by
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  rcases h with htb | hlr | hbt
  · rcases htb with ⟨m, hpY, hqY, hc⟩
    rcases hc with ⟨-, hpX, hqX⟩ | ⟨-, href⟩ | ⟨-, hpX, hqX⟩
    · have ep : p = (0, 1) := Prod.ext hpX hpY
      have eq : q = (0, 0) := Prod.ext hqX hqY
      subst p; subst q
      let z : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
      let o : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
      have h1 : EqvGen SquareRel (0, 1) (1, 1) := by simpa [o] using lr o
      have h2 : EqvGen SquareRel (1, 1) (0, 0) := by simpa [z] using (bt z).symm
      exact EqvGen.trans _ _ _ h1 h2
    · have ep : p = (p.1, 1) := Prod.ext rfl hpY
      have eq : q = (1 - p.1, 0) := Prod.ext href hqY
      rw [ep, eq]
      let t : Set.Icc (0 : ℝ) 1 := ⟨1 - p.1, by constructor <;> linarith⟩
      simpa [t] using (bt t).symm
    · have ep : p = (1, 1) := Prod.ext hpX hpY
      have eq : q = (1, 0) := Prod.ext hqX hqY
      subst p; subst q
      let z : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
      let o : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
      have h1 : EqvGen SquareRel (1, 1) (0, 0) := by simpa [z] using (bt z).symm
      have h2 : EqvGen SquareRel (0, 0) (1, 0) := by simpa [z] using lr z
      exact EqvGen.trans _ _ _ h1 h2
  · rcases hlr with ⟨m, hy, hc⟩
    rcases hc with ⟨-, hpX, hqX⟩ | ⟨-, heq⟩ | ⟨-, hpX, hqX⟩
    · let t : Set.Icc (0 : ℝ) 1 := ⟨p.2, hp2, hp3⟩
      have ep : p = (1, t.1) := Prod.ext hpX rfl
      have eq : q = (0, t.1) := Prod.ext hqX hy.symm
      rw [ep, eq]
      exact (lr t).symm
    · have : q = p := Prod.ext heq hy.symm
      subst q
      exact EqvGen.refl _
    · let t : Set.Icc (0 : ℝ) 1 := ⟨p.2, hp2, hp3⟩
      have ep : p = (0, t.1) := Prod.ext hpX rfl
      have eq : q = (1, t.1) := Prod.ext hqX hy.symm
      rw [ep, eq]
      exact lr t
  · rcases hbt with ⟨m, hpY, hqY, hc⟩
    rcases hc with ⟨-, hpX, hqX⟩ | ⟨-, href⟩ | ⟨-, hpX, hqX⟩
    · have ep : p = (0, 0) := Prod.ext hpX hpY
      have eq : q = (0, 1) := Prod.ext hqX hqY
      subst p; subst q
      let z : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
      let o : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
      have h1 : EqvGen SquareRel (0, 0) (1, 1) := by simpa [z] using bt z
      have h2 : EqvGen SquareRel (1, 1) (0, 1) := by simpa [o] using (lr o).symm
      exact EqvGen.trans _ _ _ h1 h2
    · have ep : p = (p.1, 0) := Prod.ext rfl hpY
      have eq : q = (1 - p.1, 1) := Prod.ext href hqY
      rw [ep, eq]
      let t : Set.Icc (0 : ℝ) 1 := ⟨p.1, hp0, hp1⟩
      simpa [t] using bt t
    · have ep : p = (1, 0) := Prod.ext hpX hpY
      have eq : q = (1, 1) := Prod.ext hqX hqY
      subst p; subst q
      let o : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
      have h1 : EqvGen SquareRel (1, 0) (0, 1) := by simpa [o] using bt o
      have h2 : EqvGen SquareRel (0, 1) (1, 1) := by simpa [o] using lr o
      exact EqvGen.trans _ _ _ h1 h2

#print axioms cases_eqvGen

end KleinSquareCasesToEqvGen

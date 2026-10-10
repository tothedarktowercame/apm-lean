import ConstructionTargets.UnitIntervalIntegerClassification

namespace KleinPlaneActionSquareOrbitClassification

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm
open KleinPlaneAffineAction
open UnitIntervalIntegerClassification

def InSquare (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def Cases (p q : ℝ × ℝ) : Prop :=
    (∃ m : ℤ, p.2 = 1 ∧ q.2 = 0 ∧
      ((m = 0 ∧ p.1 = 0 ∧ q.1 = 0) ∨
       (m = 1 ∧ q.1 = 1 - p.1) ∨
       (m = 2 ∧ p.1 = 1 ∧ q.1 = 1))) ∨
    (∃ m : ℤ, p.2 = q.2 ∧
      ((m = -1 ∧ p.1 = 1 ∧ q.1 = 0) ∨
       (m = 0 ∧ q.1 = p.1) ∨
       (m = 1 ∧ p.1 = 0 ∧ q.1 = 1))) ∨
    (∃ m : ℤ, p.2 = 0 ∧ q.2 = 1 ∧
      ((m = 0 ∧ p.1 = 0 ∧ q.1 = 0) ∨
       (m = 1 ∧ q.1 = 1 - p.1) ∨
       (m = 2 ∧ p.1 = 1 ∧ q.1 = 1)))

theorem sameOrbit_cases {p q : ℝ × ℝ}
    (hp : InSquare p) (hq : InSquare q)
    (h : ∃ g : PresentedKleinGroup, g • p = q) : Cases p q := by
  obtain ⟨g, hg⟩ := h
  let c := coordinateEquiv g
  let m : ℤ := Multiplicative.toAdd c.1
  let n : ℤ := Multiplicative.toAdd c.2
  have hact : coordinateAct c p = q := hg
  have hy : q.2 = (n : ℝ) + p.2 := by
    simpa [coordinateAct, n] using congrArg Prod.snd hact.symm
  rcases translation hp.2.2.1 hp.2.2.2 hq.2.2.1 hq.2.2.2 hy with
    hn | hn | hn
  · rcases hn with ⟨hn, hp2, hq2⟩
    left
    refine ⟨m, hp2, hq2, ?_⟩
    have hx : q.1 = (m : ℝ) - p.1 := by
      simpa [coordinateAct, m, n, hn, KleinPresentedGroupCoordinateModel.action,
        KleinPresentedGroupCoordinateModel.inversion] using congrArg Prod.fst hact.symm
    exact reflection hp.1 hp.2.1 hq.1 hq.2.1 hx
  · rcases hn with ⟨hn, hq2⟩
    right; left
    refine ⟨m, hq2.symm, ?_⟩
    have hx : q.1 = (m : ℝ) + p.1 := by
      simpa [coordinateAct, m, n, hn, KleinPresentedGroupCoordinateModel.action,
        KleinPresentedGroupCoordinateModel.inversion] using congrArg Prod.fst hact.symm
    exact translation hp.1 hp.2.1 hq.1 hq.2.1 hx
  · rcases hn with ⟨hn, hp2, hq2⟩
    right; right
    refine ⟨m, hp2, hq2, ?_⟩
    have hx : q.1 = (m : ℝ) - p.1 := by
      simpa [coordinateAct, m, n, hn, KleinPresentedGroupCoordinateModel.action,
        KleinPresentedGroupCoordinateModel.inversion] using congrArg Prod.fst hact.symm
    exact reflection hp.1 hp.2.1 hq.1 hq.2.1 hx

theorem cases_sameOrbit {p q : ℝ × ℝ} (h : Cases p q) :
    ∃ g : PresentedKleinGroup, g • p = q := by
  rcases h with ⟨m, hp2, hq2, hm⟩ | ⟨m, hpq2, hm⟩ | ⟨m, hp2, hq2, hm⟩
  · refine ⟨coordinateEquiv.symm
        ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd (-1 : ℤ)⟩, ?_⟩
    change coordinateAct (coordinateEquiv (coordinateEquiv.symm _)) p = q
    rw [coordinateEquiv.apply_symm_apply]
    rcases hm with ⟨rfl, hp1, hq1⟩ | ⟨rfl, hq1⟩ | ⟨rfl, hp1, hq1⟩
    all_goals ext <;> simp [coordinateAct, KleinPresentedGroupCoordinateModel.action,
      KleinPresentedGroupCoordinateModel.inversion, *] <;> ring
  · refine ⟨coordinateEquiv.symm
        ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd (0 : ℤ)⟩, ?_⟩
    change coordinateAct (coordinateEquiv (coordinateEquiv.symm _)) p = q
    rw [coordinateEquiv.apply_symm_apply]
    rcases hm with ⟨rfl, hp1, hq1⟩ | ⟨rfl, hq1⟩ | ⟨rfl, hp1, hq1⟩
    all_goals ext <;> simp [coordinateAct, KleinPresentedGroupCoordinateModel.action,
      KleinPresentedGroupCoordinateModel.inversion, *] <;> ring
  · refine ⟨coordinateEquiv.symm
        ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd (1 : ℤ)⟩, ?_⟩
    change coordinateAct (coordinateEquiv (coordinateEquiv.symm _)) p = q
    rw [coordinateEquiv.apply_symm_apply]
    rcases hm with ⟨rfl, hp1, hq1⟩ | ⟨rfl, hq1⟩ | ⟨rfl, hp1, hq1⟩
    all_goals ext <;> simp [coordinateAct, KleinPresentedGroupCoordinateModel.action,
      KleinPresentedGroupCoordinateModel.inversion, *] <;> ring

theorem sameOrbit_iff_cases {p q : ℝ × ℝ}
    (hp : InSquare p) (hq : InSquare q) :
    (∃ g : PresentedKleinGroup, g • p = q) ↔ Cases p q :=
  ⟨sameOrbit_cases hp hq, cases_sameOrbit⟩

#print axioms sameOrbit_cases
#print axioms sameOrbit_iff_cases

end KleinPlaneActionSquareOrbitClassification

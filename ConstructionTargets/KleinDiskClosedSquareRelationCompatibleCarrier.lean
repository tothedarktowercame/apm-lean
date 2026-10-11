import ConstructionTargets.KleinDiskClosedSquareCompatibleCarrier

namespace ConstructionTargets.KleinDiskClosedSquareRelationCompatibleCarrier

/-!
The boundary components are numbered in their actual cyclic orders.  For the
disk these are the four `edgePoint` arcs.  For the square the cyclic order is
bottom, right, top, left, i.e. labels `2, 1, 3, 0` from
`KleinSquareEdgeOrientation.squareEdge`.
-/

def diskAdjacent (i j : Fin 4) : Prop :=
  (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) ∨
  (i.1 = 1 ∧ j.1 = 2) ∨ (i.1 = 2 ∧ j.1 = 1) ∨
  (i.1 = 2 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 2) ∨
  (i.1 = 3 ∧ j.1 = 0) ∨ (i.1 = 0 ∧ j.1 = 3)

def squareAdjacent (i j : Fin 4) : Prop :=
  (i.1 = 2 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 2) ∨
  (i.1 = 1 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 1) ∨
  (i.1 = 3 ∧ j.1 = 0) ∨ (i.1 = 0 ∧ j.1 = 3) ∨
  (i.1 = 0 ∧ j.1 = 2) ∨ (i.1 = 2 ∧ j.1 = 0)

def diskPaired (i j : Fin 4) : Prop :=
  (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) ∨
  (i.1 = 2 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 2)

def squarePaired (i j : Fin 4) : Prop :=
  (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 1 ∧ j.1 = 0) ∨
  (i.1 = 2 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 2)

theorem diskPaired_adjacent {i j : Fin 4} (h : diskPaired i j) :
    diskAdjacent i j := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem squarePaired_not_adjacent {i j : Fin 4} (h : squarePaired i j) :
    ¬ squareAdjacent i j := by
  intro ha
  rcases h with h | h | h | h <;> rcases h with ⟨hi, hj⟩ <;>
    rcases ha with ha | ha | ha | ha | ha | ha | ha | ha <;>
    omega

/-- A cyclic-order preserving or reversing correspondence between the four
boundary components cannot conjugate the disk generator pairing to the square
generator pairing. -/
theorem no_cyclic_relation_compatible_component_equiv :
    ¬ ∃ e : Fin 4 ≃ Fin 4,
      (∀ i j, diskAdjacent i j ↔ squareAdjacent (e i) (e j)) ∧
      (∀ i j, diskPaired i j ↔ squarePaired (e i) (e j)) := by
  rintro ⟨e, hadj, hpair⟩
  have hd : diskPaired (0 : Fin 4) (1 : Fin 4) := Or.inl ⟨rfl, rfl⟩
  have ha := (hadj 0 1).mp (diskPaired_adjacent hd)
  have hp := (hpair 0 1).mp hd
  exact squarePaired_not_adjacent hp ha

#print axioms no_cyclic_relation_compatible_component_equiv

end ConstructionTargets.KleinDiskClosedSquareRelationCompatibleCarrier

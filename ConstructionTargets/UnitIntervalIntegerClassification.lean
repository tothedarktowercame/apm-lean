import ConstructionTargets.KleinSquareRepresentative

namespace UnitIntervalIntegerClassification

theorem translation {m : ℤ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h : y = (m : ℝ) + x) :
    (m = -1 ∧ x = 1 ∧ y = 0) ∨
    (m = 0 ∧ y = x) ∨
    (m = 1 ∧ x = 0 ∧ y = 1) := by
  have hmloR : (-1 : ℝ) ≤ (m : ℝ) := by linarith
  have hmhiR : (m : ℝ) ≤ 1 := by linarith
  have hmlo : (-1 : ℤ) ≤ m := by exact_mod_cast hmloR
  have hmhi : m ≤ (1 : ℤ) := by exact_mod_cast hmhiR
  rcases (show m = -1 ∨ m = 0 ∨ m = 1 by omega) with hm | hm | hm
  · left
    subst m
    norm_num at h
    exact ⟨rfl, by linarith, by linarith⟩
  · right; left
    subst m
    norm_num at h
    exact ⟨rfl, h⟩
  · right; right
    subst m
    norm_num at h
    exact ⟨rfl, by linarith, by linarith⟩

theorem reflection {m : ℤ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h : y = (m : ℝ) - x) :
    (m = 0 ∧ x = 0 ∧ y = 0) ∨
    (m = 1 ∧ y = 1 - x) ∨
    (m = 2 ∧ x = 1 ∧ y = 1) := by
  have hmloR : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hmhiR : (m : ℝ) ≤ 2 := by linarith
  have hmlo : (0 : ℤ) ≤ m := by exact_mod_cast hmloR
  have hmhi : m ≤ (2 : ℤ) := by exact_mod_cast hmhiR
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with hm | hm | hm
  · left
    subst m
    norm_num at h
    exact ⟨rfl, by linarith, by linarith⟩
  · right; left
    subst m
    norm_num at h
    exact ⟨rfl, by linarith⟩
  · right; right
    subst m
    norm_num at h
    exact ⟨rfl, by linarith, by linarith⟩

#print axioms translation
#print axioms reflection

end UnitIntervalIntegerClassification

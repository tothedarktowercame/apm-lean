import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

open FreeGroup

/-- Counting letters with sign: a surjection onto ℤ. -/
def toZ (α : Type) [Nonempty α] : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift fun _ => Multiplicative.ofAdd 1

lemma toZ_of {α : Type} [Nonempty α] (a : α) : toZ α (FreeGroup.of a) = Multiplicative.ofAdd 1 := by
  simp [toZ]

lemma of_ne_one' {α : Type} [Nonempty α] (a : α) : (FreeGroup.of a : FreeGroup α) ≠ 1 := by
  intro h
  have := congrArg (toZ α) h
  simp [toZ_of] at this

instance : Infinite (Multiplicative ℤ) := inferInstanceAs (Infinite ℤ)

instance infinite_free (α : Type) [Nonempty α] : Infinite (FreeGroup α) := by
  refine Infinite.of_surjective (toZ α) ?_
  intro z
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨FreeGroup.of a ^ (Multiplicative.toAdd z), ?_⟩
  simp only [map_zpow, toZ_of]
  rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
  rfl

/-- The old fixture's r = 3 specialization is false at n = 0 (infinite index). -/
theorem old_fin_three_false :
    ¬ ∀ (n : ℕ) (H : Subgroup (FreeGroup (Fin 3))), H.index = n →
      Nonempty (H ≃* FreeGroup (Fin (2 * n + 1))) := by
  intro h
  obtain ⟨e⟩ := h 0 ⊥ (by rw [Subgroup.index_bot]; exact Nat.card_eq_zero_of_infinite)
  apply of_ne_one' (0 : Fin 1)
  apply e.symm.injective
  exact Subsingleton.elim _ _

/-- The old universal axiom is false at r = 0 (the seat's refutation, restated). -/
theorem old_universal_false_r0 :
    ¬ ∀ (r n : ℕ) (H : Subgroup (FreeGroup (Fin r))), H.index = n →
      Nonempty (H ≃* FreeGroup (Fin ((r - 1) * n + 1))) := by
  intro h
  obtain ⟨e⟩ := h 0 1 ⊤ Subgroup.index_top
  apply of_ne_one' (0 : Fin 1)
  apply e.symm.injective
  have one : ∀ x : FreeGroup (Fin 0), x = 1 := by
    intro x
    induction x using FreeGroup.induction_on with
    | C1 => rfl
    | of a => exact a.elim0
    | inv_of a => exact a.elim0
    | mul _ _ h1 h2 => simp [h1, h2]
  haveI : Subsingleton (FreeGroup (Fin 0)) := ⟨fun x y => (one x).trans (one y).symm⟩
  haveI : Subsingleton (⊤ : Subgroup (FreeGroup (Fin 0))) := by infer_instance
  exact Subsingleton.elim _ _

#print axioms old_fin_three_false
#print axioms old_universal_false_r0

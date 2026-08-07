import Mathlib

/-!
# APM b98A04

## Statement repairs

None.

## Encoding questions

A finite direct sum of copies of `M` is represented by `Fin s → M`. A supplied
composition series is encoded as a strictly increasing finite chain of
submodules from `⊥` to `⊤`, with every successive quotient simple.
-/

lemma apm_b98a04_commonAnnihilator
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (k : ℕ) (m : Fin k → M) :
    ∃ I : Submodule R R, (I : Set R) = {r | ∀ i, r • m i = 0} := by
  let I : Submodule R R :=
    { carrier := {r | ∀ i, r • m i = 0}
      zero_mem' := fun i ↦ zero_smul R (m i)
      add_mem' := fun {a b} ha hb i ↦ by rw [add_smul, ha i, hb i, zero_add]
      smul_mem' := fun a r hr i ↦ by rw [smul_eq_mul, mul_smul, hr i, smul_zero] }
  exact ⟨I, rfl⟩

def apm_b98a04_actionMap
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : ℕ) (m : Fin s → M) : R →ₗ[R] (Fin s → M) where
  toFun r i := r • m i
  map_add' a b := by ext i; exact add_smul a b (m i)
  map_smul' a b := by ext i; exact mul_smul a b (m i)

lemma apm_b98a04_actionMap_injective
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : ℕ) (m : Fin s → M)
    (h : {r : R | ∀ i, r • m i = 0} = {0}) :
    Function.Injective (apm_b98a04_actionMap R M s m) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hrmem : a - b ∈ ({r : R | ∀ i, r • m i = 0} : Set R) := by
    intro i
    rw [sub_smul]
    exact sub_eq_zero.mpr (congrFun hab i)
  rw [h] at hrmem
  simpa using hrmem

theorem apm_b98a04 :
    ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
      [FaithfulSMul R M] [IsArtinian R R],
      (∀ (k : ℕ) (m : Fin k → M),
        ∃ I : Submodule R R,
          (I : Set R) = {r | ∀ i, r • m i = 0}) ∧
      (∃ (s : ℕ) (m : Fin s → M),
        {r : R | ∀ i, r • m i = 0} = {0}) ∧
      (∃ (s : ℕ) (f : R →ₗ[R] (Fin s → M)), Function.Injective f) ∧
      (∀ (t : ℕ) (N : Fin (t + 1) → Submodule R M),
        N 0 = ⊥ →
        N (Fin.last t) = ⊤ →
        StrictMono N →
        (∀ i : Fin t,
          IsSimpleModule R
            (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) →
        ∀ (V : Type*) [AddCommGroup V] [Module R V] [IsSimpleModule R V],
          ∃ i : Fin t,
            Nonempty
              (V ≃ₗ[R]
                (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))) := by
  /-
  Boundary (closer hop 1): Mathlib contains the DCC minimization lemma
  `IsArtinian.set_has_minimal`, the faithful annihilator characterization
  `Module.annihilator_eq_bot`, and finite-length/Jordan--Hölder infrastructure
  including `isFiniteLength_of_exists_compositionSeries`. These support the
  informal minimal-common-annihilator argument and its embedding consequence.

  Two of those bridges now compile. `apm_b98a04_commonAnnihilator` explicitly
  constructs the common annihilator as a left `Submodule R R`; this avoids the
  commutativity assumptions on Mathlib's ideal-valued annihilator API and closes
  the first conjunct. `apm_b98a04_actionMap` bundles
  `r ↦ fun i => r • m i`, and `apm_b98a04_actionMap_injective` proves it
  injective whenever the common annihilator is `{0}`, closing the implication
  from the second conjunct to the third.

  The remaining Artinian step is to apply `IsArtinian.set_has_minimal` to the
  nonempty family of finite common annihilators and prove that a nonzero
  minimal member can be strictly decreased by adjoining a module element,
  using faithfulness. Searches of `LEMMA-INDEX.md`, all solved artifacts,
  `ConstructionTargets/`, Mathlib's annihilator/Artinian sources, and git
  history found no packaged finite-tuple minimization lemma.

  The final conjunct has a separate representation mismatch: its composition
  series is supplied as a raw `StrictMono` function
  `Fin (t + 1) → Submodule R M`, whereas Mathlib's Jordan--Hölder results use a
  `CompositionSeries` object. A completion must construct that object with the
  exact quotient factors shown, build a composition series for `Fin s → M`,
  transport finite length and factors to the embedded regular module, and show
  every simple module is a quotient/factor of it. The searched APIs do not
  package this factor-transport chain. The statement appears mathematically
  sound.
  -/
  sorry

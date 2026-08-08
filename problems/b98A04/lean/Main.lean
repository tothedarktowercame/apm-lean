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

/-- An Artinian faithful module is already faithful on a finite tuple. -/
lemma apm_b98a04_exists_faithful_tuple
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [FaithfulSMul R M] [IsArtinian R R] :
    ∃ (s : ℕ) (m : Fin s → M), {r : R | ∀ i, r • m i = 0} = {0} := by
  let C : Set (Submodule R R) :=
    {I | ∃ (s : ℕ) (m : Fin s → M), (I : Set R) = {r | ∀ i, r • m i = 0}}
  have hC : C.Nonempty := by
    obtain ⟨I, hI⟩ := apm_b98a04_commonAnnihilator R M 0 (fun i => Fin.elim0 i)
    exact ⟨I, 0, fun i => Fin.elim0 i, hI⟩
  obtain ⟨I, ⟨s, m, hI⟩, hmin⟩ := IsArtinian.set_has_minimal C hC
  refine ⟨s, m, ?_⟩
  apply Set.Subset.antisymm
  · intro r hr
    rw [← hI] at hr
    by_contra hr0
    have hnot : ¬∀ x : M, r • x = 0 := by
      intro hall
      apply hr0
      have hrzero : r = 0 := by
        apply FaithfulSMul.eq_of_smul_eq_smul (M := R) (α := M) (m₁ := r) (m₂ := 0)
        intro x
        simpa using hall x
      simpa [hrzero]
    obtain ⟨x, hx⟩ := not_forall.mp hnot
    let mx : Fin (s + 1) → M := Fin.cons x m
    obtain ⟨J, hJ⟩ :=
      apm_b98a04_commonAnnihilator R M (s + 1) mx
    have hJC : J ∈ C := ⟨s + 1, mx, hJ⟩
    have hJI : J ≤ I := by
      intro a ha
      change a ∈ (I : Set R)
      rw [hI]
      intro i
      have ha' : ∀ j : Fin (s + 1), a • mx j = 0 := by
        have ha' : a ∈ (J : Set R) := ha
        rw [hJ] at ha'
        exact ha'
      simpa [mx] using ha' i.succ
    have hrJ : r ∉ J := by
      intro hrJ
      have hrJ' : ∀ j : Fin (s + 1), r • mx j = 0 := by
        have hrJ' : r ∈ (J : Set R) := hrJ
        rw [hJ] at hrJ'
        exact hrJ'
      exact hx (by simpa [mx] using hrJ' 0)
    exact hmin J hJC (lt_of_le_of_ne hJI (fun hJIeq => hrJ (hJIeq ▸ hr)))
  · intro r hr
    rcases hr with rfl
    simp

/-- Once the regular module embeds in a finite power of `M`, every simple
module is a quotient of the image submodule. This isolates the remaining
Jordan--Hölder obligation to factor transport for a submodule. -/
lemma apm_b98a04_simple_quotient_of_embedded_regular
    (R M V : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [IsSimpleModule R V]
    (s : ℕ) (f : R →ₗ[R] (Fin s → M)) (hf : Function.Injective f) :
    ∃ (S : Submodule R (Fin s → M)) (g : S →ₗ[R] V),
      Function.Surjective g := by
  letI : Nontrivial V := IsSimpleModule.nontrivial R V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let e : R ≃ₗ[R] f.range := LinearEquiv.ofInjective f hf
  let g : f.range →ₗ[R] V :=
    (LinearMap.toSpanSingleton R V v).comp e.symm.toLinearMap
  refine ⟨f.range, g, ?_⟩
  intro y
  obtain ⟨r, hr⟩ := IsSimpleModule.toSpanSingleton_surjective R hv y
  refine ⟨e r, ?_⟩
  simpa [g, e] using hr

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
  intro R M _ _ _ _ _
  have htuple := apm_b98a04_exists_faithful_tuple R M
  refine ⟨apm_b98a04_commonAnnihilator R M, htuple, ?_, ?_⟩
  · obtain ⟨s, m, hm⟩ := htuple
    exact ⟨s, apm_b98a04_actionMap R M s m,
      apm_b98a04_actionMap_injective R M s m hm⟩
  /-
  Boundary (closer hop 2): the Artinian bridge left by hop 1 is now closed.
  `apm_b98a04_exists_faithful_tuple` applies
  `IsArtinian.set_has_minimal` to the family of finite common annihilators.
  If a minimal member contains a nonzero `r`, `FaithfulSMul` supplies `x` with
  `r • x ≠ 0`; adjoining `x` via `Fin.cons` gives a strictly smaller member,
  a contradiction. Together with `apm_b98a04_actionMap_injective`, this closes
  the first three frozen conjuncts without commutativity assumptions on `R`.

  I then inspected `Order.JordanHolder`, `SimpleModule.Basic`, finite-length,
  quotient, submodule, and simple-module APIs beyond hop 1. The remaining raw
  chain can be packaged as a `CompositionSeries`, but the decisive theorem
  needed here is stronger than uniqueness of two composition series of the
  same module: one must transport the series of `M` to `Fin s → M`, restrict
  it along the embedded regular module, and prove that every simple `R`-module
  occurs among those factors. Mathlib has no packaged Schreier-refinement or
  factor-occurrence theorem for an arbitrary submodule in the exact quotient
  representation frozen here, and repository-wide searches found no sibling
  implementation. That Jordan--Hölder factor-transport bridge remains open;
  the statement is unchanged.

  CLOSER HOP 3: `apm_b98a04_simple_quotient_of_embedded_regular` now proves
  the exact reduction beyond hop 2. Given the compiled injection
  `R → Fin s → M`, `LinearEquiv.ofInjective` identifies `R` with its image;
  a nonzero vector of any simple `V` makes `LinearMap.toSpanSingleton`
  surjective, and composition gives a surjection from that image submodule
  onto `V`. Thus every target simple module is now explicitly a quotient of a
  submodule of a finite power of `M`.

  The sole remaining bridge is consequently the factor-occurrence theorem:
  a simple quotient of a submodule of `Fin s → M` must occur in the supplied
  composition series of `M`. Searches of Jordan--Hölder, modular-lattice,
  quotient, and finite-direct-product APIs found no packaged theorem deriving
  that occurrence in the frozen quotient representation.

  HOP 4 checked `JordanHolderModule.instJordanHolderLattice`,
  `CompositionSeries.jordan_holder`, `IsFiniteLength.iff_exists_compositionSeries`,
  and the quotient equivalences in `SimpleModule.Basic`. The exact missing
  theorem is the following factor-occurrence statement (with all quotient
  types matching the frozen conclusion):

    `∀ (R M V : Type*) [Ring R] [AddCommGroup M] [Module R M]
        [AddCommGroup V] [Module R V] [IsSimpleModule R V]
        (s t : ℕ) (S : Submodule R (Fin s → M))
        (g : S →ₗ[R] V), Function.Surjective g →
        ∀ (N : Fin (t + 1) → Submodule R M),
          N 0 = ⊥ → N (Fin.last t) = ⊤ → StrictMono N →
          (∀ i : Fin t,
            IsSimpleModule R
              (N i.succ ⧸ Submodule.comap (N i.succ).subtype
                (N i.castSucc))) →
          ∃ i : Fin t,
            Nonempty
              (V ≃ₗ[R]
                (N i.succ ⧸ Submodule.comap (N i.succ).subtype
                  (N i.castSucc)))`.

  Proving it requires constructing composition series for a finite product,
  its submodule `S`, and the quotient by `LinearMap.ker g`, then transporting
  factor equivalences through three Jordan--Hölder comparisons. No searched
  declaration performs those constructions or the final quotient-type
  normalization. The theorem remains the sole sorry and the frozen statement
  is unchanged.
  -/
  sorry

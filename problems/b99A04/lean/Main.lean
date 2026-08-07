import Mathlib

/-!
# APM b99A04

## Statement repairs

The conventional implicit hypothesis `n > 0` is made explicit.  For `n = 0`, the
column-vector module is the zero module and is not simple in Mathlib's sense, so part
(a) would otherwise be false.

## Encoding questions

None.  `Matrix n n F` acts on `n → F` through Mathlib's usual matrix-vector module
instance.  A left ideal is represented as a submodule of the left regular module.
-/

noncomputable section

def apmLeftIdealAction
    {R W : Type*} [Ring R] [AddCommGroup W] [Module R W]
    (L : Submodule R R) (x : W) : L →ₗ[R] W where
  toFun a := (a : R) • x
  map_add' a b := by
    change ((a : R) + (b : R)) • x = (a : R) • x + (b : R) • x
    exact add_smul (a : R) (b : R) x
  map_smul' r a := by simp [mul_smul]

private def matrixColumnsLinearEquiv
    (F : Type*) [Field F] (n : ℕ) :
    let R := Matrix (Fin n) (Fin n) F
    let V := Fin n → F
    R ≃ₗ[R] (Fin n → V) := by
  dsimp only
  refine
    { toFun := fun A i j => A j i
      invFun := fun c j i => c i j
      left_inv := fun A => rfl
      right_inv := fun c => rfl
      map_add' := fun A B => rfl
      map_smul' := ?_ }
  intro A B
  ext i j
  change (A * B) j i = ∑ k, A j k * B k i
  rfl

theorem apm_b99a04
    (F : Type*) [Field F] (n : ℕ) (hn : 0 < n) :
    let R := Matrix (Fin n) (Fin n) F
    let V := Fin n → F
    IsSimpleModule R V ∧
      ∃ L : Fin n → Submodule R R,
        iSupIndep L ∧
        (⨆ i, L i) = ⊤ ∧
        (∀ i, Nonempty (L i ≃ₗ[R] V)) ∧
        (∀ (W : Type*) [AddCommGroup W] [Module R W] (x : W) (i : Fin n),
          LinearMap.range (apmLeftIdealAction (L i) x) ≠ ⊥ →
            Nonempty (LinearMap.range (apmLeftIdealAction (L i) x) ≃ₗ[R] V)) ∧
        ∀ (W : Type*) [AddCommGroup W] [Module R W]
          [Module F W] [IsScalarTower F R W] [FiniteDimensional F W],
          ∃ m : ℕ, Nonempty (W ≃ₗ[R] (Fin m → V)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  dsimp only
  have hsimple : IsSimpleModule (Matrix (Fin n) (Fin n) F) (Fin n → F) := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    constructor
    · infer_instance
    · intro v hv w
      have hj : ∃ j : Fin n, v j ≠ 0 := by
        by_contra h
        push_neg at h
        apply hv
        funext j
        exact h j
      obtain ⟨j, hj⟩ := hj
      let A : Matrix (Fin n) (Fin n) F := fun i k =>
        if k = j then w i / v j else 0
      refine ⟨A, ?_⟩
      ext i
      change ∑ k : Fin n, A i k * v k = w i
      simp [A, hj]
  constructor
  · exact hsimple
  · -- The concrete column ideals are transported from the coordinate
    -- submodules of `Fin n →₀ V`; see `matrixColumnsLinearEquiv` above.
    let R := Matrix (Fin n) (Fin n) F
    let V := Fin n → F
    letI : IsSimpleModule R V := hsimple
    let e : R ≃ₗ[R] (Fin n → V) := matrixColumnsLinearEquiv F n
    let q : (Fin n →₀ V) ≃ₗ[R] R :=
      (Finsupp.linearEquivFunOnFinite R V (Fin n)).trans e.symm
    let c (i : Fin n) : V →ₗ[R] R :=
      q.toLinearMap.comp (Finsupp.lsingle i)
    let L (i : Fin n) : Submodule R R := LinearMap.range (c i)
    refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [L, c, LinearMap.range_comp] using
        q.toLinearMap.iSupIndep_map q.injective
          (iSupIndep_range_lsingle (Fin n) R V)
    · change (⨆ i, LinearMap.range (c i)) = ⊤
      have hs : (⨆ i : Fin n, LinearMap.range
          (Finsupp.lsingle (R := R) (M := V) i)) = ⊤ := by
        apply top_unique
        intro x hx
        classical
        rw [← Finsupp.sum_single x]
        exact Submodule.sum_mem _ fun i hi =>
          Submodule.mem_iSup_of_mem i ⟨x i, rfl⟩
      simp only [c, LinearMap.range_comp, ← Submodule.map_iSup, hs,
        Submodule.map_top, LinearEquiv.range]
    · intro i
      exact ⟨(LinearEquiv.ofInjective (c i)
        (q.injective.comp (Finsupp.single_injective i))).symm⟩
    · -- A nonzero map out of a simple column is injective, so its range is
      -- another copy of the standard simple module.
      intro W _ _ x i hrange
      let eLi : L i ≃ₗ[R] V := (LinearEquiv.ofInjective (c i)
        (q.injective.comp (Finsupp.single_injective i))).symm
      letI : IsSimpleModule R (L i) := IsSimpleModule.congr eLi
      have hne : apmLeftIdealAction (L i) x ≠ 0 := by
        intro hzero
        apply hrange
        simp [hzero]
      have hinj : Function.Injective (apmLeftIdealAction (L i) x) :=
        LinearMap.injective_of_ne_zero hne
      exact ⟨(LinearEquiv.ofInjective (apmLeftIdealAction (L i) x) hinj).symm.trans eLi⟩
    · /-
      Boundary (closer hop 1): parts (a)--(c), including the requested
      *specific* `Fin n` family of column left ideals, now compile.  The family
      is obtained by transporting `Finsupp.lsingle` through
      `matrixColumnsLinearEquiv`; `LinearMap.iSupIndep_map` proves independence,
      and `Finsupp.sum_single` proves that its supremum is `⊤`.

      The sole remaining clause is the finite-module classification. Searches
      checked `IsSimpleRing.isIsotypic`, `IsIsotypic.linearEquiv_fun`,
      `IsIsotypicOfType.linearEquiv_fun`,
      `Module.Finite.of_restrictScalars_finite`, and the Wedderburn--Artin
      matrix-ring instances.  `Module.Finite.of_restrictScalars_finite` bridges
      finite-dimensionality over `F` to module-finiteness over `R`, and the
      isotypic API decomposes `W` into copies of an abstract simple submodule.
      What remains is identifying that abstract simple type with the concrete
      standard module `V`.  A direct route is to choose a nonzero vector in the
      abstract simple submodule, use `(iSup L) = ⊤` to find a column whose
      action is nonzero, and then apply the range equivalence proved immediately
      above.  Mathlib has no packaged theorem performing this final concrete
      simple-type identification.
      -/
      sorry

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
  constructor
  · rw [isSimpleModule_iff_toSpanSingleton_surjective]
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
  · /-
    Boundary after proving part (a): the rank-one matrix construction above
    establishes `IsSimpleModule (Matrix (Fin n) (Fin n) F) (Fin n → F)`.
    Mathlib consultation found the matrix-ring semisimplicity instance
    `IsSemisimpleRing.matrix` in
    `RingTheory/SimpleModule/WedderburnArtin.lean`, together with
    `IsSimpleRing.isIsotypic`, `IsIsotypicOfType.linearEquiv_fun`, and
    `IsSimpleModule.injective_of_ne_zero`. These package the abstract routes
    for parts (c) and (d).

    The remaining formal bridge is part (b): construct the requested *specific*
    `Fin n` family of column left ideals, prove `iSupIndep` and supremum `⊤`,
    and give each column an `R`-linear equivalence with `Fin n → F`.
    Searches for `Matrix` column `LinearEquiv`, `iSupIndep.*Matrix`, and
    `stdBasisMatrix.*Submodule` found no packaged column-ideal decomposition.
    A direct proof must define the column-support submodules and verify the
    dependent lattice bookkeeping before the abstract semisimplicity APIs can
    discharge the last two conjuncts.
    -/
    sorry

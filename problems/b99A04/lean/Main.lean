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
  sorry

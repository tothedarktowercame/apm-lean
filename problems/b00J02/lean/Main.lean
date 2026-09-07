import Mathlib

/-!
# APM b00J02

## Statement repairs

None.

## Encoding questions

None. `GL (Fin 3) (ZMod 4)` is Mathlib's group of invertible `3 × 3`
matrices over `ℤ/4ℤ`.

## Proof constraints

The proof must be kernel-checked. `#print axioms` on the target declaration
must report exactly `[propext, Classical.choice, Quot.sound]`. `native_decide`
is not acceptable: it discharges the goal through the compiler rather than the
kernel and introduces a `._native.native_decide.` axiom.

A previous attempt (jit-all-open-v2 frame f60) discharged the counting
steps with `native_decide`, producing `apm_b00j02._native.native_decide.ax_1_2`
in `#print axioms`. That attempt was rejected and is not recorded as a proof.
-/

/-- The residue-field factor in the reduction-modulo-two count. -/
lemma apm_b00j02_card_GL_mod2 :
    Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field]
  decide

private def apm_b00j02_red : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num) _

private lemma apm_b00j02_isUnit_of_red_ne_zero (x : ZMod 4)
    (h : apm_b00j02_red x ≠ 0) : IsUnit x := by
  revert x h
  decide

private lemma apm_b00j02_isUnit_det_of_map_eq_one
    (A : Matrix (Fin 3) (Fin 3) (ZMod 4))
    (h : A.map apm_b00j02_red = 1) : IsUnit A.det := by
  apply apm_b00j02_isUnit_of_red_ne_zero
  rw [RingHom.map_det]
  change (A.map apm_b00j02_red).det ≠ 0
  rw [h, Matrix.det_one]
  norm_num

private noncomputable def apm_b00j02_kernelMatrixEquiv :
    (Matrix.GeneralLinearGroup.map (n := Fin 3) apm_b00j02_red).ker ≃
      {A : Matrix (Fin 3) (Fin 3) (ZMod 4) // A.map apm_b00j02_red = 1} where
  toFun g := ⟨g.1.1, by
    change ((Matrix.GeneralLinearGroup.map apm_b00j02_red) g.1).val = 1
    exact congrArg Units.val g.2⟩
  invFun A := ⟨Matrix.GeneralLinearGroup.mk'' A.1
      (apm_b00j02_isUnit_det_of_map_eq_one A.1 A.2), by
    apply Units.ext
    exact A.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

private noncomputable def apm_b00j02_matrixFiberEquiv :
    {A : Matrix (Fin 3) (Fin 3) (ZMod 4) // A.map apm_b00j02_red = 1} ≃
      ((i : Fin 3) → (j : Fin 3) →
        {x : ZMod 4 // apm_b00j02_red x = if i = j then 1 else 0}) :=
  (Equiv.subtypeEquiv (Equiv.refl _) fun A => by
      rw [← Matrix.ext_iff]
      simp [Matrix.one_apply]).trans <|
    Equiv.subtypePiEquivPi.trans <|
      Equiv.piCongrRight fun _ => Equiv.subtypePiEquivPi

private lemma apm_b00j02_card_kernel :
    Nat.card (Matrix.GeneralLinearGroup.map (n := Fin 3) apm_b00j02_red).ker = 512 := by
  rw [Nat.card_congr apm_b00j02_kernelMatrixEquiv,
    Nat.card_congr apm_b00j02_matrixFiberEquiv]
  have hf (i j : Fin 3) :
      Fintype.card {x : ZMod 4 // apm_b00j02_red x = if i = j then 1 else 0} = 2 := by
    fin_cases i <;> fin_cases j <;> decide
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_pi, hf]
  decide

private def apm_b00j02_lift (x : ZMod 2) : ZMod 4 := x.val

private lemma apm_b00j02_red_lift (x : ZMod 2) :
    apm_b00j02_red (apm_b00j02_lift x) = x := by
  revert x
  decide

private lemma apm_b00j02_map_surjective : Function.Surjective
    (Matrix.GeneralLinearGroup.map (n := Fin 3) apm_b00j02_red) := by
  intro g
  let A : Matrix (Fin 3) (Fin 3) (ZMod 4) :=
    fun i j => apm_b00j02_lift (g i j)
  have hA : A.map apm_b00j02_red = g.val := by
    ext i j
    exact apm_b00j02_red_lift (g i j)
  have hdet : IsUnit A.det := by
    apply apm_b00j02_isUnit_of_red_ne_zero
    rw [RingHom.map_det]
    change (A.map apm_b00j02_red).det ≠ 0
    rw [hA]
    exact g.det_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mk'' A hdet, ?_⟩
  apply Units.ext
  exact hA

theorem apm_b00j02 :
    Fintype.card (GL (Fin 3) (ZMod 4)) = 86016 := by
  rw [← Nat.card_eq_fintype_card]
  let f := Matrix.GeneralLinearGroup.map (n := Fin 3) apm_b00j02_red
  rw [← f.ker.card_mul_index, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr apm_b00j02_map_surjective]
  rw [apm_b00j02_card_kernel, show Nat.card (⊤ : Subgroup (GL (Fin 3) (ZMod 2))) = 168 by
    simpa using apm_b00j02_card_GL_mod2]

#print axioms apm_b00j02

import Mathlib

/-! # lts-ultraproduct-thm1: ultraproducts commute with factor algebras

## Statement encoding

The common algebraic signature, its operations, and operation-compatible
congruences are explicit.  The canonical carrier bijection is promoted to an
algebra isomorphism by proving that it preserves every operation.

## Encoding questions

Both sides are concrete quotient types.  `quotientAfter` first identifies
pointwise-congruent representatives modulo the ultrafilter; `quotientBefore`
first forms each factor and then takes their ultraproduct.
-/

namespace APMLTSUltraproduct

/-- A (single-sorted) algebraic signature, indexed by operation arity. -/
structure Signature where
  Symbol : ℕ → Type*

/-- An algebra for a fixed signature. -/
structure Algebra (S : Signature) (A : Type*) where
  op : ∀ {n}, S.Symbol n → (Fin n → A) → A

/-- A congruence is an equivalence relation compatible with every operation. -/
structure Congruence (S : Signature) {A : Type*} (alg : Algebra S A)
    extends Setoid A where
  op_compatible : ∀ {n} (s : S.Symbol n) {x y : Fin n → A},
    (∀ j, r (x j) (y j)) → r (alg.op s x) (alg.op s y)

def moduloSetoid {I : Type*} (D : Ultrafilter I) (A : I → Type*)
    (σ : ∀ i, Setoid (A i)) : Setoid (∀ i, A i) where
  r f g := {i | (σ i).r (f i) (g i)} ∈ D
  iseqv := by
    constructor
    · intro f
      convert D.univ_mem using 1
      ext i
      simp
    · intro f g hfg
      filter_upwards [hfg] with i hi
      exact (σ i).symm hi
    · intro f g h hfg hgh
      filter_upwards [hfg, hgh] with i hi₁ hi₂
      exact (σ i).trans hi₁ hi₂

def equalitySetoid {I : Type*} (D : Ultrafilter I) (B : I → Type*) :
    Setoid (∀ i, B i) where
  r f g := {i | f i = g i} ∈ D
  iseqv := by
    constructor
    · intro f
      convert D.univ_mem using 1
      ext i
      simp
    · intro f g hfg
      filter_upwards [hfg] with i hi
      exact hi.symm
    · intro f g h hfg hgh
      filter_upwards [hfg, hgh] with i hi₁ hi₂
      exact hi₁.trans hi₂

def quotientAfter {I : Type*} (D : Ultrafilter I) (A : I → Type*)
    (σ : ∀ i, Setoid (A i)) := Quotient (moduloSetoid D A σ)

def quotientBefore {I : Type*} (D : Ultrafilter I) (A : I → Type*)
    (σ : ∀ i, Setoid (A i)) :=
  Quotient (equalitySetoid D (fun i => Quotient (σ i)))

/-- Isomorphisms of algebras over the same signature. -/
structure AlgEquiv (S : Signature) {A B : Type*} (a : Algebra S A)
    (b : Algebra S B) extends A ≃ B where
  map_op : ∀ {n} (s : S.Symbol n) (x : Fin n → A),
    toFun (a.op s x) = b.op s (fun j => toFun (x j))

noncomputable def quotientAfterAlgebra {I : Type*} (D : Ultrafilter I)
    (S : Signature) (A : I → Type*) (alg : ∀ i, Algebra S (A i))
    (σ : ∀ i, Congruence S (alg i)) :
    Algebra S (quotientAfter D A (fun i => (σ i).toSetoid)) where
  op s x := @Quotient.mk _ (moduloSetoid D A (fun i => (σ i).toSetoid)) (fun i =>
    (alg i).op s (fun j => Quotient.out (x j) i))

noncomputable def factorAlgebra (S : Signature) {A : Type*}
    (alg : Algebra S A) (σ : Congruence S alg) : Algebra S (Quotient σ.toSetoid) where
  op s x := @Quotient.mk A σ.toSetoid
    (alg.op s (fun j => Quotient.out (x j)))

noncomputable def quotientBeforeAlgebra {I : Type*} (D : Ultrafilter I)
    (S : Signature) (A : I → Type*) (alg : ∀ i, Algebra S (A i))
    (σ : ∀ i, Congruence S (alg i)) :
    Algebra S (quotientBefore D A (fun i => (σ i).toSetoid)) where
  op s x := @Quotient.mk _ (equalitySetoid D (fun i => Quotient (σ i).toSetoid)) (fun i =>
    (factorAlgebra S (alg i) (σ i)).op s (fun j => Quotient.out (x j) i))

noncomputable def canonicalMap {I : Type*} (D : Ultrafilter I)
    (A : I → Type*) (σ : ∀ i, Setoid (A i)) :
    quotientAfter D A σ → quotientBefore D A σ :=
  Quotient.lift (fun f =>
    @Quotient.mk _ (equalitySetoid D (fun i => Quotient (σ i)))
      (fun i => @Quotient.mk (A i) (σ i) (f i))) (by
    intro f g h
    apply Quotient.sound
    filter_upwards [h] with i hi
    exact Quotient.sound hi)

noncomputable def canonicalInverse {I : Type*} (D : Ultrafilter I)
    (A : I → Type*) (σ : ∀ i, Setoid (A i)) :
    quotientBefore D A σ → quotientAfter D A σ :=
  Quotient.lift (fun f =>
    @Quotient.mk _ (moduloSetoid D A σ) (fun i => Quotient.out (f i))) (by
    intro f g h
    apply Quotient.sound
    filter_upwards [h] with i hi
    simpa only [hi] using (σ i).refl (Quotient.out (g i)))

theorem canonicalInverse_left {I : Type*} (D : Ultrafilter I)
    (A : I → Type*) (σ : ∀ i, Setoid (A i))
    (x : quotientAfter D A σ) :
    canonicalInverse D A σ (canonicalMap D A σ x) = x := by
  induction x using Quotient.inductionOn with
  | _ f =>
      change @Quotient.mk _ (moduloSetoid D A σ)
          (fun i => Quotient.out (@Quotient.mk (A i) (σ i) (f i))) =
        @Quotient.mk _ (moduloSetoid D A σ) f
      apply Quotient.sound
      filter_upwards [] with i
      exact Quotient.exact (Quotient.out_eq _)

theorem canonicalInverse_right {I : Type*} (D : Ultrafilter I)
    (A : I → Type*) (σ : ∀ i, Setoid (A i))
    (x : quotientBefore D A σ) :
    canonicalMap D A σ (canonicalInverse D A σ x) = x := by
  induction x using Quotient.inductionOn with
  | _ f =>
      change @Quotient.mk _ (equalitySetoid D (fun i => Quotient (σ i)))
          (fun i => @Quotient.mk (A i) (σ i) (Quotient.out (f i))) =
        @Quotient.mk _ (equalitySetoid D (fun i => Quotient (σ i))) f
      apply Quotient.sound
      filter_upwards [] with i
      exact Quotient.out_eq _

noncomputable def canonicalEquiv {I : Type*} (D : Ultrafilter I)
    (A : I → Type*) (σ : ∀ i, Setoid (A i)) :
    quotientAfter D A σ ≃ quotientBefore D A σ where
  toFun := canonicalMap D A σ
  invFun := canonicalInverse D A σ
  left_inv := canonicalInverse_left D A σ
  right_inv := canonicalInverse_right D A σ

end APMLTSUltraproduct

theorem apm_lts_ultraproduct_thm1
    {I : Type*} [Nonempty I] (D : Ultrafilter I)
    (S : APMLTSUltraproduct.Signature)
    (A : I → Type*) (alg : ∀ i, APMLTSUltraproduct.Algebra S (A i))
    (σ : ∀ i, APMLTSUltraproduct.Congruence S (alg i)) :
    ∃ e : APMLTSUltraproduct.AlgEquiv S
        (APMLTSUltraproduct.quotientAfterAlgebra D S A alg σ)
        (APMLTSUltraproduct.quotientBeforeAlgebra D S A alg σ),
      (∀ f : ∀ i, A i,
        e.toFun (@Quotient.mk _
          (APMLTSUltraproduct.moduloSetoid D A (fun i => (σ i).toSetoid)) f) =
        @Quotient.mk _ (APMLTSUltraproduct.equalitySetoid D
          (fun i => Quotient (σ i).toSetoid))
          (fun i => @Quotient.mk (A i) (σ i).toSetoid (f i))) ∧
      (∀ f : ∀ i, Quotient (σ i).toSetoid,
        e.invFun (@Quotient.mk _ (APMLTSUltraproduct.equalitySetoid D
          (fun i => Quotient (σ i).toSetoid)) f) =
        @Quotient.mk _
          (APMLTSUltraproduct.moduloSetoid D A (fun i => (σ i).toSetoid))
          (fun i => Quotient.out (f i))) := by
  let e := APMLTSUltraproduct.canonicalEquiv D A (fun i => (σ i).toSetoid)
  let ae : APMLTSUltraproduct.AlgEquiv S
      (APMLTSUltraproduct.quotientAfterAlgebra D S A alg σ)
      (APMLTSUltraproduct.quotientBeforeAlgebra D S A alg σ) :=
    { e with
      map_op := by
        intro n s x
        apply Quotient.sound
        filter_upwards [Filter.eventually_all.2
          (fun j => by
            have hx : e.toFun (x j) =
                @Quotient.mk _ (APMLTSUltraproduct.equalitySetoid D
                  (fun i => Quotient (σ i).toSetoid))
                  (fun i => @Quotient.mk (A i) (σ i).toSetoid
                    (Quotient.out (x j) i)) := by
              calc
                e.toFun (x j) = e.toFun (@Quotient.mk _
                    (APMLTSUltraproduct.moduloSetoid D A
                      (fun i => (σ i).toSetoid)) (Quotient.out (x j))) :=
                  congrArg e.toFun (Quotient.out_eq (x j)).symm
                _ = _ := rfl
            have h := Quotient.exact ((Quotient.out_eq (e.toFun (x j))).trans hx)
            change {i | Quotient.out (e.toFun (x j)) i =
              @Quotient.mk (A i) (σ i).toSetoid (Quotient.out (x j) i)} ∈ D at h
            exact h)] with i hi
        apply Quotient.sound
        apply (σ i).op_compatible
        intro j
        change (σ i).r (Quotient.out (x j) i)
          (Quotient.out (Quotient.out (e.toFun (x j)) i))
        rw [hi j]
        exact (σ i).symm (Quotient.exact (Quotient.out_eq _)) }
  refine ⟨ae, ?_, ?_⟩
  · intro f
    rfl
  · intro f
    rfl

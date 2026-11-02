import Mathlib

/-!
# APM b90A02: Free, projective, and flat modules

## Statement repairs

None.  The source permits a noncommutative unital ring and defines flatness for right
modules.  Mathlib's tensor product needs a commutative base, so `Tens R F A` below is the
balanced tensor product `F ⊗_R A`, built as the quotient of `F ⊗[ℤ] A` by the relations
`xr ⊗ a = x ⊗ ra`.  Right `R`-modules are `Rᵐᵒᵖ`-modules.

## Encoding questions

`IsFlatRight R F` is the printed definition: `F ⊗ -` preserves exactness of
`A → B → C` for left `R`-modules.  The left modules range over one universe `w`, and the
theorem is universe-polymorphic in `w`.  Parts (c) and (d) use the same definition and
Mathlib's `Module.Projective`.  `apm_b90a02` is the main theorem;
`apm_b90a02_commutative` is the earlier version via Mathlib's `Module.Flat`.
-/

noncomputable section

open scoped TensorProduct

namespace APMb90A02

universe u v v' w

variable (R : Type u) [Ring R]
variable (F : Type v) [AddCommGroup F] [Module Rᵐᵒᵖ F]
variable (A : Type w) [AddCommGroup A] [Module R A]

def balanceRel : Set (F ⊗[ℤ] A) :=
  {z | ∃ (r : R) (x : F) (a : A),
    z = (MulOpposite.op r • x) ⊗ₜ[ℤ] a - x ⊗ₜ[ℤ] (r • a)}

def balanceSubgroup : AddSubgroup (F ⊗[ℤ] A) :=
  AddSubgroup.closure (balanceRel R F A)

/-- The tensor product of a right module and a left module, constructed as
the quotient of the abelian-group tensor product by the balancing relations. -/
abbrev Tens := (F ⊗[ℤ] A) ⧸ balanceSubgroup R F A

namespace Tens

variable {R F A}

def tmul (x : F) (a : A) : Tens R F A :=
  QuotientAddGroup.mk' (balanceSubgroup R F A) (x ⊗ₜ[ℤ] a)

lemma mk_tmul (x : F) (a : A) :
    QuotientAddGroup.mk' (balanceSubgroup R F A) (x ⊗ₜ[ℤ] a) =
      tmul (R := R) x a := rfl

@[simp] lemma tmul_zero (x : F) : tmul (R := R) x (0 : A) = 0 := by
  unfold tmul
  simp

@[simp] lemma zero_tmul (a : A) : tmul (R := R) (0 : F) a = 0 := by
  unfold tmul
  simp

@[simp] lemma tmul_add (x : F) (a₁ a₂ : A) :
    tmul (R := R) x (a₁ + a₂) = tmul (R := R) x a₁ + tmul (R := R) x a₂ := by
  unfold tmul
  rw [TensorProduct.tmul_add]
  rfl

@[simp] lemma add_tmul (x₁ x₂ : F) (a : A) :
    tmul (R := R) (x₁ + x₂) a = tmul (R := R) x₁ a + tmul (R := R) x₂ a := by
  unfold tmul
  rw [TensorProduct.add_tmul]
  rfl

@[simp] lemma tmul_balance (r : R) (x : F) (a : A) :
    tmul (R := R) (MulOpposite.op r • x) a = tmul (R := R) x (r • a) := by
  unfold tmul
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact AddSubgroup.subset_closure ⟨r, x, a, rfl⟩

variable {B : Type*} [AddCommGroup B] [Module R B]

def tmap (g : A →ₗ[R] B) : Tens R F A →+ Tens R F B :=
  QuotientAddGroup.map (balanceSubgroup R F A) (balanceSubgroup R F B)
    (TensorProduct.map (LinearMap.id (R := ℤ) (M := F))
      (g.restrictScalars ℤ)).toAddMonoidHom (by
        unfold balanceSubgroup
        rw [AddSubgroup.closure_le]
        rintro z ⟨r, x, a, rfl⟩
        change (TensorProduct.map (LinearMap.id (R := ℤ) (M := F))
          (g.restrictScalars ℤ))
            ((MulOpposite.op r • x) ⊗ₜ[ℤ] a - x ⊗ₜ[ℤ] (r • a)) ∈
          AddSubgroup.closure (balanceRel R F B)
        simp only [map_sub, TensorProduct.map_tmul, LinearMap.id_coe,
          id_eq, LinearMap.coe_restrictScalars]
        apply AddSubgroup.subset_closure
        exact ⟨r, x, g a, by rw [g.map_smul]⟩)

@[simp] lemma tmap_tmul (g : A →ₗ[R] B) (x : F) (a : A) :
    tmap (F := F) g (tmul (R := R) x a) = tmul (R := R) x (g a) := by
  rfl

lemma addHom_ext {X : Type*} [AddCommGroup X]
    {u v : Tens R F A →+ X}
    (h : ∀ x a, u (tmul (R := R) x a) = v (tmul (R := R) x a)) : u = v := by
  apply QuotientAddGroup.addMonoidHom_ext (balanceSubgroup R F A)
  apply AddMonoidHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => exact h x a
  | add x y hx hy =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy

variable {C : Type*} [AddCommGroup C] [Module R C]

lemma tmap_comp (g : A →ₗ[R] B) (h : B →ₗ[R] C) :
    (tmap (F := F) h).comp (tmap (F := F) g) =
      tmap (F := F) (h.comp g) := by
  apply addHom_ext
  intro x a
  simp

lemma tmap_id :
    tmap (F := F) (LinearMap.id (R := R) (M := A)) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro x a
  simp

lemma tmap_zero : tmap (F := F) (0 : A →ₗ[R] B) = 0 := by
  apply addHom_ext
  intro x a
  simp

variable {F' : Type*} [AddCommGroup F'] [Module Rᵐᵒᵖ F']

def fmap (i : F →ₗ[Rᵐᵒᵖ] F') : Tens R F A →+ Tens R F' A :=
  QuotientAddGroup.map (balanceSubgroup R F A) (balanceSubgroup R F' A)
    (TensorProduct.map (i.restrictScalars ℤ)
      (LinearMap.id (R := ℤ) (M := A))).toAddMonoidHom (by
        unfold balanceSubgroup
        rw [AddSubgroup.closure_le]
        rintro z ⟨r, x, a, rfl⟩
        change (TensorProduct.map (i.restrictScalars ℤ)
          (LinearMap.id (R := ℤ) (M := A)))
            ((MulOpposite.op r • x) ⊗ₜ[ℤ] a - x ⊗ₜ[ℤ] (r • a)) ∈
          AddSubgroup.closure (balanceRel R F' A)
        simp only [map_sub, TensorProduct.map_tmul, LinearMap.id_coe,
          id_eq, LinearMap.coe_restrictScalars]
        apply AddSubgroup.subset_closure
        exact ⟨r, i x, a, by rw [i.map_smul]⟩)

@[simp] lemma fmap_tmul (i : F →ₗ[Rᵐᵒᵖ] F') (x : F) (a : A) :
    fmap (A := A) i (tmul (R := R) x a) = tmul (R := R) (i x) a := by
  rfl

variable {F'' : Type*} [AddCommGroup F''] [Module Rᵐᵒᵖ F'']

lemma fmap_comp (i : F →ₗ[Rᵐᵒᵖ] F') (j : F' →ₗ[Rᵐᵒᵖ] F'') :
    (fmap (A := A) j).comp (fmap (A := A) i) = fmap (A := A) (j.comp i) := by
  apply addHom_ext
  intro x a
  simp

lemma fmap_id :
    fmap (A := A) (LinearMap.id (R := Rᵐᵒᵖ) (M := F)) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro x a
  simp

lemma tmap_fmap_comm (i : F →ₗ[Rᵐᵒᵖ] F') (g : A →ₗ[R] B) :
    (tmap (F := F') g).comp (fmap (A := A) i) =
      (fmap (A := B) i).comp (tmap (F := F) g) := by
  apply addHom_ext
  intro x a
  simp

variable {X : Type*} [AddCommGroup X]

/-- The finitary universal property of the balanced tensor product. -/
def lift (b : F →ₗ[ℤ] A →ₗ[ℤ] X)
    (hbal : ∀ (r : R) (x : F) (a : A),
      b (MulOpposite.op r • x) a = b x (r • a)) : Tens R F A →+ X :=
  QuotientAddGroup.lift (balanceSubgroup R F A)
    (TensorProduct.lift b).toAddMonoidHom (by
      unfold balanceSubgroup
      rw [AddSubgroup.closure_le]
      rintro z ⟨r, x, a, rfl⟩
      change (TensorProduct.lift b)
        ((MulOpposite.op r • x) ⊗ₜ[ℤ] a - x ⊗ₜ[ℤ] (r • a)) = 0
      simp [hbal])

@[simp] lemma lift_tmul (b : F →ₗ[ℤ] A →ₗ[ℤ] X)
    (hbal : ∀ (r : R) (x : F) (a : A),
      b (MulOpposite.op r • x) a = b x (r • a)) (x : F) (a : A) :
    lift b hbal (tmul (R := R) x a) = b x a := by
  exact QuotientAddGroup.lift_mk' (balanceSubgroup R F A) _ (x ⊗ₜ[ℤ] a)

end Tens

lemma exact_mapRange
    {R : Type u} [Ring R] {A B C : Type w}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] {ι : Type*}
    (g : A →ₗ[R] B) (h : B →ₗ[R] C) (hex : Function.Exact g h) :
    Function.Exact
      (Finsupp.mapRange.addMonoidHom g.toAddMonoidHom : (ι →₀ A) →+ (ι →₀ B))
      (Finsupp.mapRange.addMonoidHom h.toAddMonoidHom : (ι →₀ B) →+ (ι →₀ C)) := by
  classical
  intro y
  constructor
  · intro hy
    have hy0 : ∀ i, h (y i) = 0 := by
      intro i
      have := congrArg (fun z : ι →₀ C => z i) hy
      simpa using this
    have hexists : ∀ b : B, h b = 0 → ∃ a : A, g a = b := by
      intro b hb
      simpa [Set.mem_range] using (hex b).mp hb
    let s : B → A := fun b => if b = 0 then 0 else
      if hb : h b = 0 then Classical.choose (hexists b hb) else 0
    have hs0 : s 0 = 0 := by simp [s]
    let x : ι →₀ A := Finsupp.mapRange s hs0 y
    refine ⟨x, ?_⟩
    ext i
    simp only [x, Finsupp.mapRange_apply]
    have hi := hy0 i
    by_cases hyz : y i = 0
    · simp [s, hyz]
    · simp [s, hyz, hi, Classical.choose_spec (hexists (y i) hi)]
  · rintro ⟨x, rfl⟩
    ext i
    have hz := (hex (g (x i))).mpr ⟨x i, rfl⟩
    simpa using hz

/-- Exactness-preserving tensoring by a right module. The quantified left
modules live in an arbitrary common universe `w`. -/
def IsFlatRight (R : Type u) [Ring R]
    (F : Type v) [AddCommGroup F] [Module Rᵐᵒᵖ F] : Prop :=
  ∀ (A B C : Type w) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (g : A →ₗ[R] B) (h : B →ₗ[R] C), Function.Exact g h →
      Function.Exact (Tens.tmap (F := F) g) (Tens.tmap (F := F) h)

lemma isFlatRight_retract
    {R : Type u} [Ring R]
    {P : Type v} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    {F : Type v'} [AddCommGroup F] [Module Rᵐᵒᵖ F]
    (i : P →ₗ[Rᵐᵒᵖ] F) (q : F →ₗ[Rᵐᵒᵖ] P)
    (hqi : q.comp i = LinearMap.id) (hflat : IsFlatRight.{u,v',w} R F) :
    IsFlatRight.{u,v,w} R P := by
  intro A B C _ _ _ _ _ _ g h hex z
  constructor
  · intro hz
    have hzF : Tens.tmap (F := F) h (Tens.fmap (A := B) i z) = 0 := by
      rw [← AddMonoidHom.comp_apply, Tens.tmap_fmap_comm,
        AddMonoidHom.comp_apply, hz, map_zero]
    obtain ⟨y, hy⟩ := (hflat A B C g h hex (Tens.fmap (A := B) i z)).mp hzF
    refine ⟨Tens.fmap (A := A) q y, ?_⟩
    rw [← AddMonoidHom.comp_apply, Tens.tmap_fmap_comm,
      AddMonoidHom.comp_apply, hy, ← AddMonoidHom.comp_apply,
      Tens.fmap_comp, hqi, Tens.fmap_id, AddMonoidHom.id_apply]
  · rintro ⟨y, rfl⟩
    have hcomp : h.comp g = 0 := by
      ext a
      exact (hex (g a)).mpr ⟨a, rfl⟩
    rw [← AddMonoidHom.comp_apply, Tens.tmap_comp, hcomp]
    rw [Tens.tmap_zero]
    rfl

namespace Tens

variable {R : Type u} [Ring R]
variable {F : Type v} [AddCommGroup F] [Module Rᵐᵒᵖ F]
variable {ι : Type*} (b : Module.Basis ι Rᵐᵒᵖ F)
variable (A : Type w) [AddCommGroup A] [Module R A]

def coeffAddHom (a : A) : Rᵐᵒᵖ →+ A where
  toFun c := c.unop • a
  map_zero' := by simp
  map_add' c d := by simp [add_smul]

def freeBilin : F →ₗ[ℤ] A →ₗ[ℤ] (ι →₀ A) where
  toFun x :=
    { toFun := fun a => Finsupp.mapRange.addMonoidHom (coeffAddHom A a) (b.repr x)
      map_add' := by
        intro a₁ a₂
        ext i
        simp [coeffAddHom, smul_add]
      map_smul' := by
        intro n a
        ext i
        simp only [Finsupp.mapRange.addMonoidHom_apply,
          Finsupp.mapRange_apply, coeffAddHom, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk, smul_eq_mul]
        exact smul_comm _ _ _ }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro a
    change Finsupp.mapRange.addMonoidHom (coeffAddHom A a) (b.repr (x + y)) = _
    rw [map_add, map_add]
    rfl
  map_smul' := by
    intro n x
    apply LinearMap.ext
    intro a
    change Finsupp.mapRange.addMonoidHom (coeffAddHom A a) (b.repr (n • x)) = _
    rw [map_zsmul, map_zsmul]
    rfl

lemma freeBilin_balance (r : R) (x : F) (a : A) :
    freeBilin b A (MulOpposite.op r • x) a =
      freeBilin b A x (r • a) := by
  ext i
  simp [freeBilin, coeffAddHom, smul_smul, mul_assoc]

def freeToFinsupp : Tens R F A →+ (ι →₀ A) :=
  lift (freeBilin b A) (freeBilin_balance b A)

@[simp] lemma freeToFinsupp_tmul (x : F) (a : A) :
    freeToFinsupp b A (tmul (R := R) x a) =
      Finsupp.mapRange.addMonoidHom (coeffAddHom A a) (b.repr x) := by
  rw [freeToFinsupp, lift_tmul]
  rfl

def freeFromFinsupp : (ι →₀ A) →+ Tens R F A :=
  Finsupp.liftAddHom (fun i =>
    { toFun := fun a => tmul (R := R) (b i) a
      map_zero' := tmul_zero _
      map_add' := tmul_add _ })

@[simp] lemma freeFromFinsupp_single (i : ι) (a : A) :
    freeFromFinsupp b A (Finsupp.single i a) = tmul (R := R) (b i) a := by
  simp [freeFromFinsupp]

@[simp] lemma freeToFinsupp_basis (i : ι) (a : A) :
    freeToFinsupp b A (tmul (R := R) (b i) a) = Finsupp.single i a := by
  rw [freeToFinsupp_tmul]
  ext j
  simp [coeffAddHom]

def freeEquiv : Tens R F A ≃+ (ι →₀ A) where
  toFun := freeToFinsupp b A
  invFun := freeFromFinsupp b A
  map_add' := map_add _
  left_inv := by
    intro z
    have heq : (freeFromFinsupp b A).comp (freeToFinsupp b A) =
        AddMonoidHom.id _ := by
      apply addHom_ext
      intro x a
      rw [AddMonoidHom.comp_apply, freeToFinsupp_tmul]
      let c := b.repr x
      have hx : x = b.repr.symm c := by simp [c]
      rw [hx]
      induction c using Finsupp.induction with
      | zero => simp [freeFromFinsupp]
      | single_add i r c hi hr ih =>
          rw [map_add, map_add]
          simp only [LinearEquiv.apply_symm_apply]
          rw [map_add, map_add]
          have hm : (Finsupp.mapRange.addMonoidHom (coeffAddHom A a))
              (Finsupp.single i r) = Finsupp.single i (r.unop • a) := by
            ext j
            simp [coeffAddHom]
          rw [hm, freeFromFinsupp_single]
          simp only [LinearEquiv.apply_symm_apply] at ih
          rw [ih]
          rw [add_tmul, AddMonoidHom.id_apply, AddMonoidHom.id_apply]
          rw [show b.repr.symm (Finsupp.single i r) = r • b i by simp]
          rw [← tmul_balance (r := r.unop)]
          simp [coeffAddHom]
    exact DFunLike.congr_fun heq z
  right_inv := by
    intro z
    have heq : (freeToFinsupp b A).comp (freeFromFinsupp b A) =
        AddMonoidHom.id _ := by
      apply Finsupp.addHom_ext
      intro i a
      rw [AddMonoidHom.comp_apply, freeFromFinsupp_single,
        freeToFinsupp_basis, AddMonoidHom.id_apply]
    exact DFunLike.congr_fun heq z

lemma freeToFinsupp_natural {B : Type*} [AddCommGroup B] [Module R B]
    (g : A →ₗ[R] B) :
    (freeToFinsupp b B).comp (tmap (F := F) g) =
      (Finsupp.mapRange.addMonoidHom g.toAddMonoidHom).comp
        (freeToFinsupp b A) := by
  apply addHom_ext
  intro x a
  rw [AddMonoidHom.comp_apply, tmap_tmul, freeToFinsupp_tmul,
    AddMonoidHom.comp_apply, freeToFinsupp_tmul]
  ext i
  simp [coeffAddHom, g.map_smul]

end Tens

lemma free_isFlatRight
    {R : Type u} [Ring R]
    {F : Type v} [AddCommGroup F] [Module Rᵐᵒᵖ F]
    [Module.Free Rᵐᵒᵖ F] : IsFlatRight.{u,v,w} R F := by
  let b := Module.Free.chooseBasis Rᵐᵒᵖ F
  intro A B C _ _ _ _ _ _ g h hex z
  constructor
  · intro hz
    have hnath := Tens.freeToFinsupp_natural b B h
    have hz' : (Finsupp.mapRange.addMonoidHom h.toAddMonoidHom)
        (Tens.freeToFinsupp b B z) = 0 := by
      rw [← AddMonoidHom.comp_apply, ← hnath, AddMonoidHom.comp_apply, hz, map_zero]
    obtain ⟨x', hx'⟩ := (exact_mapRange g h hex (Tens.freeToFinsupp b B z)).mp hz'
    let x : Tens R F A := Tens.freeFromFinsupp b A x'
    refine ⟨x, ?_⟩
    apply (Tens.freeEquiv b B).injective
    have hnatg := Tens.freeToFinsupp_natural b A g
    rw [show (Tens.freeEquiv b B) (Tens.tmap (F := F) g x) =
      Tens.freeToFinsupp b B (Tens.tmap (F := F) g x) from rfl]
    rw [← AddMonoidHom.comp_apply, hnatg, AddMonoidHom.comp_apply]
    change (Finsupp.mapRange.addMonoidHom g.toAddMonoidHom)
      (Tens.freeToFinsupp b A (Tens.freeFromFinsupp b A x')) = _
    have hfa : Tens.freeToFinsupp b A (Tens.freeFromFinsupp b A x') = x' :=
      (Tens.freeEquiv b A).apply_symm_apply x'
    rw [hfa, hx']
    rfl
  · rintro ⟨x, rfl⟩
    have hcomp : h.comp g = 0 := by
      ext a
      exact (hex (g a)).mpr ⟨a, rfl⟩
    rw [← AddMonoidHom.comp_apply, Tens.tmap_comp, hcomp, Tens.tmap_zero]
    rfl

lemma projective_isFlatRight
    {R : Type u} [Ring R]
    {P : Type v} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (hproj : Module.Projective Rᵐᵒᵖ P) : IsFlatRight.{u,v,w} R P := by
  letI : Module.Projective Rᵐᵒᵖ P := hproj
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective Rᵐᵒᵖ P).out
  let q : (P →₀ Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] P :=
    Finsupp.linearCombination Rᵐᵒᵖ (fun p : P => p)
  have hqs : q.comp s = LinearMap.id := by
    ext p
    exact hs p
  apply isFlatRight_retract s q hqs
  exact free_isFlatRight


/-- `ℚ` as a right `ℤ`-module: `q · n = n q`. -/
instance ratRight : Module ℤᵐᵒᵖ ℚ :=
  Module.compHom ℚ (RingEquiv.toOpposite ℤ).symm.toRingHom

lemma op_smul_rat (n : ℤ) (q : ℚ) : MulOpposite.op n • q = n • q := rfl

/-- Over `ℤ` the balancing relations already hold in `⊗[ℤ]`. -/
lemma rat_balanceSubgroup_eq_bot (A : Type w) [AddCommGroup A] [hA : Module ℤ A] :
    balanceSubgroup ℤ ℚ A = ⊥ := by
  obtain rfl : hA = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  unfold balanceSubgroup
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro z ⟨n, q, a, rfl⟩
  have h : (MulOpposite.op n • q) ⊗ₜ[ℤ] a = q ⊗ₜ[ℤ] (n • a) := by
    rw [op_smul_rat]
    exact TensorProduct.smul_tmul n q a
  exact sub_eq_zero.2 h

/-- Part (c). -/
lemma rat_isFlatRight : IsFlatRight.{0, 0, w} ℤ ℚ := by
  intro A B C _ mA _ mB _ mC g h hex
  obtain rfl : mA = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  obtain rfl : mB = AddCommGroup.toIntModule B := Subsingleton.elim _ _
  obtain rfl : mC = AddCommGroup.toIntModule C := Subsingleton.elim _ _
  have hex' := Module.Flat.lTensor_exact ℚ (f := g) (g := h) hex
  have hzero : h.comp g = 0 := by
    ext a
    exact (hex (g a)).2 ⟨a, rfl⟩
  intro z
  constructor
  · induction z using QuotientAddGroup.induction_on with
    | H z' =>
      intro hz
      have hz1 : (LinearMap.lTensor ℚ h) z' ∈ balanceSubgroup ℤ ℚ C :=
        (QuotientAddGroup.eq_zero_iff _).1 hz
      rw [rat_balanceSubgroup_eq_bot] at hz1
      obtain ⟨y, hy⟩ := (hex' z').1 hz1
      refine ⟨QuotientAddGroup.mk y, ?_⟩
      exact congrArg (QuotientAddGroup.mk (s := balanceSubgroup ℤ ℚ B)) hy
  · rintro ⟨w', rfl⟩
    have := congrArg (fun u => u w') (Tens.tmap_comp (F := ℚ) g h)
    simp only [AddMonoidHom.comp_apply] at this
    rw [this, hzero, Tens.tmap_zero]
    rfl

end APMb90A02

lemma apm_b90a02_rat_to_int_eq_zero (f : ℚ →ₗ[ℤ] ℤ) (q : ℚ) : f q = 0 := by
  let n : ℕ := (f q).natAbs + 1
  have hn : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (f q).natAbs)
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq : (n : ℤ) • (q / n) = q := by
    change (n : ℚ) * (q / n) = q
    field_simp [hnQ]
  have hdvd : (n : ℤ) ∣ f q := by
    refine ⟨f (q / n), ?_⟩
    calc
      f q = f ((n : ℤ) • (q / n)) := congrArg f hq.symm
      _ = (n : ℤ) • f (q / n) := f.map_smul _ _
      _ = (n : ℤ) * f (q / n) := rfl
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  change (f q).natAbs < n
  simp [n]

theorem apm_b90a02_commutative
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    (Module.Free R M → Module.Flat R M) ∧
    (Module.Projective R M → Module.Flat R M) ∧
    Module.Flat ℤ ℚ ∧
    ¬Module.Projective ℤ ℚ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro
    infer_instance
  · intro
    infer_instance
  · infer_instance
  · intro hproj
    letI : Module.Projective ℤ ℚ := hproj
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective ℤ ℚ).out
    have hs0 : s = 0 := by
      ext q i
      exact apm_b90a02_rat_to_int_eq_zero ((Finsupp.lapply i).comp s) q
    have hone := hs (1 : ℚ)
    rw [hs0] at hone
    simpa using hone

universe u v w

open APMb90A02 in
/-- Free and projective right modules over any unital ring are flat, in the sense that
tensoring with them preserves exactness of sequences of left modules; `ℚ` is flat over `ℤ` in
the same sense and is not projective. -/
theorem apm_b90a02 :
    (∀ (R : Type u) [Ring R] (F : Type v) [AddCommGroup F] [Module Rᵐᵒᵖ F],
      Module.Free Rᵐᵒᵖ F → IsFlatRight.{u, v, w} R F) ∧
    (∀ (R : Type u) [Ring R] (F : Type v) [AddCommGroup F] [Module Rᵐᵒᵖ F],
      Module.Projective Rᵐᵒᵖ F → IsFlatRight.{u, v, w} R F) ∧
    IsFlatRight.{0, 0, w} ℤ ℚ ∧
    ¬ Module.Projective ℤ ℚ :=
  ⟨fun _ _ _ _ _ _ => free_isFlatRight, fun _ _ _ _ _ h => projective_isFlatRight h,
    rat_isFlatRight, (apm_b90a02_commutative ℤ ℤ).2.2.2⟩

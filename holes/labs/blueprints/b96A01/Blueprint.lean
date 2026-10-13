import Mathlib

open Matrix

noncomputable section

def apmIntegralMatrix {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) : Prop :=
  ∀ i j, ∃ z : ℤ, A i j = z

noncomputable def apmReduction (n : Type*) [Fintype n] [DecidableEq n]
    (p m : ℕ) (h : p ^ (m - 1) ∣ p ^ m) :
    Matrix.GeneralLinearGroup n (ZMod (p ^ m)) →*
      Matrix.GeneralLinearGroup n (ZMod (p ^ (m - 1))) :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom h _)

theorem apm_b96a01_part_a :
    ∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V) (u : Finset ι),
          A = AddSubgroup.closure (b '' (u : Set ι)) := by
  intro V _ _ _ A s hs
  let N : Submodule ℤ V := A.toIntSubmodule
  have hN : N = Submodule.span ℤ (s : Set V) := by
    simp [N, hs, AddSubgroup.toIntSubmodule_closure]
  letI : Module.Finite ℤ N := by
    rw [hN]
    infer_instance
  letI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  letI : Module.IsTorsionFree ℤ V := by infer_instance
  letI : Module.IsTorsionFree ℤ N := by infer_instance
  let nb := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := N)
  let n := nb.1
  let bA : Module.Basis (Fin n) ℤ N := nb.2
  let v : Fin n → V := fun j ↦ (bA j : V)
  have hvZ : LinearIndependent ℤ v := by
    exact bA.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hvQ : LinearIndependent ℚ v := by
    exact hvZ.localization (Rₛ := ℚ) (nonZeroDivisors ℤ)
  let hset : LinearIndepOn ℚ id (Set.range v) := hvQ.linearIndepOn_id
  let t : Set V := hset.extend (Set.subset_univ _)
  let b0 : Module.Basis t ℚ V := Module.Basis.extend hset
  have hv_mem : ∀ j, v j ∈ t := by
    intro j
    exact hset.subset_extend (Set.subset_univ _) (Set.mem_range_self j)
  let e : Fin n → t := fun j ↦ ⟨v j, hv_mem j⟩
  have heinj : Function.Injective e := by
    intro j k hjk
    apply hvQ.injective
    change v j = v k
    exact congr_arg (fun z : t ↦ (z : V)) hjk
  let q := Module.finrank ℚ V
  let I := ULift (Fin q)
  let eqv : t ≃ I := (b0.indexEquiv (Module.finBasis ℚ V)).trans Equiv.ulift.symm
  let b : Module.Basis I ℚ V := b0.reindex eqv
  let e' : Fin n → I := eqv ∘ e
  have heinj' : Function.Injective e' := eqv.injective.comp heinj
  let u : Finset I := Finset.univ.map ⟨e', heinj'⟩
  refine ⟨I, b, u, ?_⟩
  have hb_e : ∀ j, b (e' j) = v j := by
    intro j
    simp [b, e', eqv, b0, Module.Basis.extend_apply_self hset (e j), e]
  have himage : b '' (u : Set I) = Set.range v := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      simp only [u, Finset.coe_map, Finset.coe_univ, Set.image_univ,
        Set.mem_range] at hj
      obtain ⟨k, rfl⟩ := hj
      exact ⟨k, (hb_e k).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨e' j, ?_, hb_e j⟩
      simp [u]
  rw [himage]
  rw [← Submodule.span_int_eq_addSubgroupClosure,
    ← AddSubgroup.toIntSubmodule_toAddSubgroup A]
  congr 1
  change N = Submodule.span ℤ (Set.range v)
  symm
  convert congrArg (Submodule.map N.subtype) bA.span_eq
  · rw [Submodule.map_span, ← Set.range_comp]
    rfl
  · exact (Submodule.map_subtype_top N).symm

lemma apm_b96a01_part_b_aux_finite_orbit
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) [Finite G] :
    ∃ s : Finset (n → ℚ),
      (∀ j : n, Pi.single j 1 ∈ AddSubgroup.closure (s : Set (n → ℚ))) ∧
      ∀ g : G, ∀ x ∈ AddSubgroup.closure (s : Set (n → ℚ)),
        (g.1 : Matrix n n ℚ) *ᵥ x ∈ AddSubgroup.closure (s : Set (n → ℚ)) := by
  letI : Fintype G := Fintype.ofFinite G
  let s : Finset (n → ℚ) := Finset.univ.image fun p : G × n ↦
    (p.1.1 : Matrix n n ℚ) *ᵥ Pi.single p.2 1
  refine ⟨s, ?_, ?_⟩
  · intro j
    apply AddSubgroup.subset_closure
    simp only [s, Finset.mem_coe, Finset.mem_image]
    refine ⟨((1 : G), j), Finset.mem_univ _, ?_⟩
    exact Matrix.one_mulVec _
  · intro g x hx
    let F : (n → ℚ) →+ (n → ℚ) :=
      { toFun := fun x ↦ (g.1 : Matrix n n ℚ) *ᵥ x
        map_zero' := Matrix.mulVec_zero _
        map_add' := fun x y ↦ Matrix.mulVec_add _ _ _ }
    change F x ∈ AddSubgroup.closure (s : Set (n → ℚ))
    refine AddSubgroup.closure_induction
      (p := fun y _ ↦ F y ∈ AddSubgroup.closure (s : Set (n → ℚ)))
      ?_ (by simp) ?_ ?_ hx
    · intro y hy
      simp only [s, Finset.mem_coe, Finset.mem_image] at hy
      obtain ⟨p, -, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      simp only [s, Finset.mem_coe, Finset.mem_image]
      refine ⟨(g * p.1, p.2), Finset.mem_univ _, ?_⟩
      dsimp [F]
      rw [← Matrix.mulVec_mulVec]
    · intro y z hy hz ihy ihz
      simpa only [map_add] using AddSubgroup.add_mem _ ihy ihz
    · intro y hy ihy
      simpa only [map_neg] using AddSubgroup.neg_mem _ ihy

lemma apm_b96a01_part_b_aux_lattice_basis_conjugacy
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) [Finite G]
    (horbit : ∃ s : Finset (n → ℚ),
      (∀ j : n, Pi.single j 1 ∈ AddSubgroup.closure (s : Set (n → ℚ))) ∧
      ∀ g : G, ∀ x ∈ AddSubgroup.closure (s : Set (n → ℚ)),
        (g.1 : Matrix n n ℚ) *ᵥ x ∈ AddSubgroup.closure (s : Set (n → ℚ))) :
    ∃ P : Matrix n n ℚ, IsUnit P ∧
      ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹) := by
  classical
  obtain ⟨s, hstd, hstable⟩ := horbit
  let A : AddSubgroup (n → ℚ) := AddSubgroup.closure (s : Set (n → ℚ))
  obtain ⟨(ι : Type), b, u, hA⟩ := apm_b96a01_part_a (n → ℚ) A s rfl
  let S : Submodule ℚ (n → ℚ) := Submodule.span ℚ (b '' (u : Set ι))
  have hAle : A ≤ S.toAddSubgroup := by
    rw [hA]
    apply (AddSubgroup.closure_le _).2
    intro x hx
    exact Submodule.subset_span hx
  have hS : S = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℚ n).span_eq]
    apply Submodule.span_le.2
    rintro x ⟨j, rfl⟩
    apply hAle
    simpa [Pi.basisFun_apply] using hstd j
  have hu : (u : Set ι) = Set.univ := by
    ext i
    simp only [Set.mem_univ, iff_true]
    have hi : b i ∈ S := by rw [hS]; trivial
    have hsupp := (b.mem_span_image).1 hi
    apply hsupp
    simp
  have hArange : A = AddSubgroup.closure (Set.range b) := by
    rw [hA]
    congr 1
    rw [hu, Set.image_univ]
  have hint : ∀ x ∈ A, ∀ i : ι, ∃ z : ℤ, b.repr x i = z := by
    intro x hx
    rw [hArange] at hx
    refine AddSubgroup.closure_induction
      (p := fun x _ ↦ ∀ i : ι, ∃ z : ℤ, b.repr x i = z) ?_ ?_ ?_ ?_ hx
    · intro x hx i
      obtain ⟨j, rfl⟩ := hx
      by_cases hji : j = i
      · subst j
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hji]⟩
    · intro i
      exact ⟨0, by simp⟩
    · intro x y hx hy ihx ihy i
      obtain ⟨a, ha⟩ := ihx i
      obtain ⟨c, hc⟩ := ihy i
      exact ⟨a + c, by simp [ha, hc]⟩
    · intro x hx ihx i
      obtain ⟨a, ha⟩ := ihx i
      exact ⟨-a, by simp [ha]⟩
  let e : ι ≃ n := b.indexEquiv (Pi.basisFun ℚ n)
  let bn : Module.Basis n ℚ (n → ℚ) := b.reindex e
  let std : Module.Basis n ℚ (n → ℚ) := Pi.basisFun ℚ n
  let P : Matrix n n ℚ := bn.toMatrix std
  have hPinv : P⁻¹ = std.toMatrix bn := by
    letI : Invertible P := Module.Basis.invertibleToMatrix bn std
    apply Matrix.inv_eq_right_inv
    exact Module.Basis.toMatrix_mul_toMatrix_flip bn std
  refine ⟨P, ?_, ?_⟩
  · letI : Invertible P := Module.Basis.invertibleToMatrix bn std
    exact isUnit_of_invertible P
  · intro g i j
    let f : (n → ℚ) →ₗ[ℚ] (n → ℚ) := Matrix.mulVecLin (g.1 : Matrix n n ℚ)
    have hmat : (g.1 : Matrix n n ℚ) = LinearMap.toMatrix std std f := by
      ext a c
      simp [f, std, LinearMap.toMatrix_apply, Matrix.mulVecLin_apply]
    have hconj : P * (g.1 : Matrix n n ℚ) * P⁻¹ =
        LinearMap.toMatrix bn bn f := by
      rw [hmat, hPinv]
      exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        bn std bn std f
    rw [hconj]
    have hbmem : f (bn j) ∈ A := by
      apply hstable g
      change bn j ∈ A
      rw [hArange]
      apply AddSubgroup.subset_closure
      exact ⟨e.symm j, by simp [bn, e]⟩
    obtain ⟨z, hz⟩ := hint (f (bn j)) hbmem (e.symm i)
    refine ⟨z, ?_⟩
    rw [LinearMap.toMatrix_apply]
    simpa [bn, e] using hz

theorem apm_b96a01_part_b :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹) := by
  intro n _ _ G hG
  letI : Finite G := hG
  exact apm_b96a01_part_b_aux_lattice_basis_conjugacy n G
    (apm_b96a01_part_b_aux_finite_orbit n G)

lemma apm_b96a01_part_c_aux_mul_eq_zero
    (p m : ℕ) (hdiv : p ^ (m - 1) ∣ p ^ m) (hm : 2 ≤ m)
    (x y : ZMod (p ^ m))
    (hx : ZMod.castHom hdiv (ZMod (p ^ (m - 1))) x = 0)
    (hy : ZMod.castHom hdiv (ZMod (p ^ (m - 1))) y = 0) :
    x * y = 0 := by
  have key : ∀ z : ZMod (p ^ m), ZMod.castHom hdiv (ZMod (p ^ (m - 1))) z = 0 →
      ((p ^ (m - 1) : ℕ) : ℤ) ∣ (z.cast : ℤ) := by
    intro z hz
    rw [← ZMod.intCast_zmod_cast z, map_intCast] at hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
  obtain ⟨k, hk⟩ := key x hx
  obtain ⟨l, hl⟩ := key y hy
  rw [← ZMod.intCast_zmod_cast x, ← ZMod.intCast_zmod_cast y, hk, hl, ← Int.cast_mul,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpow : ((p : ℤ) ^ m) ∣ (p : ℤ) ^ (m - 1) * (p : ℤ) ^ (m - 1) := by
    rw [← pow_add]; exact pow_dvd_pow _ (by omega)
  push_cast
  exact hpow.trans ⟨k * l, by ring⟩

theorem apm_b96a01_part_c :
    ∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a := by
  intro n _ _ p m hdiv hm a b ha hb
  have ha_map : apmReduction n p m hdiv a = 1 := ha
  have hb_map : apmReduction n p m hdiv b = 1 := hb
  let A : Matrix n n (ZMod (p ^ m)) := (a : Matrix n n (ZMod (p ^ m))) - 1
  let B : Matrix n n (ZMod (p ^ m)) := (b : Matrix n n (ZMod (p ^ m))) - 1
  have hA (i j : n) :
      ZMod.castHom hdiv (ZMod (p ^ (m - 1))) (A i j) = 0 := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup n (ZMod (p ^ (m - 1))) => g i j)
      ha_map
    have h' : ZMod.castHom hdiv (ZMod (p ^ (m - 1)))
        ((a : Matrix n n (ZMod (p ^ m))) i j) =
        (1 : Matrix n n (ZMod (p ^ (m - 1)))) i j := by
      simpa [apmReduction, Matrix.GeneralLinearGroup.map_apply] using h
    change ZMod.castHom hdiv (ZMod (p ^ (m - 1)))
      ((a : Matrix n n (ZMod (p ^ m))) i j -
        (1 : Matrix n n (ZMod (p ^ m))) i j) = 0
    rw [map_sub, h']
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply, if_pos]
      change (1 : ZMod (p ^ (m - 1))) -
        ZMod.castHom hdiv (ZMod (p ^ (m - 1))) (1 : ZMod (p ^ m)) = 0
      rw [map_one]
      simp
    · simp [Matrix.one_apply, hij]
  have hB (i j : n) :
      ZMod.castHom hdiv (ZMod (p ^ (m - 1))) (B i j) = 0 := by
    have h := congrArg (fun g : Matrix.GeneralLinearGroup n (ZMod (p ^ (m - 1))) => g i j)
      hb_map
    have h' : ZMod.castHom hdiv (ZMod (p ^ (m - 1)))
        ((b : Matrix n n (ZMod (p ^ m))) i j) =
        (1 : Matrix n n (ZMod (p ^ (m - 1)))) i j := by
      simpa [apmReduction, Matrix.GeneralLinearGroup.map_apply] using h
    change ZMod.castHom hdiv (ZMod (p ^ (m - 1)))
      ((b : Matrix n n (ZMod (p ^ m))) i j -
        (1 : Matrix n n (ZMod (p ^ m))) i j) = 0
    rw [map_sub, h']
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply, if_pos]
      change (1 : ZMod (p ^ (m - 1))) -
        ZMod.castHom hdiv (ZMod (p ^ (m - 1))) (1 : ZMod (p ^ m)) = 0
      rw [map_one]
      simp
    · simp [Matrix.one_apply, hij]
  have hAB : A * B = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k hk
    exact apm_b96a01_part_c_aux_mul_eq_zero p m hdiv hm (A i k) (B k j) (hA i k) (hB k j)
  have hBA : B * A = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k hk
    exact apm_b96a01_part_c_aux_mul_eq_zero p m hdiv hm (B i k) (A k j) (hB i k) (hA k j)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have ha' : (a : Matrix n n (ZMod (p ^ m))) = 1 + A := by simp [A]
  have hb' : (b : Matrix n n (ZMod (p ^ m))) = 1 + B := by simp [B]
  have hmat : (a : Matrix n n (ZMod (p ^ m))) * b =
      (b : Matrix n n (ZMod (p ^ m))) * a := by
    rw [ha', hb']
    simp only [add_mul, mul_add, one_mul, mul_one, hAB, hBA, add_zero]
    abel
  exact congrFun (congrFun hmat i) j

lemma apm_b96a01_part_d_nonabelian_aux_injective_or_trivial
    {G K : Type*} [Group G] [Group K] [IsSimpleGroup G] (f : G →* K) :
    Function.Injective f ∨ f = 1 := by
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hker | hker
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff f).mp hker)
  · right
    ext x
    have hx : x ∈ f.ker := by rw [hker]; trivial
    simpa using hx

/-- Integral conjugation (part (b)) gives reductions modulo every `p ^ m`, compatible
under `apmReduction`, jointly faithful, and the first one realised over `ZMod p`. -/
lemma apm_b96a01_part_d_nonabelian_aux_reductions_aux_integral_inverse
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) (hG : Finite G) :
    ∃ P : Matrix n n ℚ, IsUnit P ∧
      ∀ g : G,
        apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹) ∧
        apmIntegralMatrix (P * ((g⁻¹).1 : Matrix n n ℚ) * P⁻¹) := by
  obtain ⟨P, hPunit, hP⟩ := apm_b96a01_part_b n G hG
  exact ⟨P, hPunit, fun g => ⟨hP g, hP g⁻¹⟩⟩

/-- A finite subgroup of `GLₙ(ℚ)` embeds into `GLₙ(ℤ)` (conjugate by `P` from part (b);
the integer lifts of `P g P⁻¹` are unique, so they form a homomorphism). -/
lemma apm_b96a01_part_d_nonabelian_aux_reductions_aux_integral_hom
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) (hG : Finite G) :
    ∃ A : G →* Matrix.GeneralLinearGroup n ℤ, Function.Injective A := by
  sorry

/-- Reductions of an integral representation modulo the powers of `p`. -/
lemma apm_b96a01_part_d_nonabelian_aux_reductions_aux_of_integral
    (n : Type*) [Fintype n] [DecidableEq n] {G : Type*} [Group G]
    (A : G →* Matrix.GeneralLinearGroup n ℤ) (hA : Function.Injective A)
    (p : ℕ) (hp : p.Prime) :
    ∃ ρ : ∀ m : ℕ, G →* Matrix.GeneralLinearGroup n (ZMod (p ^ m)),
      (∀ m (h : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
        (apmReduction n p m h).comp (ρ m) = ρ (m - 1)) ∧
      (∀ g : G, (∀ m, 1 ≤ m → ρ m g = 1) → g = 1) ∧
      ∃ ρp : G →* Matrix.GeneralLinearGroup n (ZMod p), ∀ g, ρp g = 1 ↔ ρ 1 g = 1 := by
  sorry

lemma apm_b96a01_part_d_nonabelian_aux_reductions
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) (hG : Finite G) (p : ℕ) (hp : p.Prime) :
    ∃ ρ : ∀ m : ℕ, G →* Matrix.GeneralLinearGroup n (ZMod (p ^ m)),
      (∀ m (h : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
        (apmReduction n p m h).comp (ρ m) = ρ (m - 1)) ∧
      (∀ g : G, (∀ m, 1 ≤ m → ρ m g = 1) → g = 1) ∧
      ∃ ρp : G →* Matrix.GeneralLinearGroup n (ZMod p), ∀ g, ρp g = 1 ↔ ρ 1 g = 1 := by
  obtain ⟨A, hA⟩ := apm_b96a01_part_d_nonabelian_aux_reductions_aux_integral_hom n G hG
  exact apm_b96a01_part_d_nonabelian_aux_reductions_aux_of_integral n A hA p hp

/-- The congruence climb: if the reduction modulo `p` is trivial on a nonabelian simple
group, so is every reduction modulo `p ^ m` (each step lands in the commutative kernel of
part (c)). -/
lemma apm_b96a01_part_d_nonabelian_aux_climb
    {G : Type*} [Group G] [IsSimpleGroup G] (hnc : ¬ ∀ a b : G, a * b = b * a)
    (n : Type*) [Fintype n] [DecidableEq n] (p : ℕ)
    (ρ : ∀ m : ℕ, G →* Matrix.GeneralLinearGroup n (ZMod (p ^ m)))
    (hcompat : ∀ m (h : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      (apmReduction n p m h).comp (ρ m) = ρ (m - 1))
    (h1 : ρ 1 = 1) :
    ∀ m, 1 ≤ m → ρ m = 1 := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simpa using h1
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        have hprev : ρ m = 1 := ih hm1
        have hdiv : p ^ ((m + 1) - 1) ∣ p ^ (m + 1) := by
          simp only [Nat.add_sub_cancel]
          exact pow_dvd_pow p (Nat.le_succ m)
        have hm2 : 2 ≤ m + 1 := by omega
        have hc := hcompat (m + 1) hdiv hm2
        have hker (g : G) : ρ (m + 1) g ∈
            (apmReduction n p (m + 1) hdiv).ker := by
          change apmReduction n p (m + 1) hdiv (ρ (m + 1) g) = 1
          have hg := DFunLike.congr_fun hc g
          simp only [MonoidHom.comp_apply] at hg
          rw [hg, Nat.add_sub_cancel, hprev]
          rfl
        rcases apm_b96a01_part_d_nonabelian_aux_injective_or_trivial (ρ (m + 1)) with hinj | htriv
        · exfalso
          apply hnc
          intro a b
          apply hinj
          simpa using apm_b96a01_part_c n p (m + 1) hdiv hm2
            (ρ (m + 1) a) (ρ (m + 1) b) (hker a) (hker b)
        · exact htriv

theorem apm_b96a01_part_d_nonabelian :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → ¬(∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  intro n _ _ G hG hs hnc p hp
  obtain ⟨ρ, hcompat, hsep, ρp, hρp⟩ := apm_b96a01_part_d_nonabelian_aux_reductions n G hG p hp
  rcases apm_b96a01_part_d_nonabelian_aux_injective_or_trivial ρp with hinj | htriv
  · exact ⟨ρp, hinj⟩
  · exfalso
    have h1 : ρ 1 = 1 := by
      ext1 g
      exact (hρp g).1 (by rw [htriv]; rfl)
    have hall := apm_b96a01_part_d_nonabelian_aux_climb hnc n p ρ hcompat h1
    apply hnc
    intro a b
    have ha : a = 1 := hsep a (fun m hm => by rw [hall m hm]; rfl)
    have hb : b = 1 := hsep b (fun m hm => by rw [hall m hm]; rfl)
    rw [ha, hb]

/-- A finite commutative simple group has prime order. -/
lemma apm_b96a01_part_d_abelian_aux_representation_aux_prime_card
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (hcomm : ∀ a b : G, a * b = b * a) :
    (Nat.card G).Prime := by
  sorry

/-- An element of prime order `ℓ` in `GLₙ(ℚ)` forces `ℓ - 1 ≤ n`: its minimal polynomial
divides `X^ℓ - 1 = (X - 1) Φ_ℓ`, is not `X - 1`, and `Φ_ℓ` is irreducible over `ℚ` of degree
`ℓ - 1`. -/
lemma apm_b96a01_part_d_abelian_aux_representation_aux_dim_bound
    (n : Type*) [Fintype n] [DecidableEq n] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (g : Matrix.GeneralLinearGroup n ℚ) (hg : orderOf g = ℓ) :
    ℓ - 1 ≤ Fintype.card n := by
  sorry

/-- `GLₙ(F_p)` has an element of every prime order `ℓ` with `ℓ - 1 ≤ n`, except
`n = 1, p = 2` (a unipotent Jordan block if `ℓ = p`, a companion matrix of a factor of
`Φ_ℓ` over `F_p` padded by the identity otherwise). -/
lemma apm_b96a01_part_d_abelian_aux_representation_aux_element
    (n : Type*) [Fintype n] [DecidableEq n] (p : ℕ) (hp : p.Prime)
    (hex : ¬(Fintype.card n = 1 ∧ p = 2)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hdim : ℓ - 1 ≤ Fintype.card n) :
    ∃ x : Matrix.GeneralLinearGroup n (ZMod p), orderOf x = ℓ := by
  sorry

/-- A group of prime order embeds wherever there is an element of that order. -/
lemma apm_b96a01_part_d_abelian_aux_representation_aux_embed
    {G H : Type*} [Group G] [Group H] [Finite G] (hG : (Nat.card G).Prime)
    (x : H) (hx : orderOf x = Nat.card G) :
    ∃ ρ : G →* H, Function.Injective ρ := by
  sorry

lemma apm_b96a01_part_d_abelian_aux_representation
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ))
    (hG : Finite G) (hs : IsSimpleGroup G)
    (hcomm : ∀ a b : G, a * b = b * a)
    (p : ℕ) (hp : p.Prime)
    (hex : ¬(Fintype.card n = 1 ∧ p = 2)) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
      Function.Injective ρ := by
  letI : Finite G := hG
  have hℓ := apm_b96a01_part_d_abelian_aux_representation_aux_prime_card hcomm
  haveI : Fact (Nat.card G).Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) (Nat.card G) dvd_rfl
  have hg' : orderOf (g : Matrix.GeneralLinearGroup n ℚ) = Nat.card G := by
    rw [Subgroup.orderOf_coe, hg]
  have hdim := apm_b96a01_part_d_abelian_aux_representation_aux_dim_bound n (Nat.card G) hℓ _ hg'
  obtain ⟨x, hx⟩ := apm_b96a01_part_d_abelian_aux_representation_aux_element n p hp hex (Nat.card G) hℓ hdim
  exact apm_b96a01_part_d_abelian_aux_representation_aux_embed hℓ x hx

theorem apm_b96a01_part_d_abelian :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → (∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  intro n _ _ G hG hs hcomm p hp hex
  exact apm_b96a01_part_d_abelian_aux_representation n G hG hs hcomm p hp hex

theorem apm_b96a01_part_d :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  intro n _ _ G hG hs p hp hex
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · exact apm_b96a01_part_d_abelian n G hG hs hcomm p hp hex
  · exact apm_b96a01_part_d_nonabelian n G hG hs hcomm p hp

theorem apm_b96a01 :
    (∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V) (u : Finset ι),
          A = AddSubgroup.closure (b '' (u : Set ι))) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹)) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ) := by
  exact ⟨apm_b96a01_part_a, apm_b96a01_part_b,
    apm_b96a01_part_c, apm_b96a01_part_d⟩

#print axioms apm_b96a01

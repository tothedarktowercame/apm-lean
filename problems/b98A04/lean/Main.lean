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

/-- Package the concrete, fixed-length presentation used in the problem as
Mathlib's lattice-theoretic `CompositionSeries`.  Keeping the pointwise
identification in the result avoids later casts when reading off factors. -/
lemma apm_b98a04_compositionSeries_of_chain
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) :
    ∃ c : CompositionSeries (Submodule R M),
      c.length = t ∧ c.head = N 0 ∧ c.last = N (Fin.last t) := by
  let c : CompositionSeries (Submodule R M) :=
    { length := t
      toFun := N
      step := fun i ↦
        (covBy_iff_quot_is_simple
          (le_of_lt (hmono i.castSucc_lt_succ))).2 (hsimple i) }
  exact ⟨c, rfl, rfl, rfl⟩

/-- The concrete composition chain in the statement supplies both chain
conditions needed by the finite-length API. -/
lemma apm_b98a04_isFiniteLength_of_chain
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) :
    IsFiniteLength R M := by
  apply isFiniteLength_of_exists_compositionSeries
  obtain ⟨c, _, hc_head, hc_last⟩ :=
    apm_b98a04_compositionSeries_of_chain R M t N hmono hsimple
  exact ⟨c, hc_head.trans hbot, hc_last.trans htop⟩

/-- In a bidirectionally well-founded Jordan--Hölder lattice, every cover
occurs (up to the lattice's factor isomorphism) in every full composition
series.  This is the abstract factor-occurrence step needed below. -/
lemma apm_b98a04_covBy_occurs
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [WellFoundedLT (Submodule R M)] [WellFoundedGT (Submodule R M)]
    (c : CompositionSeries (Submodule R M))
    (hc_head : c.head = ⊥) (hc_last : c.last = ⊤)
    {A B : Submodule R M} (hAB : A ⋖ B) :
    ∃ i : Fin c.length,
      JordanHolderLattice.Iso (A, B) (c i.castSucc, c i.succ) := by
  let s : LTSeries (Submodule R M) :=
    { length := 1
      toFun := ![A, B]
      step := fun i ↦ by fin_cases i; simpa using hAB.lt }
  obtain ⟨d, e, he, hd_head, hd_last⟩ :=
    s.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  let d' : CompositionSeries (Submodule R M) := d
  have hdA : d (e 0) = A := by
    simpa [s] using congrFun he 0
  have hdB : d (e (Fin.last 1)) = B := by
    simpa [s] using congrFun he (Fin.last 1)
  have he_lt : e 0 < e (Fin.last 1) := by
    rw [← d'.strictMono.lt_iff_lt, hdA, hdB]
    exact hAB.lt
  have he_succ : (e (Fin.last 1)).val = (e 0).val + 1 := by
    by_contra hne
    have hgap : (e 0).val + 1 < (e (Fin.last 1)).val := by omega
    let k : Fin (d.length + 1) :=
      ⟨(e 0).val + 1, lt_trans hgap (e (Fin.last 1)).isLt⟩
    have hek : e 0 < k := Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
    have hke : k < e (Fin.last 1) := Fin.mk_lt_mk.mpr hgap
    have hAk : A ≤ d k := by
      rw [← hdA]
      exact d'.strictMono.monotone hek.le
    have hkB : d k ≤ B := by
      rw [← hdB]
      exact d'.strictMono.monotone hke.le
    rcases hAB.eq_or_eq hAk hkB with hk | hk
    · exact (ne_of_lt (d'.strictMono hek)) (hdA.trans hk.symm)
    · exact (ne_of_lt (d'.strictMono hke)) (hk.trans hdB.symm)
  let j : Fin d.length := ⟨(e 0).val, by omega⟩
  have hj0 : j.castSucc = e 0 := by ext; rfl
  have hj1 : j.succ = e (Fin.last 1) := by ext; simpa [j] using he_succ.symm
  have hdc := d'.jordan_holder c (hd_head.trans hc_head.symm)
    (hd_last.trans hc_last.symm)
  refine ⟨hdc.choose j, ?_⟩
  have hjiso := hdc.choose_spec j
  rw [hj0, hj1, hdA, hdB] at hjiso
  exact hjiso

/-- A simple quotient of a submodule contributes a factor to every full
composition series of the ambient finite-length module. -/
lemma apm_b98a04_simple_subquotient_occurs
    (R P V : Type*) [Ring R] [AddCommGroup P] [Module R P]
    [AddCommGroup V] [Module R V] [IsSimpleModule R V]
    [IsNoetherian R P] [IsArtinian R P]
    (S : Submodule R P) (g : S →ₗ[R] V) (hg : Function.Surjective g)
    (c : CompositionSeries (Submodule R P))
    (hc_head : c.head = ⊥) (hc_last : c.last = ⊤) :
    ∃ i : Fin c.length,
      Nonempty (V ≃ₗ[R]
        (c i.succ ⧸ Submodule.comap (c i.succ).subtype (c i.castSucc))) := by
  let K : Submodule R P := Submodule.map S.subtype (LinearMap.ker g)
  have hker : LinearMap.ker g ⋖ (⊤ : Submodule R S) :=
    covBy_top_iff.mpr (LinearMap.isCoatom_ker_of_surjective hg)
  have hKS : K ⋖ S := by
    simpa [K] using
      Submodule.map_covBy_of_injective (Submodule.injective_subtype S) hker
  obtain ⟨i, hi⟩ :=
    apm_b98a04_covBy_occurs R P c hc_head hc_last hKS
  refine ⟨i, ?_⟩
  rcases hi with ⟨hi⟩
  have hcomap : Submodule.comap S.subtype K = LinearMap.ker g := by
    simp [K, Submodule.comap_map_eq_self]
  rw [hcomap] at hi
  exact ⟨(LinearMap.quotKerEquivOfSurjective g hg).symm.trans hi⟩

/-- If a map to a simple quotient vanishes on the kernel of a projection,
it descends surjectively to the projection's range.  This is the factoring
half of the coordinate induction for finite powers. -/
lemma apm_b98a04_surjection_descends_to_range
    (R A B V : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup V] [Module R V]
    (f : A →ₗ[R] B) (g : A →ₗ[R] V) (hg : Function.Surjective g)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ h : LinearMap.range f →ₗ[R] V, Function.Surjective h := by
  let q : (A ⧸ LinearMap.ker f) →ₗ[R] V :=
    (LinearMap.ker f).liftQ g hker
  let e : (A ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
    LinearMap.quotKerEquivRange f
  let h : LinearMap.range f →ₗ[R] V := q.comp e.symm.toLinearMap
  refine ⟨h, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hg y
  refine ⟨e (Submodule.Quotient.mk x), ?_⟩
  simp [h, q, e, Submodule.liftQ_apply]

/-- A surjection onto a simple module either stays surjective on the kernel
of a chosen projection, or descends surjectively to the projection range. -/
lemma apm_b98a04_surjection_kernel_or_range
    (R A B V : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup V] [Module R V] [IsSimpleModule R V]
    (f : A →ₗ[R] B) (g : A →ₗ[R] V) (hg : Function.Surjective g) :
    (∃ h : LinearMap.ker f →ₗ[R] V, Function.Surjective h) ∨
      (∃ h : LinearMap.range f →ₗ[R] V, Function.Surjective h) := by
  by_cases hker : LinearMap.ker f ≤ LinearMap.ker g
  · exact Or.inr
      (apm_b98a04_surjection_descends_to_range R A B V f g hg hker)
  · let h : LinearMap.ker f →ₗ[R] V := g.domRestrict (LinearMap.ker f)
    have hn : h ≠ 0 := by
      intro hz
      apply hker
      intro x hx
      have hx0 : h ⟨x, hx⟩ = 0 := by rw [hz]; rfl
      simpa [h, LinearMap.mem_ker] using hx0
    exact Or.inl ⟨h, LinearMap.surjective_of_ne_zero hn⟩

/-- Every simple subquotient of a finite power of `M` is already a simple
subquotient of `M`. -/
lemma apm_b98a04_simple_subquotient_fin
    (R M V : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [IsSimpleModule R V] :
    ∀ (s : ℕ) (S : Submodule R (Fin s → M))
      (g : S →ₗ[R] V), Function.Surjective g →
      ∃ (T : Submodule R M) (h : T →ₗ[R] V), Function.Surjective h := by
  intro s
  induction s with
  | zero =>
      intro S g hg
      exfalso
      letI : Nontrivial V := IsSimpleModule.nontrivial R V
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      obtain ⟨x, hx⟩ := hg v
      have hx0 : x = 0 := by
        apply Subtype.ext
        funext i
        exact Fin.elim0 i
      exact hv (by simpa [hx0] using hx.symm)
  | succ n ih =>
      intro S g hg
      let p : S →ₗ[R] M :=
        { toFun := fun x ↦ x.1 0
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      rcases apm_b98a04_surjection_kernel_or_range R S M V p g hg with
        hkernel | hrange
      · obtain ⟨h, hh⟩ := hkernel
        let q : LinearMap.ker p →ₗ[R] (Fin n → M) :=
          { toFun := fun x i ↦ x.1.1 i.succ
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
        have hq : Function.Injective q := by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ (fun j ↦ congrFun hxy j) i
          have hx0 : x.1.1 0 = 0 := x.2
          have hy0 : y.1.1 0 = 0 := y.2
          exact hx0.trans hy0.symm
        let e : LinearMap.ker p ≃ₗ[R] LinearMap.range q :=
          LinearEquiv.ofInjective q hq
        let h' : LinearMap.range q →ₗ[R] V := h.comp e.symm.toLinearMap
        have hh' : Function.Surjective h' := by
          intro v
          obtain ⟨x, rfl⟩ := hh v
          exact ⟨e x, by simp [h', e]⟩
        exact ih (LinearMap.range q) h' hh'
      · obtain ⟨h, hh⟩ := hrange
        exact ⟨LinearMap.range p, h, hh⟩

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
  intro t N hbot htop hmono hsimple V _ _ _
  let c : CompositionSeries (Submodule R M) :=
    { length := t
      toFun := N
      step := fun i ↦
        (covBy_iff_quot_is_simple
          (le_of_lt (hmono i.castSucc_lt_succ))).2 (hsimple i) }
  have hc_ends : c.head = ⊥ ∧ c.last = ⊤ := by
    exact ⟨hbot, htop⟩
  have hMfinite : IsFiniteLength R M :=
    apm_b98a04_isFiniteLength_of_chain R M t N hbot htop hmono hsimple
  obtain ⟨hMnoetherian, hMartinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hMfinite
  letI : IsNoetherian R M := hMnoetherian
  letI : IsArtinian R M := hMartinian
  obtain ⟨s, m, hm⟩ := htuple
  let f := apm_b98a04_actionMap R M s m
  have hf : Function.Injective f :=
    apm_b98a04_actionMap_injective R M s m hm
  obtain ⟨S, g, hg⟩ :=
    apm_b98a04_simple_quotient_of_embedded_regular R M V s f hf
  have hpowfinite : IsFiniteLength R (Fin s → M) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hSfinite : IsFiniteLength R S :=
    hpowfinite.of_injective (Submodule.injective_subtype S)
  have hVfinite : IsFiniteLength R V := hSfinite.of_surjective hg
  obtain ⟨cpow, hcpow_head, hcpow_last⟩ :=
    isFiniteLength_iff_exists_compositionSeries.mp hpowfinite
  obtain ⟨ipow, hVipow⟩ :=
    apm_b98a04_simple_subquotient_occurs R (Fin s → M) V S g hg
      cpow hcpow_head hcpow_last
  obtain ⟨T, h, hh⟩ :=
    apm_b98a04_simple_subquotient_fin R M V s S g hg
  obtain ⟨i, hi⟩ :=
    apm_b98a04_simple_subquotient_occurs R M V T h hh c hc_ends.1 hc_ends.2
  exact ⟨i, by simpa [c] using hi⟩

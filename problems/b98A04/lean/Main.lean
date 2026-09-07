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

/-- Package the finite chain appearing in the frozen statement as Mathlib's
`CompositionSeries`.  Keeping the original indexing makes its factors
definitionally the quotient types in the conclusion. -/
def apm_b98a04_compositionSeriesOfChain
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) :
    CompositionSeries (Submodule R M) where
  length := t
  toFun := N
  step i := by
    apply (covBy_iff_quot_is_simple
      (show N i.castSucc ≤ N i.succ from hmono.monotone (Fin.castSucc_le_succ i))).2
    exact hsimple i

@[simp] lemma apm_b98a04_compositionSeriesOfChain_apply
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))
    (i : Fin (t + 1)) :
    apm_b98a04_compositionSeriesOfChain R M t N hmono hsimple i = N i := rfl

lemma apm_b98a04_isFiniteLength_of_supplied_chain
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) :
    IsFiniteLength R M := by
  apply isFiniteLength_of_exists_compositionSeries
  refine ⟨apm_b98a04_compositionSeriesOfChain R M t N hmono hsimple, ?_, ?_⟩
  · exact hbot
  · exact htop

lemma apm_b98a04_finiteLength_power_and_submodule
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))
    (s : ℕ) (S : Submodule R (Fin s → M)) :
    IsFiniteLength R S := by
  have hM :=
    apm_b98a04_isFiniteLength_of_supplied_chain R M t N hbot htop hmono hsimple
  have hM' := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  letI : IsNoetherian R M := hM'.1
  letI : IsArtinian R M := hM'.2
  have hpower : IsFiniteLength R (Fin s → M) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hpower.of_injective (Submodule.injective_subtype S)

/-- A surjection onto the target simple module presents it as the quotient by
its kernel, in the precise form needed when inserting that factor into a
composition series of the source submodule. -/
noncomputable def apm_b98a04_quotientKerEquivOfSurjective
    (R S V : Type*) [Ring R] [AddCommGroup S] [Module R S]
    [AddCommGroup V] [Module R V]
    (g : S →ₗ[R] V) (hg : Function.Surjective g) :
    (S ⧸ LinearMap.ker g) ≃ₗ[R] V :=
  (LinearMap.quotKerEquivRange g).trans
    ((LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.mpr hg)).trans
      Submodule.topEquiv)

lemma apm_b98a04_factors_transport_to_supplied_chain
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))
    (C : CompositionSeries (Submodule R M))
    (Cbot : C.head = ⊥) (Ctop : C.last = ⊤) :
    ∃ e : Fin C.length ≃ Fin t, ∀ j : Fin C.length,
      Nonempty
        ((C j.succ ⧸ Submodule.comap (C j.succ).subtype (C j.castSucc)) ≃ₗ[R]
          (N (e j).succ ⧸
            Submodule.comap (N (e j).succ).subtype (N (e j).castSucc))) := by
  let D := apm_b98a04_compositionSeriesOfChain R M t N hmono hsimple
  have hCD : CompositionSeries.Equivalent C D :=
    C.jordan_holder D (Cbot.trans hbot.symm) (Ctop.trans htop.symm)
  exact ⟨hCD.choose, hCD.choose_spec⟩

/-- Splice composition series across a short exact sequence.  Unlike the
length-only use of this construction in Mathlib, we retain the series itself
so a distinguished simple factor can subsequently be tracked through it. -/
noncomputable def apm_b98a04_compositionSeriesOfExact
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤) :
    CompositionSeries (Submodule R B) := by
  let left : CompositionSeries (Submodule R B) :=
    SA.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
  let right : CompositionSeries (Submodule R B) :=
    SC.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
  have hjoin : left.last = right.head := by
    change Submodule.map f SA.last = Submodule.comap g SC.head
    rw [SAtop, SCbot, Submodule.map_top, Submodule.comap_bot,
      LinearMap.exact_iff.mp hexact]
  exact left.smash right hjoin

@[simp] lemma apm_b98a04_compositionSeriesOfExact_head
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤) :
    (apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop).head = ⊥ := by
  simp only [apm_b98a04_compositionSeriesOfExact, RelSeries.head_smash,
    RelSeries.head_map]
  change Submodule.map f SA.head = ⊥
  rw [SAbot, Submodule.map_bot]

@[simp] lemma apm_b98a04_compositionSeriesOfExact_last
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤) :
    (apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop).last = ⊤ := by
  simp only [apm_b98a04_compositionSeriesOfExact, RelSeries.last_smash,
    RelSeries.last_map]
  change Submodule.comap g SC.last = ⊤
  rw [SCtop, Submodule.comap_top]

/-- The canonical one-step composition series of a simple module. -/
def apm_b98a04_simpleCompositionSeries
    (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]
    [IsSimpleModule R V] : CompositionSeries (Submodule R V) where
  length := 1
  toFun := Fin.cases ⊥ (fun _ ↦ ⊤)
  step i := by
    fin_cases i
    exact bot_covBy_top

@[simp] lemma apm_b98a04_simpleCompositionSeries_head
    (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]
    [IsSimpleModule R V] :
    (apm_b98a04_simpleCompositionSeries R V).head = ⊥ := rfl

@[simp] lemma apm_b98a04_simpleCompositionSeries_last
    (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]
    [IsSimpleModule R V] :
    (apm_b98a04_simpleCompositionSeries R V).last = ⊤ := rfl

noncomputable def apm_b98a04_topSubtypeQuotientEquiv
    (R B : Type*) [Ring R] [AddCommGroup B] [Module R B]
    (K : Submodule R B) :
    ((⊤ : Submodule R B) ⧸ Submodule.comap (⊤ : Submodule R B).subtype K) ≃ₗ[R]
      (B ⧸ K) :=
  Submodule.Quotient.equiv _ K Submodule.topEquiv (by
    ext x
    simp)

noncomputable def apm_b98a04_comapTopBotQuotientEquiv
    (R B C : Type*) [Ring R] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (g : B →ₗ[R] C) (hg : Function.Surjective g) :
    ((Submodule.comap g ⊤) ⧸
      Submodule.comap (Submodule.comap g ⊤).subtype (Submodule.comap g ⊥)) ≃ₗ[R] C := by
  rw [Submodule.comap_top, Submodule.comap_bot]
  exact (apm_b98a04_topSubtypeQuotientEquiv R B (LinearMap.ker g)).trans
    (g.quotKerEquivOfSurjective hg)

lemma apm_b98a04_compositionSeriesOfExact_right_castSucc
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤)
    (j : Fin SC.length) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    E (j.natAdd SA.length).castSucc = Submodule.comap g (SC j.castSucc) := by
  dsimp only
  unfold apm_b98a04_compositionSeriesOfExact
  apply RelSeries.smash_natAdd

lemma apm_b98a04_compositionSeriesOfExact_left_castSucc
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤)
    (j : Fin SA.length) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    E (j.castAdd SC.length).castSucc = Submodule.map f (SA j.castSucc) := by
  dsimp only
  unfold apm_b98a04_compositionSeriesOfExact
  apply RelSeries.smash_castAdd

lemma apm_b98a04_compositionSeriesOfExact_left_succ
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤)
    (j : Fin SA.length) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    E (j.castAdd SC.length).succ = Submodule.map f (SA j.succ) := by
  dsimp only
  unfold apm_b98a04_compositionSeriesOfExact
  apply RelSeries.smash_succ_castAdd

lemma apm_b98a04_compositionSeriesOfExact_right_succ
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤)
    (j : Fin SC.length) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    E (j.natAdd SA.length).succ = Submodule.comap g (SC j.succ) := by
  dsimp only
  unfold apm_b98a04_compositionSeriesOfExact
  apply RelSeries.smash_succ_natAdd

lemma apm_b98a04_exactSeries_contains_simple_quotient
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [IsSimpleModule R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA (apm_b98a04_simpleCompositionSeries R C) SAbot SAtop rfl rfl
    ∃ i : Fin E.length,
      Nonempty
        ((E i.succ ⧸ Submodule.comap (E i.succ).subtype (E i.castSucc)) ≃ₗ[R] C) := by
  dsimp only
  let SC := apm_b98a04_simpleCompositionSeries R C
  let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
    SA SC SAbot SAtop rfl rfl
  let j : Fin SC.length := ⟨0, by change 0 < 1; omega⟩
  let i : Fin E.length := j.natAdd SA.length
  refine ⟨i, ⟨?_⟩⟩
  have hi0 : E i.castSucc = Submodule.comap g ⊥ := by
    simpa [E, i, SC] using
      apm_b98a04_compositionSeriesOfExact_right_castSucc R A B C f g hf hg hexact
        SA SC SAbot SAtop rfl rfl j
  have hi1 : E i.succ = Submodule.comap g ⊤ := by
    simpa [E, i, SC] using
      apm_b98a04_compositionSeriesOfExact_right_succ R A B C f g hf hg hexact
        SA SC SAbot SAtop rfl rfl j
  rw [hi0, hi1]
  exact apm_b98a04_comapTopBotQuotientEquiv R B C g hg

/-- Mapping two nested submodules along an injection preserves their quotient
factor.  This is the factor-level companion to
`Submodule.map_covBy_of_injective`. -/
noncomputable def apm_b98a04_quotientMapEquivOfInjective
    (R A B : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective f)
    (A₀ A₁ : Submodule R A) :
    (A₁ ⧸ Submodule.comap A₁.subtype A₀) ≃ₗ[R]
      ((Submodule.map f A₁) ⧸
        Submodule.comap (Submodule.map f A₁).subtype (Submodule.map f A₀)) := by
  let e : A₁ ≃ₗ[R] Submodule.map f A₁ := A₁.equivMapOfInjective f hf
  apply Submodule.Quotient.equiv _ _ e
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change f y.1 ∈ Submodule.map f A₀
    exact ⟨y.1, hy, rfl⟩
  · intro hx
    change x.1 ∈ Submodule.map f A₀ at hx
    rcases hx with ⟨y, hy, heq⟩
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change (e.symm x).1 ∈ A₀
    have hecoe : f (e.symm x).1 = x.1 :=
      Submodule.map_equivMapOfInjective_symm_apply f hf A₁ x
    have hey : (e.symm x).1 = y := hf (hecoe.trans heq.symm)
    exact hey.symm ▸ hy

noncomputable def apm_b98a04_compositionSeriesOfExact_leftFactorEquiv
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤)
    (j : Fin SA.length) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    (SA j.succ ⧸ Submodule.comap (SA j.succ).subtype (SA j.castSucc)) ≃ₗ[R]
      (E (j.castAdd SC.length).succ ⧸
        Submodule.comap (E (j.castAdd SC.length).succ).subtype
          (E (j.castAdd SC.length).castSucc)) := by
  dsimp only
  rw [apm_b98a04_compositionSeriesOfExact_left_castSucc R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop j,
    apm_b98a04_compositionSeriesOfExact_left_succ R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop j]
  exact apm_b98a04_quotientMapEquivOfInjective R A B f hf
    (SA j.castSucc) (SA j.succ)

noncomputable def apm_b98a04_quotientComapEquivOfSurjective
    (R B C : Type*) [Ring R]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (g : B →ₗ[R] C) (hg : Function.Surjective g)
    (C₀ C₁ : Submodule R C) :
    ((Submodule.comap g C₁) ⧸
      Submodule.comap (Submodule.comap g C₁).subtype (Submodule.comap g C₀)) ≃ₗ[R]
      (C₁ ⧸ Submodule.comap C₁.subtype C₀) := by
  let r : Submodule.comap g C₁ →ₗ[R] C₁ :=
    ((g.domRestrict (Submodule.comap g C₁)).codRestrict C₁ (fun x ↦ x.2))
  let q : Submodule.comap g C₁ →ₗ[R]
      (C₁ ⧸ Submodule.comap C₁.subtype C₀) :=
    (Submodule.comap C₁.subtype C₀).mkQ.comp r
  have hq : Function.Surjective q := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro y
    obtain ⟨x, hx⟩ := hg y.1
    let x' : Submodule.comap g C₁ := ⟨x, by
      change g x ∈ C₁
      rw [hx]
      exact y.2⟩
    refine ⟨x', ?_⟩
    change Submodule.Quotient.mk (r x') = Submodule.Quotient.mk y
    congr 1
    exact Subtype.ext hx
  have hker : LinearMap.ker q =
      Submodule.comap (Submodule.comap g C₁).subtype (Submodule.comap g C₀) := by
    ext x
    change q x = 0 ↔ g x.1 ∈ C₀
    simp [q, r]
  rw [← hker]
  exact q.quotKerEquivOfSurjective hq

noncomputable def apm_b98a04_compositionSeriesOfExact_rightFactorEquiv
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤)
    (j : Fin SC.length) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    (E (j.natAdd SA.length).succ ⧸
      Submodule.comap (E (j.natAdd SA.length).succ).subtype
        (E (j.natAdd SA.length).castSucc)) ≃ₗ[R]
      (SC j.succ ⧸ Submodule.comap (SC j.succ).subtype (SC j.castSucc)) := by
  dsimp only
  rw [apm_b98a04_compositionSeriesOfExact_right_castSucc R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop j,
    apm_b98a04_compositionSeriesOfExact_right_succ R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop j]
  exact apm_b98a04_quotientComapEquivOfSurjective R B C g hg
    (SC j.castSucc) (SC j.succ)

lemma apm_b98a04_compositionSeriesOfExact_factor_cases
    (R A B C : Type*) [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : Function.Exact f g)
    (SA : CompositionSeries (Submodule R A))
    (SC : CompositionSeries (Submodule R C))
    (SAbot : SA.head = ⊥) (SAtop : SA.last = ⊤)
    (SCbot : SC.head = ⊥) (SCtop : SC.last = ⊤) :
    let E := apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
      SA SC SAbot SAtop SCbot SCtop
    ∀ k : Fin E.length,
      (∃ i : Fin SA.length, Nonempty
        ((E k.succ ⧸ Submodule.comap (E k.succ).subtype (E k.castSucc)) ≃ₗ[R]
          (SA i.succ ⧸ Submodule.comap (SA i.succ).subtype (SA i.castSucc)))) ∨
      (∃ i : Fin SC.length, Nonempty
        ((E k.succ ⧸ Submodule.comap (E k.succ).subtype (E k.castSucc)) ≃ₗ[R]
          (SC i.succ ⧸ Submodule.comap (SC i.succ).subtype (SC i.castSucc)))) := by
  dsimp only
  change ∀ k : Fin (SA.length + SC.length),
    (∃ i : Fin SA.length, Nonempty
      (((apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
          SA SC SAbot SAtop SCbot SCtop) k.succ ⧸
        Submodule.comap
          ((apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
            SA SC SAbot SAtop SCbot SCtop) k.succ).subtype
          ((apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
            SA SC SAbot SAtop SCbot SCtop) k.castSucc)) ≃ₗ[R]
        (SA i.succ ⧸ Submodule.comap (SA i.succ).subtype (SA i.castSucc)))) ∨
    (∃ i : Fin SC.length, Nonempty
      (((apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
          SA SC SAbot SAtop SCbot SCtop) k.succ ⧸
        Submodule.comap
          ((apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
            SA SC SAbot SAtop SCbot SCtop) k.succ).subtype
          ((apm_b98a04_compositionSeriesOfExact R A B C f g hf hg hexact
            SA SC SAbot SAtop SCbot SCtop) k.castSucc)) ≃ₗ[R]
        (SC i.succ ⧸ Submodule.comap (SC i.succ).subtype (SC i.castSucc))))
  intro k
  refine Fin.addCases (m := SA.length) (n := SC.length) ?_ ?_ k
  · intro i
    left
    refine ⟨i, ⟨?_⟩⟩
    exact (apm_b98a04_compositionSeriesOfExact_leftFactorEquiv R A B C
      f g hf hg hexact SA SC SAbot SAtop SCbot SCtop i).symm
  · intro i
    right
    refine ⟨i, ⟨?_⟩⟩
    exact apm_b98a04_compositionSeriesOfExact_rightFactorEquiv R A B C
      f g hf hg hexact SA SC SAbot SAtop SCbot SCtop i

def apm_b98a04_finTailInclusion
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (n : ℕ) :
    (Fin n → M) →ₗ[R] (Fin (n + 1) → M) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    ext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i
  map_smul' r x := by
    ext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i

def apm_b98a04_finHead
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (n : ℕ) :
    (Fin (n + 1) → M) →ₗ[R] M where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma apm_b98a04_finTailInclusion_injective
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Injective (apm_b98a04_finTailInclusion R M n) := by
  intro x y h
  ext i
  exact congrFun h i.succ

lemma apm_b98a04_finHead_surjective
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Surjective (apm_b98a04_finHead R M n) := by
  intro x
  exact ⟨Fin.cons x 0, rfl⟩

lemma apm_b98a04_finTail_head_exact
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (n : ℕ) :
    Function.Exact (apm_b98a04_finTailInclusion R M n)
      (apm_b98a04_finHead R M n) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change (apm_b98a04_finHead R M n) x = 0 at hx
    refine ⟨fun i ↦ x i.succ, ?_⟩
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hx.symm
    · rfl
  · rintro ⟨y, hy⟩
    change (apm_b98a04_finHead R M n) x = 0
    rw [← hy]
    rfl

noncomputable def apm_b98a04_powerCompositionSeriesData
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))
    (s : ℕ) :
    { C : CompositionSeries (Submodule R (Fin s → M)) //
      C.head = ⊥ ∧ C.last = ⊤ } := by
  induction s with
  | zero =>
      let C : CompositionSeries (Submodule R (Fin 0 → M)) :=
        RelSeries.singleton _ ⊥
      refine ⟨C, rfl, ?_⟩
      apply le_antisymm le_top
      intro x _
      change x = 0
      ext i
      exact Fin.elim0 i
  | succ s ih =>
      let CN := apm_b98a04_compositionSeriesOfChain R M t N hmono hsimple
      let C := apm_b98a04_compositionSeriesOfExact R (Fin s → M)
        (Fin (s + 1) → M) M
        (apm_b98a04_finTailInclusion R M s) (apm_b98a04_finHead R M s)
        (apm_b98a04_finTailInclusion_injective R M s)
        (apm_b98a04_finHead_surjective R M s)
        (apm_b98a04_finTail_head_exact R M s)
        ih.1 CN ih.2.1 ih.2.2 hbot htop
      refine ⟨C, ?_, ?_⟩
      · exact apm_b98a04_compositionSeriesOfExact_head R (Fin s → M)
          (Fin (s + 1) → M) M
          (apm_b98a04_finTailInclusion R M s) (apm_b98a04_finHead R M s)
          (apm_b98a04_finTailInclusion_injective R M s)
          (apm_b98a04_finHead_surjective R M s)
          (apm_b98a04_finTail_head_exact R M s)
          ih.1 CN ih.2.1 ih.2.2 hbot htop
      · exact apm_b98a04_compositionSeriesOfExact_last R (Fin s → M)
          (Fin (s + 1) → M) M
          (apm_b98a04_finTailInclusion R M s) (apm_b98a04_finHead R M s)
          (apm_b98a04_finTailInclusion_injective R M s)
          (apm_b98a04_finHead_surjective R M s)
          (apm_b98a04_finTail_head_exact R M s)
          ih.1 CN ih.2.1 ih.2.2 hbot htop

lemma apm_b98a04_powerCompositionSeries_length
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))
    (s : ℕ) :
    (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).1.length
      = s * t := by
  induction s with
  | zero => simp [apm_b98a04_powerCompositionSeriesData]
  | succ s ih =>
      simp only [apm_b98a04_powerCompositionSeriesData,
        apm_b98a04_compositionSeriesOfExact, RelSeries.smash_length,
        RelSeries.map_length]
      change
        (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).1.length
          + t = (s + 1) * t
      rw [ih]
      rw [Nat.add_mul]
      simp

lemma apm_b98a04_powerCompositionSeries_factor
    (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (t : ℕ) (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc)))
    (s : ℕ) :
    let C := (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).1
    ∀ k : Fin C.length, ∃ i : Fin t, Nonempty
      ((C k.succ ⧸ Submodule.comap (C k.succ).subtype (C k.castSucc)) ≃ₗ[R]
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) := by
  induction s with
  | zero =>
      dsimp only
      intro k
      have hlen := apm_b98a04_powerCompositionSeries_length R M t N hbot htop
        hmono hsimple 0
      exact Fin.elim0 (Fin.cast (by simpa using hlen) k)
  | succ s ih =>
      dsimp only
      intro k
      let D := (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).1
      let CN := apm_b98a04_compositionSeriesOfChain R M t N hmono hsimple
      have hc := apm_b98a04_compositionSeriesOfExact_factor_cases R (Fin s → M)
        (Fin (s + 1) → M) M
        (apm_b98a04_finTailInclusion R M s) (apm_b98a04_finHead R M s)
        (apm_b98a04_finTailInclusion_injective R M s)
        (apm_b98a04_finHead_surjective R M s)
        (apm_b98a04_finTail_head_exact R M s)
        D CN
        (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).2.1
        (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).2.2
        hbot htop k
      rcases hc with ⟨j, ⟨e⟩⟩ | ⟨j, ⟨e⟩⟩
      · obtain ⟨i, ⟨ei⟩⟩ := ih j
        exact ⟨i, ⟨e.trans ei⟩⟩
      · exact ⟨j, ⟨e⟩⟩

lemma apm_b98a04_simple_quotient_occurs_in_power
    (R M V : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [IsSimpleModule R V]
    (s t : ℕ) (S : Submodule R (Fin s → M))
    (g : S →ₗ[R] V) (hg : Function.Surjective g)
    (N : Fin (t + 1) → Submodule R M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last t) = ⊤)
    (hmono : StrictMono N)
    (hsimple : ∀ i : Fin t,
      IsSimpleModule R
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) :
    ∃ i : Fin t, Nonempty
      (V ≃ₗ[R]
        (N i.succ ⧸ Submodule.comap (N i.succ).subtype (N i.castSucc))) := by
  have hM := apm_b98a04_isFiniteLength_of_supplied_chain R M t N hbot htop hmono hsimple
  have hM' := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  letI : IsNoetherian R M := hM'.1
  letI : IsArtinian R M := hM'.2
  have hP : IsFiniteLength R (Fin s → M) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hS : IsFiniteLength R S := hP.of_injective (Submodule.injective_subtype S)
  have hK : IsFiniteLength R (LinearMap.ker g) :=
    hS.of_injective (Submodule.injective_subtype (LinearMap.ker g))
  obtain ⟨CK, CKbot, CKtop⟩ := isFiniteLength_iff_exists_compositionSeries.mp hK
  let CS := apm_b98a04_compositionSeriesOfExact R (LinearMap.ker g) S V
    (LinearMap.ker g).subtype g (Submodule.injective_subtype _) hg
    g.exact_subtype_ker_map CK (apm_b98a04_simpleCompositionSeries R V)
    CKbot CKtop rfl rfl
  have CSbot : CS.head = ⊥ := apm_b98a04_compositionSeriesOfExact_head R
    (LinearMap.ker g) S V (LinearMap.ker g).subtype g
    (Submodule.injective_subtype _) hg g.exact_subtype_ker_map
    CK (apm_b98a04_simpleCompositionSeries R V) CKbot CKtop rfl rfl
  have CStop : CS.last = ⊤ := apm_b98a04_compositionSeriesOfExact_last R
    (LinearMap.ker g) S V (LinearMap.ker g).subtype g
    (Submodule.injective_subtype _) hg g.exact_subtype_ker_map
    CK (apm_b98a04_simpleCompositionSeries R V) CKbot CKtop rfl rfl
  obtain ⟨j, ⟨ejV⟩⟩ := apm_b98a04_exactSeries_contains_simple_quotient R
    (LinearMap.ker g) S V (LinearMap.ker g).subtype g
    (Submodule.injective_subtype _) hg g.exact_subtype_ker_map CK CKbot CKtop
  have hQ : IsFiniteLength R ((Fin s → M) ⧸ S) :=
    hP.of_surjective (Submodule.mkQ_surjective S)
  obtain ⟨CQ, CQbot, CQtop⟩ := isFiniteLength_iff_exists_compositionSeries.mp hQ
  let CE := apm_b98a04_compositionSeriesOfExact R S (Fin s → M) ((Fin s → M) ⧸ S)
    S.subtype S.mkQ (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
    (LinearMap.exact_subtype_mkQ S) CS CQ CSbot CStop CQbot CQtop
  have CEbot : CE.head = ⊥ := apm_b98a04_compositionSeriesOfExact_head R S
    (Fin s → M) ((Fin s → M) ⧸ S) S.subtype S.mkQ
    (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
    (LinearMap.exact_subtype_mkQ S) CS CQ CSbot CStop CQbot CQtop
  have CEtop : CE.last = ⊤ := apm_b98a04_compositionSeriesOfExact_last R S
    (Fin s → M) ((Fin s → M) ⧸ S) S.subtype S.mkQ
    (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
    (LinearMap.exact_subtype_mkQ S) CS CQ CSbot CStop CQbot CQtop
  let k : Fin CE.length := j.castAdd CQ.length
  have ejE := apm_b98a04_compositionSeriesOfExact_leftFactorEquiv R S
    (Fin s → M) ((Fin s → M) ⧸ S) S.subtype S.mkQ
    (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
    (LinearMap.exact_subtype_mkQ S) CS CQ CSbot CStop CQbot CQtop j
  let CP := (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).1
  have hJ : CompositionSeries.Equivalent CE CP := CE.jordan_holder CP
    (CEbot.trans (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).2.1.symm)
    (CEtop.trans (apm_b98a04_powerCompositionSeriesData R M t N hbot htop hmono hsimple s).2.2.symm)
  obtain ⟨ekP⟩ := hJ.choose_spec k
  obtain ⟨i, ⟨ei⟩⟩ := apm_b98a04_powerCompositionSeries_factor R M t N
    hbot htop hmono hsimple s (hJ.choose k)
  exact ⟨i, ⟨ejV.symm |>.trans ejE |>.trans ekP |>.trans ei⟩⟩

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
  intro t N hbot htop hmono hsimple V _ _ _
  obtain ⟨s, m, hm⟩ := htuple
  let f := apm_b98a04_actionMap R M s m
  have hf : Function.Injective f := apm_b98a04_actionMap_injective R M s m hm
  obtain ⟨S, g, hg⟩ :=
    apm_b98a04_simple_quotient_of_embedded_regular R M V s f hf
  exact apm_b98a04_simple_quotient_occurs_in_power R M V s t S g hg N
    hbot htop hmono hsimple

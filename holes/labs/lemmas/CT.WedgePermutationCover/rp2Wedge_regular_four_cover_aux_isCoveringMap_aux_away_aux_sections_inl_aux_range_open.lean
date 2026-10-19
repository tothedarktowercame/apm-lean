import Mathlib

/-!
# Finite permutation covers of two point wedges

Reusable construction contracts for the concrete antipodal-projective-plane
and circle wedges used by APM t00A02 and t92J06.  The realization lemmas are
deliberately separated from transport and finite permutation calculations.
-/

open Set

noncomputable section

namespace ConstructionTargets.WedgePermutationCover

inductive WedgeRel {A B : Type*} (a : A) (b : B) : Sum A B → Sum A B → Prop
  | base : WedgeRel a b (.inl a) (.inr b)

def Wedge (A B : Type*) (a : A) (b : B) :=
  Quotient (Relation.EqvGen.setoid (WedgeRel a b))

noncomputable instance {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (a : A) (b : B) : TopologicalSpace (Wedge A B a b) :=
  TopologicalSpace.coinduced (fun z : Sum A B ↦ Quotient.mk _ z) inferInstance

def IsNfoldCover {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (n : ℕ) (p : E → B) : Prop :=
  IsCoveringMap p ∧ ∀ b, Nat.card {e : E // p e = b} = n

def IsRegularCover {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) : Prop :=
  ∀ x y, p x = p y → ∃ h : E ≃ₜ E, (∀ z, p (h z) = p z) ∧ h x = y

structure CoverWitness (B : Type*) [TopologicalSpace B]
    (n : ℕ) (regular : Bool) where
  E : Type
  topology : TopologicalSpace E
  p : E → B
  covering : @IsNfoldCover E B topology _ n p
  connected : @IsConnected E topology (Set.univ : Set E)
  regularity : if regular then @IsRegularCover E B topology _ p
    else ¬ @IsRegularCover E B topology _ p

/-- A witness transports along a homeomorphism of bases. -/
theorem coverWitness_homeomorph_base {B B' : Type*}
    [TopologicalSpace B] [TopologicalSpace B'] {n : ℕ} {r : Bool}
    (h : B ≃ₜ B') : Nonempty (CoverWitness B n r) →
      Nonempty (CoverWitness B' n r) := by
  rintro ⟨w⟩
  letI : TopologicalSpace w.E := w.topology
  let p' : w.E → B' := h ∘ w.p
  have hcover : @IsNfoldCover w.E B' w.topology _ n p' := by
    refine ⟨w.covering.1.homeomorph_comp h, ?_⟩
    intro b'
    let e : {x : w.E // p' x = b'} ≃ {x : w.E // w.p x = h.symm b'} :=
      { toFun := fun x ↦ ⟨x.1, by
          apply h.injective
          simpa [p'] using x.2⟩
        invFun := fun x ↦ ⟨x.1, by
          change h (w.p x.1) = b'
          simpa using congrArg h x.2⟩
        left_inv := fun x ↦ Subtype.ext rfl
        right_inv := fun x ↦ Subtype.ext rfl }
    exact (Nat.card_congr e).trans (w.covering.2 (h.symm b'))
  have hregular : @IsRegularCover w.E B' w.topology _ p' ↔
      @IsRegularCover w.E B w.topology _ w.p := by
    constructor
    · intro hr x y hxy
      obtain ⟨k, hk, hkxy⟩ := hr x y (congrArg h hxy)
      exact ⟨k, fun z ↦ h.injective (hk z), hkxy⟩
    · intro hr x y hxy
      obtain ⟨k, hk, hkxy⟩ := hr x y (h.injective hxy)
      exact ⟨k, fun z ↦ congrArg h (hk z), hkxy⟩
  refine ⟨{ E := w.E
            topology := w.topology
            p := p'
            covering := hcover
            connected := w.connected
            regularity := ?_ }⟩
  cases r with
  | false => exact fun hp' ↦ w.regularity (hregular.mp hp')
  | true => exact hregular.mpr w.regularity

abbrev Sphere2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

inductive AntipodalRel : Sphere2 → Sphere2 → Prop
  | antipodal (x : Sphere2) : AntipodalRel x (-x)

def RP2 := Quotient (Relation.EqvGen.setoid AntipodalRel)

noncomputable instance : TopologicalSpace RP2 :=
  TopologicalSpace.coinduced (fun x : Sphere2 ↦ Quotient.mk _ x) inferInstance

def antipodalCover : Sphere2 → RP2 := Quotient.mk _

noncomputable def rpBase : RP2 := antipodalCover
  ⟨EuclideanSpace.single 0 1, by simp⟩

@[simp] lemma rp2Wedge_regular_four_cover_aux_neg (x : Sphere2) :
    antipodalCover (-x) = antipodalCover x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ (AntipodalRel.antipodal x))

lemma rp2Wedge_regular_four_cover_aux_eqvGen_iff (x y : Sphere2) :
    Relation.EqvGen AntipodalRel x y ↔ y = x ∨ y = -x := by
  constructor
  · intro h
    induction h with
    | rel x y h => cases h; exact Or.inr rfl
    | refl => exact Or.inl rfl
    | symm x y _ ih => rcases ih with rfl | h <;> simp_all
    | trans x y z _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | h₁ <;> rcases ih₂ with rfl | h₂ <;> simp_all
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ (AntipodalRel.antipodal x)

lemma rp2Wedge_regular_four_cover_aux_cover_eq_iff (x y : Sphere2) :
    antipodalCover x = antipodalCover y ↔ y = x ∨ y = -x := by
  constructor
  · exact fun h ↦
      (rp2Wedge_regular_four_cover_aux_eqvGen_iff x y).mp (Quotient.exact h)
  · exact fun h ↦ Quotient.sound
      ((rp2Wedge_regular_four_cover_aux_eqvGen_iff x y).mpr h)

lemma rp2Wedge_regular_four_cover_aux_surjective :
    Function.Surjective antipodalCover := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, rfl⟩

lemma rp2Wedge_regular_four_cover_aux_fiber_card (b : RP2) :
    Nat.card {e : Sphere2 // antipodalCover e = b} = 2 := by
  obtain ⟨x, rfl⟩ := rp2Wedge_regular_four_cover_aux_surjective b
  have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro hx
    have hs := x.property
    simp [hx] at hs
  have hneg : (-x : Sphere2) ≠ x := by
    intro h
    apply hx0
    have h' : -(x : EuclideanSpace ℝ (Fin 3)) = x := congrArg Subtype.val h
    have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      rw [two_smul]
      simpa using
        (congrArg (fun z ↦ z + (x : EuclideanSpace ℝ (Fin 3))) h').symm
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  let e : Bool ≃ {z : Sphere2 // antipodalCover z = antipodalCover x} :=
    { toFun := fun q ↦ q.casesOn
        ⟨x, rfl⟩ ⟨-x, rp2Wedge_regular_four_cover_aux_neg x⟩
      invFun := fun z ↦ if z.1 = x then false else true
      left_inv := by
        intro q
        cases q <;> simp [hneg]
      right_inv := by
        intro z
        apply Subtype.ext
        rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff x z.1).mp z.2.symm with h | h
        · simp [h]
        · simp [h, hneg] }
  rw [Nat.card_congr e.symm]
  simp

/-! ### Gluing the associated covers (split of `rp2Wedge_regular_four_cover`)

The four-sheeted cover of `RP2 ∨ RP2` with monodromy `σ` on the left lobe and
`τ` on the right lobe: two copies of `Sphere2 × Fin 4`, quotiented by
`(x, i) ∼ (-x, σ i)` on the left copy, `(x, i) ∼ (-x, τ i)` on the right copy,
and with the left and right copies of `(e₀, i)` identified over the wedge
point.  The leaves are stated for general `σ τ` so the irregular leaf can
reuse them. -/

/-- The base point `e₀` of the sphere; `rpBase = antipodalCover e₀`. -/
def rp2Wedge_regular_four_cover_aux_e0 : Sphere2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

lemma rp2Wedge_regular_four_cover_aux_rpBase :
    rpBase = antipodalCover rp2Wedge_regular_four_cover_aux_e0 := rfl

inductive rp2Wedge_regular_four_cover_aux_Rel (σ τ : Equiv.Perm (Fin 4)) :
    (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4) →
      (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4) → Prop
  | left (x : Sphere2) (i : Fin 4) :
      rp2Wedge_regular_four_cover_aux_Rel σ τ (.inl (x, i)) (.inl (-x, σ i))
  | right (x : Sphere2) (i : Fin 4) :
      rp2Wedge_regular_four_cover_aux_Rel σ τ (.inr (x, i)) (.inr (-x, τ i))
  | glue (i : Fin 4) :
      rp2Wedge_regular_four_cover_aux_Rel σ τ
        (.inl (rp2Wedge_regular_four_cover_aux_e0, i))
        (.inr (rp2Wedge_regular_four_cover_aux_e0, i))

/-- The total space of the glued cover with monodromies `σ`, `τ`. -/
def rp2Wedge_regular_four_cover_aux_E (σ τ : Equiv.Perm (Fin 4)) : Type :=
  Quotient (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ))

noncomputable instance (σ τ : Equiv.Perm (Fin 4)) :
    TopologicalSpace (rp2Wedge_regular_four_cover_aux_E σ τ) :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

/-- The projection on the disjoint union of the two sheets of copies. -/
def rp2Wedge_regular_four_cover_aux_proj :
    (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4) → Wedge RP2 RP2 rpBase rpBase
  | .inl z => Quotient.mk _ (.inl (antipodalCover z.1))
  | .inr z => Quotient.mk _ (.inr (antipodalCover z.1))

lemma rp2Wedge_regular_four_cover_aux_proj_respects (σ τ : Equiv.Perm (Fin 4))
    {a b : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4)}
    (h : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ) a b) :
    rp2Wedge_regular_four_cover_aux_proj a =
      rp2Wedge_regular_four_cover_aux_proj b := by
  induction h with
  | rel a b h =>
    cases h with
    | left x i => simp [rp2Wedge_regular_four_cover_aux_proj]
    | right x i => simp [rp2Wedge_regular_four_cover_aux_proj]
    | glue i => exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

/-- The covering projection of the glued cover. -/
def rp2Wedge_regular_four_cover_aux_p (σ τ : Equiv.Perm (Fin 4)) :
    rp2Wedge_regular_four_cover_aux_E σ τ → Wedge RP2 RP2 rpBase rpBase :=
  Quotient.lift rp2Wedge_regular_four_cover_aux_proj
    (fun _ _ h ↦ rp2Wedge_regular_four_cover_aux_proj_respects σ τ h)

/-! #### Split of `rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge` (lemma-3 PARTIAL, 2026-10-19) -/

/-- Even covering from local sections: if the sheets over an open `U ∋ x` are the
ranges of continuous sections `s i`, open and pairwise disjoint, and they exhaust
`f ⁻¹' U`, then `x` is evenly covered with fibre `ι`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace ι] [DiscreteTopology ι]
    (f : E → X) (hf : Continuous f) (x : X) (U : Set X) (hxU : x ∈ U) (hU : IsOpen U)
    (s : ι → U → E) (hs : ∀ i, Continuous (s i)) (hfs : ∀ i u, f (s i u) = u)
    (hopen : ∀ i, IsOpen (Set.range (s i)))
    (hcover : ∀ e, f e ∈ U → ∃ i u, s i u = e)
    (hdisj : ∀ i j u v, s i u = s j v → i = j) :
    IsEvenlyCovered f x ι := by
  classical
  let idx : f ⁻¹' U → ι := fun e ↦ (hcover e.1 e.2).choose
  let arg : (e : f ⁻¹' U) → U := fun e ↦ (hcover e.1 e.2).choose_spec.choose
  have hsarg (e : f ⁻¹' U) : s (idx e) (arg e) = e.1 :=
    (hcover e.1 e.2).choose_spec.choose_spec
  have hsection (e : f ⁻¹' U) :
      s (idx e) ⟨f e.1, e.2⟩ = e.1 := by
    have ha : arg e = ⟨f e.1, e.2⟩ := by
      apply Subtype.ext
      exact (hfs (idx e) (arg e)).symm.trans (congrArg f (hsarg e))
    rw [← ha]
    exact hsarg e
  have hidx (i : ι) (u : U) : idx ⟨s i u, by simpa [hfs] using u.2⟩ = i := by
    apply hdisj _ _ _ u
    exact hsarg _
  have hidx_cont : Continuous idx := by
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_exists_open]
    intro e
    refine ⟨Subtype.val ⁻¹' Set.range (s (idx e)),
      (hopen _).preimage continuous_subtype_val, ?_, ?_⟩
    · exact ⟨arg e, hsarg e⟩
    · intro e' he'
      obtain ⟨u, hu⟩ := he'
      apply hdisj _ _ (arg e') u
      exact (hsarg e').trans hu.symm
  have hinv_cont : Continuous (fun z : U × ι ↦
      (⟨s z.2 z.1, by simpa [hfs] using z.1.2⟩ : f ⁻¹' U)) := by
    apply continuous_of_continuousOn_iUnion_of_isOpen
        (s := fun i : ι ↦ {z : U × ι | z.2 = i})
    · intro i
      have hi : Continuous (fun z : U × ι ↦
          (⟨s i z.1, by simpa [hfs] using z.1.2⟩ : f ⁻¹' U)) := by
        apply Continuous.subtype_mk
        exact (hs i).comp continuous_fst
      exact hi.continuousOn.congr (by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz
        rcases z with ⟨u, j⟩
        dsimp at hz ⊢
        subst j
        rfl)
    · intro i
      exact (isOpen_discrete {i}).preimage continuous_snd
    · ext z
      simp
  refine ⟨inferInstance, U, hxU, hU, hU.preimage hf, ?_, ?_⟩
  · exact
      { toFun := fun e ↦ (⟨f e.1, e.2⟩, idx e)
        invFun := fun z ↦ ⟨s z.2 z.1, by simpa [hfs] using z.1.2⟩
        left_inv := fun e ↦ Subtype.ext (hsection e)
        right_inv := fun z ↦ by
          apply Prod.ext
          · apply Subtype.ext
            exact hfs z.2 z.1
          · exact hidx z.2 z.1
        continuous_toFun :=
          (Continuous.subtype_mk (hf.comp continuous_subtype_val) _).prodMk hidx_cont
        continuous_invFun := hinv_cont }
  · intro e
    rfl

/-- The open hemisphere `{y | 0 < y₀}` around `e₀` embeds openly in `RP2`
(it is disjoint from its antipode, and `antipodalCover` is an open map). -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_hemi :
    Topology.IsOpenEmbedding
      (fun y : {y : Sphere2 // 0 < (y : EuclideanSpace ℝ (Fin 3)) 0} ↦
        antipodalCover y.1) := by
  let H : Set Sphere2 := {y | 0 < (y : EuclideanSpace ℝ (Fin 3)) 0}
  have hH : IsOpen H := by
    exact isOpen_lt continuous_const
      ((continuous_apply 0).comp
        ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val))
  rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨continuous_quot_mk.comp continuous_subtype_val, ?_, ?_⟩
  · intro x y hxy
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff x.1 y.1).mp hxy with h | h
    · exact Subtype.ext h.symm
    · exfalso
      have hx : 0 < (x.1 : EuclideanSpace ℝ (Fin 3)) 0 := x.2
      have hy : 0 < (y.1 : EuclideanSpace ℝ (Fin 3)) 0 := y.2
      rw [h] at hy
      change 0 < -((x.1 : EuclideanSpace ℝ (Fin 3)) 0) at hy
      linarith
  · intro V hV
    let W : Set Sphere2 := Subtype.val '' V
    have hW : IsOpen W := hH.isOpenMap_subtype_val V hV
    let n : Sphere2 → Sphere2 := fun x ↦ -x
    have hn : Continuous n := by
      exact continuous_neg
    have himage : antipodalCover ⁻¹' (antipodalCover '' W) = W ∪ n ⁻¹' W := by
      ext x
      constructor
      · rintro ⟨y, hyW, heq⟩
        rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff y x).mp heq with h | h
        · exact Or.inl (h ▸ hyW)
        · right
          change -x ∈ W
          simpa [h] using hyW
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · refine ⟨-x, hx, ?_⟩
          exact rp2Wedge_regular_four_cover_aux_neg x
    have hopen_image : IsOpen (antipodalCover '' W) := by
      apply (isQuotientMap_quot_mk : Topology.IsQuotientMap antipodalCover).isOpen_preimage.mp
      change IsOpen (antipodalCover ⁻¹' (antipodalCover '' W))
      rw [himage]
      exact hW.union (hW.preimage hn)
    simpa [W, Set.image_image] using hopen_image

/-- The glued projection is continuous. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_continuous
    (σ τ : Equiv.Perm (Fin 4)) :
    Continuous (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  rw [continuous_coinduced_dom]
  change Continuous rp2Wedge_regular_four_cover_aux_proj
  rw [continuous_sum_dom]
  constructor
  · exact continuous_coinduced_rng.comp
      (continuous_inl.comp (continuous_coinduced_rng.comp continuous_fst))
  · exact continuous_coinduced_rng.comp
      (continuous_inr.comp (continuous_coinduced_rng.comp continuous_fst))

/-- Continuity out of an open subset of a wedge is checked on the two lobes
(`Quotient.mk` restricted to the open preimage is still a quotient map). -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_lobes
    {A B Y : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]
    (a : A) (b : B) (U : Set (Wedge A B a b)) (hU : IsOpen U) (g : U → Y)
    (hl : Continuous (fun z : {z : A // (Quotient.mk _ (.inl z) : Wedge A B a b) ∈ U} ↦
      g ⟨_, z.2⟩))
    (hr : Continuous (fun z : {z : B // (Quotient.mk _ (.inr z) : Wedge A B a b) ∈ U} ↦
      g ⟨_, z.2⟩)) :
    Continuous g := by
  let q : A ⊕ B → Wedge A B a b := fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
  let qU : {z : A ⊕ B // q z ∈ U} → U := U.restrictPreimage q
  let eL : {z : A // q (.inl z) ∈ U} → {z : A ⊕ B // q z ∈ U} :=
    (q ⁻¹' U).restrictPreimage Sum.inl
  let eR : {z : B // q (.inr z) ∈ U} → {z : A ⊕ B // q z ∈ U} :=
    (q ⁻¹' U).restrictPreimage Sum.inr
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.inl.restrictPreimage (q ⁻¹' U)
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.inr.restrictPreimage (q ⁻¹' U)
  have hL : ContinuousOn (g ∘ qU) (Set.range eL) := by
    rw [← Set.image_univ]
    apply heL.isInducing.continuousOn_image_iff.mpr
    simpa [q, qU, eL, Function.comp_def] using hl
  have hR : ContinuousOn (g ∘ qU) (Set.range eR) := by
    rw [← Set.image_univ]
    apply heR.isInducing.continuousOn_image_iff.mpr
    simpa [q, qU, eR, Function.comp_def] using hr
  rw [← continuousOn_univ]
  have hc := hL.union_of_isOpen hR heL.isOpen_range heR.isOpen_range
  apply hc.mono
  rintro ⟨z, hz⟩ -
  cases z with
  | inl x => exact Set.mem_union_left _ ⟨⟨x, hz⟩, rfl⟩
  | inr x => exact Set.mem_union_right _ ⟨⟨x, hz⟩, rfl⟩

/-- The four sheets over the wedge point.  `U` is the image of the hemisphere
`{y | 0 < y₀}` in both lobes; sheet `i` sends `[inl (antipodalCover y)]` to
`[inl (y, i)]` and `[inr (antipodalCover y)]` to `[inr (y, i)]` for `y` in the
hemisphere (these agree at the wedge point by the glue at `e₀`).  Continuity by
`_aux_lobes` and `_aux_hemi`; the range of sheet `i` is the class of
`{inl (y, i), inl (-y, σ i), inr (y, i), inr (-y, τ i) | 0 < y₀}`, open in the raw
sum; disjointness by `_aux_card_aux_invariant` recording the sheet index. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_invariant
    {α : Type*} (σ τ : Equiv.Perm (Fin 4))
    (fL fR : Sphere2 × Fin 4 → α)
    (hL : ∀ x i, fL (-x, σ i) = fL (x, i))
    (hR : ∀ x i, fR (-x, τ i) = fR (x, i))
    (hG : ∀ i, fL (rp2Wedge_regular_four_cover_aux_e0, i) =
      fR (rp2Wedge_regular_four_cover_aux_e0, i))
    {a b : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4)}
    (h : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ) a b) :
    Sum.elim fL fR a = Sum.elim fL fR b := by
  induction h with
  | rel a b h =>
      cases h with
      | left x i => exact (hL x i).symm
      | right x i => exact (hR x i).symm
      | glue i => exact hG i
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- On representatives whose sphere coordinate lies in the positive hemisphere,
the sheet index is invariant under the entire gluing relation. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_index
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (x y : Sphere2) (i j : Fin 4)
    (hx : 0 < (x : EuclideanSpace ℝ (Fin 3)) 0)
    (hy : 0 < (y : EuclideanSpace ℝ (Fin 3)) 0)
    (sx sy : Bool)
    (h : Quotient.mk (Relation.EqvGen.setoid
          (rp2Wedge_regular_four_cover_aux_Rel σ τ))
          (sx.casesOn (.inl (x, i)) (.inr (x, i))) =
        Quotient.mk (Relation.EqvGen.setoid
          (rp2Wedge_regular_four_cover_aux_Rel σ τ))
          (sy.casesOn (.inl (y, j)) (.inr (y, j)))) :
    i = j := by
  let fL : Sphere2 × Fin 4 → Fin 4 := fun z ↦
    if 0 < (z.1 : EuclideanSpace ℝ (Fin 3)) 0 then z.2
    else if (z.1 : EuclideanSpace ℝ (Fin 3)) 0 < 0 then σ z.2 else 0
  let fR : Sphere2 × Fin 4 → Fin 4 := fun z ↦
    if 0 < (z.1 : EuclideanSpace ℝ (Fin 3)) 0 then z.2
    else if (z.1 : EuclideanSpace ℝ (Fin 3)) 0 < 0 then τ z.2 else 0
  have hL : ∀ z k, fL (-z, σ k) = fL (z, k) := by
    intro z k
    change (if 0 < -((z : EuclideanSpace ℝ (Fin 3)) 0) then σ k
      else if -((z : EuclideanSpace ℝ (Fin 3)) 0) < 0 then σ (σ k) else 0) =
      (if 0 < (z : EuclideanSpace ℝ (Fin 3)) 0 then k
      else if (z : EuclideanSpace ℝ (Fin 3)) 0 < 0 then σ k else 0)
    by_cases hp : 0 < (z : EuclideanSpace ℝ (Fin 3)) 0
    · have hn : ¬ (z : EuclideanSpace ℝ (Fin 3)) 0 < 0 := by linarith
      simp [hp, hn, hσ k]
    by_cases hn : (z : EuclideanSpace ℝ (Fin 3)) 0 < 0
    · simp [hp, hn]
    · have hz : (z : EuclideanSpace ℝ (Fin 3)) 0 = 0 := le_antisymm (le_of_not_gt hp)
          (le_of_not_gt hn)
      simp [hz]
  have hR : ∀ z k, fR (-z, τ k) = fR (z, k) := by
    intro z k
    change (if 0 < -((z : EuclideanSpace ℝ (Fin 3)) 0) then τ k
      else if -((z : EuclideanSpace ℝ (Fin 3)) 0) < 0 then τ (τ k) else 0) =
      (if 0 < (z : EuclideanSpace ℝ (Fin 3)) 0 then k
      else if (z : EuclideanSpace ℝ (Fin 3)) 0 < 0 then τ k else 0)
    by_cases hp : 0 < (z : EuclideanSpace ℝ (Fin 3)) 0
    · have hn : ¬ (z : EuclideanSpace ℝ (Fin 3)) 0 < 0 := by linarith
      simp [hp, hn, hτ k]
    by_cases hn : (z : EuclideanSpace ℝ (Fin 3)) 0 < 0
    · simp [hp, hn]
    · have hz : (z : EuclideanSpace ℝ (Fin 3)) 0 = 0 := le_antisymm (le_of_not_gt hp)
          (le_of_not_gt hn)
      simp [hz]
  have he0 : 0 < (rp2Wedge_regular_four_cover_aux_e0 :
      EuclideanSpace ℝ (Fin 3)) 0 := by
    simp [rp2Wedge_regular_four_cover_aux_e0]
  have hG : ∀ k, fL (rp2Wedge_regular_four_cover_aux_e0, k) =
      fR (rp2Wedge_regular_four_cover_aux_e0, k) := by
    intro k
    simp [fL, fR, he0]
  have hi := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_invariant
    σ τ fL fR hL hR hG (Quotient.exact h)
  cases sx <;> cases sy <;> simpa [fL, fR, hx, hy] using hi

/-- A representative of `b` in the closed hemisphere `{y | 0 ≤ y₀}`. -/
def rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (b : RP2) : Sphere2 :=
  if 0 ≤ ((rp2Wedge_regular_four_cover_aux_surjective b).choose :
      EuclideanSpace ℝ (Fin 3)) 0
  then (rp2Wedge_regular_four_cover_aux_surjective b).choose
  else -(rp2Wedge_regular_four_cover_aux_surjective b).choose

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_spec (b : RP2) : antipodalCover (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift b) = b := by
  have h := (rp2Wedge_regular_four_cover_aux_surjective b).choose_spec
  unfold rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift
  split_ifs <;> simp [h]

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_nonneg (b : RP2) :
    0 ≤ (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift b : EuclideanSpace ℝ (Fin 3)) 0 := by
  unfold rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift
  split_ifs with hc
  · exact hc
  · change 0 ≤ -(((rp2Wedge_regular_four_cover_aux_surjective b).choose :
      EuclideanSpace ℝ (Fin 3)) 0)
    linarith

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos (y : Sphere2) (hy : 0 < (y : EuclideanSpace ℝ (Fin 3)) 0) :
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y) = y := by
  rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff y
      (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y))).mp (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_spec _).symm with h | h
  · exact h
  · exfalso
    have hnn := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_nonneg (antipodalCover y)
    rw [h] at hnn
    change 0 ≤ -((y : EuclideanSpace ℝ (Fin 3)) 0) at hnn
    linarith

/-- Sheet `i` over the whole wedge: `[inl b] ↦ [inl (lift b, i)]`,
`[inr b] ↦ [inr (lift b, i)]`; well defined by the glue at `e₀`. -/
def rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S (σ τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    Wedge RP2 RP2 rpBase rpBase → rp2Wedge_regular_four_cover_aux_E σ τ :=
  Quotient.lift
    (Sum.elim
      (fun b ↦ Quotient.mk (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ))
        (.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift b, i)))
      (fun b ↦ Quotient.mk (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ))
        (.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift b, i))))
    (fun a b h ↦ by
      have h' : Relation.EqvGen (WedgeRel rpBase rpBase) a b := h
      clear h
      induction h' with
      | rel a b h =>
        cases h
        have he : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift rpBase = rp2Wedge_regular_four_cover_aux_e0 :=
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos _ (by simp [rp2Wedge_regular_four_cover_aux_e0])
        change Quotient.mk _ (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift rpBase, i)) =
          Quotient.mk _ (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift rpBase, i))
        rw [he]
        exact Quotient.sound (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue i))
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

/-- The image of the open hemisphere `{y | 0 < y₀}` in both lobes. -/
def rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U : Set (Wedge RP2 RP2 rpBase rpBase) :=
  {w | ∃ y : Sphere2, 0 < (y : EuclideanSpace ℝ (Fin 3)) 0 ∧
    (w = Quotient.mk (Relation.EqvGen.setoid (WedgeRel rpBase rpBase))
        (Sum.inl (antipodalCover y)) ∨
      w = Quotient.mk (Relation.EqvGen.setoid (WedgeRel rpBase rpBase))
        (Sum.inr (antipodalCover y)))}

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_p_S (σ τ : Equiv.Perm (Fin 4)) (i : Fin 4)
    (w : Wedge RP2 RP2 rpBase rpBase) :
    rp2Wedge_regular_four_cover_aux_p σ τ (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i w) = w := by
  induction w using Quotient.inductionOn with
  | _ z =>
    cases z with
    | inl b =>
      change Quotient.mk _ (Sum.inl (antipodalCover (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift b))) = _
      rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_spec]
    | inr b =>
      change Quotient.mk _ (Sum.inr (antipodalCover (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift b))) = _
      rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_spec]

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S_mem (σ τ : Equiv.Perm (Fin 4)) (w : Wedge RP2 RP2 rpBase rpBase)
    (hw : w ∈ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U) :
    ∃ y : Sphere2, 0 < (y : EuclideanSpace ℝ (Fin 3)) 0 ∧ ∃ sx : Bool, ∀ i,
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i w = Quotient.mk (Relation.EqvGen.setoid
        (rp2Wedge_regular_four_cover_aux_Rel σ τ))
        (sx.casesOn (.inl (y, i)) (.inr (y, i))) := by
  obtain ⟨y, hy, rfl | rfl⟩ := hw
  · refine ⟨y, hy, false, fun i ↦ ?_⟩
    change Quotient.mk _ (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), i)) = _
    rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy]
  · refine ⟨y, hy, true, fun i ↦ ?_⟩
    change Quotient.mk _ (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), i)) = _
    rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy]

/-- `U` is open: its preimage in `RP2 ⊕ RP2` is the hemisphere image in each lobe
(the wedge point `rpBase` lies in it on both sides); use `_aux_hemi`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
    {A B : Type*} (a : A) (b : B) (u v : Sum A B) :
    Relation.EqvGen (WedgeRel a b) u v ↔
      u = v ∨ ((u = .inl a ∨ u = .inr b) ∧ (v = .inl a ∨ v = .inr b)) := by
  constructor
  · intro h
    induction h with
    | rel u v h => cases h; exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    | refl => exact Or.inl rfl
    | symm u v _ ih =>
        rcases ih with rfl | ⟨h₁, h₂⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h₂, h₁⟩
    | trans u v w _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨h₁, h₂⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨_, h₃⟩
          · exact Or.inr ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₁, h₃⟩
  · rintro (rfl | ⟨h₁, h₂⟩)
    · exact Relation.EqvGen.refl _
    · have hab : Relation.EqvGen (WedgeRel a b) (.inl a) (.inr b) :=
        Relation.EqvGen.rel _ _ WedgeRel.base
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact Relation.EqvGen.refl _
      · exact hab
      · exact Relation.EqvGen.symm _ _ hab
      · exact Relation.EqvGen.refl _

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open : IsOpen (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U) := by
  let H : Type := {y : Sphere2 // 0 < (y : EuclideanSpace ℝ (Fin 3)) 0}
  let f : H → RP2 := fun y ↦ antipodalCover y.1
  let V : Set RP2 := Set.range f
  have hV : IsOpen V := by
    exact rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_hemi.isOpen_range
  have hb : rpBase ∈ V := by
    refine ⟨⟨rp2Wedge_regular_four_cover_aux_e0, by
      simp [rp2Wedge_regular_four_cover_aux_e0]⟩, ?_⟩
    rfl
  rw [isOpen_coinduced, isOpen_sum_iff]
  constructor
  · convert hV using 1
    ext b
    constructor
    · intro hbU
      obtain ⟨y, hy, h | h⟩ := hbU
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
          rpBase rpBase (.inl b) (.inl (antipodalCover y))).mp he with he | he
        · cases he
          exact ⟨⟨y, hy⟩, rfl⟩
        · rcases he.1 with he | he
          · cases he
            exact hb
          · contradiction
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
          rpBase rpBase (.inl b) (.inr (antipodalCover y))).mp he with he | he
        · contradiction
        · rcases he.1 with he | he
          · cases he
            exact hb
          · contradiction
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, Or.inl rfl⟩
  · convert hV using 1
    ext b
    constructor
    · intro hbU
      obtain ⟨y, hy, h | h⟩ := hbU
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
          rpBase rpBase (.inr b) (.inl (antipodalCover y))).mp he with he | he
        · contradiction
        · rcases he.1 with he | he
          · contradiction
          · cases he
            exact hb
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
          rpBase rpBase (.inr b) (.inr (antipodalCover y))).mp he with he | he
        · cases he
          exact ⟨⟨y, hy⟩, rfl⟩
        · rcases he.1 with he | he
          · contradiction
          · cases he
            exact hb
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, Or.inr rfl⟩

/-- Each sheet is continuous on `U`: check on the two lobes by `_aux_lobes`; on
each lobe it is `b ↦ [(lift b, i)]`, and on the hemisphere image `lift` is the
inverse of the open embedding `_aux_hemi`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
    {A B : Type*} (a : A) (b : B) (u v : Sum A B) :
    Relation.EqvGen (WedgeRel a b) u v ↔
      u = v ∨ ((u = .inl a ∨ u = .inr b) ∧ (v = .inl a ∨ v = .inr b)) := by
  constructor
  · intro h
    induction h with
    | rel u v h => cases h; exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    | refl => exact Or.inl rfl
    | symm u v _ ih =>
        rcases ih with rfl | ⟨h₁, h₂⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h₂, h₁⟩
    | trans u v w _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨h₁, h₂⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨_, h₃⟩
          · exact Or.inr ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₁, h₃⟩
  · rintro (rfl | ⟨h₁, h₂⟩)
    · exact Relation.EqvGen.refl _
    · have hab : Relation.EqvGen (WedgeRel a b) (.inl a) (.inr b) :=
        Relation.EqvGen.rel _ _ WedgeRel.base
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact Relation.EqvGen.refl _
      · exact hab
      · exact Relation.EqvGen.symm _ _ hab
      · exact Relation.EqvGen.refl _

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_hemi :
    Topology.IsOpenEmbedding
      (fun y : {y : Sphere2 // 0 < (y : EuclideanSpace ℝ (Fin 3)) 0} ↦
        antipodalCover y.1) := by
  let H : Set Sphere2 := {y | 0 < (y : EuclideanSpace ℝ (Fin 3)) 0}
  have hH : IsOpen H := by
    exact isOpen_lt continuous_const
      ((continuous_apply 0).comp
        ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val))
  rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨continuous_quot_mk.comp continuous_subtype_val, ?_, ?_⟩
  · intro x y hxy
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff x.1 y.1).mp hxy with h | h
    · exact Subtype.ext h.symm
    · exfalso
      have hx : 0 < (x.1 : EuclideanSpace ℝ (Fin 3)) 0 := x.2
      have hy : 0 < (y.1 : EuclideanSpace ℝ (Fin 3)) 0 := y.2
      rw [h] at hy
      change 0 < -((x.1 : EuclideanSpace ℝ (Fin 3)) 0) at hy
      linarith
  · intro V hV
    let W : Set Sphere2 := Subtype.val '' V
    have hW : IsOpen W := hH.isOpenMap_subtype_val V hV
    let n : Sphere2 → Sphere2 := fun x ↦ -x
    have hn : Continuous n := continuous_neg
    have himage : antipodalCover ⁻¹' (antipodalCover '' W) = W ∪ n ⁻¹' W := by
      ext x
      constructor
      · rintro ⟨y, hyW, heq⟩
        rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff y x).mp heq with h | h
        · exact Or.inl (h ▸ hyW)
        · right
          change -x ∈ W
          simpa [h] using hyW
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · refine ⟨-x, hx, ?_⟩
          exact rp2Wedge_regular_four_cover_aux_neg x
    have hopen_image : IsOpen (antipodalCover '' W) := by
      apply (isQuotientMap_quot_mk : Topology.IsQuotientMap antipodalCover).isOpen_preimage.mp
      change IsOpen (antipodalCover ⁻¹' (antipodalCover '' W))
      rw [himage]
      exact hW.union (hW.preimage hn)
    simpa [W, Set.image_image] using hopen_image

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_open :
    IsOpen rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U := by
  let H : Type := {y : Sphere2 // 0 < (y : EuclideanSpace ℝ (Fin 3)) 0}
  let f : H → RP2 := fun y ↦ antipodalCover y.1
  let V : Set RP2 := Set.range f
  have hV : IsOpen V :=
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_hemi.isOpen_range
  have hb : rpBase ∈ V := by
    refine ⟨⟨rp2Wedge_regular_four_cover_aux_e0, by
      simp [rp2Wedge_regular_four_cover_aux_e0]⟩, rfl⟩
  rw [isOpen_coinduced, isOpen_sum_iff]
  constructor
  · convert hV using 1
    ext b
    constructor
    · intro hbU
      obtain ⟨y, hy, h | h⟩ := hbU
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
          rpBase rpBase (.inl b) (.inl (antipodalCover y))).mp he with he | he
        · cases he; exact ⟨⟨y, hy⟩, rfl⟩
        · rcases he.1 with he | he
          · cases he; exact hb
          · contradiction
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
          rpBase rpBase (.inl b) (.inr (antipodalCover y))).mp he with he | he
        · contradiction
        · rcases he.1 with he | he
          · cases he; exact hb
          · contradiction
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, Or.inl rfl⟩
  · convert hV using 1
    ext b
    constructor
    · intro hbU
      obtain ⟨y, hy, h | h⟩ := hbU
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
          rpBase rpBase (.inr b) (.inl (antipodalCover y))).mp he with he | he
        · contradiction
        · rcases he.1 with he | he
          · contradiction
          · cases he; exact hb
      · have he := Quotient.exact h
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
          rpBase rpBase (.inr b) (.inr (antipodalCover y))).mp he with he | he
        · cases he; exact ⟨⟨y, hy⟩, rfl⟩
        · rcases he.1 with he | he
          · contradiction
          · cases he; exact hb
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, Or.inr rfl⟩

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_lobes
    {A B Y : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]
    (a : A) (b : B) (U : Set (Wedge A B a b)) (hU : IsOpen U) (g : U → Y)
    (hl : Continuous (fun z : {z : A // (Quotient.mk _ (.inl z) : Wedge A B a b) ∈ U} ↦
      g ⟨_, z.2⟩))
    (hr : Continuous (fun z : {z : B // (Quotient.mk _ (.inr z) : Wedge A B a b) ∈ U} ↦
      g ⟨_, z.2⟩)) : Continuous g := by
  let q : A ⊕ B → Wedge A B a b := fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
  let qU : {z : A ⊕ B // q z ∈ U} → U := U.restrictPreimage q
  let eL : {z : A // q (.inl z) ∈ U} → {z : A ⊕ B // q z ∈ U} :=
    (q ⁻¹' U).restrictPreimage Sum.inl
  let eR : {z : B // q (.inr z) ∈ U} → {z : A ⊕ B // q z ∈ U} :=
    (q ⁻¹' U).restrictPreimage Sum.inr
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.inl.restrictPreimage (q ⁻¹' U)
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.inr.restrictPreimage (q ⁻¹' U)
  have hL : ContinuousOn (g ∘ qU) (Set.range eL) := by
    rw [← Set.image_univ]
    apply heL.isInducing.continuousOn_image_iff.mpr
    simpa [q, qU, eL, Function.comp_def] using hl
  have hR : ContinuousOn (g ∘ qU) (Set.range eR) := by
    rw [← Set.image_univ]
    apply heR.isInducing.continuousOn_image_iff.mpr
    simpa [q, qU, eR, Function.comp_def] using hr
  rw [← continuousOn_univ]
  have hc := hL.union_of_isOpen hR heL.isOpen_range heR.isOpen_range
  apply hc.mono
  rintro ⟨z, hz⟩ -
  cases z with
  | inl x => exact Set.mem_union_left _ ⟨⟨x, hz⟩, rfl⟩
  | inr x => exact Set.mem_union_right _ ⟨⟨x, hz⟩, rfl⟩

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous (σ τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    Continuous (fun u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1) := by
  let H : Type := {y : Sphere2 // 0 < (y : EuclideanSpace ℝ (Fin 3)) 0}
  let f : H → RP2 := fun y ↦ antipodalCover y.1
  let V : Set RP2 := Set.range f
  have he : Topology.IsEmbedding f :=
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_hemi.isEmbedding
  let e : H ≃ₜ V := he.toHomeomorph
  have hmemL (z : {z : RP2 //
      (Quotient.mk _ (.inl z) : Wedge RP2 RP2 rpBase rpBase) ∈
        rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U}) : z.1 ∈ V := by
    obtain ⟨y, hy, h | h⟩ := z.2
    · have hq := Quotient.exact h
      rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
        rpBase rpBase (.inl z.1) (.inl (antipodalCover y))).mp hq with hq | hq
      · exact ⟨⟨y, hy⟩, (Sum.inl.inj hq).symm⟩
      · rcases hq.1 with hq | hq
        · exact ⟨⟨rp2Wedge_regular_four_cover_aux_e0, by
            simp [rp2Wedge_regular_four_cover_aux_e0]⟩, (Sum.inl.inj hq).symm⟩
        · contradiction
    · have hq := Quotient.exact h
      rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
        rpBase rpBase (.inl z.1) (.inr (antipodalCover y))).mp hq with hq | hq
      · contradiction
      · rcases hq.1 with hq | hq
        · exact ⟨⟨rp2Wedge_regular_four_cover_aux_e0, by
            simp [rp2Wedge_regular_four_cover_aux_e0]⟩, (Sum.inl.inj hq).symm⟩
        · contradiction
  have hmemR (z : {z : RP2 //
      (Quotient.mk _ (.inr z) : Wedge RP2 RP2 rpBase rpBase) ∈
        rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U}) : z.1 ∈ V := by
    obtain ⟨y, hy, h | h⟩ := z.2
    · have hq := Quotient.exact h
      rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
        rpBase rpBase (.inr z.1) (.inl (antipodalCover y))).mp hq with hq | hq
      · contradiction
      · rcases hq.1 with hq | hq
        · contradiction
        · exact ⟨⟨rp2Wedge_regular_four_cover_aux_e0, by
            simp [rp2Wedge_regular_four_cover_aux_e0]⟩, (Sum.inr.inj hq).symm⟩
    · have hq := Quotient.exact h
      rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
        rpBase rpBase (.inr z.1) (.inr (antipodalCover y))).mp hq with hq | hq
      · exact ⟨⟨y, hy⟩, (Sum.inr.inj hq).symm⟩
      · rcases hq.1 with hq | hq
        · contradiction
        · exact ⟨⟨rp2Wedge_regular_four_cover_aux_e0, by
            simp [rp2Wedge_regular_four_cover_aux_e0]⟩, (Sum.inr.inj hq).symm⟩
  have hLiftL (z : {z : RP2 //
      (Quotient.mk _ (.inl z) : Wedge RP2 RP2 rpBase rpBase) ∈
        rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U}) :
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift z.1 =
        (e.symm ⟨z.1, hmemL z⟩).1 := by
    have hz : antipodalCover (e.symm ⟨z.1, hmemL z⟩).1 = z.1 := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z.1, hmemL z⟩)
    calc
      _ = rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift
          (antipodalCover (e.symm ⟨z.1, hmemL z⟩).1) := congrArg _ hz.symm
      _ = _ := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos
        _ (e.symm ⟨z.1, hmemL z⟩).2
  have hLiftR (z : {z : RP2 //
      (Quotient.mk _ (.inr z) : Wedge RP2 RP2 rpBase rpBase) ∈
        rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U}) :
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift z.1 =
        (e.symm ⟨z.1, hmemR z⟩).1 := by
    have hz : antipodalCover (e.symm ⟨z.1, hmemR z⟩).1 = z.1 := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z.1, hmemR z⟩)
    calc
      _ = rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift
          (antipodalCover (e.symm ⟨z.1, hmemR z⟩).1) := congrArg _ hz.symm
      _ = _ := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos
        _ (e.symm ⟨z.1, hmemR z⟩).2
  apply rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_lobes
    rpBase rpBase _
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_open
  · have hy : Continuous (fun z : {z : RP2 //
        (Quotient.mk _ (.inl z) : Wedge RP2 RP2 rpBase rpBase) ∈
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U} ↦
        (e.symm ⟨z.1, hmemL z⟩).1) :=
      continuous_subtype_val.comp (e.symm.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val _))
    have hc : Continuous (fun z : {z : RP2 //
        (Quotient.mk _ (.inl z) : Wedge RP2 RP2 rpBase rpBase) ∈
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U} ↦
        Quotient.mk (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ))
        (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift z.1, i))) := by
      apply continuous_coinduced_rng.comp
      apply continuous_inl.comp
      simpa only [hLiftL] using hy.prodMk continuous_const
    simpa only [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S,
      Quotient.lift_mk] using hc
  · have hy : Continuous (fun z : {z : RP2 //
        (Quotient.mk _ (.inr z) : Wedge RP2 RP2 rpBase rpBase) ∈
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U} ↦
        (e.symm ⟨z.1, hmemR z⟩).1) :=
      continuous_subtype_val.comp (e.symm.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val _))
    have hc : Continuous (fun z : {z : RP2 //
        (Quotient.mk _ (.inr z) : Wedge RP2 RP2 rpBase rpBase) ∈
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U} ↦
        Quotient.mk (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ))
        (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift z.1, i))) := by
      apply continuous_coinduced_rng.comp
      apply continuous_inr.comp
      simpa only [hLiftR] using hy.prodMk continuous_const
    simpa only [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S,
      Quotient.lift_mk] using hc

/-- The range of sheet `i` is open: its preimage in the raw sum is
`{inl (y, i), inl (-y, σ i), inr (y, i), inr (-y, τ i) | 0 < y₀}` (classify the
`EqvGen` classes, e.g. via `_aux_index` and `_aux_invariant`). -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_range_open (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ) (i : Fin 4) :
    IsOpen (Set.range (fun u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1)) := by
  let V : Set ((Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4)) :=
    {z | Sum.elim
      (fun z ↦ (0 < (z.1 : EuclideanSpace ℝ (Fin 3)) 0 ∧ z.2 = i) ∨
        ((z.1 : EuclideanSpace ℝ (Fin 3)) 0 < 0 ∧ z.2 = σ i))
      (fun z ↦ (0 < (z.1 : EuclideanSpace ℝ (Fin 3)) 0 ∧ z.2 = i) ∨
        ((z.1 : EuclideanSpace ℝ (Fin 3)) 0 < 0 ∧ z.2 = τ i)) z}
  have hVopen : IsOpen V := by
    rw [isOpen_sum_iff]
    constructor <;> simp only [V, Set.preimage_setOf_eq]
    · have hc : Continuous (fun z : Sphere2 × Fin 4 ↦
          (z.1 : EuclideanSpace ℝ (Fin 3)) 0) :=
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) 0).comp
          (continuous_subtype_val.comp continuous_fst)
      exact ((isOpen_lt continuous_const hc).and
          ((isOpen_discrete ({i} : Set (Fin 4))).preimage continuous_snd)).union
        ((isOpen_lt hc continuous_const).and
          ((isOpen_discrete ({σ i} : Set (Fin 4))).preimage continuous_snd))
    · have hc : Continuous (fun z : Sphere2 × Fin 4 ↦
          (z.1 : EuclideanSpace ℝ (Fin 3)) 0) :=
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) 0).comp
          (continuous_subtype_val.comp continuous_fst)
      exact ((isOpen_lt continuous_const hc).and
          ((isOpen_discrete ({i} : Set (Fin 4))).preimage continuous_snd)).union
        ((isOpen_lt hc continuous_const).and
          ((isOpen_discrete ({τ i} : Set (Fin 4))).preimage continuous_snd))
  have hVinvar {a b : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4)}
      (h : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ) a b) :
      a ∈ V ↔ b ∈ V := by
    induction h with
    | rel a b h =>
        cases h with
        | left x k =>
            change ((0 < (x : EuclideanSpace ℝ (Fin 3)) 0 ∧ k = i) ∨
              ((x : EuclideanSpace ℝ (Fin 3)) 0 < 0 ∧ k = σ i)) ↔
              (0 < -((x : EuclideanSpace ℝ (Fin 3)) 0) ∧ σ k = i) ∨
              (-((x : EuclideanSpace ℝ (Fin 3)) 0) < 0 ∧ σ k = σ i)
            constructor <;> rintro (h | h)
            · right; exact ⟨by linarith [h.1], congrArg σ h.2⟩
            · left; exact ⟨by linarith [h.1], by simpa [hσ k, hσ i] using congrArg σ h.2⟩
            · right; exact ⟨by linarith [h.1], by simpa [hσ k, hσ i] using congrArg σ h.2⟩
            · left; exact ⟨by linarith [h.1], by simpa [hσ k, hσ i] using congrArg σ h.2⟩
        | right x k =>
            change ((0 < (x : EuclideanSpace ℝ (Fin 3)) 0 ∧ k = i) ∨
              ((x : EuclideanSpace ℝ (Fin 3)) 0 < 0 ∧ k = τ i)) ↔
              (0 < -((x : EuclideanSpace ℝ (Fin 3)) 0) ∧ τ k = i) ∨
              (-((x : EuclideanSpace ℝ (Fin 3)) 0) < 0 ∧ τ k = τ i)
            constructor <;> rintro (h | h)
            · right; exact ⟨by linarith [h.1], congrArg τ h.2⟩
            · left; exact ⟨by linarith [h.1], by simpa [hτ k, hτ i] using congrArg τ h.2⟩
            · right; exact ⟨by linarith [h.1], by simpa [hτ k, hτ i] using congrArg τ h.2⟩
            · left; exact ⟨by linarith [h.1], by simpa [hτ k, hτ i] using congrArg τ h.2⟩
        | glue k => norm_num [V, rp2Wedge_regular_four_cover_aux_e0]
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let q : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4) → rp2Wedge_regular_four_cover_aux_E σ τ :=
    fun z ↦ Quotient.mk _ z
  have hsat : q ⁻¹' (q '' V) = V := by
    ext z
    constructor
    · rintro ⟨w, hw, he⟩
      exact (hVinvar (Quotient.exact he)).mp hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hrange : Set.range (fun u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U ↦
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1) = q '' V := by
    ext e
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨y, hy, s, hs⟩ := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S_mem σ τ u.1 u.2
      refine ⟨s.casesOn (.inl (y, i)) (.inr (y, i)), ?_, (hs i).symm⟩
      cases s <;> exact Or.inl ⟨hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      cases z with
      | inl z =>
          rcases z with ⟨x, k⟩
          rcases hz with h | h
          · have hk : k = i := h.2; subst k
            let u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U :=
              ⟨Quotient.mk _ (Sum.inl (antipodalCover x)), ⟨x, h.1, Or.inl rfl⟩⟩
            refine ⟨u, ?_⟩
            change Quotient.mk _ (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover x), i)) = _
            rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos x h.1]
          · let y : Sphere2 := -x
            have hy : 0 < (y : EuclideanSpace ℝ (Fin 3)) 0 := by change 0 < -((x : EuclideanSpace ℝ (Fin 3)) 0); linarith [h.1]
            let u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U :=
              ⟨Quotient.mk _ (.inl (antipodalCover y)), ⟨y, hy, Or.inl rfl⟩⟩
            refine ⟨u, ?_⟩
            change Quotient.mk _ (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), i)) = _
            rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy]
            have hk : k = σ i := h.2
            apply Quotient.sound
            subst k
            simpa [y] using Relation.EqvGen.rel _ _ (rp2Wedge_regular_four_cover_aux_Rel.left y i)
      | inr z =>
          rcases z with ⟨x, k⟩
          rcases hz with h | h
          · have hk : k = i := h.2; subst k
            let u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U :=
              ⟨Quotient.mk _ (Sum.inr (antipodalCover x)), ⟨x, h.1, Or.inr rfl⟩⟩
            refine ⟨u, ?_⟩
            change Quotient.mk _ (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover x), i)) = _
            rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos x h.1]
          · let y : Sphere2 := -x
            have hy : 0 < (y : EuclideanSpace ℝ (Fin 3)) 0 := by change 0 < -((x : EuclideanSpace ℝ (Fin 3)) 0); linarith [h.1]
            let u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U :=
              ⟨Quotient.mk _ (.inr (antipodalCover y)), ⟨y, hy, Or.inr rfl⟩⟩
            refine ⟨u, ?_⟩
            change Quotient.mk _ (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), i)) = _
            rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy]
            have hk : k = τ i := h.2
            apply Quotient.sound
            subst k
            simpa [y] using Relation.EqvGen.rel _ _ (rp2Wedge_regular_four_cover_aux_Rel.right y i)
  rw [hrange]
  apply (isQuotientMap_quotient_mk' : Topology.IsQuotientMap q).isOpen_preimage.mp
  change IsOpen (q ⁻¹' (q '' V))
  rw [hsat]
  exact hVopen

/-- The sheets exhaust `p ⁻¹' U`: a representative `inl (x, k)` over `U` has
`x = y` or `x = -y` with `0 < y₀`; in the second case it is `[inl (y, σ k)]`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover_aux_base
    {u v : RP2 ⊕ RP2}
    (h : (Quotient.mk _ u : Wedge RP2 RP2 rpBase rpBase) = Quotient.mk _ v) :
    Sum.elim id id u = Sum.elim id id v := by
  rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous_aux_eqv
    rpBase rpBase u v).mp (Quotient.exact h) with huv | ⟨hu, hv⟩
  · simpa [huv]
  · rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp_all

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (e : rp2Wedge_regular_four_cover_aux_E σ τ)
    (he : rp2Wedge_regular_four_cover_aux_p σ τ e ∈ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U) :
    ∃ i, ∃ u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U, rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1 = e := by
  induction e using Quotient.inductionOn with
  | _ z =>
    rcases he with ⟨y, hy, hw | hw⟩
    · change rp2Wedge_regular_four_cover_aux_proj z = Quotient.mk _ (Sum.inl (antipodalCover y)) at hw
      cases z with
      | inl z => exact cover_inl z y hy (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover_aux_base hw)
      | inr z => exact cover_inr z y hy (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover_aux_base hw)
    · change rp2Wedge_regular_four_cover_aux_proj z = Quotient.mk _ (Sum.inr (antipodalCover y)) at hw
      cases z with
      | inl z => exact cover_inl z y hy (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover_aux_base hw)
      | inr z => exact cover_inr z y hy (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover_aux_base hw)
  where
    cover_inl (z : Sphere2 × Fin 4) (y : Sphere2)
        (hy : 0 < (y : EuclideanSpace ℝ (Fin 3)) 0)
        (hxy : antipodalCover z.1 = antipodalCover y) :
        ∃ i, ∃ u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U,
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1 =
            Quotient.mk (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ)) (Sum.inl z) := by
      rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff y z.1).mp hxy.symm with hx | hx
      · refine ⟨z.2, ⟨_, ⟨y, hy, Or.inl rfl⟩⟩, ?_⟩
        change Quotient.mk _ (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), z.2)) = Quotient.mk _ (Sum.inl z)
        rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy,
          ← Prod.eta z, hx]
      · refine ⟨σ z.2, ⟨_, ⟨y, hy, Or.inl rfl⟩⟩, ?_⟩
        change Quotient.mk _ (Sum.inl (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), σ z.2)) = Quotient.mk _ (Sum.inl z)
        rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy]
        apply Quotient.sound
        rw [← Prod.eta z, hx]
        simpa only [hσ z.2] using Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ) y (σ z.2))
    cover_inr (z : Sphere2 × Fin 4) (y : Sphere2)
        (hy : 0 < (y : EuclideanSpace ℝ (Fin 3)) 0)
        (hxy : antipodalCover z.1 = antipodalCover y) :
        ∃ i, ∃ u : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U,
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1 =
            Quotient.mk (Relation.EqvGen.setoid (rp2Wedge_regular_four_cover_aux_Rel σ τ)) (Sum.inr z) := by
      rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff y z.1).mp hxy.symm with hx | hx
      · refine ⟨z.2, ⟨_, ⟨y, hy, Or.inr rfl⟩⟩, ?_⟩
        change Quotient.mk _ (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), z.2)) = Quotient.mk _ (Sum.inr z)
        rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy,
          ← Prod.eta z, hx]
      · refine ⟨τ z.2, ⟨_, ⟨y, hy, Or.inr rfl⟩⟩, ?_⟩
        change Quotient.mk _ (Sum.inr (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift (antipodalCover y), τ z.2)) = Quotient.mk _ (Sum.inr z)
        rw [rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_lift_pos y hy]
        apply Quotient.sound
        rw [← Prod.eta z, hx]
        simpa only [hτ z.2] using Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ) y (τ z.2))

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ) :
    ∃ U : Set (Wedge RP2 RP2 rpBase rpBase),
      Quotient.mk _ (.inl rpBase) ∈ U ∧ IsOpen U ∧
      ∃ s : Fin 4 → U → rp2Wedge_regular_four_cover_aux_E σ τ,
        (∀ i, Continuous (s i)) ∧
        (∀ i u, rp2Wedge_regular_four_cover_aux_p σ τ (s i u) = u) ∧
        (∀ i, IsOpen (Set.range (s i))) ∧
        (∀ e, rp2Wedge_regular_four_cover_aux_p σ τ e ∈ U → ∃ i u, s i u = e) ∧
        (∀ i j u v, s i u = s j v → i = j) := by
  refine ⟨rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U, ⟨rp2Wedge_regular_four_cover_aux_e0,
      by simp [rp2Wedge_regular_four_cover_aux_e0], Or.inl rfl⟩, rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open,
    fun i u ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S σ τ i u.1, fun i ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_continuous σ τ i,
    fun i u ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_p_S σ τ i u.1, fun i ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_range_open σ τ hσ hτ i,
    fun e he ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_cover σ τ hσ hτ e he, ?_⟩
  intro i j u v h
  obtain ⟨x, hx, sx, hu⟩ := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S_mem σ τ u.1 u.2
  obtain ⟨y, hy, sy, hv⟩ := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_S_mem σ τ v.1 v.2
  simp only at h
  rw [hu, hv] at h
  exact rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_index σ τ hσ hτ x y i j hx hy sx sy h

/-! #### Split of `rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away` (lemma-2 PARTIAL, 2026-10-19) -/

/-- Every non-wedge point is the image of a sphere point in one lobe, with
projective image different from `rpBase`.  (Banked by lemma-2.) -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_rep
    (x : Wedge RP2 RP2 rpBase rpBase)
    (hx : x ≠ Quotient.mk _ (.inl rpBase)) :
    (∃ u : Sphere2, x = Quotient.mk _ (.inl (antipodalCover u)) ∧
      antipodalCover u ≠ rpBase) ∨
    (∃ u : Sphere2, x = Quotient.mk _ (.inr (antipodalCover u)) ∧
      antipodalCover u ≠ rpBase) := by
  induction x using Quotient.inductionOn with
  | _ z =>
    cases z with
    | inl q =>
      induction q using Quotient.inductionOn with
      | _ u =>
        left
        refine ⟨u, rfl, ?_⟩
        intro hu
        apply hx
        exact congrArg (fun q : RP2 ↦ Quotient.mk _ (Sum.inl q : Sum RP2 RP2)) hu
    | inr q =>
      induction q using Quotient.inductionOn with
      | _ u =>
        right
        refine ⟨u, rfl, ?_⟩
        intro hu
        apply hx
        exact (congrArg (fun q : RP2 ↦ Quotient.mk _ (Sum.inr q : Sum RP2 RP2)) hu).trans
          (Quotient.sound (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ WedgeRel.base)))

/-- The open cap `{y | 0 < ⟪y, u⟫}` with the two points `±e₀` removed embeds
openly in `RP2` (it is open, disjoint from its antipode, and `antipodalCover` is
an open map since the saturation of an open `W` is `W ∪ -W`). -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_cap (u : Sphere2) :
    Topology.IsOpenEmbedding
      (fun y : {y : Sphere2 // 0 < inner ℝ (y : EuclideanSpace ℝ (Fin 3)) u ∧
          antipodalCover y ≠ rpBase} ↦ antipodalCover y.1) := by
  let C : Set Sphere2 :=
    {y | 0 < inner ℝ (y : EuclideanSpace ℝ (Fin 3)) u ∧
      antipodalCover y ≠ rpBase}
  let f : C → RP2 := fun y ↦ antipodalCover y.1
  have hC : IsOpen C := by
    have hi : Continuous (fun y : Sphere2 ↦
        inner ℝ (y : EuclideanSpace ℝ (Fin 3)) u) :=
      (continuous_subtype_val.inner continuous_const)
    have hb : IsOpen {y : Sphere2 | antipodalCover y ≠ rpBase} := by
      have he : {y : Sphere2 | antipodalCover y ≠ rpBase} =
          ({rp2Wedge_regular_four_cover_aux_e0,
            -rp2Wedge_regular_four_cover_aux_e0} : Set Sphere2)ᶜ := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        constructor
        · intro hn hcases
          apply hn
          rcases hcases with rfl | rfl
          · exact rp2Wedge_regular_four_cover_aux_rpBase.symm
          · exact (rp2Wedge_regular_four_cover_aux_neg
              rp2Wedge_regular_four_cover_aux_e0).trans
              rp2Wedge_regular_four_cover_aux_rpBase.symm
        · intro hn heq
          apply hn
          rw [rp2Wedge_regular_four_cover_aux_rpBase] at heq
          rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff
            rp2Wedge_regular_four_cover_aux_e0 y).mp heq.symm with h | h
          · exact Or.inl h
          · exact Or.inr h
      rw [he]
      exact (Set.toFinite _).isClosed.isOpen_compl
    exact (isOpen_lt continuous_const hi).inter hb
  have hneg : Continuous (fun y : Sphere2 ↦ -y) := continuous_neg
  have hf_cont : Continuous f := continuous_coinduced_rng.comp continuous_subtype_val
  have hf_inj : Function.Injective f := by
    intro x y hxy
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff x.1 y.1).mp hxy with h | h
    · exact Subtype.ext h.symm
    · exfalso
      have hx := x.property.1
      have hy := y.property.1
      rw [h] at hy
      change 0 < inner ℝ (-(x.1 : EuclideanSpace ℝ (Fin 3))) u at hy
      simp only [inner_neg_left] at hy
      linarith
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf_cont hf_inj ?_
  intro S hS
  obtain ⟨T, hT, rfl⟩ := isOpen_induced_iff.mp hS
  rw [isOpen_coinduced]
  have heq : antipodalCover ⁻¹' (f '' (Subtype.val ⁻¹' T)) =
      (T ∩ C) ∪ (fun y : Sphere2 ↦ -y) ⁻¹' (T ∩ C) := by
    ext y
    constructor
    · rintro ⟨z, hzT, hz⟩
      have hz' : antipodalCover z.1 = antipodalCover y := by simpa [f] using hz
      rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff z.1 y).mp hz' with h | h
      · left
        simpa [h, C] using And.intro hzT z.property
      · right
        have : -y = z.1 := by simpa [h]
        change -y ∈ T ∩ C
        simpa [this] using And.intro hzT z.property
    · intro hy
      rcases hy with hy | hy
      · refine ⟨⟨y, hy.2⟩, hy.1, rfl⟩
      · change -y ∈ T ∩ C at hy
        refine ⟨⟨-y, hy.2⟩, hy.1, ?_⟩
        change antipodalCover (-y) = antipodalCover y
        exact rp2Wedge_regular_four_cover_aux_neg y
  change IsOpen (antipodalCover ⁻¹' (f '' (Subtype.val ⁻¹' T)))
  rw [heq]
  exact (hT.inter hC).union ((hT.inter hC).preimage hneg)

/-- An open subset of the left lobe missing the base point embeds openly in the
wedge: its preimage in `A ⊕ B` is `inl '' V`, already saturated. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl_aux_eqv
    {A B : Type*} (a : A) (b : B) (u v : Sum A B) :
    Relation.EqvGen (WedgeRel a b) u v ↔
      u = v ∨ ((u = .inl a ∨ u = .inr b) ∧ (v = .inl a ∨ v = .inr b)) := by
  constructor
  · intro h
    induction h with
    | rel u v h => cases h; exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    | refl => exact Or.inl rfl
    | symm u v _ ih =>
        rcases ih with rfl | ⟨h₁, h₂⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h₂, h₁⟩
    | trans u v w _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨h₁, h₂⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨_, h₃⟩
          · exact Or.inr ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₁, h₃⟩
  · rintro (rfl | ⟨h₁, h₂⟩)
    · exact Relation.EqvGen.refl _
    · have hab : Relation.EqvGen (WedgeRel a b) (.inl a) (.inr b) :=
        Relation.EqvGen.rel _ _ WedgeRel.base
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact Relation.EqvGen.refl _
      · exact hab
      · exact Relation.EqvGen.symm _ _ hab
      · exact Relation.EqvGen.refl _

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (V : Set A) (hV : IsOpen V) (ha : a ∉ V) :
    Topology.IsOpenEmbedding
      (fun z : V ↦ (Quotient.mk _ (.inl z.1) : Wedge A B a b)) := by
  rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨continuous_quotient_mk'.comp
      (continuous_inl.comp continuous_subtype_val), ?_, ?_⟩
  · intro x y hxy
    have he := Quotient.exact hxy
    rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl_aux_eqv
      a b (.inl x.1) (.inl y.1)).mp he with h | ⟨hx, _⟩
    · exact Subtype.ext (Sum.inl.inj h)
    · rcases hx with hx | hx
      · exact (ha ((Sum.inl.inj hx) ▸ x.2)).elim
      · cases hx
  · intro S hS
    let W : Set (Sum A B) := Sum.inl '' (Subtype.val '' S)
    have hW : IsOpen W := by
      exact isOpenMap_inl _ (hV.isOpenMap_subtype_val S hS)
    have hpre :
        (fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) ⁻¹'
            ((fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) '' W) = W := by
      ext z
      constructor
      · rintro ⟨w, hw, he⟩
        rcases hw with ⟨_, ⟨sx, hsx, rfl⟩, rfl⟩
        have hr := Quotient.exact he
        rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl_aux_eqv
          a b (.inl sx.1) z).mp hr with hz | ⟨hx, _⟩
        · exact hz ▸ ⟨sx.1, ⟨sx, hsx, rfl⟩, rfl⟩
        · rcases hx with hx | hx
          · exact (ha ((Sum.inl.inj hx) ▸ sx.property)).elim
          · cases hx
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hopen : IsOpen
        ((fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) '' W) := by
      rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
      change IsOpen
        ((fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) ⁻¹'
          ((fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) '' W))
      rw [hpre]
      exact hW
    simpa [W, Set.image_image] using hopen

/-- The same for the right lobe. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inr_aux_eq
    {A B : Type*} (a : A) (b x : B) (hx : x ≠ b)
    {z : Sum A B}
    (h : Relation.EqvGen (WedgeRel a b) (.inr x) z) :
    z = .inr x := by
  have hinv : ∀ {u v : Sum A B},
      Relation.EqvGen (WedgeRel a b) u v →
        (u = .inr x ↔ v = .inr x) := by
    intro u v huv
    induction huv with
    | rel u v huv =>
        cases huv
        simp [hx, Ne.symm hx]
    | refl => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hinv h).mp rfl

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inr
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (V : Set B) (hV : IsOpen V) (hb : b ∉ V) :
    Topology.IsOpenEmbedding
      (fun z : V ↦ (Quotient.mk _ (.inr z.1) : Wedge A B a b)) := by
  rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨continuous_quot_mk.comp (continuous_inr.comp continuous_subtype_val), ?_, ?_⟩
  · intro x y hxy
    have hrel : Relation.EqvGen (WedgeRel a b) (.inr x.1) (.inr y.1) :=
      Quotient.exact hxy
    have hx : x.1 ≠ b := fun hxb ↦ hb (hxb ▸ x.2)
    have heq :=
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inr_aux_eq
        a b x.1 hx hrel
    exact Subtype.ext (Sum.inr.inj heq.symm)
  · intro U hU
    let W : Set B := Subtype.val '' U
    have hW : IsOpen W := hV.isOpenMap_subtype_val U hU
    have hpre :
        (fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) ⁻¹'
            ((fun z : V ↦ (Quotient.mk _ (.inr z.1) : Wedge A B a b)) '' U) =
          Sum.inr '' W := by
      ext z
      constructor
      · rintro ⟨u, hu, heq⟩
        have hrel : Relation.EqvGen (WedgeRel a b) (.inr u.1) z :=
          Quotient.exact heq
        have hu_ne : u.1 ≠ b := fun hub ↦ hb (hub ▸ u.2)
        have hz :=
          rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inr_aux_eq
            a b u.1 hu_ne hrel
        exact ⟨u.1, ⟨u, hu, rfl⟩, hz.symm⟩
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, rfl⟩
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    change IsOpen
      ((fun z : Sum A B ↦ (Quotient.mk _ z : Wedge A B a b)) ⁻¹'
        ((fun z : V ↦ (Quotient.mk _ (.inr z.1) : Wedge A B a b)) '' U))
    rw [hpre]
    exact isOpenMap_inr W hW

/-! #### Split of `rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl` (lemma-3 PARTIAL, 2026-10-19) -/

/-- The cap point `u` itself lies in the cap.  (Banked by lemma-3.) -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_mem_cap
    (u : Sphere2) (hu : antipodalCover u ≠ rpBase) :
    0 < inner ℝ (u : EuclideanSpace ℝ (Fin 3)) u ∧
      antipodalCover u ≠ rpBase := by
  refine ⟨?_, hu⟩
  rw [real_inner_self_eq_norm_sq]
  norm_num [u.property]

/-- The cap of `_aux_cap`: `{y | 0 < ⟪y, u⟫}` with `±e₀` removed. -/
def rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_C (u : Sphere2) : Set Sphere2 :=
  {y | 0 < inner ℝ (y : EuclideanSpace ℝ (Fin 3)) u ∧ antipodalCover y ≠ rpBase}

/-- The cap mapped into the left lobe of the wedge. -/
def rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb (u : Sphere2) :
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_C u → Wedge RP2 RP2 rpBase rpBase :=
  fun y ↦ Quotient.mk _ (.inl (antipodalCover y.1))

/-- `_aux_cap` followed by `_aux_lobe_inl`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb_isOpenEmbedding (u : Sphere2) :
    Topology.IsOpenEmbedding (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb u) := by
  have hg := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_cap u
  have hV : IsOpen (Set.range (fun y : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_C u ↦ antipodalCover y.1)) :=
    hg.isOpen_range
  have hb : rpBase ∉ Set.range (fun y : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_C u ↦ antipodalCover y.1) := by
    rintro ⟨y, hy⟩
    exact y.2.2 hy
  have hh := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl
    rpBase rpBase _ hV hb
  exact hh.comp hg.toIsEmbedding.toHomeomorph.isOpenEmbedding

/-- Sheet `i` over the cap: `y ↦ [inl (y, i)]`. -/
def rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet (σ τ : Equiv.Perm (Fin 4)) (u : Sphere2) (i : Fin 4) :
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_C u → rp2Wedge_regular_four_cover_aux_E σ τ :=
  fun y ↦ Quotient.mk _ (.inl (y.1, i))

/-- **Leaf.** The range of a sheet is open: its preimage in the raw sum is
`{inl (y, i), inl (-y, σ i) | y in the cap}` (saturated: `σ` is involutive and
the cap misses `±e₀`, so no glue applies), open in `inl`. -/
-- BEGIN SEAT AREA
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_range_open
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (u : Sphere2) (i : Fin 4) :
    IsOpen (Set.range (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u i)) := by
  sorry
-- END SEAT AREA

/-- **Leaf.** Every point over the image of the cap is on some sheet: a lift of
`[inl [y]]` with `y` in the cap is `[inl (y', j)]` with `y' = ±y`; if `y' = -y`
it equals `[inl (y, σ j)]`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_cover
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (u : Sphere2) (e : rp2Wedge_regular_four_cover_aux_E σ τ)
    (he : rp2Wedge_regular_four_cover_aux_p σ τ e ∈ Set.range (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb u)) :
    ∃ i y, rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u i y = e := by
  sorry

/-- **Leaf.** Distinct sheets do not meet: `(y, i) ∼ (y', j)` in the left lobe
off `±e₀` forces `y' = y, j = i` or `y' = -y, j = σ i`, and the cap is disjoint
from its antipode. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_disjoint
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (u : Sphere2) (i j : Fin 4) (y y' : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_C u)
    (h : rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u i y = rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u j y') :
    i = j := by
  sorry

/-- The four sheets over a left-lobe point `[inl (antipodalCover u)] ≠` wedge
point.  `U` is the image under `_aux_lobe_inl` of the image under `_aux_cap u` of
the cap; sheet `i` sends `[inl (antipodalCover y)]` (`y` in the cap) to
`[inl (y, i)]`.  Continuity: `U` is homeomorphic to the cap by the two open
embeddings.  The range of sheet `i` is the class of
`{inl (y, i), inl (-y, σ i) | y in the cap}` (saturated since `σ` is involutive
and the cap misses `e₀`, so no glue applies), open in the raw sum; the four
ranges are disjoint because `(y, i) ∼ (y', j)` with `y, y'` in the cap forces
`y = y'`, `i = j` (the cap is disjoint from its antipode). -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (u : Sphere2) (hu : antipodalCover u ≠ rpBase) :
    ∃ U : Set (Wedge RP2 RP2 rpBase rpBase),
      Quotient.mk _ (.inl (antipodalCover u)) ∈ U ∧ IsOpen U ∧
      ∃ s : Fin 4 → U → rp2Wedge_regular_four_cover_aux_E σ τ,
        (∀ i, Continuous (s i)) ∧
        (∀ i u, rp2Wedge_regular_four_cover_aux_p σ τ (s i u) = u) ∧
        (∀ i, IsOpen (Set.range (s i))) ∧
        (∀ e, rp2Wedge_regular_four_cover_aux_p σ τ e ∈ U → ∃ i u, s i u = e) ∧
        (∀ i j u v, s i u = s j v → i = j) := by
  have hemb := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb_isOpenEmbedding u
  let Φ := hemb.toIsEmbedding.toHomeomorph
  refine ⟨Set.range (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb u),
    ⟨⟨u, rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_mem_cap u hu⟩, rfl⟩, hemb.isOpen_range,
    fun i w ↦ rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u i (Φ.symm w), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact continuous_coinduced_rng.comp (continuous_inl.comp
      ((continuous_subtype_val.comp Φ.symm.continuous).prodMk continuous_const))
  · intro i w
    change rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_emb u (Φ.symm w) = w
    exact congrArg Subtype.val (Φ.apply_symm_apply w)
  · intro i
    change IsOpen (Set.range (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u i ∘ Φ.symm))
    rw [Φ.symm.surjective.range_comp (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_sheet σ τ u i)]
    exact rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_range_open σ τ hσ hτ u i
  · intro e he
    obtain ⟨i, y, hy⟩ := rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_cover σ τ hσ hτ u e
      (by simpa using he)
    exact ⟨i, Φ y, by simpa using hy⟩
  · intro i j w v h
    exact rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl_aux_disjoint σ τ hσ hτ u i j _ _ h

/-- The same over a right-lobe point, with `τ` and `_aux_lobe_inr`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inr
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (u : Sphere2) (hu : antipodalCover u ≠ rpBase) :
    ∃ U : Set (Wedge RP2 RP2 rpBase rpBase),
      Quotient.mk _ (.inr (antipodalCover u)) ∈ U ∧ IsOpen U ∧
      ∃ s : Fin 4 → U → rp2Wedge_regular_four_cover_aux_E σ τ,
        (∀ i, Continuous (s i)) ∧
        (∀ i u, rp2Wedge_regular_four_cover_aux_p σ τ (s i u) = u) ∧
        (∀ i, IsOpen (Set.range (s i))) ∧
        (∀ e, rp2Wedge_regular_four_cover_aux_p σ τ e ∈ U → ∃ i u, s i u = e) ∧
        (∀ i j u v, s i u = s j v → i = j) := by
  sorry

/-- **LIBRARY.** The glued projection is a covering map.  Charts: away from the
wedge point, over the image `V` of an open set of `Sphere2` disjoint from its
antipode, the preimage is four copies of `V` in one lobe; at the wedge point,
take `V` = images of small caps around `±e₀` in both lobes, whose preimage is
four wedges of two caps, one per fibre point `[(e₀, i)]`. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (x : Wedge RP2 RP2 rpBase rpBase)
    (hx : x ≠ Quotient.mk _ (.inl rpBase)) :
    IsEvenlyCovered (rp2Wedge_regular_four_cover_aux_p σ τ) x
      ((rp2Wedge_regular_four_cover_aux_p σ τ) ⁻¹' {x}) := by
  rcases rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_rep x hx with
    ⟨u, rfl, hu⟩ | ⟨u, rfl, hu⟩
  · obtain ⟨U, hxU, hU, s, hs, hfs, hopen, hcover, hdisj⟩ :=
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inl
        σ τ hσ hτ u hu
    exact (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections
      (ι := Fin 4) _
      (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_continuous σ τ)
      _ U hxU hU s hs hfs hopen hcover hdisj).to_isEvenlyCovered_preimage
  · obtain ⟨U, hxU, hU, s, hs, hfs, hopen, hcover, hdisj⟩ :=
      rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_sections_inr
        σ τ hσ hτ u hu
    exact (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections
      (ι := Fin 4) _
      (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_continuous σ τ)
      _ U hxU hU s hs hfs hopen hcover hdisj).to_isEvenlyCovered_preimage

lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge
    (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ) :
    IsEvenlyCovered (rp2Wedge_regular_four_cover_aux_p σ τ)
      (Quotient.mk _ (.inl rpBase))
      ((rp2Wedge_regular_four_cover_aux_p σ τ) ⁻¹'
        {Quotient.mk _ (.inl rpBase)}) := by
  obtain ⟨U, hxU, hU, s, hs, hfs, hopen, hcover, hdisj⟩ :=
    rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections σ τ hσ hτ
  exact (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections
    (ι := Fin 4) _
    (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_continuous σ τ)
    _ U hxU hU s hs hfs hopen hcover hdisj).to_isEvenlyCovered_preimage

theorem rp2Wedge_regular_four_cover_aux_isCoveringMap (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ) :
    IsCoveringMap (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  intro x
  classical
  by_cases hx : x = Quotient.mk _ (.inl rpBase)
  · subst x
    exact rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge σ τ hσ hτ
  · exact rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away σ τ hσ hτ x hx

/-! #### Split of `rp2Wedge_regular_four_cover_aux_card` (lemma-2 PARTIAL, 2026-10-18) -/

/-- An invariant of the sheets that respects the gluing descends through the
equivalence relation (banked from lemma-2).  Used for injectivity of the
fibre parametrisations: choose `fL`, `fR` recording the sheet index. -/
lemma rp2Wedge_regular_four_cover_aux_card_aux_invariant
    {α : Type*} (σ τ : Equiv.Perm (Fin 4))
    (fL fR : Sphere2 × Fin 4 → α)
    (hL : ∀ x i, fL (-x, σ i) = fL (x, i))
    (hR : ∀ x i, fR (-x, τ i) = fR (x, i))
    (hG : ∀ i, fL (rp2Wedge_regular_four_cover_aux_e0, i) =
      fR (rp2Wedge_regular_four_cover_aux_e0, i))
    {a b : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4)}
    (h : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ) a b) :
    Sum.elim fL fR a = Sum.elim fL fR b := by
  induction h with
  | rel a b h =>
      cases h with
      | left x i => exact (hL x i).symm
      | right x i => exact (hR x i).symm
      | glue i => exact hG i
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The wedge relation identifies only the two base points. -/
lemma rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff {A B : Type*}
    (a : A) (b : B) (u v : Sum A B) :
    Relation.EqvGen (WedgeRel a b) u v ↔
      u = v ∨ ((u = .inl a ∨ u = .inr b) ∧ (v = .inl a ∨ v = .inr b)) := by
  constructor
  · intro h
    induction h with
    | rel u v h => cases h; exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    | refl => exact Or.inl rfl
    | symm u v _ ih =>
        rcases ih with rfl | ⟨h₁, h₂⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h₂, h₁⟩
    | trans u v w _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨h₁, h₂⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨_, h₃⟩
          · exact Or.inr ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₁, h₃⟩
  · rintro (rfl | ⟨h₁, h₂⟩)
    · exact Relation.EqvGen.refl _
    · have hab : Relation.EqvGen (WedgeRel a b) (.inl a) (.inr b) :=
        Relation.EqvGen.rel _ _ WedgeRel.base
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact Relation.EqvGen.refl _
      · exact hab
      · exact Relation.EqvGen.symm _ _ hab
      · exact Relation.EqvGen.refl _

/-- Fibre over a non-base point of the left lobe: `i ↦ [inl (x, i)]` is a
bijection from `Fin 4`.  Surjective: a preimage is `[inl (y, j)]` with
`y = ±x` (by `_aux_card_aux_wedge_eqvGen_iff`, the point is not the wedge
point, and `_aux_cover_eq_iff`), and `[inl (-x, j)] = [inl (x, σ j)]` since
`σ` is an involution.  Injective: `_aux_card_aux_invariant` with
`fL (y, k) = if y = x then k else if y = -x then σ k else 0`, `fR = 0`
(`hG` holds because `e₀ ≠ ±x`). -/
theorem rp2Wedge_regular_four_cover_aux_card_aux_left (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (x : Sphere2) (hx : antipodalCover x ≠ rpBase) :
    Nat.card {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inl (antipodalCover x))} = 4 := by
  have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have := x.property
    simp [h] at this
  have hxx : (-x : Sphere2) ≠ x := by
    intro h
    apply hx0
    have h' : -(x : EuclideanSpace ℝ (Fin 3)) = x := congrArg Subtype.val h
    have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      rw [two_smul]
      simpa using
        (congrArg (fun z ↦ z + (x : EuclideanSpace ℝ (Fin 3))) h').symm
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  let fL : Sphere2 × Fin 4 → Fin 4 := fun z ↦
    if z.1 = x then z.2 else if z.1 = -x then σ z.2 else 0
  let fR : Sphere2 × Fin 4 → Fin 4 := fun _ ↦ 0
  have hL : ∀ y i, fL (-y, σ i) = fL (y, i) := by
    intro y i
    simp only [fL]
    by_cases hy : y = x
    · subst y
      simp [hxx, hσ i]
    by_cases hyn : y = -x
    · subst y
      simp [hxx, hσ i]
    have hny : -y ≠ x := by
      intro h
      apply hyn
      rw [← h]
      simp
    have hnyn : -y ≠ -x := by
      intro h
      apply hy
      exact neg_injective h
    simp [hy, hyn, hny, hnyn]
  have he0x : rp2Wedge_regular_four_cover_aux_e0 ≠ x := by
    intro h
    apply hx
    rw [← h, ← rp2Wedge_regular_four_cover_aux_rpBase]
  have he0nx : rp2Wedge_regular_four_cover_aux_e0 ≠ -x := by
    intro h
    apply hx
    exact (calc
      antipodalCover x = antipodalCover (-x) :=
        (rp2Wedge_regular_four_cover_aux_neg x).symm
      _ = antipodalCover rp2Wedge_regular_four_cover_aux_e0 := congrArg _ h.symm
      _ = rpBase := rp2Wedge_regular_four_cover_aux_rpBase.symm)
  have hG : ∀ i, fL (rp2Wedge_regular_four_cover_aux_e0, i) =
      fR (rp2Wedge_regular_four_cover_aux_e0, i) := by
    intro i
    simp [fL, fR, he0x, he0nx]
  let e : Fin 4 → {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inl (antipodalCover x))} := fun i ↦
    ⟨Quotient.mk _ (.inl (x, i)), rfl⟩
  have einj : Function.Injective e := by
    intro i j hij
    have hq : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ)
        (.inl (x, i)) (.inl (x, j)) := Quotient.exact (congrArg Subtype.val hij)
    have hi := rp2Wedge_regular_four_cover_aux_card_aux_invariant σ τ fL fR
      hL (by simp [fR]) hG hq
    simpa [fL] using hi
  have esurj : Function.Surjective e := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha⟩ := Quotient.exists_rep z
    subst z
    rcases a with ⟨y, i⟩ | ⟨y, i⟩
    · have hw : Relation.EqvGen (WedgeRel rpBase rpBase)
          (.inl (antipodalCover y)) (.inl (antipodalCover x)) :=
        Quotient.exact hz
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
          rpBase rpBase _ _).mp hw with h | h
      · have hc : antipodalCover y = antipodalCover x := Sum.inl.inj h
        rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff x y).mp hc.symm with rfl | rfl
        · exact ⟨i, rfl⟩
        · refine ⟨σ i, ?_⟩
          apply Subtype.ext
          apply Quotient.sound
          simpa using (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.left (-x) i :
              rp2Wedge_regular_four_cover_aux_Rel σ τ _ _)))
      · rcases h with ⟨_, hv⟩
        rcases hv with hv | hv
        · exact (hx (Sum.inl.inj hv)).elim
        · contradiction
    · have hw : Relation.EqvGen (WedgeRel rpBase rpBase)
          (.inr (antipodalCover y)) (.inl (antipodalCover x)) :=
        Quotient.exact hz
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
          rpBase rpBase _ _).mp hw with h | h
      · contradiction
      · rcases h with ⟨_, hv⟩
        rcases hv with hv | hv
        · exact (hx (Sum.inl.inj hv)).elim
        · contradiction
  rw [Nat.card_congr (Equiv.ofBijective e ⟨einj, esurj⟩).symm]
  simp

/-- Fibre over a non-base point of the right lobe; the mirror image of
`_aux_card_aux_left` with `τ` in place of `σ`. -/
theorem rp2Wedge_regular_four_cover_aux_card_aux_right (σ τ : Equiv.Perm (Fin 4))
    (hτ : Function.Involutive τ) (x : Sphere2) (hx : antipodalCover x ≠ rpBase) :
    Nat.card {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inr (antipodalCover x))} = 4 := by
  have hxneg : (-x : Sphere2) ≠ x := by
    intro h
    have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
      intro hx0
      have hs := x.property
      simp [hx0] at hs
    apply hx0
    have h' : -(x : EuclideanSpace ℝ (Fin 3)) = x := congrArg Subtype.val h
    have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      rw [two_smul]
      simpa using
        (congrArg (fun z ↦ z + (x : EuclideanSpace ℝ (Fin 3))) h').symm
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have he0x : rp2Wedge_regular_four_cover_aux_e0 ≠ x := by
    intro h
    apply hx
    rw [← h, ← rp2Wedge_regular_four_cover_aux_rpBase]
  have he0negx : rp2Wedge_regular_four_cover_aux_e0 ≠ -x := by
    intro h
    apply hx
    rw [← rp2Wedge_regular_four_cover_aux_neg x,
      ← h, ← rp2Wedge_regular_four_cover_aux_rpBase]
  let F : Sphere2 × Fin 4 → Fin 4 := fun z ↦
    if z.1 = x then z.2 else if z.1 = -x then τ z.2 else 0
  have hF : ∀ y i, F (-y, τ i) = F (y, i) := by
    intro y i
    by_cases hyx : y = x
    · subst y
      simp [F, hxneg, hτ i]
    · by_cases hynx : y = -x
      · subst y
        simp [F, hxneg, hτ i]
      · have hnyx : -y ≠ x := by
          intro h
          apply hynx
          simpa using congrArg Neg.neg h
        have hnynx : -y ≠ -x := by
          intro h
          apply hyx
          simpa using congrArg Neg.neg h
        simp [F, hyx, hynx, hnyx, hnynx]
  let f : Fin 4 → {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inr (antipodalCover x))} := fun i ↦
    ⟨Quotient.mk _ (.inr (x, i)), rfl⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hq : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ)
        (.inr (x, i)) (.inr (x, j)) :=
      Quotient.exact (congrArg Subtype.val hij)
    have hi := rp2Wedge_regular_four_cover_aux_card_aux_invariant σ τ
      (fun _ ↦ (0 : Fin 4)) F
      (by simp) hF (by intro k; simp [F, he0x, he0negx]) hq
    simpa [F] using hi
  have hf_surj : Function.Surjective f := by
    intro e
    obtain ⟨z, hz⟩ := Quotient.exists_rep e.1
    rcases z with ⟨y, i⟩ | ⟨y, i⟩
    · exfalso
      have hp := e.2
      rw [← hz] at hp
      change (Quotient.mk _ (.inl (antipodalCover y)) :
        Wedge RP2 RP2 rpBase rpBase) = Quotient.mk _ (.inr (antipodalCover x)) at hp
      have hw := (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inl (antipodalCover y)) (.inr (antipodalCover x))).mp
        (Quotient.exact hp)
      rcases hw with h | ⟨_, hr⟩
      · cases h
      · rcases hr with h | h
        · cases h
        · exact hx (Sum.inr.inj h)
    · have hp := e.2
      rw [← hz] at hp
      change (Quotient.mk _ (.inr (antipodalCover y)) :
        Wedge RP2 RP2 rpBase rpBase) = Quotient.mk _ (.inr (antipodalCover x)) at hp
      have hw := (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inr (antipodalCover y)) (.inr (antipodalCover x))).mp
        (Quotient.exact hp)
      have hc : antipodalCover y = antipodalCover x := by
        rcases hw with h | ⟨_, hr⟩
        · exact Sum.inr.inj h
        · rcases hr with h | h
          · cases h
          · exact (hx (Sum.inr.inj h)).elim
      rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff x y).mp hc.symm with rfl | rfl
      · exact ⟨i, Subtype.ext hz⟩
      · refine ⟨τ i, ?_⟩
        apply Subtype.ext
        apply (Quotient.sound (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.right x (τ i)))).trans
        simpa [hτ i] using hz
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm]
  simp

/-- Fibre over the wedge point: `i ↦ [inl (e₀, i)]` is a bijection from
`Fin 4`.  Surjective: a preimage is `[inl (±e₀, j)]` or `[inr (±e₀, j)]`;
these equal `[inl (e₀, j)]`, `[inl (e₀, σ j)]`, `[inl (e₀, j)]`,
`[inl (e₀, τ j)]` (involutions, then `glue`).  Injective:
`_aux_card_aux_invariant` with `fL (y, k) = if y = e₀ then k else if y = -e₀
then σ k else 0` and `fR` the same with `τ`. -/
theorem rp2Wedge_regular_four_cover_aux_card_aux_base (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ) :
    Nat.card {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inl rpBase)} = 4 := by
  let e0 := rp2Wedge_regular_four_cover_aux_e0
  have hne : (-e0 : Sphere2) ≠ e0 := by
    intro h
    have hval := congrArg (fun z : Sphere2 ↦ (z : EuclideanSpace ℝ (Fin 3))) h
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ z 0) hval
    norm_num [e0, rp2Wedge_regular_four_cover_aux_e0] at this
  let fL : Sphere2 × Fin 4 → Fin 4 := fun z ↦
    if z.1 = e0 then z.2 else if z.1 = -e0 then σ z.2 else 0
  let fR : Sphere2 × Fin 4 → Fin 4 := fun z ↦
    if z.1 = e0 then z.2 else if z.1 = -e0 then τ z.2 else 0
  have hL : ∀ x i, fL (-x, σ i) = fL (x, i) := by
    intro x i
    by_cases hx : x = e0
    · subst x
      simp [fL, hne, hσ i]
    · by_cases hx' : x = -e0
      · subst x
        simp [fL, hne, hσ i]
      · have hn₁ : -x ≠ e0 := by
          intro h
          apply hx'
          simpa using congrArg Neg.neg h
        have hn₂ : -x ≠ -e0 := by
          intro h
          apply hx
          simpa only [neg_inj] using h
        simp [fL, hx, hx', hn₁, hn₂]
  have hR : ∀ x i, fR (-x, τ i) = fR (x, i) := by
    intro x i
    by_cases hx : x = e0
    · subst x
      simp [fR, hne, hτ i]
    · by_cases hx' : x = -e0
      · subst x
        simp [fR, hne, hτ i]
      · have hn₁ : -x ≠ e0 := by
          intro h
          apply hx'
          simpa using congrArg Neg.neg h
        have hn₂ : -x ≠ -e0 := by
          intro h
          apply hx
          simpa only [neg_inj] using h
        simp [fR, hx, hx', hn₁, hn₂]
  let F : Fin 4 → {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inl rpBase)} := fun i ↦
    ⟨Quotient.mk _ (.inl (e0, i)), rfl⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have hq : Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ)
        (.inl (e0, i)) (.inl (e0, j)) := Quotient.exact (congrArg Subtype.val hij)
    have hi := rp2Wedge_regular_four_cover_aux_card_aux_invariant σ τ fL fR
      hL hR (by intro k; simp [e0, fL, fR]) hq
    simpa [fL] using hi
  have hsurj : Function.Surjective F := by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | _ z =>
      rcases z with z | z <;> rcases z with ⟨x, i⟩
      · have hw := Quotient.exact hq
        have hc : antipodalCover x = rpBase := by
          rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
              rpBase rpBase (.inl (antipodalCover x)) (.inl rpBase)).mp hw with h | h
          · exact Sum.inl.inj h
          · rcases h.1 with h | h
            · exact Sum.inl.inj h
            · contradiction
        rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff e0 x).mp hc.symm with rfl | rfl
        · exact ⟨i, rfl⟩
        · refine ⟨σ i, ?_⟩
          apply Subtype.ext
          apply Quotient.sound
          simpa [hσ i] using Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ) e0 (σ i))
      · have hw := Quotient.exact hq
        have hc : antipodalCover x = rpBase := by
          rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
              rpBase rpBase (.inr (antipodalCover x)) (.inl rpBase)).mp hw with h | h
          · contradiction
          · rcases h.1 with h | h
            · contradiction
            · exact Sum.inr.inj h
        rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff e0 x).mp hc.symm with rfl | rfl
        · refine ⟨i, ?_⟩
          apply Subtype.ext
          exact Quotient.sound (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) i))
        · refine ⟨τ i, ?_⟩
          apply Subtype.ext
          apply Quotient.sound
          have hg := Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) (τ i))
          have hr := Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ) e0 (τ i))
          exact Relation.EqvGen.trans _ _ _ hg (by simpa [hτ i] using hr)
  let E : Fin 4 ≃ {e // rp2Wedge_regular_four_cover_aux_p σ τ e =
      Quotient.mk _ (.inl rpBase)} := Equiv.ofBijective F ⟨hinj, hsurj⟩
  simpa using Nat.card_congr E.symm

/-- Every fibre has four points: over a point of the left lobe the fibre is
`{[(x, i)] | i}` (the class of `(x, i)` is `{(x, i), (-x, σ i)}`, using that
`σ` is an involution); likewise on the right; over the wedge point it is
`{[(e₀, i)] | i}`.  Uses `rp2Wedge_regular_four_cover_aux_cover_eq_iff`. -/
theorem rp2Wedge_regular_four_cover_aux_card (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (b : Wedge RP2 RP2 rpBase rpBase) :
    Nat.card {e // rp2Wedge_regular_four_cover_aux_p σ τ e = b} = 4 := by
  obtain ⟨z, rfl⟩ := Quotient.exists_rep b
  rcases z with q | q <;>
    obtain ⟨x, rfl⟩ := rp2Wedge_regular_four_cover_aux_surjective q
  · by_cases hx : antipodalCover x = rpBase
    · rw [hx]
      exact rp2Wedge_regular_four_cover_aux_card_aux_base σ τ hσ hτ
    · exact rp2Wedge_regular_four_cover_aux_card_aux_left σ τ hσ x hx
  · by_cases hx : antipodalCover x = rpBase
    · have hw : (⟦.inr (antipodalCover x)⟧ : Wedge RP2 RP2 rpBase rpBase) =
          ⟦.inl rpBase⟧ := by
        rw [hx]
        exact (Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base)).symm
      rw [hw]
      exact rp2Wedge_regular_four_cover_aux_card_aux_base σ τ hσ hτ
    · exact rp2Wedge_regular_four_cover_aux_card_aux_right σ τ hτ x hx

/-- If `σ`, `τ` generate a transitive action on `Fin 4`, the glued space is
connected: the image of `Sphere2 × {i}` in either copy is connected, the left
sheets `i` and `σ i` have the same image, and the left and right sheets `i`
meet at `[(e₀, i)]`. -/
theorem rp2Wedge_regular_four_cover_aux_connected (σ τ : Equiv.Perm (Fin 4))
    (hT : ∀ i j : Fin 4, Relation.ReflTransGen (fun a b ↦ b = σ a ∨ b = τ a) i j) :
    IsConnected (Set.univ : Set (rp2Wedge_regular_four_cover_aux_E σ τ)) := by
  let q : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4) →
      rp2Wedge_regular_four_cover_aux_E σ τ := Quotient.mk _
  let l : Fin 4 → Sphere2 → rp2Wedge_regular_four_cover_aux_E σ τ :=
    fun i x ↦ q (.inl (x, i))
  let r : Fin 4 → Sphere2 → rp2Wedge_regular_four_cover_aux_E σ τ :=
    fun i x ↦ q (.inr (x, i))
  let U : Fin 4 → Set (rp2Wedge_regular_four_cover_aux_E σ τ) :=
    fun i ↦ Set.range (l i) ∪ Set.range (r i)
  letI : ConnectedSpace Sphere2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (by rw [← Module.finrank_eq_rank']; norm_num [finrank_euclideanSpace_fin]) 0
      (by norm_num : (0 : ℝ) ≤ 1))
  have hl (i : Fin 4) : IsConnected (Set.range (l i)) := by
    apply isConnected_range
    exact continuous_coinduced_rng.comp
      (continuous_inl.comp (continuous_id.prodMk continuous_const))
  have hr (i : Fin 4) : IsConnected (Set.range (r i)) := by
    apply isConnected_range
    exact continuous_coinduced_rng.comp
      (continuous_inr.comp (continuous_id.prodMk continuous_const))
  have hU (i : Fin 4) : IsConnected (U i) := by
    apply IsConnected.union
    · refine ⟨q (.inl (rp2Wedge_regular_four_cover_aux_e0, i)), ?_⟩
      constructor
      · exact ⟨_, rfl⟩
      · refine ⟨rp2Wedge_regular_four_cover_aux_e0, ?_⟩
        exact (Quotient.sound (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) i))).symm
    · exact hl i
    · exact hr i
  have hstep (i j : Fin 4) (h : j = σ i ∨ j = τ i) :
      (U i ∩ U j).Nonempty := by
    rcases h with rfl | rfl
    · refine ⟨l i rp2Wedge_regular_four_cover_aux_e0, ?_, ?_⟩
      · exact Or.inl ⟨_, rfl⟩
      · apply Or.inl
        refine ⟨-rp2Wedge_regular_four_cover_aux_e0, ?_⟩
        exact (Quotient.sound (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ)
            rp2Wedge_regular_four_cover_aux_e0 i))).symm
    · refine ⟨r i rp2Wedge_regular_four_cover_aux_e0, ?_, ?_⟩
      · exact Or.inr ⟨_, rfl⟩
      · apply Or.inr
        refine ⟨-rp2Wedge_regular_four_cover_aux_e0, ?_⟩
        exact (Quotient.sound (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ)
            rp2Wedge_regular_four_cover_aux_e0 i))).symm
  have hall : IsConnected (⋃ i, U i) :=
    IsConnected.iUnion_of_reflTransGen hU (fun i j ↦ (hT i j).mono hstep)
  rw [show (⋃ i, U i) = (Set.univ : Set (rp2Wedge_regular_four_cover_aux_E σ τ)) by
    apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | _ z =>
      rcases z with ⟨x, i⟩ | ⟨x, i⟩
      · exact Set.mem_iUnion.2 ⟨i, Or.inl ⟨x, rfl⟩⟩
      · exact Set.mem_iUnion.2 ⟨i, Or.inr ⟨x, rfl⟩⟩] at hall
  exact hall

/-! #### Split of `rp2Wedge_regular_four_cover_aux_regular` (lemma-3 PARTIAL, 2026-10-19) -/

/-- The sheet relabelling `(x, i) ↦ (x, g i)` on both copies. -/
def rp2Wedge_regular_four_cover_aux_raw (g : Equiv.Perm (Fin 4)) :
    (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4) → (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4)
  | .inl z => .inl (z.1, g z.2)
  | .inr z => .inr (z.1, g z.2)

/-- A permutation commuting with `σ` and `τ` induces a homeomorphism of the
glued space acting on representatives by `raw g` (banked from lemma-3). -/
theorem rp2Wedge_regular_four_cover_aux_regular_aux_deck (σ τ : Equiv.Perm (Fin 4))
    (g : Equiv.Perm (Fin 4)) (hgσ : g * σ = σ * g) (hgτ : g * τ = τ * g) :
    ∃ h : rp2Wedge_regular_four_cover_aux_E σ τ ≃ₜ rp2Wedge_regular_four_cover_aux_E σ τ,
      ∀ z, h (Quotient.mk _ z) = Quotient.mk _ (rp2Wedge_regular_four_cover_aux_raw g z) := by
  have raw_cont (g : Equiv.Perm (Fin 4)) :
      Continuous (rp2Wedge_regular_four_cover_aux_raw g) := by
    apply continuous_sum_dom.mpr
    constructor
    · exact continuous_inl.comp (Continuous.prodMk continuous_fst
        (continuous_of_discreteTopology.comp continuous_snd))
    · exact continuous_inr.comp (Continuous.prodMk continuous_fst
        (continuous_of_discreteTopology.comp continuous_snd))
  have respects (g : Equiv.Perm (Fin 4))
      (hgσ : g * σ = σ * g) (hgτ : g * τ = τ * g)
      {a b} (hab : Relation.EqvGen
        (rp2Wedge_regular_four_cover_aux_Rel σ τ) a b) :
      Relation.EqvGen (rp2Wedge_regular_four_cover_aux_Rel σ τ) (rp2Wedge_regular_four_cover_aux_raw g a) (rp2Wedge_regular_four_cover_aux_raw g b) := by
    induction hab with
    | rel a b hab =>
        cases hab with
        | left z i =>
            apply Relation.EqvGen.rel
            have hi := DFunLike.congr_fun hgσ i
            change g (σ i) = σ (g i) at hi
            simpa [rp2Wedge_regular_four_cover_aux_raw] using
              (show rp2Wedge_regular_four_cover_aux_Rel σ τ
                (.inl (z, g i)) (.inl (-z, g (σ i))) by
                  simpa [hi] using
                    (rp2Wedge_regular_four_cover_aux_Rel.left
                      (σ := σ) (τ := τ) z (g i)))
        | right z i =>
            apply Relation.EqvGen.rel
            have hi := DFunLike.congr_fun hgτ i
            change g (τ i) = τ (g i) at hi
            simpa [rp2Wedge_regular_four_cover_aux_raw] using
              (show rp2Wedge_regular_four_cover_aux_Rel σ τ
                (.inr (z, g i)) (.inr (-z, g (τ i))) by
                  simpa [hi] using
                    (rp2Wedge_regular_four_cover_aux_Rel.right
                      (σ := σ) (τ := τ) z (g i)))
        | glue i =>
            exact Relation.EqvGen.rel _ _
              (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) (g i))
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  let deck (g : Equiv.Perm (Fin 4))
      (hgσ : g * σ = σ * g) (hgτ : g * τ = τ * g) :
      rp2Wedge_regular_four_cover_aux_E σ τ →
        rp2Wedge_regular_four_cover_aux_E σ τ :=
    Quotient.lift (fun z => Quotient.mk _ (rp2Wedge_regular_four_cover_aux_raw g z))
      (fun _ _ h => Quotient.sound (respects g hgσ hgτ h))
  have deck_mk (g) (hgσ) (hgτ) (z) :
      deck g hgσ hgτ (Quotient.mk _ z) = Quotient.mk _ (rp2Wedge_regular_four_cover_aux_raw g z) := rfl
  have inv_comm (g : Equiv.Perm (Fin 4)) (hgσ : g * σ = σ * g)
      (hgτ : g * τ = τ * g) :
      g⁻¹ * σ = σ * g⁻¹ ∧ g⁻¹ * τ = τ * g⁻¹ := by
    constructor <;> apply Equiv.ext <;> intro i
    · have hi := DFunLike.congr_fun hgσ (g⁻¹ i)
      apply g.injective
      simpa using hi.symm
    · have hi := DFunLike.congr_fun hgτ (g⁻¹ i)
      apply g.injective
      simpa using hi.symm
  have deck_cont (g) (hgσ) (hgτ) : Continuous (deck g hgσ hgτ) := by
    apply continuous_coinduced_dom.mpr
    exact continuous_coinduced_rng.comp (raw_cont g)
  let make_homeomorph (g : Equiv.Perm (Fin 4))
      (hgσ : g * σ = σ * g) (hgτ : g * τ = τ * g) :
      rp2Wedge_regular_four_cover_aux_E σ τ ≃ₜ
        rp2Wedge_regular_four_cover_aux_E σ τ := by
    let hi := inv_comm g hgσ hgτ
    refine
      { toFun := deck g hgσ hgτ
        invFun := deck g⁻¹ hi.1 hi.2
        left_inv := ?_
        right_inv := ?_
        continuous_toFun := deck_cont g hgσ hgτ
        continuous_invFun := deck_cont g⁻¹ hi.1 hi.2 }
    · intro q
      induction q using Quotient.inductionOn with
      | _ z => rcases z with z | z <;> rcases z with ⟨u, i⟩ <;> simp [deck, rp2Wedge_regular_four_cover_aux_raw]
    · intro q
      induction q using Quotient.inductionOn with
      | _ z => rcases z with z | z <;> rcases z with ⟨u, i⟩ <;> simp [deck, rp2Wedge_regular_four_cover_aux_raw]
  exact ⟨make_homeomorph g hgσ hgτ, fun _ => rfl⟩

/-- Two points of one fibre are related by a sheet relabelling from the
centralizer: normalize both representatives (using `(x, i) ∼ (-x, σ i)`,
`(x, i) ∼ (-x, τ i)` and, over the wedge point, the glue `(e₀, i)`) to the same
sphere point and lobe, then pick `g` with `hC`. -/
theorem rp2Wedge_regular_four_cover_aux_regular_aux_fibre (σ τ : Equiv.Perm (Fin 4))
    (hC : ∀ i j : Fin 4, ∃ g : Equiv.Perm (Fin 4),
      g * σ = σ * g ∧ g * τ = τ * g ∧ g i = j)
    (a b : (Sphere2 × Fin 4) ⊕ (Sphere2 × Fin 4))
    (hab : rp2Wedge_regular_four_cover_aux_proj a = rp2Wedge_regular_four_cover_aux_proj b) :
    ∃ g : Equiv.Perm (Fin 4), g * σ = σ * g ∧ g * τ = τ * g ∧
      (Quotient.mk _ (rp2Wedge_regular_four_cover_aux_raw g a) :
        rp2Wedge_regular_four_cover_aux_E σ τ) = Quotient.mk _ b := by
  rcases a with ⟨u, i⟩ | ⟨u, i⟩ <;>
    rcases b with ⟨v, j⟩ | ⟨v, j⟩
  · have hw := Quotient.exact hab
    have hc : antipodalCover u = antipodalCover v := by
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inl (antipodalCover u)) (.inl (antipodalCover v))).mp hw with
        h | ⟨hu, hv⟩
      · exact Sum.inl.inj h
      · rcases hu with hu | hu <;> rcases hv with hv | hv <;>
          simp_all
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff u v).mp hc with rfl | rfl
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i j
      refine ⟨g, hgσ, hgτ, ?_⟩
      simp [rp2Wedge_regular_four_cover_aux_raw, hgi]
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (σ⁻¹ j)
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      have hj : σ (g i) = j := by simp [hgi]
      simpa [rp2Wedge_regular_four_cover_aux_raw, hj] using
        (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ) u (g i)))
  · have hw := Quotient.exact hab
    have hu : antipodalCover u = rpBase := by
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inl (antipodalCover u)) (.inr (antipodalCover v))).mp hw with
        h | ⟨hu, hv⟩
      · cases h
      · rcases hu with hu | hu
        · exact Sum.inl.inj hu
        · cases hu
    have hv : antipodalCover v = rpBase := by
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inl (antipodalCover u)) (.inr (antipodalCover v))).mp hw with
        h | ⟨hu, hv⟩
      · cases h
      · rcases hv with hv | hv
        · cases hv
        · exact Sum.inr.inj hv
    rw [rp2Wedge_regular_four_cover_aux_rpBase] at hu hv
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff
      rp2Wedge_regular_four_cover_aux_e0 u).mp hu.symm with rfl | rfl <;>
      rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff
        rp2Wedge_regular_four_cover_aux_e0 v).mp hv.symm with rfl | rfl
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i j
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      simpa [rp2Wedge_regular_four_cover_aux_raw, hgi] using
        (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) j))
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (τ⁻¹ j)
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      have hj : τ (g i) = j := by simp [hgi]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) (g i)))
        (by simpa [rp2Wedge_regular_four_cover_aux_raw, hj] using
          (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ)
              rp2Wedge_regular_four_cover_aux_e0 (g i))))
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (σ j)
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (by
          simpa [rp2Wedge_regular_four_cover_aux_raw, hgi] using
            (Relation.EqvGen.rel _ _
              (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ)
                rp2Wedge_regular_four_cover_aux_e0 j))))
        (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) j))
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (σ (τ⁻¹ j))
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      have hk : σ⁻¹ (g i) = τ⁻¹ j := by simp [hgi]
      have hj : τ (σ⁻¹ (g i)) = j := by simp [hk]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (by
          simpa [rp2Wedge_regular_four_cover_aux_raw] using
            (Relation.EqvGen.rel _ _
              (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ)
                rp2Wedge_regular_four_cover_aux_e0 (σ⁻¹ (g i))))))
        (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) (σ⁻¹ (g i))))
          (by
            have hh := Relation.EqvGen.rel _ _
              (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ)
                rp2Wedge_regular_four_cover_aux_e0 (σ⁻¹ (g i)))
            rw [hj] at hh
            exact hh))
  · have hab' := hab.symm
    have hw := Quotient.exact hab'
    have hu : antipodalCover u = rpBase := by
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inl (antipodalCover v)) (.inr (antipodalCover u))).mp hw with
        h | ⟨hv, hu⟩
      · cases h
      · rcases hu with hu | hu
        · cases hu
        · exact Sum.inr.inj hu
    have hv : antipodalCover v = rpBase := by
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inl (antipodalCover v)) (.inr (antipodalCover u))).mp hw with
        h | ⟨hv, hu⟩
      · cases h
      · rcases hv with hv | hv
        · exact Sum.inl.inj hv
        · cases hv
    rw [rp2Wedge_regular_four_cover_aux_rpBase] at hu hv
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff
      rp2Wedge_regular_four_cover_aux_e0 u).mp hu.symm with rfl | rfl <;>
      rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff
        rp2Wedge_regular_four_cover_aux_e0 v).mp hv.symm with rfl | rfl
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i j
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      exact Relation.EqvGen.symm _ _ (by simpa [rp2Wedge_regular_four_cover_aux_raw, hgi] using
        (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) j)))
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (σ⁻¹ j)
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      have hj : σ (g i) = j := by simp [hgi]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (by
          simpa [rp2Wedge_regular_four_cover_aux_raw] using
            (Relation.EqvGen.rel _ _
              (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) (g i)))))
        (by
          have hh := Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ)
              rp2Wedge_regular_four_cover_aux_e0 (g i))
          rw [hj] at hh
          exact hh)
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (τ j)
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (by simpa [rp2Wedge_regular_four_cover_aux_raw, hgi] using
          (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ)
              rp2Wedge_regular_four_cover_aux_e0 j))))
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) j)))
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (τ (σ⁻¹ j))
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      have hk : τ⁻¹ (g i) = σ⁻¹ j := by simp [hgi]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (by simpa [rp2Wedge_regular_four_cover_aux_raw] using
          (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ)
              rp2Wedge_regular_four_cover_aux_e0 (τ⁻¹ (g i))))))
        (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
            (rp2Wedge_regular_four_cover_aux_Rel.glue (σ := σ) (τ := τ) (τ⁻¹ (g i)))))
          (by
            have hh := Relation.EqvGen.rel _ _
              (rp2Wedge_regular_four_cover_aux_Rel.left (σ := σ) (τ := τ)
                rp2Wedge_regular_four_cover_aux_e0 (σ⁻¹ j))
            rw [hk]
            simpa using hh))
  · have hw := Quotient.exact hab
    have hc : antipodalCover u = antipodalCover v := by
      rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
        rpBase rpBase (.inr (antipodalCover u)) (.inr (antipodalCover v))).mp hw with
        h | ⟨hu, hv⟩
      · exact Sum.inr.inj h
      · rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp_all
    rcases (rp2Wedge_regular_four_cover_aux_cover_eq_iff u v).mp hc with rfl | rfl
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i j
      exact ⟨g, hgσ, hgτ, by simp [rp2Wedge_regular_four_cover_aux_raw, hgi]⟩
    · obtain ⟨g, hgσ, hgτ, hgi⟩ := hC i (τ⁻¹ j)
      refine ⟨g, hgσ, hgτ, ?_⟩
      apply Quotient.sound
      have hj : τ (g i) = j := by simp [hgi]
      simpa [rp2Wedge_regular_four_cover_aux_raw, hj] using
        (Relation.EqvGen.rel _ _
          (rp2Wedge_regular_four_cover_aux_Rel.right (σ := σ) (τ := τ) u (g i)))

/-- If the centralizer of `σ`, `τ` acts transitively on `Fin 4`, the cover is
regular: `g` commuting with `σ`, `τ` gives the deck homeomorphism
`[(x, i)] ↦ [(x, g i)]` on both copies (inverse from `g⁻¹`), and any two points
of one fibre can be written `[(x, i)]`, `[(x, j)]` with the same `x`. -/
theorem rp2Wedge_regular_four_cover_aux_regular (σ τ : Equiv.Perm (Fin 4))
    (hC : ∀ i j : Fin 4, ∃ g : Equiv.Perm (Fin 4),
      g * σ = σ * g ∧ g * τ = τ * g ∧ g i = j) :
    IsRegularCover (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  obtain ⟨g, hgσ, hgτ, hg⟩ :=
    rp2Wedge_regular_four_cover_aux_regular_aux_fibre σ τ hC a b hxy
  obtain ⟨h, hh⟩ := rp2Wedge_regular_four_cover_aux_regular_aux_deck σ τ g hgσ hgτ
  refine ⟨h, ?_, by rw [hh]; exact hg⟩
  intro z
  induction z using Quotient.inductionOn with
  | _ z =>
    rw [hh]
    rcases z with z | z <;> rfl

/-- The two fixed-point-free involutions `(12)(34)` and `(13)(24)` realize
the connected regular Klein-four cover of the projective-plane wedge. -/
theorem rp2Wedge_regular_four_cover :
    Nonempty (CoverWitness (Wedge RP2 RP2 rpBase rpBase) 4 true) := by
  have hσ : Function.Involutive (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) := by
    intro i; fin_cases i <;> decide
  have hτ : Function.Involutive (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) := by
    intro i; fin_cases i <;> decide
  have hT : ∀ i j : Fin 4, Relation.ReflTransGen
      (fun a b ↦ b = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) a ∨
        b = (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) a) i j := by
    intro i j
    have : j = i ∨ j = (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) i ∨
        j = (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i ∨
        j = (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
          ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) i) := by
      fin_cases i <;> fin_cases j <;> decide
    rcases this with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (Or.inl rfl)
    · exact Relation.ReflTransGen.single (Or.inr rfl)
    · exact Relation.ReflTransGen.tail
        (b := (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) i)
        (Relation.ReflTransGen.single (Or.inl rfl)) (Or.inr rfl)
  have hC : ∀ i j : Fin 4, ∃ g : Equiv.Perm (Fin 4),
      g * (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) =
        (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) * g ∧
      g * (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) =
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) * g ∧ g i = j := by
    decide
  exact ⟨{ E := rp2Wedge_regular_four_cover_aux_E _ _
           topology := inferInstance
           p := rp2Wedge_regular_four_cover_aux_p _ _
           covering := ⟨rp2Wedge_regular_four_cover_aux_isCoveringMap _ _ hσ hτ,
             rp2Wedge_regular_four_cover_aux_card _ _ hσ hτ⟩
           connected := rp2Wedge_regular_four_cover_aux_connected _ _ hT
           regularity := rp2Wedge_regular_four_cover_aux_regular _ _ hC }⟩

/-! ### Split of `rp2Wedge_irregular_four_cover`

The same glued cover with `σ = (12)` and `τ = (14)(23)`.  Covering, fibre
count and connectedness come from the general leaves above; non-regularity
comes from `_aux_not_regular` and the centralizer computation. -/

def rp2Wedge_irregular_four_cover_aux_sigma : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

def rp2Wedge_irregular_four_cover_aux_tau : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 3).trans (Equiv.swap 1 2)

/-- The centralizer of the two monodromies is not transitive: no permutation
commuting with both can carry sheet `0` to sheet `2`. -/
lemma rp2Wedge_irregular_four_cover_aux_centralizer
    (f : Equiv.Perm (Fin 4))
    (hs : f * rp2Wedge_irregular_four_cover_aux_sigma =
      rp2Wedge_irregular_four_cover_aux_sigma * f)
    (ht : f * rp2Wedge_irregular_four_cover_aux_tau =
      rp2Wedge_irregular_four_cover_aux_tau * f) :
    f 0 ≠ 2 := by
  intro h02
  have hs0 := DFunLike.congr_fun hs (0 : Fin 4)
  have h12 : f 1 = 2 := by
    simpa [rp2Wedge_irregular_four_cover_aux_sigma, h02] using hs0
  exact (by decide : (0 : Fin 4) ≠ 1) (f.injective (h02.trans h12.symm))

/-- **LIBRARY.** A deck homeomorphism `h` permutes the fibre
`{[(e₀, i)] | i}` over the wedge point by some `g`, and `g` commutes with `σ`
and `τ`: the path `t ↦ [(γ t, i)]` in the left copy, with `γ` a path from `e₀`
to `-e₀` in `Sphere2`, lifts a loop at the wedge point from `[(e₀, i)]` to
`[(e₀, σ i)]`; `h` carries it to a lift of the same loop starting at
`[(e₀, g i)]`, which by uniqueness of lifts (`IsCoveringMap.eq_of_comp_eq`,
using `_aux_isCoveringMap`) ends at `[(e₀, σ (g i))]`.  Likewise for `τ` in the
right copy.  So if some sheet `i` cannot be moved to `j` by the centralizer, no
deck map sends `[(e₀, i)]` to `[(e₀, j)]`. -/
theorem rp2Wedge_irregular_four_cover_aux_not_regular (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (hN : ∃ i j : Fin 4, ∀ g : Equiv.Perm (Fin 4),
      g * σ = σ * g → g * τ = τ * g → g i ≠ j) :
    ¬ IsRegularCover (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  sorry

/-- The involutions `(12)` and `(14)(23)` realize a connected nonregular
four-sheeted cover of the projective-plane wedge. -/
theorem rp2Wedge_irregular_four_cover :
    Nonempty (CoverWitness (Wedge RP2 RP2 rpBase rpBase) 4 false) := by
  have hσ : Function.Involutive rp2Wedge_irregular_four_cover_aux_sigma := by
    intro i; fin_cases i <;> decide
  have hτ : Function.Involutive rp2Wedge_irregular_four_cover_aux_tau := by
    intro i; fin_cases i <;> decide
  have hT : ∀ i j : Fin 4, Relation.ReflTransGen
      (fun a b ↦ b = rp2Wedge_irregular_four_cover_aux_sigma a ∨
        b = rp2Wedge_irregular_four_cover_aux_tau a) i j := by
    have step : ∀ a b : Fin 4, (b = rp2Wedge_irregular_four_cover_aux_sigma a ∨
        b = rp2Wedge_irregular_four_cover_aux_tau a) →
        Relation.ReflTransGen (fun a b ↦ b = rp2Wedge_irregular_four_cover_aux_sigma a ∨
          b = rp2Wedge_irregular_four_cover_aux_tau a) a b :=
      fun _ _ h ↦ Relation.ReflTransGen.single h
    have from0 : ∀ j : Fin 4, Relation.ReflTransGen
        (fun a b ↦ b = rp2Wedge_irregular_four_cover_aux_sigma a ∨
          b = rp2Wedge_irregular_four_cover_aux_tau a) 0 j := by
      intro j; fin_cases j
      · exact Relation.ReflTransGen.refl
      · exact step _ _ (by decide)
      · exact (step 0 1 (by decide)).trans (step 1 2 (by decide))
      · exact step _ _ (by decide)
    have to0 : ∀ i : Fin 4, Relation.ReflTransGen
        (fun a b ↦ b = rp2Wedge_irregular_four_cover_aux_sigma a ∨
          b = rp2Wedge_irregular_four_cover_aux_tau a) i 0 := by
      intro i; fin_cases i
      · exact Relation.ReflTransGen.refl
      · exact step _ _ (by decide)
      · exact (step 2 1 (by decide)).trans (step 1 0 (by decide))
      · exact step _ _ (by decide)
    exact fun i j ↦ (to0 i).trans (from0 j)
  have hN : ∃ i j : Fin 4, ∀ g : Equiv.Perm (Fin 4),
      g * rp2Wedge_irregular_four_cover_aux_sigma =
        rp2Wedge_irregular_four_cover_aux_sigma * g →
      g * rp2Wedge_irregular_four_cover_aux_tau =
        rp2Wedge_irregular_four_cover_aux_tau * g → g i ≠ j :=
    ⟨0, 2, fun g hs ht ↦ rp2Wedge_irregular_four_cover_aux_centralizer g hs ht⟩
  exact ⟨{ E := rp2Wedge_regular_four_cover_aux_E _ _
           topology := inferInstance
           p := rp2Wedge_regular_four_cover_aux_p _ _
           covering := ⟨rp2Wedge_regular_four_cover_aux_isCoveringMap _ _ hσ hτ,
             rp2Wedge_regular_four_cover_aux_card _ _ hσ hτ⟩
           connected := rp2Wedge_regular_four_cover_aux_connected _ _ hT
           regularity := rp2Wedge_irregular_four_cover_aux_not_regular _ _ hσ hτ hN }⟩

abbrev Circle := Metric.sphere (0 : ℂ) 1
def circleBase : Circle := ⟨1, by simp⟩
abbrev CircleWedge := Wedge Circle Circle circleBase circleBase

structure ThreeCover where
  E : Type
  topology : TopologicalSpace E
  p : E → CircleWedge
  covering : @IsNfoldCover E CircleWedge topology _ 3 p

/-- The permutation pair `(1,1)`: the trivial three-sheeted cover, with three
components. -/
lemma circleWedge_three_cover_three_components_aux_connected :
    IsConnected (Set.univ : Set CircleWedge) := by
  letI : ConnectedSpace Circle := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := ℂ) (by norm_num [Complex.rank_real_complex]) 0 (by norm_num))
  let l : Circle → CircleWedge := fun x ↦ Quotient.mk _ (.inl x)
  let r : Circle → CircleWedge := fun x ↦ Quotient.mk _ (.inr x)
  have hl : IsConnected (Set.range l) :=
    isConnected_range (continuous_coinduced_rng.comp continuous_inl)
  have hr : IsConnected (Set.range r) :=
    isConnected_range (continuous_coinduced_rng.comp continuous_inr)
  have hcover : Set.range l ∪ Set.range r = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    rcases x with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  rw [← hcover]
  exact hl.union ⟨Quotient.mk _ (.inl circleBase), ⟨circleBase, rfl⟩,
    circleBase, Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base) |>.symm⟩ hr

theorem circleWedge_three_cover_three_components : ∃ C : ThreeCover,
    Nat.card (@ConnectedComponents C.E C.topology) = 3 := by
  letI : ConnectedSpace CircleWedge := connectedSpace_iff_univ.mpr
    circleWedge_three_cover_three_components_aux_connected
  let p : CircleWedge × Fin 3 → CircleWedge := Prod.fst
  have hp : IsCoveringMap p := by
    have h := FiberBundle.isCoveringMap (X := CircleWedge) (F := Fin 3)
      (E := Bundle.Trivial CircleWedge (Fin 3))
    simpa [p, Function.comp_def] using
      h.comp_homeomorph (Bundle.Trivial.homeomorphProd CircleWedge (Fin 3)).symm
  have hcard (b : CircleWedge) : Nat.card {e : CircleWedge × Fin 3 // p e = b} = 3 := by
    let e : {x // p x = b} ≃ Fin 3 :=
      { toFun := fun x ↦ x.1.2
        invFun := fun i ↦ ⟨(b, i), rfl⟩
        left_inv := fun x ↦ Subtype.ext (Prod.ext x.2.symm (by rfl))
        right_inv := fun _ ↦ rfl }
    simpa using Nat.card_congr e
  let U : Fin 3 → Set (CircleWedge × Fin 3) := fun i ↦ Prod.snd ⁻¹' {i}
  have hclopen : ∀ i, IsClopen (U i) := fun i ↦
    (isClopen_discrete {i}).preimage continuous_snd
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    exact Disjoint.preimage _ (by simpa using Set.disjoint_singleton.2 hij)
  have hunion : ⋃ i, U i = Set.univ := by
    ext x
    simp [U]
  have hconn : ∀ i, IsConnected (U i) := by
    intro i
    rw [show U i = Set.range (fun x : CircleWedge ↦ (x, i)) by
      ext x
      constructor
      · intro hx
        change x.2 = i at hx
        exact ⟨x.1, Prod.ext rfl hx.symm⟩
      · rintro ⟨y, rfl⟩
        simp [U]]
    exact isConnected_range (continuous_id.prodMk continuous_const)
  let e := ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn
  refine ⟨{ E := CircleWedge × Fin 3
            topology := inferInstance
            p := p
            covering := ⟨hp, hcard⟩ }, ?_⟩
  simpa using Nat.card_congr e

/-- The permutation pair `((12),(12))`: a three-sheeted cover with two
components. -/
def circleWedge_three_cover_two_components_aux_sq (z : Circle) : Circle :=
  ⟨(z : ℂ) * z, by
    simpa [Metric.mem_sphere, dist_zero_right, norm_mul] using
      congrArg (fun r : ℝ ↦ r * r) z.property⟩

inductive circleWedge_three_cover_two_components_aux_Rel :
    Circle ⊕ Circle → Circle ⊕ Circle → Prop
  | pos : circleWedge_three_cover_two_components_aux_Rel
      (.inl circleBase) (.inr circleBase)
  | neg : circleWedge_three_cover_two_components_aux_Rel
      (.inl (-circleBase)) (.inr (-circleBase))

def circleWedge_three_cover_two_components_aux_Double : Type :=
  Quotient (Relation.EqvGen.setoid
    circleWedge_three_cover_two_components_aux_Rel)

noncomputable instance circleWedge_three_cover_two_components_aux_Double_topology :
    TopologicalSpace circleWedge_three_cover_two_components_aux_Double :=
  TopologicalSpace.coinduced (fun z : Circle ⊕ Circle ↦ Quotient.mk _ z)
    inferInstance

def circleWedge_three_cover_two_components_aux_raw :
    Circle ⊕ Circle → CircleWedge
  | .inl z => Quotient.mk _ (.inl
      (circleWedge_three_cover_two_components_aux_sq z))
  | .inr z => Quotient.mk _ (.inr
      (circleWedge_three_cover_two_components_aux_sq z))

lemma circleWedge_three_cover_two_components_aux_raw_respects
    {x y : Circle ⊕ Circle}
    (h : Relation.EqvGen circleWedge_three_cover_two_components_aux_Rel x y) :
    circleWedge_three_cover_two_components_aux_raw x =
      circleWedge_three_cover_two_components_aux_raw y := by
  induction h with
  | rel x y h =>
      cases h with
      | pos =>
          have hs : circleWedge_three_cover_two_components_aux_sq circleBase =
              circleBase := by
            apply Subtype.ext
            simp [circleWedge_three_cover_two_components_aux_sq, circleBase]
          change Quotient.mk _ (Sum.inl _) = Quotient.mk _ (Sum.inr _)
          rw [hs]
          exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base)
      | neg =>
          change Quotient.mk _ (Sum.inl _) = Quotient.mk _ (Sum.inr _)
          have hs : circleWedge_three_cover_two_components_aux_sq (-circleBase) =
              circleBase := by
            apply Subtype.ext
            simp [circleWedge_three_cover_two_components_aux_sq, circleBase]
          rw [hs]
          exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def circleWedge_three_cover_two_components_aux_doubleMap :
    circleWedge_three_cover_two_components_aux_Double → CircleWedge :=
  Quotient.lift circleWedge_three_cover_two_components_aux_raw
    (fun _ _ h ↦ circleWedge_three_cover_two_components_aux_raw_respects h)

def circleWedge_three_cover_two_components_aux_Total : Type :=
  CircleWedge ⊕ circleWedge_three_cover_two_components_aux_Double

noncomputable instance circleWedge_three_cover_two_components_aux_Total_topology :
    TopologicalSpace circleWedge_three_cover_two_components_aux_Total := by
  change TopologicalSpace
    (CircleWedge ⊕ circleWedge_three_cover_two_components_aux_Double)
  infer_instance

def circleWedge_three_cover_two_components_aux_map :
    circleWedge_three_cover_two_components_aux_Total → CircleWedge
  | .inl x => x
  | .inr x => circleWedge_three_cover_two_components_aux_doubleMap x

/-! #### Split of `circleWedge_three_cover_two_components_aux_covering` (lemma-1 PARTIAL, 2026-10-19) -/

lemma circleWedge_three_cover_two_components_aux_covering_aux_sq :
    IsCoveringMap circleWedge_three_cover_two_components_aux_sq := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have h : IsCoveringMap (fun z : Circle ↦ z ^ (2 : ℕ)) :=
    (Circle.isQuotientCoveringMap_npow 2).isCoveringMap
  simpa [circleWedge_three_cover_two_components_aux_sq, pow_two] using h

/-! #### Split of `circleWedge_three_cover_two_components_aux_covering_aux_double` (lemma-1 PARTIAL, 2026-10-19) -/

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_rel_iff
    (a b : Circle ⊕ Circle) :
    Relation.EqvGen circleWedge_three_cover_two_components_aux_Rel a b ↔
      a = b ∨ ∃ z : Circle, (z = circleBase ∨ z = -circleBase) ∧
        ((a = .inl z ∧ b = .inr z) ∨ (a = .inr z ∧ b = .inl z)) := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
        cases h with
        | pos => exact Or.inr ⟨circleBase, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
        | neg => exact Or.inr ⟨-circleBase, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
    | refl => exact Or.inl rfl
    | symm a b _ ih =>
        rcases ih with h | ⟨z, hz, h⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨z, hz, h.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
            (fun h ↦ Or.inl ⟨h.2, h.1⟩)⟩
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨z, hz, hab⟩
        · exact ih₂
        rcases ih₂ with rfl | ⟨w, hw, hbc⟩
        · exact Or.inr ⟨z, hz, hab⟩
        · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases hbc with ⟨h, _⟩ | ⟨h, _⟩ <;>
            simp_all
  · rintro (rfl | ⟨z, hz, h⟩)
    · exact Relation.EqvGen.refl _
    rcases hz with rfl | rfl <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.pos
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.pos)
    · exact Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.neg
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.neg)

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_continuous :
    Continuous circleWedge_three_cover_two_components_aux_doubleMap := by
  apply (show Topology.IsQuotientMap
      (fun z : Circle ⊕ Circle ↦ (Quotient.mk _ z :
        circleWedge_three_cover_two_components_aux_Double)) from
      isQuotientMap_quot_mk).continuous_iff.mpr
  change Continuous circleWedge_three_cover_two_components_aux_raw
  rw [continuous_sum_dom]
  constructor
  · simpa [Function.comp_def, circleWedge_three_cover_two_components_aux_raw] using
      continuous_coinduced_rng.comp (continuous_inl.comp
        circleWedge_three_cover_two_components_aux_covering_aux_sq.continuous)
  · simpa [Function.comp_def, circleWedge_three_cover_two_components_aux_raw] using
      continuous_coinduced_rng.comp (continuous_inr.comp
        circleWedge_three_cover_two_components_aux_covering_aux_sq.continuous)

/-- Away from the wedge point: `x = [inl w]` or `[inr w]` with `w ≠ 1`; take a
small arc `V ∋ w` avoiding `1` in that lobe. Its preimage is the two arcs
`±√V` in the matching lobe of the double cover, each mapped homeomorphically by
squaring (`circleWedge_three_cover_two_components_aux_covering_aux_sq`). -/
def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim id (fun _ ↦ circleBase)) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim (fun _ ↦ circleBase) id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total :
    circleWedge_three_cover_two_components_aux_Double → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h <;> rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL_continuous :
    Continuous circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR_continuous :
    Continuous circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total_continuous :
    Continuous circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_id, continuous_id⟩

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_square
    (e : circleWedge_three_cover_two_components_aux_Double)
    (he : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL
        (circleWedge_three_cover_two_components_aux_doubleMap e) ≠ circleBase) :
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL
        (circleWedge_three_cover_two_components_aux_doubleMap e) =
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total e ^ 2 := by
  refine Quotient.inductionOn e ?_ he
  rintro (e | e) he
  ·
      change circleWedge_three_cover_two_components_aux_sq e = e ^ 2
      apply Subtype.ext
      simp [circleWedge_three_cover_two_components_aux_sq, pow_two]
  ·
      exfalso
      apply he
      rfl

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_squareR
    (e : circleWedge_three_cover_two_components_aux_Double)
    (he : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR
        (circleWedge_three_cover_two_components_aux_doubleMap e) ≠ circleBase) :
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR
        (circleWedge_three_cover_two_components_aux_doubleMap e) =
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total e ^ 2 := by
  refine Quotient.inductionOn e ?_ he
  rintro (e | e) he
  ·
      exfalso
      apply he
      rfl
  ·
      change circleWedge_three_cover_two_components_aux_sq e = e ^ 2
      apply Subtype.ext
      simp [circleWedge_three_cover_two_components_aux_sq, pow_two]

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_left
    (z : Circle) (hz : z ≠ circleBase) :
    IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap
      (Quotient.mk _ (.inl z))
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' {Quotient.mk _ (.inl z)}) := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hd, U, hzU, hU, hpU, H, hH⟩ :=
    IsQuotientCoveringMap.isCoveringMap _ _
      (Circle.isQuotientCoveringMap_npow 2) z
  let V : Set Circle := U \ {circleBase}
  have hzV : z ∈ V := ⟨hzU, hz⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set CircleWedge :=
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL_continuous
  have hzUX : (Quotient.mk _ (.inl z) : CircleWedge) ∈ UX := hzV
  let W : Set Circle := (fun w : Circle ↦ w ^ 2) ⁻¹' V
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hopenpre : IsOpen
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' UX) := by
    exact hUX.preimage
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_continuous
  have himage (e : circleWedge_three_cover_two_components_aux_Double)
      (he : e ∈ circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' UX) :
      circleWedge_three_cover_two_components_aux_doubleMap e = Quotient.mk _ (.inl
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total e ^ 2)) := by
    induction e using Quotient.inductionOn with
    | _ e =>
      rcases e with w | w
      · change Quotient.mk _ (Sum.inl
            (circleWedge_three_cover_two_components_aux_sq w)) = _
        congr 2
        apply Subtype.ext
        change (w : ℂ) * w = ((w ^ 2 : Circle) : ℂ)
        simp [pow_two]
      · exfalso
        change circleBase ∈ V at he
        exact he.2 rfl
  let I := (fun w : Circle ↦ w ^ 2) ⁻¹' {z}
  have hWV : W ⊆ (fun w : Circle ↦ w ^ 2) ⁻¹' U := fun w hw ↦ hw.1
  let HW : W ≃ₜ V × I :=
    { toFun := fun w =>
        let y := H ⟨w.1, hWV w.2⟩
        (⟨y.1.1, ⟨y.1.2, by rw [hH ⟨w.1, hWV w.2⟩]; exact w.2.2⟩⟩, y.2)
      invFun := fun y => ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
        have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
        have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 2 = y.1.1 := by
          simpa using hh.symm
        constructor
        · change _ ^ 2 ∈ U
          have hy : y.1.1 ∈ U := y.1.2.1
          rw [← hh'] at hy
          exact hy
        · change _ ^ 2 ≠ circleBase
          intro heq
          exact y.1.2.2 (hh'.symm.trans heq)⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa only [Function.comp_apply] using
            (continuous_subtype_val.comp continuous_fst).comp (H.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val _))
        · exact continuous_snd.comp (H.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (H.symm.continuous.comp
          ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
            continuous_snd)) }
  have hHW (w : W) : (HW w).1.1 = w.1 ^ 2 := hH ⟨w.1, hWV w.2⟩
  let E : circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' UX ≃ₜ W :=
    { toFun := fun e =>
        ⟨circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total e.1,
          by
            change _ ^ 2 ∈ V
            rw [← circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_square e.1]
            · exact e.2
            · exact fun h ↦ e.2.2 h⟩
      invFun := fun w => ⟨Quotient.mk _ (Sum.inl w.1), by
        change circleWedge_three_cover_two_components_aux_sq w.1 ∈ V
        have hw : w.1 ^ 2 ∈ V := w.2
        simpa [circleWedge_three_cover_two_components_aux_sq, pow_two] using hw⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        induction e using Quotient.inductionOn with
        | _ e =>
          rcases e with w | w
          · rfl
          · exfalso
            change circleBase ∈ V at he
            exact he.2 rfl
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total_continuous.comp
          continuous_subtype_val) (fun e => by
            change _ ^ 2 ∈ V
            simp only [Function.comp_apply]
            rw [← circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_square e.1]
            · exact e.2
            · exact fun h ↦ e.2.2 h)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u :
            circleWedge_three_cover_two_components_aux_Double))).comp
              (continuous_inl.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x =>
        ⟨circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL x.1,
          x.2⟩
      invFun := fun v => ⟨Quotient.mk _ (.inl v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        induction x using Quotient.inductionOn with
        | _ x => rcases x with w | w
                 · rfl
                 · exact (hx.2 rfl).elim
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseL_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u : CircleWedge))).comp
              (continuous_inl.comp continuous_subtype_val) }
  refine (show IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap
      (Quotient.mk _ (.inl z)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hzUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change Quotient.mk _ (Sum.inl (HW (E e)).1.1) = _
    rw [hHW]
    exact (himage e.1 e.2).symm

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_right
    (z : Circle) (hz : z ≠ circleBase) :
    IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap
      (Quotient.mk _ (.inr z))
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' {Quotient.mk _ (.inr z)}) := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hd, U, hzU, hU, hpU, H, hH⟩ :=
    IsQuotientCoveringMap.isCoveringMap _ _
      (Circle.isQuotientCoveringMap_npow 2) z
  let V : Set Circle := U \ {circleBase}
  have hzV : z ∈ V := ⟨hzU, hz⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set CircleWedge :=
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR_continuous
  have hzUX : (Quotient.mk _ (.inr z) : CircleWedge) ∈ UX := hzV
  let W : Set Circle := (fun w : Circle ↦ w ^ 2) ⁻¹' V
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hopenpre : IsOpen
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' UX) :=
    hUX.preimage
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_continuous
  have himage (e : circleWedge_three_cover_two_components_aux_Double)
      (he : e ∈ circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' UX) :
      circleWedge_three_cover_two_components_aux_doubleMap e = Quotient.mk _ (.inr
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total e ^ 2)) := by
    induction e using Quotient.inductionOn with
    | _ e =>
      rcases e with w | w
      · exfalso
        change circleBase ∈ V at he
        exact he.2 rfl
      · change Quotient.mk _ (Sum.inr
            (circleWedge_three_cover_two_components_aux_sq w)) = _
        congr 2
        apply Subtype.ext
        change (w : ℂ) * w = ((w ^ 2 : Circle) : ℂ)
        simp [pow_two]
  let I := (fun w : Circle ↦ w ^ 2) ⁻¹' {z}
  have hWV : W ⊆ (fun w : Circle ↦ w ^ 2) ⁻¹' U := fun w hw ↦ hw.1
  let HW : W ≃ₜ V × I :=
    { toFun := fun w =>
        let y := H ⟨w.1, hWV w.2⟩
        (⟨y.1.1, ⟨y.1.2, by rw [hH ⟨w.1, hWV w.2⟩]; exact w.2.2⟩⟩, y.2)
      invFun := fun y => ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
        have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
        have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 2 = y.1.1 := by
          simpa using hh.symm
        constructor
        · change _ ^ 2 ∈ U
          have hy : y.1.1 ∈ U := y.1.2.1
          rw [← hh'] at hy
          exact hy
        · change _ ^ 2 ≠ circleBase
          intro heq
          exact y.1.2.2 (hh'.symm.trans heq)⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa only [Function.comp_apply] using
            (continuous_subtype_val.comp continuous_fst).comp (H.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val _))
        · exact continuous_snd.comp (H.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (H.symm.continuous.comp
          ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
            continuous_snd)) }
  have hHW (w : W) : (HW w).1.1 = w.1 ^ 2 := hH ⟨w.1, hWV w.2⟩
  let E : circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' UX ≃ₜ W :=
    { toFun := fun e =>
        ⟨circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total e.1,
          by
            change _ ^ 2 ∈ V
            rw [← circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_squareR e.1]
            · exact e.2
            · exact fun h ↦ e.2.2 h⟩
      invFun := fun w => ⟨Quotient.mk _ (Sum.inr w.1), by
        change circleWedge_three_cover_two_components_aux_sq w.1 ∈ V
        have hw : w.1 ^ 2 ∈ V := w.2
        simpa [circleWedge_three_cover_two_components_aux_sq, pow_two] using hw⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        induction e using Quotient.inductionOn with
        | _ e =>
          rcases e with w | w
          · exfalso
            change circleBase ∈ V at he
            exact he.2 rfl
          · rfl
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_total_continuous.comp
          continuous_subtype_val) (fun e => by
            change _ ^ 2 ∈ V
            simp only [Function.comp_apply]
            rw [← circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_squareR e.1]
            · exact e.2
            · exact fun h ↦ e.2.2 h)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u :
            circleWedge_three_cover_two_components_aux_Double))).comp
              (continuous_inr.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x =>
        ⟨circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR x.1,
          x.2⟩
      invFun := fun v => ⟨Quotient.mk _ (.inr v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        induction x using Quotient.inductionOn with
        | _ x => rcases x with w | w
                 · exact (hx.2 rfl).elim
                 · rfl
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_baseR_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u : CircleWedge))).comp
              (continuous_inr.comp continuous_subtype_val) }
  refine (show IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap
      (Quotient.mk _ (.inr z)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hzUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change Quotient.mk _ (Sum.inr (HW (E e)).1.1) = _
    rw [hHW]
    exact (himage e.1 e.2).symm

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away
    (x : CircleWedge) (hx : x ≠ Quotient.mk _ (.inl circleBase)) :
    IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap x
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' {x}) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    rcases x with z | z
    · apply circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_left
      intro hz
      subst z
      exact hx rfl
    · apply circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_right
      intro hz
      subst z
      apply hx
      exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base) |>.symm

/-! #### Split of `circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge` (lemma-1 PARTIAL, 2026-10-19) -/

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_rel
    (z : Circle) (h : circleWedge_three_cover_two_components_aux_sq z = circleBase) :
    Quotient.mk (Relation.EqvGen.setoid circleWedge_three_cover_two_components_aux_Rel)
        (Sum.inr z) = Quotient.mk _ (Sum.inl z) := by
  have hz : (z : ℂ) * z = 1 := by
    have hz' := congrArg Subtype.val h
    simpa [circleWedge_three_cover_two_components_aux_sq, circleBase] using hz'
  rcases (mul_self_eq_one_iff.mp hz) with hz | hz
  · have hz' : z = circleBase := Subtype.ext hz
    subst z
    exact Quotient.sound
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.pos))
  · have hz' : z = -circleBase := by
      apply Subtype.ext
      simpa [circleBase] using hz
    subst z
    exact Quotient.sound
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.neg))

/-- The neighbourhood of the wedge point: the wedge minus the two points `-1`. -/
def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U :
    Set CircleWedge :=
  {q | q ≠ Quotient.mk _ (.inl (-circleBase)) ∧ q ≠ Quotient.mk _ (.inr (-circleBase))}

/-- The cross through `[±1]` in the double cover: the points of either lobe in the
open half-circle `{Re (±z) > 0}` (`b = true` is `+`). -/
def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross
    (b : Bool) : Set circleWedge_three_cover_two_components_aux_Double :=
  {e | ∃ z : Circle, 0 < ((if b then (1 : ℂ) else -1) * (z : ℂ)).re ∧
    (e = Quotient.mk _ (.inl z) ∨ e = Quotient.mk _ (.inr z))}

/-- The principal square root on the circle minus `-1`: continuous, lands in
`{Re > 0}`, and every square root of `w` is `±` it. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_norm
    (w : Circle) : ‖(w : ℂ)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using w.property

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_sq
    (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  exact Complex.cpow_nat_inv_pow w (by norm_num)

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_mem
    (w : Circle) : Complex.sqrt (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hs := congrArg norm
    (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_sq
      (w : ℂ))
  rw [norm_pow,
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_norm w]
    at hs
  nlinarith [norm_nonneg (Complex.sqrt (w : ℂ))]

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt :
    ∃ r : {w : Circle // w ≠ -circleBase} → Circle, Continuous r ∧
      (∀ w, circleWedge_three_cover_two_components_aux_sq (r w) = w.1) ∧
      (∀ w, 0 < (r w : ℂ).re) ∧
      (∀ w z, circleWedge_three_cover_two_components_aux_sq z = w.1 → z = r w ∨ z = -r w) := by
  let r : {w : Circle // w ≠ -circleBase} → Circle := fun w ↦
    ⟨Complex.sqrt (w.1 : ℂ),
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_mem w.1⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.2
    intro w
    have hc : 0 ≤ (w.1 : ℂ).re ∨ (w.1 : ℂ).im ≠ 0 := by
      by_cases hi : (w.1 : ℂ).im = 0
      · left
        by_contra hn
        have hr : (w.1 : ℂ).re < 0 := lt_of_not_ge hn
        have hw : w.1 = -circleBase := by
          apply Subtype.ext
          apply Complex.ext
          · have hnrm := circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_norm w.1
            rw [Complex.norm_def, Complex.normSq_apply, hi, mul_zero, add_zero,
              show (w.1 : ℂ).re * (w.1 : ℂ).re = (w.1 : ℂ).re ^ 2 by ring,
              Real.sqrt_sq_eq_abs, abs_of_neg hr] at hnrm
            simp [circleBase]
            linarith
          · simpa [circleBase, hi]
        exact w.2 hw
      · exact Or.inr hi
    let g : {w : Circle // w ≠ -circleBase} → ℂ := fun x ↦ x.1.1
    have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
    change ContinuousAt (Complex.sqrt ∘ g) w
    have hs : ContinuousAt Complex.sqrt (g w) :=
      Complex.continuousAt_sqrt (by simpa [g] using hc)
    exact hs.comp hg.continuousAt
  · intro w
    apply Subtype.ext
    simpa [circleWedge_three_cover_two_components_aux_sq, r, pow_two] using
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_sq
        (w.1 : ℂ)
  · intro w
    change 0 < (Complex.sqrt (w.1 : ℂ)).re
    rw [Complex.sqrt, Complex.cpow_def]
    have hw0 : (w.1 : ℂ) ≠ 0 := by
      intro h
      have hn := circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_norm w.1
      simp [h] at hn
    rw [if_neg hw0, Complex.exp_re]
    norm_num [Complex.mul_im, Complex.log_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply]
    apply mul_pos (Real.exp_pos _)
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have h := Complex.neg_pi_lt_arg (w.1 : ℂ)
      norm_num at h ⊢
      linarith [Real.pi_pos]
    · have hle := Complex.arg_le_pi (w.1 : ℂ)
      have hne : (w.1 : ℂ).arg ≠ Real.pi := by
        intro he
        have hp := Complex.arg_eq_pi_iff.1 he
        have hw : w.1 = -circleBase := by
          apply Subtype.ext
          apply Complex.ext
          · have hnrm := circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_norm w.1
            rw [Complex.norm_def, Complex.normSq_apply, hp.2, mul_zero, add_zero,
              ← pow_two, Real.sqrt_sq_eq_abs, abs_of_neg hp.1] at hnrm
            simp [circleBase]
            linarith
          · simpa [circleBase, hp.2]
        exact w.2 hw
      have hlt : (w.1 : ℂ).arg < Real.pi := lt_of_le_of_ne hle hne
      norm_num at hlt ⊢
      linarith [Real.pi_pos]
  · intro w z hz
    have hv : (z : ℂ) = (r w : ℂ) ∨ (z : ℂ) = -(r w : ℂ) :=
      (sq_eq_sq_iff_eq_or_eq_neg).mp (by
        have hr := circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt_aux_sq
          (w.1 : ℂ)
        have hz' : (z : ℂ) ^ 2 = (w.1 : ℂ) := by
          simpa [circleWedge_three_cover_two_components_aux_sq, pow_two] using
            congrArg Subtype.val hz
        exact hz'.trans hr.symm)
    rcases hv with hv | hv
    · exact Or.inl (Subtype.ext hv)
    · exact Or.inr (Subtype.ext hv)

/-- Points of the wedge are closed (each has a closed preimage in `Circle ⊕ Circle`),
so `U` is open. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U_open :
    IsOpen circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U := by
  let V : Set Circle := ({-circleBase} : Set Circle)ᶜ
  let W : Set (Sum Circle Circle) := Sum.inl '' V ∪ Sum.inr '' V
  have hV : IsOpen V := by
    have h : IsOpen ((Subtype.val : Circle → ℂ) ⁻¹' ({(-1 : ℂ)} : Set ℂ)ᶜ) :=
      isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
    simpa [V, circleBase] using h
  have hW : IsOpen W := (isOpenMap_inl V hV).union (isOpenMap_inr V hV)
  have key : ∀ u v : Sum Circle Circle, (Quotient.mk _ u : CircleWedge) = Quotient.mk _ v ↔
      u = v ∨ ((u = .inl circleBase ∨ u = .inr circleBase) ∧
        (v = .inl circleBase ∨ v = .inr circleBase)) := fun u v ↦
    Quotient.eq.trans
      (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl_aux_eqv _ _ u v)
  have hne : -circleBase ≠ circleBase := by
    intro h
    have h1 := congrArg (fun x : Circle ↦ (x : ℂ)) h
    norm_num [circleBase] at h1
  have hpre :
      (fun z : Sum Circle Circle ↦ (Quotient.mk _ z : CircleWedge)) ⁻¹'
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U = W := by
    ext z
    rcases z with z | z
    · show ((Quotient.mk _ (Sum.inl z) : CircleWedge) ≠ Quotient.mk _ (Sum.inl (-circleBase)) ∧
          (Quotient.mk _ (Sum.inl z) : CircleWedge) ≠ Quotient.mk _ (Sum.inr (-circleBase))) ↔
          Sum.inl z ∈ W
      simp [W, V, key, hne]
    · show ((Quotient.mk _ (Sum.inr z) : CircleWedge) ≠ Quotient.mk _ (Sum.inl (-circleBase)) ∧
          (Quotient.mk _ (Sum.inr z) : CircleWedge) ≠ Quotient.mk _ (Sum.inr (-circleBase))) ↔
          Sum.inr z ∈ W
      simp [W, V, key, hne]
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen ((fun z : Sum Circle Circle ↦ (Quotient.mk _ z : CircleWedge)) ⁻¹'
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U)
  rw [hpre]
  exact hW

/-- A cross is open: its preimage in `Circle ⊕ Circle` is the half-circle
`{Re (±z) > 0}` in both summands (it is saturated, since the glued points `±1`
lie in the same cross). -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross_open
    (b : Bool) :
    IsOpen (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross b) := by
  let H : Set Circle :=
    {z | 0 < ((if b then (1 : ℂ) else -1) * (z : ℂ)).re}
  have hH : IsOpen H := by
    exact isOpen_lt continuous_const
      (Complex.continuous_re.comp
        (continuous_const.mul continuous_subtype_val))
  let P : Circle ⊕ Circle → Prop := Sum.elim (· ∈ H) (· ∈ H)
  have hP {x y : Circle ⊕ Circle}
      (hxy : Relation.EqvGen circleWedge_three_cover_two_components_aux_Rel x y) :
      P x ↔ P y := by
    rcases (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_rel_iff
      x y).mp hxy with rfl | ⟨z, hz, h⟩
    · rfl
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hpre :
      (fun z : Circle ⊕ Circle ↦
        (Quotient.mk _ z :
          circleWedge_three_cover_two_components_aux_Double)) ⁻¹'
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross b =
        Sum.inl '' H ∪ Sum.inr '' H := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨z, hz, heq | heq⟩
      · have hxP : P x := (hP (Quotient.exact heq)).mpr hz
        rcases x with x | x
        · exact Or.inl ⟨x, hxP, rfl⟩
        · exact Or.inr ⟨x, hxP, rfl⟩
      · have hxP : P x := (hP (Quotient.exact heq)).mpr hz
        rcases x with x | x
        · exact Or.inl ⟨x, hxP, rfl⟩
        · exact Or.inr ⟨x, hxP, rfl⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨z, hz, Or.inl rfl⟩
      · exact ⟨z, hz, Or.inr rfl⟩
  have hq : Topology.IsQuotientMap
      (fun z : Circle ⊕ Circle ↦
        (Quotient.mk _ z : circleWedge_three_cover_two_components_aux_Double)) :=
    ⟨Quotient.mk_surjective, rfl⟩
  apply hq.isOpen_preimage.mp
  rw [hpre]
  exact (isOpenMap_inl H hH).union (isOpenMap_inr H hH)

/-- Combinatorics: the base point lies in `U`; the crosses cover `doubleMap ⁻¹' U`;
they are disjoint. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cover :
    Quotient.mk _ (.inl circleBase) ∈
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U ∧
      (∀ e, circleWedge_three_cover_two_components_aux_doubleMap e ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U →
        ∃ b, e ∈ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross b) ∧
      Disjoint (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross true)
        (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross false) := by
  have hbase : circleBase ≠ -circleBase := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [circleBase] at h'
  have hsquare_neg (z : Circle) (hz : (z : ℂ).re = 0) :
      circleWedge_three_cover_two_components_aux_sq z = -circleBase := by
    have hn : ‖(z : ℂ)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using z.property
    have him : (z : ℂ).im * (z : ℂ).im = 1 := by
      calc
        (z : ℂ).im * (z : ℂ).im = Complex.normSq z := by
          simp [Complex.normSq_apply, hz]
        _ = ‖(z : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
        _ = 1 := by simp [hn]
    apply Subtype.ext
    apply Complex.ext
    · simp [circleWedge_three_cover_two_components_aux_sq, circleBase,
        Complex.mul_re, hz, him]
    · simp [circleWedge_three_cover_two_components_aux_sq, circleBase,
        Complex.mul_im, hz]
  have hwedgeL : (Quotient.mk _ (.inl circleBase) : CircleWedge) ≠
      Quotient.mk _ (.inl (-circleBase)) := by
    intro h
    rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
      circleBase circleBase (.inl circleBase) (.inl (-circleBase))).mp
        (Quotient.exact h) with h | h
    · exact hbase (Sum.inl.inj h)
    · rcases h.2 with h | h
      · exact hbase (Sum.inl.inj h).symm
      · contradiction
  have hwedgeR : (Quotient.mk _ (.inl circleBase) : CircleWedge) ≠
      Quotient.mk _ (.inr (-circleBase)) := by
    intro h
    rcases (rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
      circleBase circleBase (.inl circleBase) (.inr (-circleBase))).mp
        (Quotient.exact h) with h | h
    · contradiction
    · rcases h.2 with h | h
      · contradiction
      · exact hbase (Sum.inr.inj h).symm
  refine ⟨⟨hwedgeL, hwedgeR⟩, ?_, ?_⟩
  · intro e he
    induction e using Quotient.inductionOn with
    | _ e =>
      rcases e with z | z
      · have hz : (z : ℂ).re ≠ 0 := by
          intro hz
          have hz' := hsquare_neg z hz
          exact he.1 (by simpa [circleWedge_three_cover_two_components_aux_doubleMap,
            circleWedge_three_cover_two_components_aux_raw, hz'])
        rcases lt_or_gt_of_ne hz with hz | hz
        · exact ⟨false, z, by simpa, Or.inl rfl⟩
        · exact ⟨true, z, by simpa, Or.inl rfl⟩
      · have hz : (z : ℂ).re ≠ 0 := by
          intro hz
          have hz' := hsquare_neg z hz
          exact he.2 (by simpa [circleWedge_three_cover_two_components_aux_doubleMap,
            circleWedge_three_cover_two_components_aux_raw, hz'])
        rcases lt_or_gt_of_ne hz with hz | hz
        · exact ⟨false, z, by simpa, Or.inr rfl⟩
        · exact ⟨true, z, by simpa, Or.inr rfl⟩
  · rw [Set.disjoint_left]
    intro e ht hf
    rcases ht with ⟨z, hz, hez⟩
    rcases hf with ⟨w, hw, hew⟩
    have hzw : z = w := by
      rcases hez with hez | hez <;> rcases hew with hew | hew
      all_goals
        rcases (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_rel_iff
          _ _).mp (Quotient.exact (hez.symm.trans hew)) with h | ⟨u, hu, h⟩
        · simpa using h
        · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp_all
    subst w
    simp at hz hw
    linarith

/-! Split of `circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections` (lemma-1 PARTIAL, 2026-10-19): `_aux_lift`, `_aux_base`, `_aux_S`
banked from the seat; `_aux_cont`, `_aux_right`, `_aux_range` queued. -/

def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift
    (r : {w : Circle // w ≠ -circleBase} → Circle) (w : Circle) : Circle :=
  if h : w ≠ -circleBase then r ⟨w, h⟩ else circleBase

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_base
    (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hsq : ∀ w, circleWedge_three_cover_two_components_aux_sq (r w) = w.1)
    (hre : ∀ w, 0 < (r w : ℂ).re) :
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift
      r circleBase = circleBase := by
  have hn : circleBase ≠ -circleBase := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num [circleBase] at hh
  rw [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift,
    dif_pos hn]
  let w : {w : Circle // w ≠ -circleBase} := ⟨circleBase, hn⟩
  have hm : ((r w : Circle) : ℂ) * r w = 1 := by
    have h := congrArg Subtype.val (hsq w)
    simpa [circleWedge_three_cover_two_components_aux_sq, circleBase] using h
  rcases (mul_self_eq_one_iff.mp hm) with h | h
  · exact Subtype.ext h
  · have hp := hre w
    rw [h] at hp
    norm_num at hp

def circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S
    (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift
      r circleBase = circleBase) (b : Bool) :
    CircleWedge → circleWedge_three_cover_two_components_aux_Double :=
  Quotient.lift
    (Sum.elim
      (fun w ↦ Quotient.mk _ (.inl (if b then
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r w
        else -circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r w)))
      (fun w ↦ Quotient.mk _ (.inr (if b then
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r w
        else -circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r w))))
    (by
      intro x y h
      induction h with
      | rel x y h =>
          cases h
          change Quotient.mk _ (Sum.inl (if b then _ else _)) =
            Quotient.mk _ (Sum.inr (if b then _ else _))
          cases b <;> simp [hrbase]
          · exact Quotient.sound (Relation.EqvGen.rel _ _
              circleWedge_three_cover_two_components_aux_Rel.neg)
          · exact Quotient.sound (Relation.EqvGen.rel _ _
              circleWedge_three_cover_two_components_aux_Rel.pos)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

/-- Each section is continuous on `U` (`U` avoids both `-1`s, where `_aux_lift`
jumps; its preimage in `Circle ⊕ Circle` is open and saturated). -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_cont_aux_lobes
    {A B Y : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]
    (a : A) (b : B) (U : Set (Wedge A B a b)) (hU : IsOpen U) (g : U → Y)
    (hl : Continuous (fun z : {z : A // (Quotient.mk _ (.inl z) : Wedge A B a b) ∈ U} ↦
      g ⟨_, z.2⟩))
    (hr : Continuous (fun z : {z : B // (Quotient.mk _ (.inr z) : Wedge A B a b) ∈ U} ↦
      g ⟨_, z.2⟩)) : Continuous g := by
  let q : A ⊕ B → Wedge A B a b := fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
  let qU : {z : A ⊕ B // q z ∈ U} → U := U.restrictPreimage q
  let eL : {z : A // q (.inl z) ∈ U} → {z : A ⊕ B // q z ∈ U} :=
    (q ⁻¹' U).restrictPreimage Sum.inl
  let eR : {z : B // q (.inr z) ∈ U} → {z : A ⊕ B // q z ∈ U} :=
    (q ⁻¹' U).restrictPreimage Sum.inr
  have heL : Topology.IsOpenEmbedding eL :=
    Topology.IsOpenEmbedding.inl.restrictPreimage (q ⁻¹' U)
  have heR : Topology.IsOpenEmbedding eR :=
    Topology.IsOpenEmbedding.inr.restrictPreimage (q ⁻¹' U)
  have hL : ContinuousOn (g ∘ qU) (Set.range eL) := by
    rw [← Set.image_univ]
    apply heL.isInducing.continuousOn_image_iff.mpr
    simpa [q, qU, eL, Function.comp_def] using hl
  have hR : ContinuousOn (g ∘ qU) (Set.range eR) := by
    rw [← Set.image_univ]
    apply heR.isInducing.continuousOn_image_iff.mpr
    simpa [q, qU, eR, Function.comp_def] using hr
  rw [← continuousOn_univ]
  have hc := hL.union_of_isOpen hR heL.isOpen_range heR.isOpen_range
  apply hc.mono
  rintro ⟨z, hz⟩ -
  cases z with
  | inl x => exact Set.mem_union_left _ ⟨⟨x, hz⟩, rfl⟩
  | inr x => exact Set.mem_union_right _ ⟨⟨x, hz⟩, rfl⟩

lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_cont
    (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift
      r circleBase = circleBase) (hr : Continuous r) (b : Bool) :
    Continuous (fun u : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U ↦
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S r hrbase b u.1) := by
  apply circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_cont_aux_lobes
    circleBase circleBase _
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U_open
  · have hn (z : {z : Circle //
        (Quotient.mk _ (.inl z) : CircleWedge) ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U}) :
        z.1 ≠ -circleBase := by
      intro h
      exact z.2.1 (congrArg (fun x : Circle ↦ (Quotient.mk _ (.inl x) : CircleWedge)) h)
    have hlift : Continuous (fun z : {z : Circle //
        (Quotient.mk _ (.inl z) : CircleWedge) ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r z.1) := by
      have hc : Continuous (fun z : {z : Circle //
          (Quotient.mk _ (.inl z) : CircleWedge) ∈
            circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
          r ⟨z.1, hn z⟩) :=
        hr.comp (Continuous.subtype_mk continuous_subtype_val _)
      simpa [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift,
        hn] using hc
    cases b
    · have hc := continuous_neg.comp hlift
      have hq : Continuous (fun z : {z : Circle //
          (Quotient.mk _ (.inl z) : CircleWedge) ∈ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
          (Quotient.mk (Relation.EqvGen.setoid circleWedge_three_cover_two_components_aux_Rel)
            (Sum.inl (-circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r z.1)) :
              circleWedge_three_cover_two_components_aux_Double)) :=
        continuous_coinduced_rng.comp (continuous_inl.comp hc)
      simpa [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S] using hq
    · have hq : Continuous (fun z : {z : Circle //
          (Quotient.mk _ (.inl z) : CircleWedge) ∈ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
          (Quotient.mk (Relation.EqvGen.setoid circleWedge_three_cover_two_components_aux_Rel)
            (Sum.inl (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r z.1)) :
              circleWedge_three_cover_two_components_aux_Double)) :=
        continuous_coinduced_rng.comp (continuous_inl.comp hlift)
      simpa [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S] using hq
  · have hn (z : {z : Circle //
        (Quotient.mk _ (.inr z) : CircleWedge) ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U}) :
        z.1 ≠ -circleBase := by
      intro h
      exact z.2.2 (congrArg (fun x : Circle ↦ (Quotient.mk _ (.inr x) : CircleWedge)) h)
    have hlift : Continuous (fun z : {z : Circle //
        (Quotient.mk _ (.inr z) : CircleWedge) ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r z.1) := by
      have hc : Continuous (fun z : {z : Circle //
          (Quotient.mk _ (.inr z) : CircleWedge) ∈
            circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
          r ⟨z.1, hn z⟩) :=
        hr.comp (Continuous.subtype_mk continuous_subtype_val _)
      simpa [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift,
        hn] using hc
    cases b
    · have hc := continuous_neg.comp hlift
      have hq : Continuous (fun z : {z : Circle //
          (Quotient.mk _ (.inr z) : CircleWedge) ∈ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
          (Quotient.mk (Relation.EqvGen.setoid circleWedge_three_cover_two_components_aux_Rel)
            (Sum.inr (-circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r z.1)) :
              circleWedge_three_cover_two_components_aux_Double)) :=
        continuous_coinduced_rng.comp (continuous_inr.comp hc)
      simpa [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S] using hq
    · have hq : Continuous (fun z : {z : Circle //
          (Quotient.mk _ (.inr z) : CircleWedge) ∈ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U} ↦
          (Quotient.mk (Relation.EqvGen.setoid circleWedge_three_cover_two_components_aux_Rel)
            (Sum.inr (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift r z.1)) :
              circleWedge_three_cover_two_components_aux_Double)) :=
        continuous_coinduced_rng.comp (continuous_inr.comp hlift)
      simpa [circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S] using hq

/-- Each section is a right inverse of `doubleMap` on `U`. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_right
    (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift
      r circleBase = circleBase)
    (hsq : ∀ w, circleWedge_three_cover_two_components_aux_sq (r w) = w.1)
    (b : Bool) (u : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U) :
    circleWedge_three_cover_two_components_aux_doubleMap
      (circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S r hrbase b u.1) = u := by
  sorry

/-- The `b`-section over `U` has range exactly the `b`-cross. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_range
    (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_lift
      r circleBase = circleBase)
    (hsq : ∀ w, circleWedge_three_cover_two_components_aux_sq (r w) = w.1)
    (hre : ∀ w, 0 < (r w : ℂ).re)
    (hroots : ∀ w z, circleWedge_three_cover_two_components_aux_sq z = w.1 → z = r w ∨ z = -r w)
    (b : Bool) :
    Set.range (fun u : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U ↦
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S r hrbase b u.1) =
      circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross b := by
  sorry

/-- The two local sections over `U`, built from a square-root branch `r`:
`[inl w] ↦ [inl (±r w)]`, `[inr w] ↦ [inr (±r w)]` (well defined at the wedge point
since `r 1 = 1`). Continuity: `U`'s preimage in `Circle ⊕ Circle` is open and
saturated, so the quotient map restricts to a quotient map there
(`IsQuotientMap.restrictPreimage_isOpen`). -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections
    (r : {w : Circle // w ≠ -circleBase} → Circle) (hr : Continuous r)
    (hsq : ∀ w, circleWedge_three_cover_two_components_aux_sq (r w) = w.1)
    (hre : ∀ w, 0 < (r w : ℂ).re)
    (hroots : ∀ w z, circleWedge_three_cover_two_components_aux_sq z = w.1 → z = r w ∨ z = -r w) :
    ∃ s : Bool → circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U →
        circleWedge_three_cover_two_components_aux_Double,
      (∀ b, Continuous (s b)) ∧
      (∀ b u, circleWedge_three_cover_two_components_aux_doubleMap (s b u) = u) ∧
      (∀ b, Set.range (s b) =
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross b) := by
  have hrbase := circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_base r hsq hre
  exact ⟨fun b u ↦ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_S r hrbase b u.1,
    fun b ↦ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_cont r hrbase hr b,
    fun b u ↦ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_right r hrbase hsq b u,
    fun b ↦ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections_aux_range r hrbase hsq hre hroots b⟩

/-- At the wedge point: `V` = the image of the open arcs `{Re z > 0}` in both
lobes. Its preimage is two disjoint open "crosses", one through `[inl 1] = [inr 1]`
and one through `[inl (-1)] = [inr (-1)]`; each is the wedge of two half-arcs
mapped homeomorphically onto `V` by squaring on each lobe. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge :
    IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap
      (Quotient.mk _ (.inl circleBase))
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹'
        {Quotient.mk _ (.inl circleBase)}) := by
  obtain ⟨r, hr, hsq, hre, hroots⟩ :=
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sqrt
  obtain ⟨s, hs, hfs, hrange⟩ :=
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_sections
      r hr hsq hre hroots
  obtain ⟨hmem, hcov, hdisj⟩ :=
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cover
  refine (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections
    circleWedge_three_cover_two_components_aux_doubleMap
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_continuous
    _ _ hmem
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U_open
    s hs hfs (fun b ↦ by
      rw [hrange b]
      exact circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross_open b)
    (fun e he ↦ by
      obtain ⟨b, hb⟩ := hcov e he
      rw [← hrange b] at hb
      obtain ⟨u, hu⟩ := hb
      exact ⟨b, u, hu⟩)
    (fun i j u v h ↦ by
      have hi : s i u ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross i :=
        hrange i ▸ ⟨u, rfl⟩
      have hj : s i u ∈
          circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cross j :=
        h ▸ hrange j ▸ ⟨v, rfl⟩
      cases i <;> cases j
      · rfl
      · exact absurd hi (Set.disjoint_left.mp hdisj hj)
      · exact absurd hj (Set.disjoint_left.mp hdisj hi)
      · rfl)).to_isEvenlyCovered_preimage

lemma circleWedge_three_cover_two_components_aux_covering_aux_double :
    IsCoveringMap circleWedge_three_cover_two_components_aux_doubleMap := by
  intro x
  classical
  by_cases hx : x = Quotient.mk _ (.inl circleBase)
  · subst x
    exact circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge
  · exact circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away x hx

lemma circleWedge_three_cover_two_components_aux_covering_aux_id :
    IsCoveringMap (id : CircleWedge → CircleWedge) := by
  intro x
  exact IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit) ⟨inferInstance, Set.univ, trivial,
    isOpen_univ, isOpen_univ, (Homeomorph.prodPUnit _).symm, fun _ ↦ rfl⟩

/-- A disjoint sum of two covering maps over the same base is a covering map. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_open
    {E₁ E₂ X : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X]
    {f : E₁ → X} {g : E₂ → X} {U : Set X}
    (hf : IsOpen (f ⁻¹' U)) (hg : IsOpen (g ⁻¹' U)) :
    IsOpen (Sum.elim f g ⁻¹' U) := by
  rw [isOpen_sum_iff]
  exact ⟨hf, hg⟩

/-- A local trivialisation over `U` restricts to one over any `V ⊆ U`. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_shrink
    {E X I : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace I]
    {f : E → X} {U V : Set X} (H : f ⁻¹' U ≃ₜ U × I) (hH : ∀ e, (H e).1.1 = f e)
    (hVU : V ⊆ U) :
    ∃ H' : f ⁻¹' V ≃ₜ V × I, ∀ e, (H' e).1.1 = f e := by
  let inc : f ⁻¹' V → f ⁻¹' U := fun e ↦ ⟨e.1, hVU e.2⟩
  let lift : V × I → U × I := fun y ↦ (⟨y.1.1, hVU y.1.2⟩, y.2)
  let toFun : f ⁻¹' V → V × I := fun e ↦
    (⟨(H (inc e)).1.1, hH (inc e) ▸ e.2⟩, (H (inc e)).2)
  let invFun : V × I → f ⁻¹' V := fun y ↦
    ⟨(H.symm (lift y)).1, by
      have heq : H (H.symm (lift y)) = lift y := H.apply_symm_apply (lift y)
      have := hH (H.symm (lift y))
      rw [heq] at this
      change f (H.symm (lift y)).1 ∈ V
      exact this ▸ y.1.2⟩
  let H' : f ⁻¹' V ≃ₜ V × I :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun e ↦ by
        apply Subtype.ext
        change (invFun (toFun e)).1 = e.1
        have hz : H (H.symm (lift (toFun e))) = H (inc e) := by
          rw [H.apply_symm_apply]
        exact congrArg (fun z : f ⁻¹' U ↦ z.1) (H.injective hz)
      right_inv := fun y ↦ by
        have hi : inc (invFun y) = H.symm (lift y) := Subtype.ext rfl
        have hz : H (inc (invFun y)) = lift y :=
          (congrArg H hi).trans (H.apply_symm_apply (lift y))
        apply Prod.ext
        · apply Subtype.ext
          change (H (inc (invFun y))).1.1 = y.1.1
          exact congrArg (fun z ↦ z.1.1) hz
        · change (H (inc (invFun y))).2 = y.2
          exact congrArg Prod.snd hz
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa [inc, toFun] using
            (continuous_subtype_val.comp
              (H.continuous.comp (continuous_subtype_val.subtype_mk _)).fst)
        · simpa [inc, toFun] using
            (H.continuous.comp (continuous_subtype_val.subtype_mk _)).snd
      continuous_invFun := by
        apply Continuous.subtype_mk
        have hlift : Continuous lift :=
          ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
        simpa only [invFun] using
          continuous_subtype_val.comp (H.symm.continuous.comp hlift) }
  exact ⟨H', fun e ↦ hH (inc e)⟩

/-- Two local trivialisations over the same `W` glue to one for `Sum.elim f g`,
with fibre the disjoint union of the fibres. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_glue
    {E₁ E₂ X I J : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X]
    [TopologicalSpace I] [TopologicalSpace J] {f : E₁ → X} {g : E₂ → X} {W : Set X}
    (H₁ : f ⁻¹' W ≃ₜ W × I) (hH₁ : ∀ e, (H₁ e).1.1 = f e)
    (H₂ : g ⁻¹' W ≃ₜ W × J) (hH₂ : ∀ e, (H₂ e).1.1 = g e) :
    ∃ H : Sum.elim f g ⁻¹' W ≃ₜ W × (I ⊕ J), ∀ e, (H e).1.1 = Sum.elim f g e := by
  let e : Sum.elim f g ⁻¹' W ≃ (f ⁻¹' W) ⊕ (g ⁻¹' W) :=
    { toFun := fun z ↦ match z with
        | ⟨.inl x, h⟩ => .inl ⟨x, h⟩
        | ⟨.inr y, h⟩ => .inr ⟨y, h⟩
      invFun := Sum.elim (fun x ↦ ⟨.inl x.1, x.2⟩) (fun y ↦ ⟨.inr y.1, y.2⟩)
      left_inv := by rintro ⟨x | y, h⟩ <;> rfl
      right_inv := by rintro (x | y) <;> rfl }
  have hec : Continuous e := by
    rw [continuous_def]
    intro s hs
    rw [isOpen_sum_iff] at hs
    obtain ⟨u, hu, eu⟩ := hs.1
    obtain ⟨v, hv, ev⟩ := hs.2
    refine ⟨(Sum.inl '' u) ∪ (Sum.inr '' v),
      (isOpenMap_inl u hu).union (isOpenMap_inr v hv), ?_⟩
    ext z
    rcases z with ⟨x | y, hx⟩
    · change Sum.inl x ∈ (Sum.inl '' u) ∪ (Sum.inr '' v) ↔
        (⟨x, hx⟩ : f ⁻¹' W) ∈ Sum.inl ⁻¹' s
      rw [← eu]; simp
    · change Sum.inr y ∈ (Sum.inl '' u) ∪ (Sum.inr '' v) ↔
        (⟨y, hx⟩ : g ⁻¹' W) ∈ Sum.inr ⁻¹' s
      rw [← ev]; simp
  have hes : Continuous e.symm :=
    continuous_sum_dom.2 ⟨(continuous_inl.comp continuous_subtype_val).subtype_mk _,
      (continuous_inr.comp continuous_subtype_val).subtype_mk _⟩
  let K : Sum.elim f g ⁻¹' W ≃ₜ (f ⁻¹' W) ⊕ (g ⁻¹' W) :=
    { e with continuous_toFun := hec, continuous_invFun := hes }
  let L := Homeomorph.sumCongr H₁ H₂
  let D : (W × I) ⊕ (W × J) ≃ₜ W × (I ⊕ J) := Homeomorph.prodSumDistrib.symm
  refine ⟨K.trans (L.trans D), ?_⟩
  rintro ⟨x | y, h⟩
  · exact hH₁ ⟨x, h⟩
  · exact hH₂ ⟨y, h⟩

lemma circleWedge_three_cover_two_components_aux_covering_aux_sum
    {E₁ E₂ X : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X]
    {f : E₁ → X} {g : E₂ → X} (hf : IsCoveringMap f) (hg : IsCoveringMap g) :
    IsCoveringMap (Sum.elim f g) := by
  intro x
  obtain ⟨hI, U₁, hxU₁, hU₁, hfU₁, H₁, hH₁⟩ := hf x
  obtain ⟨hJ, U₂, hxU₂, hU₂, hgU₂, H₂, hH₂⟩ := hg x
  obtain ⟨K₁, hK₁⟩ := circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_shrink
    H₁ hH₁ (Set.inter_subset_left : U₁ ∩ U₂ ⊆ U₁)
  obtain ⟨K₂, hK₂⟩ := circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_shrink
    H₂ hH₂ (Set.inter_subset_right : U₁ ∩ U₂ ⊆ U₂)
  obtain ⟨K, hK⟩ := circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_glue
    K₁ hK₁ K₂ hK₂
  have hW : IsOpen (U₁ ∩ U₂) := hU₁.inter hU₂
  have hev : IsEvenlyCovered (Sum.elim f g) x ((f ⁻¹' {x}) ⊕ (g ⁻¹' {x})) :=
    ⟨inferInstance, U₁ ∩ U₂, ⟨hxU₁, hxU₂⟩, hW,
      circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_open
        (hf.continuous.isOpen_preimage _ hW) (hg.continuous.isOpen_preimage _ hW), K, hK⟩
  exact hev.to_isEvenlyCovered_preimage

lemma circleWedge_three_cover_two_components_aux_covering :
    IsCoveringMap circleWedge_three_cover_two_components_aux_map := by
  have h := circleWedge_three_cover_two_components_aux_covering_aux_sum
    circleWedge_three_cover_two_components_aux_covering_aux_id
    circleWedge_three_cover_two_components_aux_covering_aux_double
  have he : circleWedge_three_cover_two_components_aux_map =
      Sum.elim id circleWedge_three_cover_two_components_aux_doubleMap := by
    funext e; rcases e with x | x <;> rfl
  rw [he]; exact h

lemma circleWedge_three_cover_two_components_aux_fiber_sq_card (y : Circle) :
    Nat.card {z : Circle // circleWedge_three_cover_two_components_aux_sq z = y} = 2 := by
  let f : Circle →* Circle := powMonoidHom 2
  have hs : Function.Surjective f :=
    (Circle.isQuotientCoveringMap_npow 2).surjective
  let a : Circle := Function.surjInv hs y
  have ha : f a = y := Function.surjInv_eq hs y
  let m : Circle := ⟨-1, by simp⟩
  have hm1 : m ≠ 1 := by
    intro h
    have := congrArg (fun z : Circle ↦ (z : ℂ)) h
    norm_num [m] at this
  have hmk : m ∈ f.ker := by
    change m ^ 2 = 1
    ext
    simp [m, pow_two]
  have hk : Nat.card f.ker = 2 := by
    let e : f.ker ≃ Bool :=
      { toFun := fun z ↦ if z.1 = 1 then false else true
        invFun := fun i ↦ if i then ⟨m, hmk⟩ else 1
        left_inv := fun z ↦ by
          have hz : (z.1 : ℂ) * z.1 = 1 := by
            have h2 : z.1 ^ 2 = 1 := z.2
            have := congrArg (fun w : Circle ↦ (w : ℂ)) h2
            simpa [pow_two] using this
          rcases (mul_self_eq_one_iff.mp hz) with hz | hz
          · have hz' : z.1 = 1 := Circle.ext (by simpa using hz)
            apply Subtype.ext
            simp [hz']
          · have hz' : z.1 = m := Circle.ext (by simpa [m] using hz)
            apply Subtype.ext
            simp [hz', hm1]
        right_inv := fun i ↦ by
          cases i <;> simp [hm1] }
    simpa using Nat.card_congr e
  have hc : Nat.card {z : Circle // f z = y} = 2 := by
    rw [← ha]
    exact (Nat.card_congr (MonoidHom.fiberEquivKer f a)).trans hk
  simpa [f, circleWedge_three_cover_two_components_aux_sq, pow_two] using hc

lemma circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_rel
    (z : Circle) (h : circleWedge_three_cover_two_components_aux_sq z = circleBase) :
    Quotient.mk (Relation.EqvGen.setoid circleWedge_three_cover_two_components_aux_Rel)
        (Sum.inr z) = Quotient.mk _ (Sum.inl z) := by
  have hz : (z : ℂ) * z = 1 := by
    have := congrArg Subtype.val h
    simpa [circleWedge_three_cover_two_components_aux_sq, circleBase] using this
  rcases (mul_self_eq_one_iff.mp hz) with hz | hz
  · have hz' : z = circleBase := Subtype.ext hz
    subst z
    exact Quotient.sound
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.pos))
  · have hz' : z = -circleBase := by
      apply Subtype.ext
      simpa [circleBase] using hz
    subst z
    exact Quotient.sound
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        circleWedge_three_cover_two_components_aux_Rel.neg))

def circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_value :
    circleWedge_three_cover_two_components_aux_Double → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h <;> rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_baseValue :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_three_cover_two_components_aux_fiber_aux_double
    (x : Circle) (left : Bool) :
    Nat.card {e : circleWedge_three_cover_two_components_aux_Double //
      circleWedge_three_cover_two_components_aux_doubleMap e =
        Quotient.mk _ (if left then Sum.inl x else Sum.inr x)} = 2 := by
  let F := {e : circleWedge_three_cover_two_components_aux_Double //
      circleWedge_three_cover_two_components_aux_doubleMap e =
        Quotient.mk _ (if left then Sum.inl x else Sum.inr x)}
  let S := {z : Circle // circleWedge_three_cover_two_components_aux_sq z = x}
  let toS : F → S := fun e ↦
    ⟨circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_value e.1, by
      obtain ⟨u, hu⟩ := Quotient.exists_rep e.1
      rw [← hu]
      have he := e.2
      rw [← hu] at he
      rcases u with z | z
      · change circleWedge_three_cover_two_components_aux_sq z = x
        have := congrArg
          circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_baseValue he
        cases left <;> simpa [circleWedge_three_cover_two_components_aux_doubleMap,
          circleWedge_three_cover_two_components_aux_raw,
          circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_baseValue] using this
      · change circleWedge_three_cover_two_components_aux_sq z = x
        have := congrArg
          circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_baseValue he
        cases left <;> simpa [circleWedge_three_cover_two_components_aux_doubleMap,
          circleWedge_three_cover_two_components_aux_raw,
          circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_baseValue] using this⟩
  let fromS : S → F := fun z ↦
    ⟨Quotient.mk _ (if left then Sum.inl z.1 else Sum.inr z.1), by
      cases left <;> simp [circleWedge_three_cover_two_components_aux_doubleMap,
        circleWedge_three_cover_two_components_aux_raw, z.2]⟩
  let E : F ≃ S :=
    { toFun := toS
      invFun := fromS
      right_inv := fun z ↦ by apply Subtype.ext; cases left <;> rfl
      left_inv := fun e ↦ by
        apply Subtype.ext
        obtain ⟨u, hu⟩ := Quotient.exists_rep e.1
        change Quotient.mk _ (if left then Sum.inl
          (circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_value e.1)
          else Sum.inr
          (circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_value e.1)) = e.1
        rw [← hu]
        rcases u with z | z
        · cases left
          · exact circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_rel z
              (by
                have he := (congrArg circleWedge_three_cover_two_components_aux_doubleMap hu).trans e.2
                change Quotient.mk _ (Sum.inl (circleWedge_three_cover_two_components_aux_sq z)) =
                  Quotient.mk _ (Sum.inr x) at he
                rw [Quotient.eq_iff_equiv] at he
                change Relation.EqvGen (WedgeRel circleBase circleBase) _ _ at he
                rw [
                  rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
                    circleBase circleBase] at he
                rcases he with he | ⟨hz, hx⟩
                · cases he
                · rcases hz with hz | hz <;> simp_all)
          · rfl
        · cases left
          · rfl
          · symm
            exact circleWedge_three_cover_two_components_aux_fiber_aux_double_aux_rel z
              (by
                have he := (congrArg circleWedge_three_cover_two_components_aux_doubleMap hu).trans e.2
                change Quotient.mk _ (Sum.inr (circleWedge_three_cover_two_components_aux_sq z)) =
                  Quotient.mk _ (Sum.inl x) at he
                rw [Quotient.eq_iff_equiv] at he
                change Relation.EqvGen (WedgeRel circleBase circleBase) _ _ at he
                rw [
                  rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
                    circleBase circleBase] at he
                rcases he with he | ⟨hz, hx⟩
                · cases he
                · rcases hz with hz | hz <;> simp_all) }
  rw [Nat.card_congr E]
  exact circleWedge_three_cover_two_components_aux_fiber_sq_card x

lemma circleWedge_three_cover_two_components_aux_fiber (b : CircleWedge) :
    Nat.card {e : circleWedge_three_cover_two_components_aux_Total //
      circleWedge_three_cover_two_components_aux_map e = b} = 3 := by
  obtain ⟨u, rfl⟩ := Quotient.exists_rep b
  rcases u with x | x
  · let E : {e : circleWedge_three_cover_two_components_aux_Total //
          circleWedge_three_cover_two_components_aux_map e = Quotient.mk _ (Sum.inl x)} ≃
          Unit ⊕ {e : circleWedge_three_cover_two_components_aux_Double //
            circleWedge_three_cover_two_components_aux_doubleMap e =
              Quotient.mk _ (Sum.inl x)} :=
        { toFun := fun e ↦ by
            rcases e with ⟨y, hy⟩
            rcases y with y | z
            · exact .inl ()
            · exact .inr ⟨z, hy⟩
          invFun := fun e ↦ match e with
            | .inl _ => ⟨.inl (Quotient.mk _ (.inl x)), rfl⟩
            | .inr z => ⟨.inr z.1, z.2⟩
          left_inv := fun e ↦ by
            rcases e with ⟨y, hy⟩
            rcases y with y | y
            · exact Subtype.ext (congrArg Sum.inl (show y = _ from hy).symm)
            · rfl
          right_inv := fun e ↦ by rcases e with ⟨⟩ | e <;> rfl }
    have hd : Nat.card {e : circleWedge_three_cover_two_components_aux_Double //
        circleWedge_three_cover_two_components_aux_doubleMap e =
          Quotient.mk _ (Sum.inl x)} = 2 := by
      simpa using circleWedge_three_cover_two_components_aux_fiber_aux_double x true
    letI : Finite {e : circleWedge_three_cover_two_components_aux_Double //
        circleWedge_three_cover_two_components_aux_doubleMap e =
          Quotient.mk _ (Sum.inl x)} := Nat.finite_of_card_ne_zero (by rw [hd]; norm_num)
    rw [Nat.card_congr E, Nat.card_sum, Nat.card_unique, hd]
  · let E : {e : circleWedge_three_cover_two_components_aux_Total //
          circleWedge_three_cover_two_components_aux_map e = Quotient.mk _ (Sum.inr x)} ≃
          Unit ⊕ {e : circleWedge_three_cover_two_components_aux_Double //
            circleWedge_three_cover_two_components_aux_doubleMap e =
              Quotient.mk _ (Sum.inr x)} :=
        { toFun := fun e ↦ by
            rcases e with ⟨y, hy⟩
            rcases y with y | z
            · exact .inl ()
            · exact .inr ⟨z, hy⟩
          invFun := fun e ↦ match e with
            | .inl _ => ⟨.inl (Quotient.mk _ (.inr x)), rfl⟩
            | .inr z => ⟨.inr z.1, z.2⟩
          left_inv := fun e ↦ by
            rcases e with ⟨y, hy⟩
            rcases y with y | y
            · exact Subtype.ext (congrArg Sum.inl (show y = _ from hy).symm)
            · rfl
          right_inv := fun e ↦ by rcases e with ⟨⟩ | e <;> rfl }
    have hd : Nat.card {e : circleWedge_three_cover_two_components_aux_Double //
        circleWedge_three_cover_two_components_aux_doubleMap e =
          Quotient.mk _ (Sum.inr x)} = 2 := by
      simpa using circleWedge_three_cover_two_components_aux_fiber_aux_double x false
    letI : Finite {e : circleWedge_three_cover_two_components_aux_Double //
        circleWedge_three_cover_two_components_aux_doubleMap e =
          Quotient.mk _ (Sum.inr x)} := Nat.finite_of_card_ne_zero (by rw [hd]; norm_num)
    rw [Nat.card_congr E, Nat.card_sum, Nat.card_unique, hd]

lemma circleWedge_three_cover_two_components_aux_components :
    Nat.card (ConnectedComponents
      circleWedge_three_cover_two_components_aux_Total) = 2 := by
  letI : ConnectedSpace Circle := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := ℂ) (by norm_num [Complex.rank_real_complex]) 0 (by norm_num))
  let q : Circle ⊕ Circle →
      circleWedge_three_cover_two_components_aux_Double := Quotient.mk _
  let l : Circle → circleWedge_three_cover_two_components_aux_Double :=
    fun z ↦ q (.inl z)
  let r : Circle → circleWedge_three_cover_two_components_aux_Double :=
    fun z ↦ q (.inr z)
  have hl : IsConnected (Set.range l) :=
    isConnected_range (continuous_coinduced_rng.comp continuous_inl)
  have hr : IsConnected (Set.range r) :=
    isConnected_range (continuous_coinduced_rng.comp continuous_inr)
  have hinter : (Set.range l ∩ Set.range r).Nonempty := by
    refine ⟨q (.inl circleBase), ⟨⟨circleBase, rfl⟩, ⟨circleBase, ?_⟩⟩⟩
    exact (Quotient.sound (Relation.EqvGen.rel _ _
      circleWedge_three_cover_two_components_aux_Rel.pos)).symm
  have hcover : Set.range l ∪ Set.range r = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    rcases x with a | b
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  have hdouble : IsConnected
      (Set.univ : Set circleWedge_three_cover_two_components_aux_Double) := by
    rw [← hcover]
    exact hl.union hinter hr
  let U : Bool → Set circleWedge_three_cover_two_components_aux_Total
    | false => Set.range Sum.inl
    | true => Set.range Sum.inr
  have hclopen : ∀ b, IsClopen (U b) := by
    intro b
    cases b
    · exact isClopen_range_inl
    · exact isClopen_range_inr
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · refine Set.disjoint_left.2 ?_
      rintro _ ⟨x, rfl⟩ ⟨y, h⟩
      exact Sum.inr_ne_inl h
    · refine Set.disjoint_left.2 ?_
      rintro _ ⟨x, rfl⟩ ⟨y, h⟩
      exact Sum.inl_ne_inr h
    · exact (hbc rfl).elim
  have hunion : ⋃ b, U b = Set.univ := by
    ext z
    rcases z with z | z <;> simp [U]
  have hconn : ∀ b, IsConnected (U b) := by
    intro b
    cases b
    · simpa [U] using
        circleWedge_three_cover_three_components_aux_connected.image Sum.inl
          continuous_inl.continuousOn
    · simpa [U] using hdouble.image Sum.inr continuous_inr.continuousOn
  let e := ConnectedComponents.equivOfIsClopenOfIsConnected
    hclopen hdisj hunion hconn
  simpa using Nat.card_congr e

theorem circleWedge_three_cover_two_components : ∃ C : ThreeCover,
    Nat.card (@ConnectedComponents C.E C.topology) = 2 := by
  let C : ThreeCover :=
    { E := circleWedge_three_cover_two_components_aux_Total
      topology := inferInstance
      p := circleWedge_three_cover_two_components_aux_map
      covering := ⟨circleWedge_three_cover_two_components_aux_covering,
        circleWedge_three_cover_two_components_aux_fiber⟩ }
  exact ⟨C, circleWedge_three_cover_two_components_aux_components⟩

/-- The pairs `((123),1)` and `((123),(123))` realize two connected
three-sheeted covers whose total spaces are not homeomorphic: deleting the
topologically intrinsic valence-four locus leaves three loop edges in the
first graph and none in the second. -/
lemma circleWedge_connected_pair_aux_circleBase_cube :
    (circleBase : ℂ) ^ 3 = circleBase := by
  simp [circleBase]

/-- The three cube roots of the base point, used as the common fibre at which
the two lifted circles are glued.  Keeping the fibre as a subtype avoids making
an arbitrary choice of an enumeration of the roots. -/
abbrev circleWedge_connected_pair_aux_Root :=
  {z : Circle // (⟨(z : ℂ) ^ 3, by simpa using pow_mem_sphere z.property 3⟩ : Circle) =
    circleBase}

/-- Cubing on the unit circle. -/
def circleWedge_connected_pair_aux_cube (z : Circle) : Circle :=
  ⟨(z : ℂ) ^ 3, by simpa using pow_mem_sphere z.property 3⟩

/-- Raw space for `((123),1)`: one connected threefold lift on the left and
three identity lifts on the right. -/
abbrev circleWedge_connected_pair_aux_RawC :=
  Circle ⊕ (Circle × circleWedge_connected_pair_aux_Root)

inductive circleWedge_connected_pair_aux_RelC :
    circleWedge_connected_pair_aux_RawC →
      circleWedge_connected_pair_aux_RawC → Prop
  | glue (r : circleWedge_connected_pair_aux_Root) :
      circleWedge_connected_pair_aux_RelC (.inl r.1) (.inr (circleBase, r))

/-- Raw space for `((123),(123))`: connected threefold lifts on both sides. -/
abbrev circleWedge_connected_pair_aux_RawD := Circle ⊕ Circle

inductive circleWedge_connected_pair_aux_RelD :
    circleWedge_connected_pair_aux_RawD →
      circleWedge_connected_pair_aux_RawD → Prop
  | glue (r : circleWedge_connected_pair_aux_Root) :
      circleWedge_connected_pair_aux_RelD (.inl r.1) (.inr r.1)

def circleWedge_connected_pair_aux_EC :=
  Quotient (Relation.EqvGen.setoid circleWedge_connected_pair_aux_RelC)

def circleWedge_connected_pair_aux_ED :=
  Quotient (Relation.EqvGen.setoid circleWedge_connected_pair_aux_RelD)

noncomputable instance : TopologicalSpace circleWedge_connected_pair_aux_EC :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

noncomputable instance : TopologicalSpace circleWedge_connected_pair_aux_ED :=
  TopologicalSpace.coinduced (fun z ↦ Quotient.mk _ z) inferInstance

def circleWedge_connected_pair_aux_projC :
    circleWedge_connected_pair_aux_RawC → CircleWedge
  | .inl z => Quotient.mk _ (.inl (circleWedge_connected_pair_aux_cube z))
  | .inr z => Quotient.mk _ (.inr z.1)

def circleWedge_connected_pair_aux_projD :
    circleWedge_connected_pair_aux_RawD → CircleWedge
  | .inl z => Quotient.mk _ (.inl (circleWedge_connected_pair_aux_cube z))
  | .inr z => Quotient.mk _ (.inr (circleWedge_connected_pair_aux_cube z))

lemma circleWedge_connected_pair_aux_projC_respects {a b}
    (h : Relation.EqvGen circleWedge_connected_pair_aux_RelC a b) :
    circleWedge_connected_pair_aux_projC a =
      circleWedge_connected_pair_aux_projC b := by
  induction h with
  | rel a b h =>
      cases h with
      | glue r =>
          have hr : circleWedge_connected_pair_aux_cube r.1 = circleBase := r.2
          apply Quotient.sound
          rw [hr]
          apply Relation.EqvGen.rel
          exact WedgeRel.base
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma circleWedge_connected_pair_aux_projD_respects {a b}
    (h : Relation.EqvGen circleWedge_connected_pair_aux_RelD a b) :
    circleWedge_connected_pair_aux_projD a =
      circleWedge_connected_pair_aux_projD b := by
  induction h with
  | rel a b h =>
      cases h with
      | glue r =>
          have hr : circleWedge_connected_pair_aux_cube r.1 = circleBase := r.2
          apply Quotient.sound
          rw [hr]
          exact Relation.EqvGen.rel _ _ WedgeRel.base
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def circleWedge_connected_pair_aux_pC :
    circleWedge_connected_pair_aux_EC → CircleWedge :=
  Quotient.lift circleWedge_connected_pair_aux_projC
    (fun _ _ h ↦ circleWedge_connected_pair_aux_projC_respects h)

def circleWedge_connected_pair_aux_pD :
    circleWedge_connected_pair_aux_ED → CircleWedge :=
  Quotient.lift circleWedge_connected_pair_aux_projD
    (fun _ _ h ↦ circleWedge_connected_pair_aux_projD_respects h)

/-! #### Split of `circleWedge_connected_pair_aux_covering` (lemma-1 PARTIAL, 2026-10-19) -/

/-- Cubing is continuous.  (Banked by lemma-1.) -/
lemma circleWedge_connected_pair_aux_covering_aux_cube_continuous :
    Continuous circleWedge_connected_pair_aux_cube := by
  exact Continuous.subtype_mk (continuous_subtype_val.pow 3) _

/-! #### Split of `circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap` (lemma-2 PARTIAL, 2026-10-19) -/

/-- `pC` is continuous.  (Banked by lemma-2.) -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_continuous :
    Continuous circleWedge_connected_pair_aux_pC := by
  apply (show Topology.IsQuotientMap
      (fun z : circleWedge_connected_pair_aux_RawC ↦
        (Quotient.mk _ z : circleWedge_connected_pair_aux_EC)) from
      isQuotientMap_quot_mk).continuous_iff.mpr
  change Continuous circleWedge_connected_pair_aux_projC
  rw [continuous_sum_dom]
  constructor
  · simpa [Function.comp_def, circleWedge_connected_pair_aux_projC] using
      continuous_coinduced_rng.comp (continuous_inl.comp
        circleWedge_connected_pair_aux_covering_aux_cube_continuous)
  · simpa [Function.comp_def, circleWedge_connected_pair_aux_projC] using
      continuous_coinduced_rng.comp (continuous_inr.comp continuous_fst)

/-- Left lobe away from the wedge point: take an open arc `V` around `z` missing
`circleBase`.  Its preimage under `cube` is three disjoint arcs containing no cube
root of `circleBase`, so no glue applies there and `cube` maps each arc
homeomorphically onto `V` (`Circle.isQuotientCoveringMap_npow 3`, as in
`circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away_aux_left`
for squaring).  Use `circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_continuous`. -/
def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim id (fun _ ↦ circleBase)) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total :
    circleWedge_connected_pair_aux_EC → Circle :=
  Quotient.lift (Sum.elim id (fun z ↦ z.2.1)) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL_continuous :
    Continuous circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total_continuous :
    Continuous circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_id,
    continuous_subtype_val.comp continuous_snd⟩

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_cube
    (e : circleWedge_connected_pair_aux_EC)
    (he : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL
        (circleWedge_connected_pair_aux_pC e) ≠ circleBase) :
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL
        (circleWedge_connected_pair_aux_pC e) =
      circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total e ^ 3 := by
  refine Quotient.inductionOn e ?_ he
  rintro (w | w) he
  · rfl
  · exact (he rfl).elim

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left
    (z : Circle) (hz : z ≠ circleBase) :
    IsEvenlyCovered circleWedge_connected_pair_aux_pC (Quotient.mk _ (.inl z))
      (circleWedge_connected_pair_aux_pC ⁻¹' {Quotient.mk _ (.inl z)}) := by
  letI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hd, U, hzU, hU, hpU, H, hH⟩ :=
    IsQuotientCoveringMap.isCoveringMap _ _
      (Circle.isQuotientCoveringMap_npow 3) z
  let V : Set Circle := U \ {circleBase}
  have hzV : z ∈ V := ⟨hzU, hz⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set CircleWedge :=
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL_continuous
  have hzUX : (Quotient.mk _ (.inl z) : CircleWedge) ∈ UX := hzV
  let W : Set Circle := (fun w : Circle ↦ w ^ 3) ⁻¹' V
  have hWV : W ⊆ (fun w : Circle ↦ w ^ 3) ⁻¹' U := fun w hw ↦ hw.1
  let HW : W ≃ₜ V × ((fun w : Circle ↦ w ^ 3) ⁻¹' {z}) :=
    { toFun := fun w =>
        let y := H ⟨w.1, hWV w.2⟩
        (⟨y.1.1, ⟨y.1.2, by rw [hH ⟨w.1, hWV w.2⟩]; exact w.2.2⟩⟩, y.2)
      invFun := fun y => ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
        have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
        have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 3 = y.1.1 := by
          simpa using hh.symm
        exact ⟨by
          change (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 3 ∈ U
          exact hh'.symm ▸ y.1.2.1,
          fun heq ↦ y.1.2.2 (hh'.symm.trans heq)⟩⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa only [Function.comp_apply] using
            (continuous_subtype_val.comp continuous_fst).comp (H.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val _))
        · exact continuous_snd.comp (H.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (H.symm.continuous.comp
          ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
            continuous_snd)) }
  have hHW (w : W) : (HW w).1.1 = w.1 ^ 3 := hH ⟨w.1, hWV w.2⟩
  have hopenpre : IsOpen (circleWedge_connected_pair_aux_pC ⁻¹' UX) :=
    hUX.preimage
      circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_continuous
  let E : circleWedge_connected_pair_aux_pC ⁻¹' UX ≃ₜ W :=
    { toFun := fun e =>
        ⟨circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total e.1,
          by
            change circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total
              e.1 ^ 3 ∈ V
            rw [← circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_cube]
            · exact e.2
            · exact e.2.2⟩
      invFun := fun w => ⟨Quotient.mk _ (Sum.inl w.1), by exact w.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        induction e using Quotient.inductionOn with
        | _ a =>
          rcases a with w | w
          · rfl
          · exact (he.2 rfl).elim
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total_continuous.comp
          continuous_subtype_val) (fun e => by
            change circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total
              e.1 ^ 3 ∈ V
            rw [← circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_cube]
            · exact e.2
            · exact e.2.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : circleWedge_connected_pair_aux_RawC ↦
            (Quotient.mk _ u : circleWedge_connected_pair_aux_EC))).comp
              (continuous_inl.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x =>
        ⟨circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL x.1,
          x.2⟩
      invFun := fun v => ⟨Quotient.mk _ (.inl v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        induction x using Quotient.inductionOn with
        | _ x => rcases x with w | w
                 · rfl
                 · exact (hx.2 rfl).elim
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u : CircleWedge))).comp
              (continuous_inl.comp continuous_subtype_val) }
  let I := (fun w : Circle ↦ w ^ 3) ⁻¹' {z}
  refine (show IsEvenlyCovered circleWedge_connected_pair_aux_pC
      (Quotient.mk _ (.inl z)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hzUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change Quotient.mk _ (Sum.inl (HW (E e)).1.1) = _
    rw [hHW]
    change Quotient.mk _ (Sum.inl
      (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_total e.1 ^ 3)) = _
    rw [← circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_cube]
    · have hleft (x : CircleWedge) (hx : x ∈ UX) :
          Quotient.mk _ (Sum.inl
            (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL x)) = x := by
        induction x using Quotient.inductionOn with
        | _ a => rcases a with w | w
                 · rfl
                 · exact (hx.2 rfl).elim
      exact hleft _ e.2
    · exact e.2.2

/-- Right lobe away from the wedge point: take an open arc `V` around `z` missing
`circleBase`.  Its preimage is the three copies `V × {r}` in the right summand
(one per root `r`), none glued, each mapped by `fst` homeomorphically onto `V`. -/
def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim (fun _ ↦ circleBase) id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR_continuous :
    Continuous circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩

def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total :
    circleWedge_connected_pair_aux_EC → Circle × Circle :=
  Quotient.lift (Sum.elim (fun w ↦ (circleBase, w)) (fun z ↦ (z.1, z.2.1))) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total_continuous :
    Continuous circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_const.prodMk continuous_id,
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

/-- Off the left lobe, a point of `EC` is an unglued point of the right summand. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_spec (e : circleWedge_connected_pair_aux_EC)
    (he : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR (circleWedge_connected_pair_aux_pC e) ≠ circleBase) :
    ∃ r : circleWedge_connected_pair_aux_Root,
      (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total e).2 = r.1 ∧
      e = Quotient.mk _ (.inr (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR (circleWedge_connected_pair_aux_pC e), r)) := by
  refine Quotient.inductionOn e ?_ he
  rintro (w | ⟨v, r⟩) he
  · exact (he rfl).elim
  · exact ⟨r, rfl, rfl⟩

lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right
    (z : Circle) (hz : z ≠ circleBase) :
    IsEvenlyCovered circleWedge_connected_pair_aux_pC (Quotient.mk _ (.inr z))
      (circleWedge_connected_pair_aux_pC ⁻¹' {Quotient.mk _ (.inr z)}) := by
  haveI : Finite circleWedge_connected_pair_aux_Root :=
    Finite.of_injective (fun r : circleWedge_connected_pair_aux_Root =>
      (⟨r.1, (Polynomial.mem_nthRoots (by omega)).2 (by
        have h := congrArg Subtype.val r.2
        simpa [circleWedge_connected_pair_aux_cube, circleBase] using h)⟩ :
        {z : ℂ // z ∈ Polynomial.nthRoots 3 (1 : ℂ)})) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {z : ℂ // z ∈ Polynomial.nthRoots 3 (1 : ℂ)} => z.1) h)
  let V : Set Circle := {circleBase}ᶜ
  let UX : Set CircleWedge := circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR ⁻¹' V
  have hUX : IsOpen UX := isClosed_singleton.isOpen_compl.preimage
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR_continuous
  have hzUX : (Quotient.mk _ (.inr z) : CircleWedge) ∈ UX := hz
  have hopenpre : IsOpen (circleWedge_connected_pair_aux_pC ⁻¹' UX) :=
    hUX.preimage
      circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_continuous
  have hright (x : CircleWedge) (hx : x ∈ UX) :
      Quotient.mk _ (Sum.inr (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR x)) = x := by
    induction x using Quotient.inductionOn with
    | _ a => rcases a with w | w
             · exact (hx rfl).elim
             · rfl
  let E : circleWedge_connected_pair_aux_pC ⁻¹' UX ≃ₜ
      UX × circleWedge_connected_pair_aux_Root :=
    { toFun := fun e =>
        (⟨circleWedge_connected_pair_aux_pC e.1, e.2⟩,
          ⟨(circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total e.1).2, by
            obtain ⟨r, h, -⟩ := circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_spec e.1 e.2
            exact h ▸ r.2⟩)
      invFun := fun y => ⟨Quotient.mk _ (.inr (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR y.1.1, y.2)), y.1.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        obtain ⟨r, h, he'⟩ := circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_spec e he
        change Quotient.mk _ (.inr (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR (circleWedge_connected_pair_aux_pC e),
          (⟨(circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total e).2, _⟩ : circleWedge_connected_pair_aux_Root))) = e
        conv_rhs => rw [he']
        congr 3
        exact Subtype.ext h
      right_inv := by
        rintro ⟨⟨x, hx⟩, r⟩
        ext
        · exact hright x hx
        · rfl
      continuous_toFun := by
        apply Continuous.prodMk
        · exact Continuous.subtype_mk
            (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_continuous.comp
              continuous_subtype_val) _
        · exact Continuous.subtype_mk (continuous_snd.comp
            (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_total_continuous.comp continuous_subtype_val)) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : circleWedge_connected_pair_aux_RawC ↦
            (Quotient.mk _ u : circleWedge_connected_pair_aux_EC))).comp
              (continuous_inr.comp
                ((circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right_aux_baseR_continuous.comp
                  (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)) }
  refine (show IsEvenlyCovered circleWedge_connected_pair_aux_pC
      (Quotient.mk _ (.inr z)) circleWedge_connected_pair_aux_Root from ?_).to_isEvenlyCovered_preimage
  exact ⟨inferInstance, UX, hzUX, hUX, hopenpre, E, fun e => rfl⟩

/-! #### Split of `circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge` (lemma-1 PARTIAL, 2026-10-19)

Same shape as the split of
`circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge`: the
neighbourhood is that lemma's `_aux_U` (the wedge minus both `-1`s), the sections
come from a principal cube-root branch `r`, and the sheet over `U` indexed by a
root `ρ` is the arc around `ρ` on the left glued to copy `ρ` on the right. -/

/-- There are finitely many cube roots of `1` (so `Root` is discrete). -/
instance circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_finite : Finite circleWedge_connected_pair_aux_Root :=
  Finite.of_injective (fun r : circleWedge_connected_pair_aux_Root =>
    (⟨r.1, (Polynomial.mem_nthRoots (by omega)).2 (by
      have h := congrArg Subtype.val r.2
      simpa [circleWedge_connected_pair_aux_cube, circleBase] using h)⟩ :
      {z : ℂ // z ∈ Polynomial.nthRoots 3 (1 : ℂ)})) (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {z : ℂ // z ∈ Polynomial.nthRoots 3 (1 : ℂ)} => z.1) h)

def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift (r : {w : Circle // w ≠ -circleBase} → Circle) (w : Circle) : Circle :=
  if h : w ≠ -circleBase then r ⟨w, h⟩ else circleBase

/-- The principal cube root `w ↦ w ^ (1/3 : ℂ)` on the circle minus `-1`: continuous
(the slit avoids the branch cut), lands in the open sector `{Re > 1/2}`
(`arg ∈ (-π/3, π/3)`), fixes `1`, and every cube root of `w` is a cube root of
unity times it. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_cbrt :
    ∃ r : {w : Circle // w ≠ -circleBase} → Circle, Continuous r ∧
      (∀ w, circleWedge_connected_pair_aux_cube (r w) = w.1) ∧
      (∀ w, (1 / 2 : ℝ) < (r w : ℂ).re) ∧
      circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r circleBase = circleBase ∧
      (∀ w z, circleWedge_connected_pair_aux_cube z = w.1 →
        ∃ ρ : circleWedge_connected_pair_aux_Root, z = ρ.1 * r w) := by
  sorry

/-- Sheet `ρ` over `U`: the open arc `{Re (z ρ̄) > 1/2}` around `ρ` in the left
circle, glued at `[inl ρ] = [inr (1, ρ)]` to copy `ρ` of the right circle minus `-1`. -/
def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet (ρ : circleWedge_connected_pair_aux_Root) :
    Set circleWedge_connected_pair_aux_EC :=
  {e | (∃ z : Circle, (1 / 2 : ℝ) < ((z : ℂ) * star (ρ.1 : ℂ)).re ∧
        e = Quotient.mk _ (.inl z)) ∨
    (∃ w : Circle, w ≠ -circleBase ∧ e = Quotient.mk _ (.inr (w, ρ)))}

/-- Each sheet is open: its preimage in `RawC` is an open arc on the left and copy
`ρ` minus `-1` on the right, and it is saturated (the only glued point it meets on
the left is `ρ` itself, whose partner `(1, ρ)` is in copy `ρ`). -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet_open (ρ : circleWedge_connected_pair_aux_Root) :
    IsOpen (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet ρ) := by
  sorry

/-- The section of sheet `ρ`: `[inl w] ↦ [inl (ρ · r w)]`, `[inr w] ↦ [inr (w, ρ)]`
(well defined at the wedge point since `r 1 = 1`). -/
def circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r circleBase = circleBase)
    (ρ : circleWedge_connected_pair_aux_Root) :
    CircleWedge → circleWedge_connected_pair_aux_EC :=
  Quotient.lift
    (Sum.elim
      (fun w ↦ (Quotient.mk _ (.inl (ρ.1 * circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r w)) :
        circleWedge_connected_pair_aux_EC))
      (fun w ↦ (Quotient.mk _ (.inr (w, ρ)) : circleWedge_connected_pair_aux_EC)))
    (by
      intro x y h
      induction h with
      | rel x y h =>
          cases h
          change (Quotient.mk _ (Sum.inl (ρ.1 * circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r circleBase)) :
              circleWedge_connected_pair_aux_EC) =
            Quotient.mk _ (Sum.inr (circleBase, ρ))
          have h1 : ρ.1 * circleBase = ρ.1 := by
            apply Subtype.ext
            simp [circleBase]
          rw [hrbase, h1]
          exact Quotient.sound (Relation.EqvGen.rel _ _
            (circleWedge_connected_pair_aux_RelC.glue ρ))
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

/-- Each section is continuous on `U` (`U` avoids both `-1`s, where `_aux_lift`
jumps; its preimage in `Circle ⊕ Circle` is open and saturated, so the quotient map
restricts to a quotient map there: `IsQuotientMap.restrictPreimage_isOpen`). -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_cont (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r circleBase = circleBase) (hr : Continuous r)
    (ρ : circleWedge_connected_pair_aux_Root) :
    Continuous (fun u : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U ↦
      circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1) := by
  sorry

/-- Each section is a right inverse of `pC` on `U`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_right (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r circleBase = circleBase)
    (hcube : ∀ w, circleWedge_connected_pair_aux_cube (r w) = w.1)
    (ρ : circleWedge_connected_pair_aux_Root)
    (u : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U) :
    circleWedge_connected_pair_aux_pC (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1) = u := by
  sorry

/-- The `ρ`-section over `U` has range exactly sheet `ρ`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_range (r : {w : Circle // w ≠ -circleBase} → Circle)
    (hrbase : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_lift r circleBase = circleBase)
    (hcube : ∀ w, circleWedge_connected_pair_aux_cube (r w) = w.1)
    (hre : ∀ w, (1 / 2 : ℝ) < (r w : ℂ).re)
    (hroots : ∀ w z, circleWedge_connected_pair_aux_cube z = w.1 →
      ∃ ρ : circleWedge_connected_pair_aux_Root, z = ρ.1 * r w)
    (ρ : circleWedge_connected_pair_aux_Root) :
    Set.range (fun u : circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U ↦
      circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1) = circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet ρ := by
  sorry

/-- Combinatorics: the sheets cover `pC ⁻¹' U` and are pairwise disjoint (on the
left, the arcs of half-width `π/3` around distinct cube roots of unity are
disjoint; on the right, copies are disjoint; `_aux_rel_iff` handles the glued
points). -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_cover :
    (∀ e, circleWedge_connected_pair_aux_pC e ∈
        circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U →
      ∃ ρ, e ∈ circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet ρ) ∧
    (∀ ρ σ : circleWedge_connected_pair_aux_Root, ρ ≠ σ →
      Disjoint (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet ρ) (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet σ)) := by
  sorry

/-- At the wedge point: `V` = image of a small open arc around `circleBase` in
each lobe.  Sheet `r` is the arc around `r.1` on the left (a local section of
`cube`) glued at `inl r.1 ~ inr (circleBase, r)` to the arc around `circleBase`
in copy `r` on the right.  The three sheets are disjoint and open; the
section-gluing pattern is
`rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections`, as used
in `circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge :
    IsEvenlyCovered circleWedge_connected_pair_aux_pC (Quotient.mk _ (.inl circleBase))
      (circleWedge_connected_pair_aux_pC ⁻¹' {Quotient.mk _ (.inl circleBase)}) := by
  obtain ⟨r, hr, hcube, hre, hrbase, hroots⟩ := circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_cbrt
  obtain ⟨hcov, hdisj⟩ := circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_cover
  have hrange := circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_range r hrbase hcube hre hroots
  refine (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections
    circleWedge_connected_pair_aux_pC
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_continuous
    _ _ circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_cover.1
    circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge_aux_U_open
    (fun ρ u ↦ circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1) (fun ρ ↦ circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_cont r hrbase hr ρ)
    (fun ρ u ↦ circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_right r hrbase hcube ρ u)
    (fun ρ ↦ by rw [hrange ρ]; exact circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet_open ρ)
    (fun e he ↦ by
      obtain ⟨ρ, hρ⟩ := hcov e he
      rw [← hrange ρ] at hρ
      obtain ⟨u, hu⟩ := hρ
      exact ⟨ρ, u, hu⟩)
    (fun ρ σ u v h ↦ by
      by_contra hne
      have h' : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1 = circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase σ v.1 := h
      have hi : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1 ∈ circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet ρ := by
        rw [← hrange ρ]; exact ⟨u, rfl⟩
      have hj : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_S r hrbase ρ u.1 ∈ circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge_aux_sheet σ := by
        rw [h', ← hrange σ]; exact ⟨v, rfl⟩
      exact Set.disjoint_left.mp (hdisj ρ σ hne) hi hj)).to_isEvenlyCovered_preimage

/-- `pC` is a covering map.  Away from the wedge point: over a left-lobe point
`[inl w]`, `w ≠ circleBase`, take an open arc around `w` missing `circleBase`;
its preimage under `cube` is three disjoint arcs, none containing a root, so no
glue applies and `cube` restricts to a homeomorphism on each (cubing is a
covering map of the circle).  Over a right-lobe point `[inr w]` the sheets are
the three copies `{(z, r)}`.  At the wedge point: a neighbourhood that is a small
arc around `circleBase` in each lobe; sheet `r` is the arc around `r.1` on the
left glued to the arc around `circleBase` in copy `r` on the right.  Continuity
uses `_aux_cube_continuous` and the quotient topology on both raw sums. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap :
    IsCoveringMap circleWedge_connected_pair_aux_pC := by
  intro x
  classical
  by_cases hx : x = Quotient.mk _ (.inl circleBase)
  · subst x
    exact circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge
  · induction x using Quotient.inductionOn with
    | _ x =>
      rcases x with z | z
      · apply circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left
        intro hz
        subst z
        exact hx rfl
      · apply circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_right
        intro hz
        subst z
        apply hx
        exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base) |>.symm

/-! #### Split of `circleWedge_connected_pair_aux_covering_aux_pC_fiber` (lemma-3 PARTIAL, 2026-10-19) -/

/-- The quotient relation for `EC`, classified exactly.  (Banked by lemma-3.) -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_rel_iff (a b) :
    Relation.EqvGen circleWedge_connected_pair_aux_RelC a b ↔
      a = b ∨ ∃ r : circleWedge_connected_pair_aux_Root,
        (a = .inl r.1 ∧ b = .inr (circleBase, r)) ∨
        (b = .inl r.1 ∧ a = .inr (circleBase, r)) := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
        cases h with
        | glue r => exact Or.inr ⟨r, Or.inl ⟨rfl, rfl⟩⟩
    | refl => exact Or.inl rfl
    | symm a b _ ih =>
        rcases ih with rfl | ⟨r, h | h⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r, Or.inr ⟨h.1, h.2⟩⟩
        · exact Or.inr ⟨r, Or.inl ⟨h.1, h.2⟩⟩
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨r, h | h⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨s, hs | hs⟩
          · exact Or.inr ⟨r, Or.inl h⟩
          · simp_all
          · simp_all
        · rcases ih₂ with rfl | ⟨s, hs | hs⟩
          · exact Or.inr ⟨r, Or.inr h⟩
          · simp_all <;> exact Subtype.ext h.1.symm
          · simp_all
  · rintro (rfl | ⟨r, h | h⟩)
    · exact Relation.EqvGen.refl _
    · exact h.1 ▸ h.2 ▸ Relation.EqvGen.rel _ _
        (circleWedge_connected_pair_aux_RelC.glue r)
    · exact h.2 ▸ h.1 ▸ Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (circleWedge_connected_pair_aux_RelC.glue r))

/-- Every point of the circle has exactly three cube roots: the fibre of
`powMonoidHom 3` over `y` is a coset of its kernel, which is `{1, ω, ω²}`.
Copy `circleWedge_three_cover_two_components_aux_fiber_sq_card` (the squaring
case, kernel `{1, -1}`) with `Fin 3` in place of `Bool`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_cube_card (y : Circle) :
    Nat.card {z : Circle // circleWedge_connected_pair_aux_cube z = y} = 3 := by
  let f : Circle →* Circle := powMonoidHom 3
  have hs : Function.Surjective f :=
    (Circle.isQuotientCoveringMap_npow 3).surjective
  let a : Circle := Function.surjInv hs y
  have ha : f a = y := Function.surjInv_eq hs y
  have hk : Nat.card f.ker = 3 := by
    let e : f.ker ≃ rootsOfUnity 3 ℂ :=
      { toFun := fun z ↦ rootsOfUnity.mkOfPowEq (z.1 : ℂ) (by
          have h := congrArg Subtype.val z.2
          simpa [f] using h)
        invFun := fun z ↦ ⟨⟨(z.1 : ℂ), by
            exact mem_sphere_zero_iff_norm.2
              (Complex.norm_eq_one_of_mem_rootsOfUnity z.2)⟩, by
            apply Subtype.ext
            exact (mem_rootsOfUnity' 3 z.1).mp z.2⟩
        left_inv := fun z ↦ by
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := fun z ↦ by
          apply Subtype.ext
          apply Units.ext
          rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    exact Complex.card_rootsOfUnity 3
  have hc : Nat.card {z : Circle // f z = y} = 3 := by
    rw [← ha]
    exact (Nat.card_congr (MonoidHom.fiberEquivKer f a)).trans hk
  simpa [f, circleWedge_connected_pair_aux_cube] using hc

/-- Fibre over a left-lobe point `[inl w]`, `w ≠ circleBase`: by
`_aux_rel_iff`, a class mapping there is `[inl z]` with `cube z = w` (a class
`[inr (u, r)]` maps to the right lobe, which meets the left only at the wedge
point).  So `z ↦ [inl z]` is a bijection from the cube roots of `w`; conclude
with `_aux_cube_card`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_left
    (w : Circle) (hw : w ≠ circleBase) :
    Nat.card {e : circleWedge_connected_pair_aux_EC //
      circleWedge_connected_pair_aux_pC e = Quotient.mk _ (.inl w)} = 3 := by
  sorry

/-- Fibre over a right-lobe point `[inr w]`, `w ≠ circleBase`: the classes
`[inr (w, r)]`, one per root `r`, none glued since `w ≠ circleBase`.  So
`r ↦ [inr (w, r)]` is a bijection from `circleWedge_connected_pair_aux_Root`,
which is `{z // cube z = circleBase}` and has card 3 by `_aux_cube_card`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_right
    (w : Circle) (hw : w ≠ circleBase) :
    Nat.card {e : circleWedge_connected_pair_aux_EC //
      circleWedge_connected_pair_aux_pC e = Quotient.mk _ (.inr w)} = 3 := by
  sorry

/-- Fibre over the wedge point: the classes `{inl r.1, inr (circleBase, r)}`,
one per root `r` (`_aux_rel_iff` says these are the only identifications).
So `r ↦ [inl r.1]` is a bijection from `circleWedge_connected_pair_aux_Root`,
card 3 by `_aux_cube_card`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_wedge :
    Nat.card {e : circleWedge_connected_pair_aux_EC //
      circleWedge_connected_pair_aux_pC e = Quotient.mk _ (.inl circleBase)} = 3 := by
  classical
  let g : circleWedge_connected_pair_aux_Root →
      {e : circleWedge_connected_pair_aux_EC //
        circleWedge_connected_pair_aux_pC e = Quotient.mk _ (.inl circleBase)} :=
    fun r ↦ ⟨Quotient.mk _ (.inl r.1), by
      change (Quotient.mk _ (Sum.inl (circleWedge_connected_pair_aux_cube r.1)) : CircleWedge) = _
      exact congrArg (fun w : Circle ↦
        (Quotient.mk _ (Sum.inl w) : CircleWedge)) r.2⟩
  have hg : Function.Bijective g := by
    constructor
    · intro r s h
      have hq : Relation.EqvGen circleWedge_connected_pair_aux_RelC
          (Sum.inl r.1) (Sum.inl s.1) := Quotient.exact (congrArg Subtype.val h)
      rcases (circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_rel_iff
        (Sum.inl r.1) (Sum.inl s.1)).mp hq with h | ⟨t, h | h⟩
      · exact Subtype.ext (Sum.inl.inj h)
      · cases h.2
      · cases h.2
    · rintro ⟨e, he⟩
      induction e using Quotient.inductionOn with
      | _ x =>
        rcases x with z | z
        · have hw : circleWedge_connected_pair_aux_cube z = circleBase := by
            have hq : Relation.EqvGen (WedgeRel circleBase circleBase)
                (.inl (circleWedge_connected_pair_aux_cube z))
                (.inl circleBase) := Quotient.exact he
            rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
              circleBase circleBase (.inl (circleWedge_connected_pair_aux_cube z))
                (.inl circleBase)).mp hq with h | h
            · exact Sum.inl.inj h
            · rcases h.1 with h | h
              · exact Sum.inl.inj h
              · contradiction
          refine ⟨⟨z, hw⟩, ?_⟩
          apply Subtype.ext
          rfl
        · have hw : z.1 = circleBase := by
            have hq : Relation.EqvGen (WedgeRel circleBase circleBase)
                (.inr z.1) (.inl circleBase) := Quotient.exact he
            rcases (rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_sections_aux_U_open_aux_eqv
              circleBase circleBase (.inr z.1) (.inl circleBase)).mp hq with h | h
            · contradiction
            · rcases h.1 with h | h
              · contradiction
              · exact Sum.inr.inj h
          refine ⟨z.2, ?_⟩
          apply Subtype.ext
          change (Quotient.mk _ (Sum.inl z.2.1) : circleWedge_connected_pair_aux_EC) =
            Quotient.mk _ (Sum.inr z)
          have hz : z = (circleBase, z.2) := Prod.ext hw rfl
          rw [hz]
          exact Quotient.sound (Relation.EqvGen.rel _ _
            (circleWedge_connected_pair_aux_RelC.glue z.2))
  rw [← circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_cube_card circleBase]
  exact Nat.card_congr (Equiv.ofBijective g hg).symm

/-- Fibres of `pC` have three points: over `[inl w]` the three cube roots of `w`
on the left (the right contributes nothing unless `w = circleBase`); over
`[inr w]`, `w ≠ circleBase`, the three points `(w, r)`; over the wedge point the
three classes `{inl r.1, inr (circleBase, r)}`, one per root `r`.  Count via a
bijection with `circleWedge_connected_pair_aux_Root` (or with the cube roots of
`w`), which has card 3. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber (b : CircleWedge) :
    Nat.card {e : circleWedge_connected_pair_aux_EC //
      circleWedge_connected_pair_aux_pC e = b} = 3 := by
  classical
  by_cases hb : b = Quotient.mk _ (.inl circleBase)
  · subst b
    exact circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_wedge
  · induction b using Quotient.inductionOn with
    | _ b =>
      rcases b with w | w
      · apply circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_left
        intro hw
        subst w
        exact hb rfl
      · apply circleWedge_connected_pair_aux_covering_aux_pC_fiber_aux_right
        intro hw
        subst w
        apply hb
        exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base) |>.symm

/-! #### Split of `circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap` (lemma-1 PARTIAL, 2026-10-19) -/

/-- `pD` is continuous.  (Banked by lemma-1.) -/
lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_continuous :
    Continuous circleWedge_connected_pair_aux_pD := by
  apply (show Topology.IsQuotientMap
      (fun z : circleWedge_connected_pair_aux_RawD ↦
        (Quotient.mk _ z : circleWedge_connected_pair_aux_ED)) from
      isQuotientMap_quot_mk).continuous_iff.mpr
  change Continuous circleWedge_connected_pair_aux_projD
  rw [continuous_sum_dom]
  constructor
  · simpa [Function.comp_def, circleWedge_connected_pair_aux_projD] using
      continuous_coinduced_rng.comp
        (continuous_inl.comp
          circleWedge_connected_pair_aux_covering_aux_cube_continuous)
  · simpa [Function.comp_def, circleWedge_connected_pair_aux_projD] using
      continuous_coinduced_rng.comp
        (continuous_inr.comp
          circleWedge_connected_pair_aux_covering_aux_cube_continuous)

/-- Left lobe away from the wedge point: take an open arc `V` around `z` missing
`circleBase`.  Its preimage under `cube` in the left summand is three disjoint
arcs containing no cube root of `circleBase`, so no glue applies there and
`cube` maps each arc homeomorphically onto `V` (`Circle.isQuotientCoveringMap_npow 3`).
The proof is the same as
`circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left`; use
`circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_continuous`. -/
def circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total :
    circleWedge_connected_pair_aux_ED → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total_continuous :
    Continuous
      circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_id, continuous_id⟩

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_cube
    (e : circleWedge_connected_pair_aux_ED)
    (he : circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL
        (circleWedge_connected_pair_aux_pD e) ≠ circleBase) :
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL
        (circleWedge_connected_pair_aux_pD e) =
      circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total e ^ 3 := by
  refine Quotient.inductionOn e ?_ he
  rintro (w | w) he
  · rfl
  · exact (he rfl).elim

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left
    (z : Circle) (hz : z ≠ circleBase) :
    IsEvenlyCovered circleWedge_connected_pair_aux_pD (Quotient.mk _ (.inl z))
      (circleWedge_connected_pair_aux_pD ⁻¹' {Quotient.mk _ (.inl z)}) := by
  letI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hd, U, hzU, hU, hpU, H, hH⟩ :=
    IsQuotientCoveringMap.isCoveringMap _ _
      (Circle.isQuotientCoveringMap_npow 3) z
  let V : Set Circle := U \ {circleBase}
  have hzV : z ∈ V := ⟨hzU, hz⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set CircleWedge :=
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL_continuous
  have hzUX : (Quotient.mk _ (.inl z) : CircleWedge) ∈ UX := hzV
  let W : Set Circle := (fun w : Circle ↦ w ^ 3) ⁻¹' V
  have hWV : W ⊆ (fun w : Circle ↦ w ^ 3) ⁻¹' U := fun w hw ↦ hw.1
  let HW : W ≃ₜ V × ((fun w : Circle ↦ w ^ 3) ⁻¹' {z}) :=
    { toFun := fun w =>
        let y := H ⟨w.1, hWV w.2⟩
        (⟨y.1.1, ⟨y.1.2, by rw [hH ⟨w.1, hWV w.2⟩]; exact w.2.2⟩⟩, y.2)
      invFun := fun y => ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
        have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
        have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 3 = y.1.1 := by
          simpa using hh.symm
        exact ⟨by
          change (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 3 ∈ U
          exact hh'.symm ▸ y.1.2.1,
          fun heq ↦ y.1.2.2 (hh'.symm.trans heq)⟩⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa only [Function.comp_apply] using
            (continuous_subtype_val.comp continuous_fst).comp (H.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val _))
        · exact continuous_snd.comp (H.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (H.symm.continuous.comp
          ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
            continuous_snd)) }
  have hHW (w : W) : (HW w).1.1 = w.1 ^ 3 := hH ⟨w.1, hWV w.2⟩
  have hopenpre : IsOpen (circleWedge_connected_pair_aux_pD ⁻¹' UX) :=
    hUX.preimage
      circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_continuous
  let E : circleWedge_connected_pair_aux_pD ⁻¹' UX ≃ₜ W :=
    { toFun := fun e =>
        ⟨circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total e.1,
          by
            change circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total
              e.1 ^ 3 ∈ V
            rw [← circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_cube]
            · exact e.2
            · exact e.2.2⟩
      invFun := fun w => ⟨Quotient.mk _ (Sum.inl w.1), by exact w.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        induction e using Quotient.inductionOn with
        | _ a =>
          rcases a with w | w
          · rfl
          · exact (he.2 rfl).elim
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total_continuous.comp
          continuous_subtype_val) (fun e => by
            change circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total
              e.1 ^ 3 ∈ V
            rw [← circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_cube]
            · exact e.2
            · exact e.2.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : circleWedge_connected_pair_aux_RawD ↦
            (Quotient.mk _ u : circleWedge_connected_pair_aux_ED))).comp
              (continuous_inl.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x =>
        ⟨circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL x.1,
          x.2⟩
      invFun := fun v => ⟨Quotient.mk _ (.inl v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        induction x using Quotient.inductionOn with
        | _ x => rcases x with w | w
                 · rfl
                 · exact (hx.2 rfl).elim
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u : CircleWedge))).comp
              (continuous_inl.comp continuous_subtype_val) }
  let I := (fun w : Circle ↦ w ^ 3) ⁻¹' {z}
  refine (show IsEvenlyCovered circleWedge_connected_pair_aux_pD
      (Quotient.mk _ (.inl z)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hzUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change Quotient.mk _ (Sum.inl (HW (E e)).1.1) = _
    rw [hHW]
    change Quotient.mk _ (Sum.inl
      (circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_total e.1 ^ 3)) = _
    rw [← circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left_aux_cube]
    · have hleft (x : CircleWedge) (hx : x ∈ UX) :
          Quotient.mk _ (Sum.inl
            (circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_left_aux_baseL x)) = x := by
        induction x using Quotient.inductionOn with
        | _ a => rcases a with w | w
                 · rfl
                 · exact (hx.2 rfl).elim
      exact hleft _ e.2
    · exact e.2.2

/-- Right lobe away from the wedge point: the mirror image of `_aux_left`, with
the right summand of `RawD` (also covered by `cube`) in place of the left. -/
def circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim (fun _ ↦ circleBase) id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total :
    circleWedge_connected_pair_aux_ED → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR_continuous :
    Continuous circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total_continuous :
    Continuous circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total := by
  apply continuous_coinduced_dom.mpr
  exact continuous_sum_dom.2 ⟨continuous_id, continuous_id⟩

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_cube
    (e : circleWedge_connected_pair_aux_ED)
    (he : circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR
        (circleWedge_connected_pair_aux_pD e) ≠ circleBase) :
    circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR
        (circleWedge_connected_pair_aux_pD e) =
      circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total e ^ 3 := by
  refine Quotient.inductionOn e ?_ he
  rintro (w | w) he
  · exact (he rfl).elim
  · rfl

lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right
    (z : Circle) (hz : z ≠ circleBase) :
    IsEvenlyCovered circleWedge_connected_pair_aux_pD (Quotient.mk _ (.inr z))
      (circleWedge_connected_pair_aux_pD ⁻¹' {Quotient.mk _ (.inr z)}) := by
  letI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hd, U, hzU, hU, hpU, H, hH⟩ :=
    IsQuotientCoveringMap.isCoveringMap _ _
      (Circle.isQuotientCoveringMap_npow 3) z
  let V : Set Circle := U \ {circleBase}
  have hzV : z ∈ V := ⟨hzU, hz⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set CircleWedge :=
    circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR_continuous
  have hzUX : (Quotient.mk _ (.inr z) : CircleWedge) ∈ UX := hzV
  let W : Set Circle := (fun w : Circle ↦ w ^ 3) ⁻¹' V
  have hWV : W ⊆ (fun w : Circle ↦ w ^ 3) ⁻¹' U := fun w hw ↦ hw.1
  let HW : W ≃ₜ V × ((fun w : Circle ↦ w ^ 3) ⁻¹' {z}) :=
    { toFun := fun w =>
        let y := H ⟨w.1, hWV w.2⟩
        (⟨y.1.1, ⟨y.1.2, by rw [hH ⟨w.1, hWV w.2⟩]; exact w.2.2⟩⟩, y.2)
      invFun := fun y => ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
        have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
        have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 3 = y.1.1 := by
          simpa using hh.symm
        exact ⟨by
          change (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 3 ∈ U
          exact hh'.symm ▸ y.1.2.1,
          fun heq ↦ y.1.2.2 (hh'.symm.trans heq)⟩⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa only [Function.comp_apply] using
            (continuous_subtype_val.comp continuous_fst).comp (H.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val _))
        · exact continuous_snd.comp (H.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (H.symm.continuous.comp
          ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
            continuous_snd)) }
  have hHW (w : W) : (HW w).1.1 = w.1 ^ 3 := hH ⟨w.1, hWV w.2⟩
  have hopenpre : IsOpen (circleWedge_connected_pair_aux_pD ⁻¹' UX) :=
    hUX.preimage circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_continuous
  let E : circleWedge_connected_pair_aux_pD ⁻¹' UX ≃ₜ W :=
    { toFun := fun e =>
        ⟨circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total e.1,
          by
            change circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total
              e.1 ^ 3 ∈ V
            rw [← circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_cube]
            · exact e.2
            · exact e.2.2⟩
      invFun := fun w => ⟨Quotient.mk _ (Sum.inr w.1), by exact w.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        induction e using Quotient.inductionOn with
        | _ a =>
          rcases a with w | w
          · exact (he.2 rfl).elim
          · rfl
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total_continuous.comp
          continuous_subtype_val) (fun e => by
            change circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total
              e.1 ^ 3 ∈ V
            rw [← circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_cube]
            · exact e.2
            · exact e.2.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : circleWedge_connected_pair_aux_RawD ↦
            (Quotient.mk _ u : circleWedge_connected_pair_aux_ED))).comp
              (continuous_inr.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x =>
        ⟨circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR x.1,
          x.2⟩
      invFun := fun v => ⟨Quotient.mk _ (.inr v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        induction x using Quotient.inductionOn with
        | _ x => rcases x with w | w
                 · exact (hx.2 rfl).elim
                 · rfl
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Circle ⊕ Circle ↦ (Quotient.mk _ u : CircleWedge))).comp
              (continuous_inr.comp continuous_subtype_val) }
  let I := (fun w : Circle ↦ w ^ 3) ⁻¹' {z}
  refine (show IsEvenlyCovered circleWedge_connected_pair_aux_pD
      (Quotient.mk _ (.inr z)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hzUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change Quotient.mk _ (Sum.inr (HW (E e)).1.1) = _
    rw [hHW]
    change Quotient.mk _ (Sum.inr
      (circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_total e.1 ^ 3)) = _
    rw [← circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_cube]
    · have hright (x : CircleWedge) (hx : x ∈ UX) :
          Quotient.mk _ (Sum.inr
            (circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right_aux_baseR x)) = x := by
        induction x using Quotient.inductionOn with
        | _ a => rcases a with w | w
                 · exact (hx.2 rfl).elim
                 · rfl
      exact hright _ e.2
    · exact e.2.2

/-- At the wedge point: `V` = image of a small open arc around `circleBase` in
each lobe.  Sheet `r` is the arc around `r.1` on the left glued at
`inl r.1 ~ inr r.1` to the arc around `r.1` on the right, each a local section
of `cube`.  The three sheets are disjoint and open; the section-gluing pattern is
`rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_of_sections`, as for
`circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap_aux_wedge`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_wedge :
    IsEvenlyCovered circleWedge_connected_pair_aux_pD (Quotient.mk _ (.inl circleBase))
      (circleWedge_connected_pair_aux_pD ⁻¹' {Quotient.mk _ (.inl circleBase)}) := by
  sorry

/-- `pD` is a covering map: as for `pC`, but the right lobe is also covered by
`cube`; at the wedge point sheet `r` is the arc around `r.1` on the left glued
to the arc around `r.1` on the right. -/
lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap :
    IsCoveringMap circleWedge_connected_pair_aux_pD := by
  intro x
  classical
  by_cases hx : x = Quotient.mk _ (.inl circleBase)
  · subst x
    exact circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_wedge
  · induction x using Quotient.inductionOn with
    | _ x =>
      rcases x with z | z
      · apply circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_left
        intro hz
        subst z
        exact hx rfl
      · apply circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap_aux_right
        intro hz
        subst z
        apply hx
        exact Quotient.sound (Relation.EqvGen.rel _ _ WedgeRel.base) |>.symm

/-- Fibres of `pD` have three points: the cube roots of `w` in the relevant lobe,
and over the wedge point the three classes `{inl r.1, inr r.1}`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_cube_card
    (y : Circle) :
    Nat.card {z : Circle // circleWedge_connected_pair_aux_cube z = y} = 3 := by
  let f : Circle →* Circle := powMonoidHom 3
  have hs : Function.Surjective f :=
    (Circle.isQuotientCoveringMap_npow 3).surjective
  let a : Circle := Function.surjInv hs y
  have ha : f a = y := Function.surjInv_eq hs y
  let e : f.ker ≃ rootsOfUnity 3 ℂ :=
    { toFun := fun z ↦
        ⟨Units.mk0 (z.1 : ℂ) (by
            intro hz
            have hz' := z.1.property
            simp [Metric.mem_sphere, hz] at hz'), by
          apply Units.ext
          exact congrArg Subtype.val z.2⟩
      invFun := fun z ↦
        ⟨⟨(z.1 : ℂ), by
            simpa [Metric.mem_sphere] using
              Complex.norm_eq_one_of_mem_rootsOfUnity z.2⟩, by
          apply Subtype.ext
          exact congrArg Units.val z.2⟩
      left_inv := fun z ↦ by apply Subtype.ext; rfl
      right_inv := fun z ↦ by apply Subtype.ext; apply Units.ext; rfl }
  have hk : Nat.card f.ker = 3 := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    exact Complex.card_rootsOfUnity 3
  have hc : Nat.card {z : Circle // f z = y} = 3 := by
    rw [← ha]
    exact (Nat.card_congr (MonoidHom.fiberEquivKer f a)).trans hk
  simpa [f, circleWedge_connected_pair_aux_cube] using hc

lemma circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_rel
    (z : Circle) (h : circleWedge_connected_pair_aux_cube z = circleBase) :
    (Quotient.mk _ (.inr z) : circleWedge_connected_pair_aux_ED) =
      Quotient.mk _ (.inl z) := by
  let r : circleWedge_connected_pair_aux_Root := ⟨z, h⟩
  exact Quotient.sound (Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ (circleWedge_connected_pair_aux_RelD.glue r)))

def circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value :
    circleWedge_connected_pair_aux_ED → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_baseValue :
    CircleWedge → Circle :=
  Quotient.lift (Sum.elim id id) (by
    intro a b h
    induction h with
    | rel a b h => cases h; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma circleWedge_connected_pair_aux_covering_aux_pD_fiber (b : CircleWedge) :
    Nat.card {e : circleWedge_connected_pair_aux_ED //
      circleWedge_connected_pair_aux_pD e = b} = 3 := by
  obtain ⟨u, rfl⟩ := Quotient.exists_rep b
  rcases u with x | x
  · let F := {e : circleWedge_connected_pair_aux_ED //
        circleWedge_connected_pair_aux_pD e = Quotient.mk _ (.inl x)}
    let S := {z : Circle // circleWedge_connected_pair_aux_cube z = x}
    let E : F ≃ S :=
      { toFun := fun e ↦
          ⟨circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value e.1, by
            obtain ⟨v, hv⟩ := Quotient.exists_rep e.1
            rw [← hv]
            have he := e.2
            rw [← hv] at he
            rcases v with z | z <;>
              simpa [circleWedge_connected_pair_aux_pD,
                circleWedge_connected_pair_aux_projD,
                circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value] using
                congrArg circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_baseValue he⟩
        invFun := fun z ↦ ⟨Quotient.mk _ (.inl z.1), by
          simp [circleWedge_connected_pair_aux_pD,
            circleWedge_connected_pair_aux_projD, z.2]⟩
        right_inv := fun z ↦ by apply Subtype.ext; rfl
        left_inv := fun e ↦ by
          apply Subtype.ext
          obtain ⟨v, hv⟩ := Quotient.exists_rep e.1
          change Quotient.mk _ (Sum.inl
            (circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value e.1)) = e.1
          rw [← hv]
          rcases v with z | z
          · rfl
          · change (Quotient.mk _ (Sum.inl z) :
                circleWedge_connected_pair_aux_ED) = Quotient.mk _ (Sum.inr z)
            symm
            exact circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_rel z (by
              have he := (congrArg circleWedge_connected_pair_aux_pD hv).trans e.2
              change Quotient.mk _ (Sum.inr (circleWedge_connected_pair_aux_cube z)) =
                Quotient.mk _ (Sum.inl x) at he
              rw [Quotient.eq_iff_equiv] at he
              change Relation.EqvGen (WedgeRel circleBase circleBase) _ _ at he
              rw [
                rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
                  circleBase circleBase] at he
              rcases he with he | ⟨hz, hx⟩
              · cases he
              · rcases hz with hz | hz <;> simp_all) }
    rw [Nat.card_congr E]
    exact circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_cube_card x
  · let F := {e : circleWedge_connected_pair_aux_ED //
        circleWedge_connected_pair_aux_pD e = Quotient.mk _ (.inr x)}
    let S := {z : Circle // circleWedge_connected_pair_aux_cube z = x}
    let E : F ≃ S :=
      { toFun := fun e ↦
          ⟨circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value e.1, by
            obtain ⟨v, hv⟩ := Quotient.exists_rep e.1
            rw [← hv]
            have he := e.2
            rw [← hv] at he
            rcases v with z | z <;>
              simpa [circleWedge_connected_pair_aux_pD,
                circleWedge_connected_pair_aux_projD,
                circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value] using
                congrArg circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_baseValue he⟩
        invFun := fun z ↦ ⟨Quotient.mk _ (.inr z.1), by
          simp [circleWedge_connected_pair_aux_pD,
            circleWedge_connected_pair_aux_projD, z.2]⟩
        right_inv := fun z ↦ by apply Subtype.ext; rfl
        left_inv := fun e ↦ by
          apply Subtype.ext
          obtain ⟨v, hv⟩ := Quotient.exists_rep e.1
          change Quotient.mk _ (Sum.inr
            (circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_value e.1)) = e.1
          rw [← hv]
          rcases v with z | z
          · change (Quotient.mk _ (Sum.inr z) :
                circleWedge_connected_pair_aux_ED) = Quotient.mk _ (Sum.inl z)
            exact circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_rel z (by
              have he := (congrArg circleWedge_connected_pair_aux_pD hv).trans e.2
              change Quotient.mk _ (Sum.inl (circleWedge_connected_pair_aux_cube z)) =
                Quotient.mk _ (Sum.inr x) at he
              rw [Quotient.eq_iff_equiv] at he
              change Relation.EqvGen (WedgeRel circleBase circleBase) _ _ at he
              rw [
                rp2Wedge_regular_four_cover_aux_card_aux_wedge_eqvGen_iff
                  circleBase circleBase] at he
              rcases he with he | ⟨hz, hx⟩
              · cases he
              · rcases hz with hz | hz <;> simp_all)
          · rfl }
    rw [Nat.card_congr E]
    exact circleWedge_connected_pair_aux_covering_aux_pD_fiber_aux_cube_card x

/-- Local evenly-covered charts for the two quotient graphs. -/
lemma circleWedge_connected_pair_aux_covering :
    IsNfoldCover 3 circleWedge_connected_pair_aux_pC ∧
      IsNfoldCover 3 circleWedge_connected_pair_aux_pD := by
  exact
    ⟨⟨circleWedge_connected_pair_aux_covering_aux_pC_isCoveringMap,
        circleWedge_connected_pair_aux_covering_aux_pC_fiber⟩,
      ⟨circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap,
        circleWedge_connected_pair_aux_covering_aux_pD_fiber⟩⟩

/-- Both quotient graphs are connected. -/
lemma circleWedge_connected_pair_aux_connected_aux_C :
    PreconnectedSpace circleWedge_connected_pair_aux_EC := by
  letI : PreconnectedSpace Circle := Subtype.preconnectedSpace
    (isPreconnected_sphere (E := ℂ) (by simp) 0 1)
  let q : circleWedge_connected_pair_aux_RawC →
      circleWedge_connected_pair_aux_EC := Quotient.mk _
  let L : Set circleWedge_connected_pair_aux_EC :=
    Set.range (fun z : Circle ↦ q (.inl z))
  let R (r : circleWedge_connected_pair_aux_Root) :
      Set circleWedge_connected_pair_aux_EC :=
    Set.range (fun z : Circle ↦ q (.inr (z, r)))
  have hq : Continuous q := continuous_coinduced_rng
  have hL : IsPreconnected L := by
    exact isPreconnected_range (hq.comp continuous_inl)
  have hR (r : circleWedge_connected_pair_aux_Root) : IsPreconnected (R r) := by
    exact isPreconnected_range
      (hq.comp (continuous_inr.comp (continuous_id.prodMk continuous_const)))
  have hmeet (r : circleWedge_connected_pair_aux_Root) :
      (L ∩ R r).Nonempty := by
    refine ⟨q (.inl r.1), ⟨⟨r.1, rfl⟩, ?_⟩⟩
    refine ⟨circleBase, ?_⟩
    exact (Quotient.sound (Relation.EqvGen.rel _ _
      (circleWedge_connected_pair_aux_RelC.glue r))).symm
  have hLR (r : circleWedge_connected_pair_aux_Root) :
      IsPreconnected (L ∪ R r) :=
    IsPreconnected.union' (hmeet r) hL (hR r)
  have hinter : (⋂ r : circleWedge_connected_pair_aux_Root, L ∪ R r).Nonempty := by
    refine ⟨q (.inl circleBase), ?_⟩
    simp only [mem_iInter, mem_union, L]
    intro r
    exact Or.inl ⟨circleBase, rfl⟩
  have hall : (⋃ r : circleWedge_connected_pair_aux_Root, L ∪ R r) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
    cases a with
    | inl z =>
        let r : circleWedge_connected_pair_aux_Root :=
          ⟨circleBase, by
            apply Subtype.ext
            exact circleWedge_connected_pair_aux_circleBase_cube⟩
        exact mem_iUnion.2 ⟨r, Or.inl ⟨z, rfl⟩⟩
    | inr zr =>
        exact mem_iUnion.2 ⟨zr.2, Or.inr ⟨zr.1, rfl⟩⟩
  rw [preconnectedSpace_iff_univ, ← hall]
  exact isPreconnected_iUnion hinter hLR

lemma circleWedge_connected_pair_aux_connected_aux_D :
    PreconnectedSpace circleWedge_connected_pair_aux_ED := by
  letI : PreconnectedSpace Circle := Subtype.preconnectedSpace
    (isPreconnected_sphere (E := ℂ) (by simp) 0 1)
  let q : circleWedge_connected_pair_aux_RawD →
      circleWedge_connected_pair_aux_ED := Quotient.mk _
  let L : Set circleWedge_connected_pair_aux_ED :=
    Set.range (fun z : Circle ↦ q (.inl z))
  let R : Set circleWedge_connected_pair_aux_ED :=
    Set.range (fun z : Circle ↦ q (.inr z))
  have hq : Continuous q := continuous_coinduced_rng
  have hL : IsPreconnected L :=
    isPreconnected_range (hq.comp continuous_inl)
  have hR : IsPreconnected R :=
    isPreconnected_range (hq.comp continuous_inr)
  let r : circleWedge_connected_pair_aux_Root :=
    ⟨circleBase, by
      apply Subtype.ext
      exact circleWedge_connected_pair_aux_circleBase_cube⟩
  have hmeet : (L ∩ R).Nonempty := by
    refine ⟨q (.inl r.1), ⟨⟨r.1, rfl⟩, ⟨r.1, ?_⟩⟩⟩
    exact (Quotient.sound (Relation.EqvGen.rel _ _
      (circleWedge_connected_pair_aux_RelD.glue r))).symm
  rw [preconnectedSpace_iff_univ]
  have hu : L ∪ R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
    cases a with
    | inl z => exact Or.inl ⟨z, rfl⟩
    | inr z => exact Or.inr ⟨z, rfl⟩
  rw [← hu]
  exact IsPreconnected.union' hmeet hL hR

lemma circleWedge_connected_pair_aux_connected :
    Nat.card (ConnectedComponents circleWedge_connected_pair_aux_EC) = 1 ∧
      Nat.card (ConnectedComponents circleWedge_connected_pair_aux_ED) = 1 := by
  letI := circleWedge_connected_pair_aux_connected_aux_C
  letI := circleWedge_connected_pair_aux_connected_aux_D
  constructor
  · apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨(Quotient.mk'' (Quotient.mk _ (.inl circleBase)) :
      ConnectedComponents circleWedge_connected_pair_aux_EC), ?_⟩
    exact fun y ↦ Subsingleton.elim _ _
  · apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨(Quotient.mk'' (Quotient.mk _ (.inl circleBase)) :
      ConnectedComponents circleWedge_connected_pair_aux_ED), ?_⟩
    exact fun y ↦ Subsingleton.elim _ _

lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_relC_iff (a b) :
    Relation.EqvGen circleWedge_connected_pair_aux_RelC a b ↔
      a = b ∨ ∃ r : circleWedge_connected_pair_aux_Root,
        (a = .inl r.1 ∧ b = .inr (circleBase, r)) ∨
        (b = .inl r.1 ∧ a = .inr (circleBase, r)) := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
        cases h with
        | glue r => exact Or.inr ⟨r, Or.inl ⟨rfl, rfl⟩⟩
    | refl => exact Or.inl rfl
    | symm a b _ ih =>
        rcases ih with rfl | ⟨r, h | h⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r, Or.inr ⟨h.1, h.2⟩⟩
        · exact Or.inr ⟨r, Or.inl ⟨h.1, h.2⟩⟩
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨r, h | h⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨s, hs | hs⟩
          · exact Or.inr ⟨r, Or.inl h⟩
          · simp_all
          · simp_all
        · rcases ih₂ with rfl | ⟨s, hs | hs⟩
          · exact Or.inr ⟨r, Or.inr h⟩
          · simp_all <;> exact Subtype.ext h.1.symm
          · simp_all
  · rintro (rfl | ⟨r, h | h⟩)
    · exact Relation.EqvGen.refl _
    · exact h.1 ▸ h.2 ▸ Relation.EqvGen.rel _ _
        (circleWedge_connected_pair_aux_RelC.glue r)
    · exact h.2 ▸ h.1 ▸ Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (circleWedge_connected_pair_aux_RelC.glue r))

lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_relD_iff (a b) :
    Relation.EqvGen circleWedge_connected_pair_aux_RelD a b ↔
      a = b ∨ ∃ r : circleWedge_connected_pair_aux_Root,
        (a = .inl r.1 ∧ b = .inr r.1) ∨
        (b = .inl r.1 ∧ a = .inr r.1) := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
        cases h with
        | glue r => exact Or.inr ⟨r, Or.inl ⟨rfl, rfl⟩⟩
    | refl => exact Or.inl rfl
    | symm a b _ ih =>
        rcases ih with rfl | ⟨r, h | h⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r, Or.inr ⟨h.1, h.2⟩⟩
        · exact Or.inr ⟨r, Or.inl ⟨h.1, h.2⟩⟩
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨r, h | h⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨s, hs | hs⟩
          · exact Or.inr ⟨r, Or.inl h⟩
          · simp_all
          · simp_all
        · rcases ih₂ with rfl | ⟨s, hs | hs⟩
          · exact Or.inr ⟨r, Or.inr h⟩
          · simp_all
          · simp_all
  · rintro (rfl | ⟨r, h | h⟩)
    · exact Relation.EqvGen.refl _
    · exact h.1 ▸ h.2 ▸ Relation.EqvGen.rel _ _
        (circleWedge_connected_pair_aux_RelD.glue r)
    · exact h.2 ▸ h.1 ▸ Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (circleWedge_connected_pair_aux_RelD.glue r))

/-- `EC` has a cut point: removing a glue point detaches the open arc of the
right circle attached there. -/
lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_cutC :
    ∃ x : circleWedge_connected_pair_aux_EC,
      ¬ IsPreconnected ({x}ᶜ : Set circleWedge_connected_pair_aux_EC) := by
  let q : circleWedge_connected_pair_aux_RawC →
      circleWedge_connected_pair_aux_EC := Quotient.mk _
  let r₀ : circleWedge_connected_pair_aux_Root :=
    ⟨circleBase, by
      apply Subtype.ext
      exact circleWedge_connected_pair_aux_circleBase_cube⟩
  let roots : circleWedge_connected_pair_aux_Root →
      {z : ℂ // z ∈ Polynomial.nthRoots 3 1} := fun r =>
    ⟨r.1, (Polynomial.mem_nthRoots (by omega)).2 (by
      have h := congrArg Subtype.val r.2
      simpa [circleWedge_connected_pair_aux_cube, circleBase] using h)⟩
  letI : Finite circleWedge_connected_pair_aux_Root :=
    Finite.of_injective roots (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {z : ℂ // z ∈ Polynomial.nthRoots 3 1} => z.1) h)
  let U : Set circleWedge_connected_pair_aux_EC :=
    {y | ∃ z : Circle, z ≠ circleBase ∧ q (.inr (z, r₀)) = y}
  let V : Set circleWedge_connected_pair_aux_EC :=
    {y | ∀ z : Circle, q (.inr (z, r₀)) ≠ y}
  have hU : IsOpen U := by
    rw [isOpen_coinduced]
    have heq : q ⁻¹' U = {a | ∃ z : Circle,
        z ≠ circleBase ∧ a = .inr (z, r₀)} := by
      ext a
      constructor
      · rintro ⟨z, hz, hq⟩
        have hr := (Quotient.exact hq).symm
        rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relC_iff
          a (.inr (z, r₀))).mp hr with h | ⟨r, h | h⟩
        · exact ⟨z, hz, h⟩
        · exfalso
          apply hz
          exact congrArg Prod.fst (Sum.inr.inj h.2)
        · cases h.1
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [heq]
    have hopen : IsOpen ({z : Circle | z ≠ circleBase}) := isOpen_ne
    have hopenR : IsOpen ({r₀} : Set circleWedge_connected_pair_aux_Root) :=
      isOpen_discrete _
    rw [isOpen_sum_iff]
    constructor
    · simp
    · have he : {a : Circle × circleWedge_connected_pair_aux_Root |
          ∃ z : Circle, z ≠ circleBase ∧ a = (z, r₀)} =
          ({z : Circle | z ≠ circleBase} ×ˢ
            ({r₀} : Set circleWedge_connected_pair_aux_Root)) := by
        ext a
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨hz, rfl⟩
        · rintro ⟨hz, hr⟩
          exact ⟨a.1, hz, Prod.ext rfl hr⟩
      have hp : Sum.inr ⁻¹' {a | ∃ z : Circle, z ≠ circleBase ∧
          a = (Sum.inr (z, r₀) : circleWedge_connected_pair_aux_RawC)} =
          {a : Circle × circleWedge_connected_pair_aux_Root |
            ∃ z : Circle, z ≠ circleBase ∧ a = (z, r₀)} := by
        ext a
        constructor <;> rintro ⟨z, hz, ha⟩
        · exact ⟨z, hz, Sum.inr.inj ha⟩
        · exact ⟨z, hz, congrArg Sum.inr ha⟩
      rw [hp, he]
      exact hopen.prod hopenR
  have hV : IsOpen V := by
    rw [isOpen_coinduced]
    have heq : q ⁻¹' V = {a | ¬ (a = .inl r₀.1 ∨
        ∃ z : Circle, a = .inr (z, r₀))} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_setOf_eq, V]
      constructor
      · intro h ha
        rcases ha with ha | ⟨z, ha⟩
        · apply h circleBase
          rw [ha]
          exact (Quotient.sound (Relation.EqvGen.rel _ _
            (circleWedge_connected_pair_aux_RelC.glue r₀))).symm
        · exact h z (congrArg q ha).symm
      · intro h z hq
        apply h
        have hr := Quotient.exact hq
        rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relC_iff
          (.inr (z, r₀)) a).mp hr with h' | ⟨r, h' | h'⟩
        · exact Or.inr ⟨z, h'.symm⟩
        · cases h'.1
        · have hre : r₀ = r := congrArg Prod.snd (Sum.inr.inj h'.2)
          exact Or.inl (h'.1.trans (by rw [hre]))
    rw [heq]
    apply isOpen_compl_iff.mpr
    have he : {a | a = (Sum.inl r₀.1 : circleWedge_connected_pair_aux_RawC) ∨
        ∃ z : Circle, a = .inr (z, r₀)} =
        ({Sum.inl r₀.1} ∪ Sum.inr ''
          (Set.univ ×ˢ ({r₀} : Set circleWedge_connected_pair_aux_Root))) := by
      ext a
      rcases a with a | ⟨z, r⟩
      · simp
      · constructor
        · rintro (_ | ⟨w, hw⟩)
          · contradiction
          · have hr : r = r₀ := congrArg Prod.snd (Sum.inr.inj hw)
            exact Or.inr ⟨(z, r₀), ⟨Set.mem_univ _, rfl⟩,
              congrArg Sum.inr (Prod.ext rfl hr.symm)⟩
        · rintro (_ | ⟨⟨w, s⟩, ⟨_, hs⟩, hw⟩)
          · contradiction
          · rw [Set.mem_singleton_iff] at hs
            change s = r₀ at hs
            subst s
            exact Or.inr ⟨w, hw.symm⟩
    change IsClosed {a | a = (Sum.inl r₀.1 : circleWedge_connected_pair_aux_RawC) ∨
      ∃ z : Circle, a = .inr (z, r₀)}
    rw [he]
    exact isClosed_singleton.union
      (isClosedMap_inr _ (isClosed_univ.prod isClosed_singleton))
  refine ⟨q (.inl r₀.1), ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  push_neg
  refine ⟨U, V, hU, hV, ?_, ?_, ?_⟩
  · intro y hy
    by_cases h : ∃ z : Circle, q (.inr (z, r₀)) = y
    · obtain ⟨z, rfl⟩ := h
      by_cases hz : z = circleBase
      · subst z
        exfalso
        apply hy
        exact (Quotient.sound (Relation.EqvGen.rel _ _
          (circleWedge_connected_pair_aux_RelC.glue r₀))).symm
      · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr (by simpa [V] using h)
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, hyU, hyV⟩
    obtain ⟨z, _, hz⟩ := hyU
    exact hyV z hz
  · constructor
    · intro hsub
      have hmem : q (.inl (-circleBase)) ∈ ({q (.inl r₀.1)}ᶜ :
          Set circleWedge_connected_pair_aux_EC) := by
        intro h
        have hr := Quotient.exact h
        rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relC_iff
          (.inl (-circleBase)) (.inl r₀.1)).mp hr with h' | ⟨r, h' | h'⟩
        · have := congrArg (fun a => a.elim id (fun _ => circleBase)) h'
          have hc := congrArg Subtype.val this
          norm_num [r₀, circleBase] at hc
        · exact Sum.inl_ne_inr h'.2
        · exact Sum.inl_ne_inr h'.2
      have hv : q (.inl (-circleBase)) ∈ V := by
        simp only [V, Set.mem_setOf_eq]
        intro z hq
        have hr := Quotient.exact hq
        rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relC_iff
          (.inr (z, r₀)) (.inl (-circleBase))).mp hr with h' | ⟨r, h' | h'⟩
        · exact Sum.inr_ne_inl h'
        · exact Sum.inr_ne_inl h'.1
        · have hz : z = circleBase := congrArg Prod.fst (Sum.inr.inj h'.2)
          have hrneg : r.1 = -circleBase := (Sum.inl.inj h'.1).symm
          have hc := congrArg Subtype.val r.2
          rw [hrneg] at hc
          norm_num [circleBase] at hc
      obtain ⟨z, _, hz⟩ := hsub hmem
      exact hv z hz
    · intro hsub
      have hmem : q (.inr (-circleBase, r₀)) ∈ ({q (.inl r₀.1)}ᶜ :
          Set circleWedge_connected_pair_aux_EC) := by
        intro h
        have hr := Quotient.exact h
        rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relC_iff
          (.inr (-circleBase, r₀)) (.inl r₀.1)).mp hr with h' | ⟨r, h' | h'⟩
        · exact Sum.inr_ne_inl h'
        · exact Sum.inr_ne_inl h'.1
        · have hc := congrArg Subtype.val
            (congrArg Prod.fst (Sum.inr.inj h'.2))
          norm_num [circleBase] at hc
      have hu : q (.inr (-circleBase, r₀)) ∈ U :=
        ⟨-circleBase, by
          intro h
          have hc := congrArg Subtype.val h
          norm_num [circleBase] at hc, rfl⟩
      obtain hv := hsub hmem
      exact hv (-circleBase) rfl

/-- `ED` has no cut point: the two circles are glued at three points, so
removing any one point leaves two arcs that still meet. -/
lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_punctured
    (z : Circle) : IsPreconnected ({z}ᶜ : Set Circle) := by
  have h : ‖(z : ℂ)‖ = 1 := by
    simpa [Circle, Metric.mem_sphere] using z.2
  have hr : Set.range (stereographic h).symm = ({z}ᶜ : Set Circle) := by
    simpa using range_stereographic_symm h z.2
  rw [← hr]
  simpa only [Set.image_univ] using isPreconnected_univ.image _ (by
    simpa using (stereographic h).symm.continuousOn)

/-- A continuous map from the circle that takes the value `x` at most once is
preconnected off `x`. -/
lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_lobe
    {X : Type*} [TopologicalSpace X] {f : Circle → X} (hf : Continuous f) (x : X)
    (hx : ∀ z w, f z = x → f w = x → z = w) :
    IsPreconnected (f '' {z | f z ≠ x}) := by
  by_cases h : ∃ w, f w = x
  · obtain ⟨w, hw⟩ := h
    have hset : {z | f z ≠ x} = ({w}ᶜ : Set Circle) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨fun hz hzw ↦ hz (hzw ▸ hw), fun hzw hz ↦ hzw (hx z w hz hw)⟩
    rw [hset]
    exact (circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_punctured w).image
      f hf.continuousOn
  · push_neg at h
    have hset : {z | f z ≠ x} = Set.univ := Set.eq_univ_of_forall h
    rw [hset]
    letI : PreconnectedSpace Circle := Subtype.preconnectedSpace
      (isPreconnected_sphere (E := ℂ) (by simp) 0 1)
    exact isPreconnected_univ.image f hf.continuousOn

lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_inl_inj
    {z w : Circle}
    (h : (Quotient.mk (Relation.EqvGen.setoid circleWedge_connected_pair_aux_RelD) (.inl z) :
        circleWedge_connected_pair_aux_ED) = Quotient.mk _ (.inl w)) : z = w := by
  rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relD_iff _ _).1
      (Quotient.exact h) with h | ⟨r, h | h⟩
  · exact Sum.inl_injective h
  · simp at h
  · simp at h

lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_inr_inj
    {z w : Circle}
    (h : (Quotient.mk (Relation.EqvGen.setoid circleWedge_connected_pair_aux_RelD) (.inr z) :
        circleWedge_connected_pair_aux_ED) = Quotient.mk _ (.inr w)) : z = w := by
  rcases (circleWedge_connected_pair_aux_not_homeomorphic_aux_relD_iff _ _).1
      (Quotient.exact h) with h | ⟨r, h | h⟩
  · exact Sum.inr_injective h
  · simp at h
  · simp at h

/-- There are at least two cube roots of unity on the circle. -/
lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_two_roots :
    ∃ r s : circleWedge_connected_pair_aux_Root, r ≠ s := by
  let ζ : ℂ := (-1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℂ) * Complex.I
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hζnorm : ‖ζ‖ = 1 := by
    rw [Complex.norm_def]
    have hnormSq : Complex.normSq ζ = 1 := by
      simp [ζ, Complex.normSq_apply]
      nlinarith [hsqrt]
    rw [hnormSq]
    norm_num
  let z : Circle := ⟨ζ, by simpa [Metric.mem_sphere, dist_zero_right] using hζnorm⟩
  have hsqrt3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, hsqrt]
  have hζcube : ζ ^ 3 = 1 := by
    apply Complex.ext <;> simp [ζ, pow_succ] <;>
      ring_nf <;> nlinarith [hsqrt, hsqrt3]
  let r : circleWedge_connected_pair_aux_Root := ⟨circleBase, by
    apply Subtype.ext
    simp [circleBase]⟩
  let s : circleWedge_connected_pair_aux_Root := ⟨z, by
    apply Subtype.ext
    exact hζcube⟩
  refine ⟨r, s, ?_⟩
  intro hrs
  have hval := congrArg (fun x : circleWedge_connected_pair_aux_Root ↦
    ((x.1 : Circle) : ℂ)) hrs
  change (1 : ℂ) = ζ at hval
  have hre := congrArg Complex.re hval
  norm_num [ζ] at hre

lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD
    (x : circleWedge_connected_pair_aux_ED) :
    IsPreconnected ({x}ᶜ : Set circleWedge_connected_pair_aux_ED) := by
  let q : circleWedge_connected_pair_aux_RawD → circleWedge_connected_pair_aux_ED :=
    Quotient.mk _
  have hq : Continuous q := continuous_coinduced_rng
  have hL := circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_lobe
    (hq.comp continuous_inl) x (fun z w hz hw ↦
      circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_inl_inj (hz.trans hw.symm))
  have hR := circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_lobe
    (hq.comp continuous_inr) x (fun z w hz hw ↦
      circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_inr_inj (hz.trans hw.symm))
  have hu : (q ∘ Sum.inl) '' {z | (q ∘ Sum.inl) z ≠ x} ∪
      (q ∘ Sum.inr) '' {z | (q ∘ Sum.inr) z ≠ x} = {x}ᶜ := by
    ext y
    constructor
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact hz
    · intro hy
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective y
      cases a with
      | inl z => exact Or.inl ⟨z, hy, rfl⟩
      | inr z => exact Or.inr ⟨z, hy, rfl⟩
  obtain ⟨r, s, hrs⟩ := circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_two_roots
  have ht : ∃ t : circleWedge_connected_pair_aux_Root, q (.inl t.1) ≠ x := by
    by_contra h
    push_neg at h
    exact hrs (Subtype.ext
      (circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD_aux_inl_inj
        ((h r).trans (h s).symm)))
  obtain ⟨t, ht⟩ := ht
  have hglue : q (.inl t.1) = q (.inr t.1) :=
    Quotient.sound (Relation.EqvGen.rel _ _ (circleWedge_connected_pair_aux_RelD.glue t))
  rw [← hu]
  exact IsPreconnected.union' ⟨q (.inl t.1), ⟨t.1, ht, rfl⟩, ⟨t.1, fun h ↦ ht (hglue.trans h), hglue.symm⟩⟩
    hL hR

/-- `EC` and `ED` are not homeomorphic: `EC` has a cut point and `ED` has
none, and having a cut point is preserved by homeomorphisms. -/
lemma circleWedge_connected_pair_aux_not_homeomorphic :
    ¬ Nonempty (circleWedge_connected_pair_aux_EC ≃ₜ
      circleWedge_connected_pair_aux_ED) := by
  rintro ⟨h⟩
  obtain ⟨x, hx⟩ := circleWedge_connected_pair_aux_not_homeomorphic_aux_cutC
  apply hx
  have himg : h.symm '' ({h x}ᶜ : Set circleWedge_connected_pair_aux_ED) = {x}ᶜ := by
    ext y
    simp [h.image_symm, h.injective.eq_iff]
  rw [← himg]
  exact (circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD (h x)).image _
    h.symm.continuous.continuousOn

theorem circleWedge_connected_pair : ∃ C D : ThreeCover,
    Nat.card (@ConnectedComponents C.E C.topology) = 1 ∧
    Nat.card (@ConnectedComponents D.E D.topology) = 1 ∧
    ¬ Nonempty (@Homeomorph C.E D.E C.topology D.topology) := by
  rcases circleWedge_connected_pair_aux_covering with ⟨hC, hD⟩
  rcases circleWedge_connected_pair_aux_connected with ⟨hcC, hcD⟩
  exact ⟨{ E := circleWedge_connected_pair_aux_EC
           topology := inferInstance
           p := circleWedge_connected_pair_aux_pC
           covering := hC },
    { E := circleWedge_connected_pair_aux_ED
      topology := inferInstance
      p := circleWedge_connected_pair_aux_pD
      covering := hD }, hcC, hcD,
    circleWedge_connected_pair_aux_not_homeomorphic⟩

/-- Homeomorphic spaces have the same number of connected components. -/
theorem natCard_connectedComponents_eq_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents Y) := by
  apply Nat.card_congr
  exact
    { toFun := h.continuous.connectedComponentsMap
      invFun := h.symm.continuous.connectedComponentsMap
      left_inv := by
        rintro ⟨x⟩
        change ((h.symm (h x) : X) : ConnectedComponents X) =
          (x : ConnectedComponents X)
        simp
      right_inv := by
        rintro ⟨y⟩
        change ((h (h.symm y) : Y) : ConnectedComponents Y) =
          (y : ConnectedComponents Y)
        simp }

/-- Assembly of the component-count and loop-edge invariants. -/
theorem circleWedge_four_pairwise_nonhomeomorphic :
    ∃ C : Fin 4 → ThreeCover, Pairwise fun i j ↦
      ¬ Nonempty (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology) := by
  obtain ⟨C₀, h₀⟩ := circleWedge_three_cover_three_components
  obtain ⟨C₁, h₁⟩ := circleWedge_three_cover_two_components
  obtain ⟨C₂, C₃, h₂, h₃, h₂₃⟩ := circleWedge_connected_pair
  have hcard : ∀ (A B : ThreeCover),
      Nat.card (@ConnectedComponents A.E A.topology) ≠
        Nat.card (@ConnectedComponents B.E B.topology) →
      ¬ Nonempty (@Homeomorph A.E B.E A.topology B.topology) := by
    rintro A B hne ⟨h⟩
    letI := A.topology
    letI := B.topology
    exact hne (natCard_connectedComponents_eq_of_homeomorph h)
  have h₃₂ : ¬ Nonempty (@Homeomorph C₃.E C₂.E C₃.topology C₂.topology) := by
    rintro ⟨h⟩
    letI := C₂.topology
    letI := C₃.topology
    exact h₂₃ ⟨h.symm⟩
  let C : Fin 4 → ThreeCover := ![C₀, C₁, C₂, C₃]
  have hc : ∀ i, Nat.card (@ConnectedComponents (C i).E (C i).topology) =
      ![3, 2, 1, 1] i := by
    intro i
    fin_cases i
    exacts [h₀, h₁, h₂, h₃]
  refine ⟨C, fun i j hij ↦ ?_⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h₂₃
    | exact h₃₂
    | (refine hcard _ _ ?_; rw [hc, hc]; decide)

end ConstructionTargets.WedgePermutationCover

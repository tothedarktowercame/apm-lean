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
  sorry

/-- The open hemisphere `{y | 0 < y₀}` around `e₀` embeds openly in `RP2`
(it is disjoint from its antipode, and `antipodalCover` is an open map). -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_hemi :
    Topology.IsOpenEmbedding
      (fun y : {y : Sphere2 // 0 < (y : EuclideanSpace ℝ (Fin 3)) 0} ↦
        antipodalCover y.1) := by
  sorry

/-- The glued projection is continuous. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_wedge_aux_continuous
    (σ τ : Equiv.Perm (Fin 4)) :
    Continuous (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  sorry

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
  sorry

/-- The four sheets over the wedge point.  `U` is the image of the hemisphere
`{y | 0 < y₀}` in both lobes; sheet `i` sends `[inl (antipodalCover y)]` to
`[inl (y, i)]` and `[inr (antipodalCover y)]` to `[inr (y, i)]` for `y` in the
hemisphere (these agree at the wedge point by the glue at `e₀`).  Continuity by
`_aux_lobes` and `_aux_hemi`; the range of sheet `i` is the class of
`{inl (y, i), inl (-y, σ i), inr (y, i), inr (-y, τ i) | 0 < y₀}`, open in the raw
sum; disjointness by `_aux_card_aux_invariant` recording the sheet index. -/
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
  sorry

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
  sorry

/-- An open subset of the left lobe missing the base point embeds openly in the
wedge: its preimage in `A ⊕ B` is `inl '' V`, already saturated. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inl
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (V : Set A) (hV : IsOpen V) (ha : a ∉ V) :
    Topology.IsOpenEmbedding
      (fun z : V ↦ (Quotient.mk _ (.inl z.1) : Wedge A B a b)) := by
  sorry

/-- The same for the right lobe. -/
lemma rp2Wedge_regular_four_cover_aux_isCoveringMap_aux_away_aux_lobe_inr
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (V : Set B) (hV : IsOpen V) (hb : b ∉ V) :
    Topology.IsOpenEmbedding
      (fun z : V ↦ (Quotient.mk _ (.inr z.1) : Wedge A B a b)) := by
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
  sorry

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
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_away
    (x : CircleWedge) (hx : x ≠ Quotient.mk _ (.inl circleBase)) :
    IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap x
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹' {x}) := by
  sorry

/-- At the wedge point: `V` = the image of the open arcs `{Re z > 0}` in both
lobes. Its preimage is two disjoint open "crosses", one through `[inl 1] = [inr 1]`
and one through `[inl (-1)] = [inr (-1)]`; each is the wedge of two half-arcs
mapped homeomorphically onto `V` by squaring on each lobe. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_double_aux_wedge :
    IsEvenlyCovered circleWedge_three_cover_two_components_aux_doubleMap
      (Quotient.mk _ (.inl circleBase))
      (circleWedge_three_cover_two_components_aux_doubleMap ⁻¹'
        {Quotient.mk _ (.inl circleBase)}) := by
  sorry

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
-- BEGIN SEAT AREA
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
  sorry

/-- Two local trivialisations over the same `W` glue to one for `Sum.elim f g`,
with fibre the disjoint union of the fibres. -/
lemma circleWedge_three_cover_two_components_aux_covering_aux_sum_aux_glue
    {E₁ E₂ X I J : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X]
    [TopologicalSpace I] [TopologicalSpace J] {f : E₁ → X} {g : E₂ → X} {W : Set X}
    (H₁ : f ⁻¹' W ≃ₜ W × I) (hH₁ : ∀ e, (H₁ e).1.1 = f e)
    (H₂ : g ⁻¹' W ≃ₜ W × J) (hH₂ : ∀ e, (H₂ e).1.1 = g e) :
    ∃ H : Sum.elim f g ⁻¹' W ≃ₜ W × (I ⊕ J), ∀ e, (H e).1.1 = Sum.elim f g e := by
  sorry

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
-- END SEAT AREA

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
  sorry

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
  sorry

/-- Fibres of `pC` have three points: over `[inl w]` the three cube roots of `w`
on the left (the right contributes nothing unless `w = circleBase`); over
`[inr w]`, `w ≠ circleBase`, the three points `(w, r)`; over the wedge point the
three classes `{inl r.1, inr (circleBase, r)}`, one per root `r`.  Count via a
bijection with `circleWedge_connected_pair_aux_Root` (or with the cube roots of
`w`), which has card 3. -/
lemma circleWedge_connected_pair_aux_covering_aux_pC_fiber (b : CircleWedge) :
    Nat.card {e : circleWedge_connected_pair_aux_EC //
      circleWedge_connected_pair_aux_pC e = b} = 3 := by
  sorry

/-- `pD` is a covering map: as for `pC`, but the right lobe is also covered by
`cube`; at the wedge point sheet `r` is the arc around `r.1` on the left glued
to the arc around `r.1` on the right. -/
lemma circleWedge_connected_pair_aux_covering_aux_pD_isCoveringMap :
    IsCoveringMap circleWedge_connected_pair_aux_pD := by
  sorry

/-- Fibres of `pD` have three points: the cube roots of `w` in the relevant lobe,
and over the wedge point the three classes `{inl r.1, inr r.1}`. -/
lemma circleWedge_connected_pair_aux_covering_aux_pD_fiber (b : CircleWedge) :
    Nat.card {e : circleWedge_connected_pair_aux_ED //
      circleWedge_connected_pair_aux_pD e = b} = 3 := by
  sorry

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
lemma circleWedge_connected_pair_aux_not_homeomorphic_aux_noCutD
    (x : circleWedge_connected_pair_aux_ED) :
    IsPreconnected ({x}ᶜ : Set circleWedge_connected_pair_aux_ED) := by
  sorry

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

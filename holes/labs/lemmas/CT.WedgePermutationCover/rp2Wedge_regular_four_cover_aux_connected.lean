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
  sorry

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

/-- **LIBRARY.** The glued projection is a covering map.  Charts: away from the
wedge point, over the image `V` of an open set of `Sphere2` disjoint from its
antipode, the preimage is four copies of `V` in one lobe; at the wedge point,
take `V` = images of small caps around `±e₀` in both lobes, whose preimage is
four wedges of two caps, one per fibre point `[(e₀, i)]`. -/
theorem rp2Wedge_regular_four_cover_aux_isCoveringMap (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ) :
    IsCoveringMap (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  sorry

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
  sorry

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
-- BEGIN SEAT AREA
theorem rp2Wedge_regular_four_cover_aux_connected (σ τ : Equiv.Perm (Fin 4))
    (hT : ∀ i j : Fin 4, Relation.ReflTransGen (fun a b ↦ b = σ a ∨ b = τ a) i j) :
    IsConnected (Set.univ : Set (rp2Wedge_regular_four_cover_aux_E σ τ)) := by
  sorry
-- END SEAT AREA

/-- If the centralizer of `σ`, `τ` acts transitively on `Fin 4`, the cover is
regular: `g` commuting with `σ`, `τ` gives the deck homeomorphism
`[(x, i)] ↦ [(x, g i)]` on both copies (inverse from `g⁻¹`), and any two points
of one fibre can be written `[(x, i)]`, `[(x, j)]` with the same `x`. -/
theorem rp2Wedge_regular_four_cover_aux_regular (σ τ : Equiv.Perm (Fin 4))
    (hC : ∀ i j : Fin 4, ∃ g : Equiv.Perm (Fin 4),
      g * σ = σ * g ∧ g * τ = τ * g ∧ g i = j) :
    IsRegularCover (rp2Wedge_regular_four_cover_aux_p σ τ) := by
  sorry

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
theorem circleWedge_three_cover_three_components : ∃ C : ThreeCover,
    Nat.card (@ConnectedComponents C.E C.topology) = 3 := by
  sorry

/-- The permutation pair `((12),(12))`: a three-sheeted cover with two
components. -/
theorem circleWedge_three_cover_two_components : ∃ C : ThreeCover,
    Nat.card (@ConnectedComponents C.E C.topology) = 2 := by
  sorry

/-- The pairs `((123),1)` and `((123),(123))` realize two connected
three-sheeted covers whose total spaces are not homeomorphic: deleting the
topologically intrinsic valence-four locus leaves three loop edges in the
first graph and none in the second. -/
theorem circleWedge_connected_pair : ∃ C D : ThreeCover,
    Nat.card (@ConnectedComponents C.E C.topology) = 1 ∧
    Nat.card (@ConnectedComponents D.E D.topology) = 1 ∧
    ¬ Nonempty (@Homeomorph C.E D.E C.topology D.topology) := by
  sorry

/-- Homeomorphic spaces have the same number of connected components. -/
theorem natCard_connectedComponents_eq_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Nat.card (ConnectedComponents X) = Nat.card (ConnectedComponents Y) := by
  sorry

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

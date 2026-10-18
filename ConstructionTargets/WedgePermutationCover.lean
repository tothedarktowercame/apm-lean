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

/-- Every fibre has four points: over a point of the left lobe the fibre is
`{[(x, i)] | i}` (the class of `(x, i)` is `{(x, i), (-x, σ i)}`, using that
`σ` is an involution); likewise on the right; over the wedge point it is
`{[(e₀, i)] | i}`.  Uses `rp2Wedge_regular_four_cover_aux_cover_eq_iff`. -/
theorem rp2Wedge_regular_four_cover_aux_card (σ τ : Equiv.Perm (Fin 4))
    (hσ : Function.Involutive σ) (hτ : Function.Involutive τ)
    (b : Wedge RP2 RP2 rpBase rpBase) :
    Nat.card {e // rp2Wedge_regular_four_cover_aux_p σ τ e = b} = 4 := by
  sorry

/-- If `σ`, `τ` generate a transitive action on `Fin 4`, the glued space is
connected: the image of `Sphere2 × {i}` in either copy is connected, the left
sheets `i` and `σ i` have the same image, and the left and right sheets `i`
meet at `[(e₀, i)]`. -/
theorem rp2Wedge_regular_four_cover_aux_connected (σ τ : Equiv.Perm (Fin 4))
    (hT : ∀ i j : Fin 4, Relation.ReflTransGen (fun a b ↦ b = σ a ∨ b = τ a) i j) :
    IsConnected (Set.univ : Set (rp2Wedge_regular_four_cover_aux_E σ τ)) := by
  sorry

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

/-- The involutions `(12)` and `(14)(23)` realize a connected nonregular
four-sheeted cover of the projective-plane wedge. -/
theorem rp2Wedge_irregular_four_cover :
    Nonempty (CoverWitness (Wedge RP2 RP2 rpBase rpBase) 4 false) := by
  sorry

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

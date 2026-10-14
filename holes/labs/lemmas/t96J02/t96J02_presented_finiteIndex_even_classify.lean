import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.KleinPresentedGroupCoordinateNormalForm
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.KleinOrbitQuotientHomeomorph

/-! # Blueprint for t96J02

The geometric input identifies the registered Klein-bottle fundamental group
with the already-banked presented/coordinate Klein group.  The subgroup
classification is then purely algebraic. -/

open ConstructionTargets.StatementSurfaceModels
open KleinPresentedGroupCoordinateModel

abbrev T96J02Group := FundamentalGroup KleinBottle (surfacePoint false 2)
abbrev T96J02TorusGroup := Multiplicative (ℤ × ℤ)

abbrev T96J02PresentedGroup := PresentedKleinGroup

noncomputable abbrev T96J02KleinPlaneQuotient :=
  MulAction.orbitRel.Quotient T96J02PresentedGroup (ℝ × ℝ)

noncomputable abbrev T96J02KleinPlaneOrigin : T96J02KleinPlaneQuotient :=
  Quotient.mk _ (0, 0)

/-! The definitions above are the complete shared interface used by the
independent lemma seats. -/

/-- The deck-group calculation at the canonical orbit of the origin. -/
theorem t96J02_kleinPlaneQuotient_pi1_origin :
    Nonempty
      (FundamentalGroup T96J02KleinPlaneQuotient T96J02KleinPlaneOrigin ≃*
        T96J02PresentedGroup) := by
  sorry

/-- Move the deck-group calculation to every point of the orbit quotient.
The origin calculation is an explicit hypothesis so this seat is parallel. -/
theorem t96J02_kleinPlaneQuotient_pi1_every_basepoint
    (h₀ : Nonempty
      (FundamentalGroup T96J02KleinPlaneQuotient T96J02KleinPlaneOrigin ≃*
        T96J02PresentedGroup)) :
    ∀ q : T96J02KleinPlaneQuotient,
      Nonempty
        (FundamentalGroup T96J02KleinPlaneQuotient q ≃*
          T96J02PresentedGroup) := by
  sorry

/-- The explicit affine orbit quotient is the frozen polygon model of the
Klein bottle.  This is the sole residual quotient-comparison leaf. -/
theorem t96J02_kleinPlaneQuotient_homeomorph :
    Nonempty (T96J02KleinPlaneQuotient ≃ₜ KleinBottle) := by
  sorry

/-- Transport an all-basepoint fundamental-group calculation across a
homeomorphism.  Both substantive conclusions are hypotheses, so this seat is
independent of the Klein-specific geometry. -/
theorem t96J02_pi1_every_basepoint_of_homeomorph
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
    (e : X ≃ₜ Y)
    (hX : ∀ x : X, Nonempty (FundamentalGroup X x ≃* G)) :
    ∀ y : Y, Nonempty (FundamentalGroup Y y ≃* G) := by
  sorry

/-- The fundamental group of the frozen Klein polygon is its standard
presented group.  This is now a sorry-free assembly of the four leaves above. -/
theorem t96J02_kleinBottle_pi1 :
    Nonempty (T96J02Group ≃* T96J02PresentedGroup) := by
  obtain ⟨e⟩ := t96J02_kleinPlaneQuotient_homeomorph
  exact t96J02_pi1_every_basepoint_of_homeomorph e
    (t96J02_kleinPlaneQuotient_pi1_every_basepoint
      t96J02_kleinPlaneQuotient_pi1_origin)
    (surfacePoint false 2)

/-- The element with normal-form coordinates `(m,n)`. -/
noncomputable def t96J02_presented_coordinate (m n : ℤ) :
    T96J02PresentedGroup :=
  KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
    ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd n⟩

/-- A finite-index subgroup meets the horizontal infinite cyclic subgroup in
a nonzero cyclic subgroup. -/
theorem t96J02_presented_finiteIndex_horizontal_step
    (H : Subgroup T96J02PresentedGroup) (hH : H.FiniteIndex) :
    ∃ p : ℤ, 0 < p ∧
      ∀ m : ℤ, t96J02_presented_coordinate m 0 ∈ H ↔ p ∣ m := by
  sorry

/-- The set of vertical exponents occurring in a finite-index subgroup is a
nonzero subgroup `qℤ` of `ℤ`.  This leaf is independent of the horizontal one. -/
theorem t96J02_presented_finiteIndex_vertical_step
    (H : Subgroup T96J02PresentedGroup) (hH : H.FiniteIndex) :
    ∃ q : ℤ, 0 < q ∧
      ∀ n : ℤ,
        (∃ m : ℤ, t96J02_presented_coordinate m n ∈ H) ↔ q ∣ n := by
  sorry

/-- Choose a subgroup element above the positive generator of its vertical
projection.  The projection description is an explicit hypothesis so this
leaf can be proved in parallel with the preceding leaf. -/
theorem t96J02_presented_finiteIndex_choose_vertical_lift
    (H : Subgroup T96J02PresentedGroup) (q : ℤ)
    (hq : ∀ n : ℤ,
      (∃ m : ℤ, t96J02_presented_coordinate m n ∈ H) ↔ q ∣ n) :
    ∃ r : ℤ, t96J02_presented_coordinate r q ∈ H := by
  exact (hq q).2 (dvd_refl q)

/-- The horizontal generator and a chosen lift of the vertical generator
generate the whole subgroup.  All structural inputs are hypotheses, keeping
this leaf independent of the three existence leaves. -/
theorem t96J02_presented_finiteIndex_generated
    (H : Subgroup T96J02PresentedGroup) (p q r : ℤ)
    (hp : ∀ m : ℤ, t96J02_presented_coordinate m 0 ∈ H ↔ p ∣ m)
    (hq : ∀ n : ℤ,
      (∃ m : ℤ, t96J02_presented_coordinate m n ∈ H) ↔ q ∣ n)
    (hr : t96J02_presented_coordinate r q ∈ H) :
    H = Subgroup.closure
      ({t96J02_presented_coordinate p 0,
        t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) := by
  sorry

/-- If the vertical step is even, the two normal-form generators commute and
give a rank-two free abelian group. -/
-- BEGIN SEAT AREA
theorem t96J02_presented_finiteIndex_even_classify_aux_action
    (q n : ℤ) (hq : Even q) (x : ZMul) :
    action (Multiplicative.ofAdd (q * n)) x = x := by
  obtain ⟨k, rfl⟩ := hq
  change (inversion ^ ((k + k) * n)) x = x
  rw [show (k + k) * n = 2 * (k * n) by ring, zpow_mul]
  have hi : inversion ^ (2 : ℤ) = 1 := by
    ext y
    change inversion (inversion y) = y
    simp [inversion]
  rw [hi, one_zpow]
  rfl

def t96J02_presented_finiteIndex_even_classify_aux_map
    (p q r : ℤ) (hq : Even q) :
    T96J02TorusGroup →* T96J02PresentedGroup :=
  KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm.toMonoidHom.comp
    { toFun := fun z =>
        ⟨Multiplicative.ofAdd (p * z.toAdd.1 + r * z.toAdd.2),
          Multiplicative.ofAdd (q * z.toAdd.2)⟩
      map_one' := by ext <;> simp
      map_mul' := by
        intro x y
        apply SemidirectProduct.ext
        · change Multiplicative.ofAdd
              (p * (x.toAdd.1 + y.toAdd.1) + r * (x.toAdd.2 + y.toAdd.2)) =
            Multiplicative.ofAdd (p * x.toAdd.1 + r * x.toAdd.2) *
              action (Multiplicative.ofAdd (q * x.toAdd.2))
                (Multiplicative.ofAdd (p * y.toAdd.1 + r * y.toAdd.2))
          rw [t96J02_presented_finiteIndex_even_classify_aux_action q x.toAdd.2 hq]
          change Multiplicative.ofAdd
              (p * (x.toAdd.1 + y.toAdd.1) + r * (x.toAdd.2 + y.toAdd.2)) =
            Multiplicative.ofAdd
              ((p * x.toAdd.1 + r * x.toAdd.2) +
                (p * y.toAdd.1 + r * y.toAdd.2))
          congr 1 <;> ring
        · change Multiplicative.ofAdd (q * (x.toAdd.2 + y.toAdd.2)) =
            Multiplicative.ofAdd (q * x.toAdd.2) *
              Multiplicative.ofAdd (q * y.toAdd.2)
          change Multiplicative.ofAdd (q * (x.toAdd.2 + y.toAdd.2)) =
            Multiplicative.ofAdd (q * x.toAdd.2 + q * y.toAdd.2)
          congr 1 <;> ring }

theorem t96J02_presented_finiteIndex_even_classify
    (H : Subgroup T96J02PresentedGroup) (p q r : ℤ)
    (hp : 0 < p) (hq : 0 < q) (heven : Even q)
    (hgen : H = Subgroup.closure
      ({t96J02_presented_coordinate p 0,
        t96J02_presented_coordinate r q} : Set T96J02PresentedGroup)) :
    Nonempty (H ≃* T96J02TorusGroup) := by
  let f := t96J02_presented_finiteIndex_even_classify_aux_map p q r heven
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hc := congrArg KleinPresentedGroupCoordinateNormalForm.coordinateEquiv hxy
    change KleinPresentedGroupCoordinateNormalForm.coordinateEquiv
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
          ⟨Multiplicative.ofAdd (p * x.toAdd.1 + r * x.toAdd.2),
            Multiplicative.ofAdd (q * x.toAdd.2)⟩) =
      KleinPresentedGroupCoordinateNormalForm.coordinateEquiv
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
          ⟨Multiplicative.ofAdd (p * y.toAdd.1 + r * y.toAdd.2),
            Multiplicative.ofAdd (q * y.toAdd.2)⟩) at hc
    simp only [MulEquiv.apply_symm_apply] at hc
    have hrgt := congrArg
      (fun z : Coordinates => Multiplicative.toAdd z.right) hc
    have hlft := congrArg
      (fun z : Coordinates => Multiplicative.toAdd z.left) hc
    have hrgt' : q * x.toAdd.2 = q * y.toAdd.2 := by
      exact hrgt
    have hlft' : p * x.toAdd.1 + r * x.toAdd.2 =
        p * y.toAdd.1 + r * y.toAdd.2 := by
      exact hlft
    have hv : x.toAdd.2 = y.toAdd.2 :=
      mul_left_cancel₀ (ne_of_gt hq) hrgt'
    rw [hv] at hlft'
    have hpEq : p * x.toAdd.1 = p * y.toAdd.1 := by omega
    have hh : x.toAdd.1 = y.toAdd.1 :=
      mul_left_cancel₀ (ne_of_gt hp) hpEq
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · change x.toAdd.1 = y.toAdd.1
      exact hh
    · change x.toAdd.2 = y.toAdd.2
      exact hv
  have hf1 : f (Multiplicative.ofAdd (1, 0)) =
      t96J02_presented_coordinate p 0 := by
    apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
    apply SemidirectProduct.ext <;> simp [f,
      t96J02_presented_finiteIndex_even_classify_aux_map,
      t96J02_presented_coordinate]
  have hf2 : f (Multiplicative.ofAdd (0, 1)) =
      t96J02_presented_coordinate r q := by
    apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
    apply SemidirectProduct.ext <;> simp [f,
      t96J02_presented_finiteIndex_even_classify_aux_map,
      t96J02_presented_coordinate]
  have hfirst : t96J02_presented_coordinate p 0 ∈ MonoidHom.range f :=
    ⟨Multiplicative.ofAdd (1, 0), hf1⟩
  have hsecond : t96J02_presented_coordinate r q ∈ MonoidHom.range f :=
    ⟨Multiplicative.ofAdd (0, 1), hf2⟩
  have hrange : MonoidHom.range f = H := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      rw [hgen]
      have ha := (Subgroup.closure _).zpow_mem (Subgroup.subset_closure
        (show t96J02_presented_coordinate p 0 ∈
          ({t96J02_presented_coordinate p 0,
            t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) by simp)) z.toAdd.1
      have hb := (Subgroup.closure _).zpow_mem (Subgroup.subset_closure
        (show t96J02_presented_coordinate r q ∈
          ({t96J02_presented_coordinate p 0,
            t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) by simp)) z.toAdd.2
      have hz : z = (Multiplicative.ofAdd (1, 0)) ^ z.toAdd.1 *
          (Multiplicative.ofAdd (0, 1)) ^ z.toAdd.2 := by
        apply Multiplicative.toAdd.injective
        ext <;> simp
      rw [hz, map_mul, map_zpow, map_zpow, hf1, hf2]
      exact Subgroup.mul_mem _ ha hb
    · rw [hgen]
      apply (Subgroup.closure_le _).2
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hfirst
      · exact hsecond
  let g : T96J02TorusGroup →* H :=
    { toFun := fun z => ⟨f z, hrange ▸ ⟨z, rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul x y) }
  have hg_bij : Function.Bijective g := by
    constructor
    · intro x y h
      apply hf_inj
      exact congrArg Subtype.val h
    · intro x
      have hx : x.1 ∈ MonoidHom.range f := hrange.symm ▸ x.2
      obtain ⟨z, hz⟩ := hx
      exact ⟨z, Subtype.ext hz⟩
  exact ⟨(MulEquiv.ofBijective g hg_bij).symm⟩
-- END SEAT AREA

/-- If the vertical step is odd, conjugation by its lift inverts the
horizontal generator, and normal forms give another Klein group. -/
theorem t96J02_presented_finiteIndex_odd_classify
    (H : Subgroup T96J02PresentedGroup) (p q r : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hodd : Odd q)
    (hgen : H = Subgroup.closure
      ({t96J02_presented_coordinate p 0,
        t96J02_presented_coordinate r q} : Set T96J02PresentedGroup)) :
    Nonempty (H ≃* T96J02PresentedGroup) := by
  sorry

/-- Every finite-index subgroup of the coordinate Klein group is either
another Klein group or a rank-two free abelian group. -/
theorem t96J02_presented_finiteIndex_classify :
    ∀ H : Subgroup T96J02PresentedGroup, H.FiniteIndex →
      Nonempty (H ≃* T96J02PresentedGroup) ∨
        Nonempty (H ≃* T96J02TorusGroup) := by
  intro H hH
  obtain ⟨p, hp, hp_mem⟩ :=
    t96J02_presented_finiteIndex_horizontal_step H hH
  obtain ⟨q, hq, hq_mem⟩ :=
    t96J02_presented_finiteIndex_vertical_step H hH
  obtain ⟨r, hr⟩ :=
    t96J02_presented_finiteIndex_choose_vertical_lift H q hq_mem
  have hgen := t96J02_presented_finiteIndex_generated H p q r hp_mem hq_mem hr
  rcases Int.even_or_odd q with heven | hodd
  · exact Or.inr
      (t96J02_presented_finiteIndex_even_classify H p q r hp hq heven hgen)
  · exact Or.inl
      (t96J02_presented_finiteIndex_odd_classify H p q r hp hq hodd hgen)

/-- The whole presented Klein group realizes the Klein-group alternative. -/
theorem t96J02_presented_self_subgroup :
    ∃ H : Subgroup T96J02PresentedGroup,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02PresentedGroup) := by
  refine ⟨⊤, ?_, ⟨Subgroup.topEquiv⟩⟩
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  infer_instance

/-- The subgroup with even second coordinate realizes the torus-group
alternative. -/
theorem t96J02_presented_torus_subgroup_aux_even_action
    (n : ℤ) (x : ZMul) :
    action (Multiplicative.ofAdd (2 * n)) x = x := by
  change (inversion ^ (2 * n)) x = x
  rw [zpow_mul]
  have hi : inversion ^ (2 : ℤ) = 1 := by
    ext y
    change inversion (inversion y) = y
    simp [inversion]
  rw [hi, one_zpow]
  rfl

def t96J02_presented_torus_subgroup_aux_embedding :
    T96J02TorusGroup →* Coordinates where
  toFun p := ⟨Multiplicative.ofAdd p.toAdd.1,
    Multiplicative.ofAdd (2 * p.toAdd.2)⟩
  map_one' := by ext <;> simp
  map_mul' p q := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (p.toAdd.1 + q.toAdd.1) =
        Multiplicative.ofAdd p.toAdd.1 *
          action (Multiplicative.ofAdd (2 * p.toAdd.2))
            (Multiplicative.ofAdd q.toAdd.1)
      rw [t96J02_presented_torus_subgroup_aux_even_action]
      rfl
    · change Multiplicative.ofAdd (2 * (p.toAdd.2 + q.toAdd.2)) =
        Multiplicative.ofAdd (2 * p.toAdd.2) *
          Multiplicative.ofAdd (2 * q.toAdd.2)
      change Multiplicative.ofAdd (2 * (p.toAdd.2 + q.toAdd.2)) =
        Multiplicative.ofAdd (2 * p.toAdd.2 + 2 * q.toAdd.2)
      congr 1 <;> ring

@[simp] theorem t96J02_presented_torus_subgroup_aux_embedding_left
    (p : T96J02TorusGroup) :
    (t96J02_presented_torus_subgroup_aux_embedding p).left =
      Multiplicative.ofAdd p.toAdd.1 := rfl

@[simp] theorem t96J02_presented_torus_subgroup_aux_embedding_right
    (p : T96J02TorusGroup) :
    (t96J02_presented_torus_subgroup_aux_embedding p).right =
      Multiplicative.ofAdd (2 * p.toAdd.2) := rfl

theorem t96J02_presented_torus_subgroup_aux_embedding_injective :
    Function.Injective t96J02_presented_torus_subgroup_aux_embedding := by
  intro p q h
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · have hh := congrArg (fun z : Coordinates => z.left) h
    change Multiplicative.ofAdd p.toAdd.1 =
      Multiplicative.ofAdd q.toAdd.1 at hh
    exact Multiplicative.ofAdd.injective hh
  · have hh := congrArg
      (fun z : Coordinates => Multiplicative.toAdd z.right) h
    change 2 * p.toAdd.2 = 2 * q.toAdd.2 at hh
    omega

def t96J02_presented_torus_subgroup_aux_toPresented :
    T96J02TorusGroup →* T96J02PresentedGroup :=
  KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm.toMonoidHom.comp
    t96J02_presented_torus_subgroup_aux_embedding

def t96J02_presented_torus_subgroup_aux_parity :
    T96J02PresentedGroup →* Multiplicative (ZMod 2) :=
  (Int.castAddHom (ZMod 2)).toMultiplicative.comp
    (SemidirectProduct.rightHom.comp
      KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.toMonoidHom)

theorem t96J02_presented_torus_subgroup_aux_range_eq_ker :
    t96J02_presented_torus_subgroup_aux_toPresented.range =
      t96J02_presented_torus_subgroup_aux_parity.ker := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change t96J02_presented_torus_subgroup_aux_parity
      (t96J02_presented_torus_subgroup_aux_toPresented p) = 1
    change Multiplicative.ofAdd (((Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
          (t96J02_presented_torus_subgroup_aux_embedding p))).right : ℤ) :
            ZMod 2)) = 1
    rw [KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.apply_symm_apply]
    rw [t96J02_presented_torus_subgroup_aux_embedding_right]
    apply Multiplicative.toAdd.injective
    change (((2 * p.toAdd.2 : ℤ) : ZMod 2)) = 0
    rw [Int.cast_mul]
    change (2 : ZMod 2) * (p.toAdd.2 : ZMod 2) = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  · intro hx
    change Multiplicative.ofAdd
      ((Multiplicative.toAdd
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).right : ℤ) :
          ZMod 2) = 1 at hx
    have hz :
        ((Multiplicative.toAdd
          (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).right : ℤ) :
            ZMod 2) = 0 := by
      exact Multiplicative.ofAdd.injective hx
    have hd : (2 : ℤ) ∣ Multiplicative.toAdd
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).right := by
      have hd' : (2 : ℤ) ∣ 0 - Multiplicative.toAdd
          (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).right :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp hz
      obtain ⟨k, hk⟩ := hd'
      use -k
      omega
    obtain ⟨k, hk⟩ := hd
    let p : T96J02TorusGroup := Multiplicative.ofAdd
      (Multiplicative.toAdd
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).left, k)
    refine ⟨p, ?_⟩
    apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
    change KleinPresentedGroupCoordinateNormalForm.coordinateEquiv
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
        (t96J02_presented_torus_subgroup_aux_embedding p)) =
          KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x
    rw [KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.apply_symm_apply]
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd p.toAdd.1 =
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).left
      rfl
    · change Multiplicative.ofAdd (2 * k) =
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).right
      apply Multiplicative.toAdd.injective
      simp [hk]
      ring

theorem t96J02_presented_torus_subgroup :
    ∃ H : Subgroup T96J02PresentedGroup,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02TorusGroup) := by
  refine ⟨t96J02_presented_torus_subgroup_aux_parity.ker, inferInstance, ?_⟩
  refine ⟨((MonoidHom.ofInjective
    (f := t96J02_presented_torus_subgroup_aux_toPresented) ?_).trans
      (MulEquiv.subgroupCongr
        t96J02_presented_torus_subgroup_aux_range_eq_ker)).symm⟩
  intro p q h
  apply t96J02_presented_torus_subgroup_aux_embedding_injective
  apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm.injective
  exact h

/-- Transport classification and the two witnesses across an arbitrary group
equivalence.  This isolates all `Subgroup.map` and finite-index bookkeeping
from both substantive seats. -/
lemma t96J02_transport_across_equiv_aux_index_map
    {G K : Type*} [Group G] [Group K] (e : G ≃* K) (H : Subgroup G) :
    (H.map (e : G →* K)).index = H.index := by
  have h := Subgroup.relIndex_map_map_of_injective
    (f := (e : G →* K)) H (⊤ : Subgroup G) e.injective
  simpa using h

lemma t96J02_transport_across_equiv_aux_finiteIndex_map
    {G K : Type*} [Group G] [Group K] (e : G ≃* K) (H : Subgroup G)
    (hH : H.FiniteIndex) : (H.map (e : G →* K)).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,
    t96J02_transport_across_equiv_aux_index_map e H]
  exact Subgroup.finiteIndex_iff.mp hH

theorem t96J02_transport_across_equiv
    {G K A : Type*} [Group G] [Group K] [Group A]
    (e : G ≃* K)
    (hclass : ∀ H : Subgroup K, H.FiniteIndex →
      Nonempty (H ≃* K) ∨ Nonempty (H ≃* A))
    (hK : ∃ H : Subgroup K, H.FiniteIndex ∧ Nonempty (H ≃* K))
    (hA : ∃ H : Subgroup K, H.FiniteIndex ∧ Nonempty (H ≃* A)) :
    (∀ H : Subgroup G, H.FiniteIndex →
      Nonempty (H ≃* G) ∨ Nonempty (H ≃* A)) ∧
    (∃ H : Subgroup G, H.FiniteIndex ∧ Nonempty (H ≃* G)) ∧
    (∃ H : Subgroup G, H.FiniteIndex ∧ Nonempty (H ≃* A)) := by
  constructor
  · intro H hH
    have hm : (H.map (e : G →* K)).FiniteIndex :=
      t96J02_transport_across_equiv_aux_finiteIndex_map e H hH
    rcases hclass (H.map (e : G →* K)) hm with h | h
    · left
      rcases h with ⟨f⟩
      exact ⟨((e.subgroupMap H).trans f).trans e.symm⟩
    · right
      rcases h with ⟨f⟩
      exact ⟨(e.subgroupMap H).trans f⟩
  constructor
  · rcases hK with ⟨H, hH, ⟨f⟩⟩
    let H' : Subgroup G := H.map (e.symm : K →* G)
    refine ⟨H', ?_, ?_⟩
    · exact t96J02_transport_across_equiv_aux_finiteIndex_map e.symm H hH
    · exact ⟨((e.symm.subgroupMap H).symm.trans f).trans e.symm⟩
  · rcases hA with ⟨H, hH, ⟨f⟩⟩
    let H' : Subgroup G := H.map (e.symm : K →* G)
    refine ⟨H', ?_, ?_⟩
    · exact t96J02_transport_across_equiv_aux_finiteIndex_map e.symm H hH
    · exact ⟨(e.symm.subgroupMap H).symm.trans f⟩

theorem apm_t96j02 :
    (∀ H : Subgroup T96J02Group, H.FiniteIndex →
      Nonempty (H ≃* T96J02Group) ∨ Nonempty (H ≃* T96J02TorusGroup)) ∧
    (∃ H : Subgroup T96J02Group,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02Group)) ∧
    (∃ H : Subgroup T96J02Group,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02TorusGroup)) := by
  obtain ⟨e⟩ := t96J02_kleinBottle_pi1
  exact t96J02_transport_across_equiv e
    t96J02_presented_finiteIndex_classify
    t96J02_presented_self_subgroup
    t96J02_presented_torus_subgroup

#print axioms apm_t96j02

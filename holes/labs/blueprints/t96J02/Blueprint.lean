import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.KleinPresentedGroupCoordinateNormalForm
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.KleinOrbitQuotientHomeomorph
import ConstructionTargets.KleinClosedSquareOrbitInverseContinuity

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
theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_coordinates
    (g : T96J02PresentedGroup) (p q : ℝ × ℝ) (h : g • p = q) :
    (((Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 : ℤ) : ℝ) =
        q.2 - p.2) ∧
    (((Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).1 : ℤ) : ℝ) =
        q.1 - ((Multiplicative.toAdd
          (action (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2
            (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * p.1) := by
  change KleinPlaneAffineAction.coordinateAct
    (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g) p = q at h
  constructor
  · have hy := congrArg Prod.snd h
    dsimp [KleinPlaneAffineAction.coordinateAct] at hy
    linarith
  · have hx := congrArg Prod.fst h
    dsimp [KleinPlaneAffineAction.coordinateAct] at hx
    linarith

theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_cast
    {A : Type*} [TopologicalSpace A] {K : Set A} (hK : IsCompact K)
    (f : A → ℝ) (hf : Continuous f) :
    {z : ZMul | ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}.Finite := by
  let S : Set ZMul :=
    {z | ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}
  have hc : IsCompact (f '' K) := hK.image hf
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  obtain ⟨za : ℤ, hza : (za : ℝ) ≤ a⟩ := exists_int_le a
  obtain ⟨zb : ℤ, hzb : b ≤ (zb : ℝ)⟩ := exists_int_ge b
  have hbelow : BddBelow S := by
    refine ⟨Multiplicative.ofAdd za, ?_⟩
    intro z hz
    change za ≤ Multiplicative.toAdd z
    rw [← Int.cast_le (R := ℝ)]
    exact hza.trans (ha hz)
  have habove : BddAbove S := by
    refine ⟨Multiplicative.ofAdd zb, ?_⟩
    intro z hz
    change Multiplicative.toAdd z ≤ zb
    rw [← Int.cast_le (R := ℝ)]
    exact (hb hz).trans hzb
  exact hbelow.finite_of_bddAbove habove

theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_vertical
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {n : ZMul | ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}.Finite := by
  apply t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_cast (hK.prod hL)
  fun_prop

theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_horizontal
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) (n : ZMul) :
    {m : ZMul | ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.1 -
        ((Multiplicative.toAdd (action n (Multiplicative.ofAdd 1)) : ℤ) : ℝ) *
          pq.1.1) '' (K ×ˢ L)}.Finite := by
  apply t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_cast (hK.prod hL)
  fun_prop

theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_actors
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {g : T96J02PresentedGroup | ((g • ·) '' K ∩ L).Nonempty}.Finite := by
  let V : Set ZMul := {n | ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
    (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}
  let H : ZMul → Set ZMul := fun n => {m |
    ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.1 -
        ((Multiplicative.toAdd (action n (Multiplicative.ofAdd 1)) : ℤ) : ℝ) *
          pq.1.1) '' (K ×ˢ L)}
  have hV : V.Finite :=
    t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_vertical hK hL
  have hH : ∀ n, (H n).Finite := fun n =>
    t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_horizontal hK hL n
  have hPairs : (⋃ n ∈ V, H n ×ˢ ({n} : Set ZMul)).Finite :=
    hV.biUnion fun n _ => (hH n).prod (Set.finite_singleton n)
  apply (hPairs.preimage
    KleinPresentedGroupCoordinateNormalForm.coordinatePairEquiv.injective.injOn).subset
  intro g hg
  obtain ⟨q, ⟨p, hp, hgp⟩, hq⟩ := hg
  have heq := t96J02_kleinPlaneQuotient_pi1_origin_aux_coordinates g p q hgp
  apply Set.mem_iUnion₂.mpr
  refine ⟨(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2, ?_, ?_⟩
  · exact ⟨⟨p, q⟩, ⟨hp, hq⟩, heq.1.symm⟩
  · change (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).1 ∈
        H (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 ∧
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 ∈
        ({(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2} : Set ZMul)
    exact ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, heq.2.symm⟩, Set.mem_singleton _⟩

theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_continuous
    (g : T96J02PresentedGroup) : Continuous (fun p : ℝ × ℝ => g • p) := by
  change Continuous (fun p : ℝ × ℝ => KleinPlaneAffineAction.coordinateAct
    (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g) p)
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    (continuous_const.add continuous_snd)

theorem t96J02_kleinPlaneQuotient_pi1_origin_aux_free
    (g : T96J02PresentedGroup) (p : ℝ × ℝ) (h : g • p = p) : g = 1 := by
  let c := KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g
  have hc : KleinPlaneAffineAction.coordinateAct c p = p := by
    simpa [c, KleinPlaneAffineAction.planeAction] using h
  have hy := congrArg Prod.snd hc
  have hnR : ((Multiplicative.toAdd c.2 : ℤ) : ℝ) = 0 := by
    dsimp [KleinPlaneAffineAction.coordinateAct] at hy
    linarith
  have hn : Multiplicative.toAdd c.2 = 0 := by exact_mod_cast hnR
  have hc2 : c.2 = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hn
  have hx := congrArg Prod.fst hc
  have hc1 : c.1 = 1 := by
    dsimp [KleinPlaneAffineAction.coordinateAct] at hx
    simpa [hc2] using hx
  apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
  change c = KleinPresentedGroupCoordinateNormalForm.coordinateEquiv 1
  rw [map_one]
  apply SemidirectProduct.ext
  · exact hc1
  · exact hc2

theorem t96J02_kleinPlaneQuotient_pi1_origin :
    Nonempty
      (FundamentalGroup T96J02KleinPlaneQuotient T96J02KleinPlaneOrigin ≃*
        T96J02PresentedGroup) := by
  letI : ContinuousConstSMul T96J02PresentedGroup (ℝ × ℝ) :=
    ⟨t96J02_kleinPlaneQuotient_pi1_origin_aux_continuous⟩
  letI : ProperlyDiscontinuousSMul T96J02PresentedGroup (ℝ × ℝ) :=
    ⟨fun hK hL =>
      t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_actors hK hL⟩
  exact
    ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      t96J02_kleinPlaneQuotient_pi1_origin_aux_free (0, 0)

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
  intro q
  obtain ⟨e₀⟩ := h₀
  exact
    ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        q T96J02KleinPlaneOrigin).trans e₀⟩

theorem t96J02_kleinPlaneQuotient_homeomorph_aux_sameOrbit
    (p q : ℝ × ℝ) :
    KleinSquareEqvGenToCases.SameOrbit p q ↔
      MulAction.orbitRel T96J02PresentedGroup (ℝ × ℝ) p q := by
  change q ∈ MulAction.orbit T96J02PresentedGroup p ↔
    p ∈ MulAction.orbit T96J02PresentedGroup q
  exact MulAction.mem_orbit_symm

noncomputable def t96J02_kleinPlaneQuotient_homeomorph_aux_planeOrbitRel :
    ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient ≃ₜ
      T96J02KleinPlaneQuotient where
  toFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound
      ((t96J02_kleinPlaneQuotient_homeomorph_aux_sameOrbit p q).mp h)
  invFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound
      ((t96J02_kleinPlaneQuotient_homeomorph_aux_sameOrbit p q).mpr h)
  left_inv := by rintro ⟨p⟩; rfl
  right_inv := by rintro ⟨p⟩; rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

/-- The plane orbit relation is closed enough that its quotient is Hausdorff.
This is independent of either polygon presentation. -/
theorem t96J02_kleinPlaneOrbitQuotient_t2 :
    T2Space ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient := by
  sorry

/-- The already-banked fundamental-domain equivalence, packaged as a
homeomorphism once Hausdorffness is supplied explicitly. -/
theorem t96J02_kleinPlaneQuotient_homeomorph_aux_closedSquarePlane
    (hT2 : T2Space
      ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient) :
    Nonempty
      (ConstructionTargets.KleinOrbitQuotientHomeomorph.ClosedSquareOrbitQuotient ≃ₜ
        ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient) := by
  letI := hT2
  exact ⟨{
    toEquiv :=
      ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv.closedSquareOrbitQuotientEquiv
    continuous_toFun :=
      ConstructionTargets.KleinOrbitQuotientHomeomorph.continuous_closedSquareOrbitQuotientEquiv
    continuous_invFun :=
      ConstructionTargets.KleinClosedSquareOrbitInverseContinuity.closedSquareOrbitQuotientEquiv_continuous_symm_of_t2
  }⟩

abbrev T96J02ClosedSquare :=
  ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv.ClosedSquare

def T96J02ClosedSquareRel (p q : T96J02ClosedSquare) : Prop :=
  KleinSquareBoundaryRelation.SquareRel p.1 q.1

abbrev T96J02SquarePolygonQuotient :=
  Quotient (Relation.EqvGen.setoid T96J02ClosedSquareRel)

noncomputable instance : TopologicalSpace T96J02SquarePolygonQuotient :=
  TopologicalSpace.coinduced
    (fun p : T96J02ClosedSquare => Quotient.mk _ p) inferInstance

/-- On the closed fundamental square, action orbits are exactly the
equivalence relation generated by the two edge pairings. -/
theorem t96J02_kleinSquare_orbit_iff_eqvGen
    (p q : T96J02ClosedSquare) :
    ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv.closedSquareOrbitSetoid.r p q ↔
      Relation.EqvGen T96J02ClosedSquareRel p q := by
  sorry

/-- Quotient adapter for two extensionally equal equivalence relations on the
same compact square.  The relation comparison is an explicit hypothesis so
this leaf is parallel to the preceding one. -/
theorem t96J02_kleinClosedSquareOrbit_homeomorph_squarePolygon
    (hrel : ∀ p q : T96J02ClosedSquare,
      ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv.closedSquareOrbitSetoid.r p q ↔
        Relation.EqvGen T96J02ClosedSquareRel p q) :
    Nonempty
      (ConstructionTargets.KleinOrbitQuotientHomeomorph.ClosedSquareOrbitQuotient ≃ₜ
        T96J02SquarePolygonQuotient) := by
  sorry

/-- The genuine polygon-move bridge: the opposite-edge square presentation
and the frozen adjacent-arc disk presentation have homeomorphic quotient
spaces.  This cannot be induced by a homeomorphism of the two carriers; a
proof needs a cut-and-paste map defined only after passage to the quotient. -/
theorem t96J02_kleinSquarePolygonQuotient_homeomorph_diskPolygon :
    Nonempty (T96J02SquarePolygonQuotient ≃ₜ KleinBottle) := by
  sorry

theorem t96J02_kleinPlaneQuotient_homeomorph :
    Nonempty (T96J02KleinPlaneQuotient ≃ₜ KleinBottle) := by
  obtain ⟨eSquare⟩ :=
    t96J02_kleinClosedSquareOrbit_homeomorph_squarePolygon
      t96J02_kleinSquare_orbit_iff_eqvGen
  obtain ⟨eDisk⟩ :=
    t96J02_kleinSquarePolygonQuotient_homeomorph_diskPolygon
  obtain ⟨eFundamentalDomain⟩ :=
    t96J02_kleinPlaneQuotient_homeomorph_aux_closedSquarePlane
      t96J02_kleinPlaneOrbitQuotient_t2
  exact ⟨t96J02_kleinPlaneQuotient_homeomorph_aux_planeOrbitRel.symm |>.trans
    (eFundamentalDomain.symm.trans
      (eSquare.trans eDisk))⟩

/-- Transport an all-basepoint fundamental-group calculation across a
homeomorphism.  Both substantive conclusions are hypotheses, so this seat is
independent of the Klein-specific geometry. -/
noncomputable def t96J02_pi1_every_basepoint_of_homeomorph_aux_equiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

theorem t96J02_pi1_every_basepoint_of_homeomorph
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
    (e : X ≃ₜ Y)
    (hX : ∀ x : X, Nonempty (FundamentalGroup X x ≃* G)) :
    ∀ y : Y, Nonempty (FundamentalGroup Y y ≃* G) := by
  intro y
  obtain ⟨eX⟩ := hX (e.symm y)
  let E := (t96J02_pi1_every_basepoint_of_homeomorph_aux_equiv
    e (e.symm y)).symm.trans eX
  rw [e.apply_symm_apply y] at E
  exact ⟨E⟩

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
theorem t96J02_presented_finiteIndex_horizontal_step_aux_add (m n : ℤ) :
    t96J02_presented_coordinate (m + n) 0 =
      t96J02_presented_coordinate m 0 * t96J02_presented_coordinate n 0 := by
  apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
  simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply, map_mul]
  ext <;> simp

theorem t96J02_presented_finiteIndex_horizontal_step_aux_neg (m : ℤ) :
    t96J02_presented_coordinate (-m) 0 =
      (t96J02_presented_coordinate m 0)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← t96J02_presented_finiteIndex_horizontal_step_aux_add]
  simp [t96J02_presented_coordinate]

def t96J02_presented_finiteIndex_horizontal_step_aux_subgroup
    (H : Subgroup T96J02PresentedGroup) : AddSubgroup ℤ where
  carrier := {m | t96J02_presented_coordinate m 0 ∈ H}
  zero_mem' := by
    change KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
      ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 0⟩ ∈ H
    simpa using H.one_mem
  add_mem' := by
    intro m n hm hn
    change t96J02_presented_coordinate (m + n) 0 ∈ H
    change t96J02_presented_coordinate m 0 ∈ H at hm
    change t96J02_presented_coordinate n 0 ∈ H at hn
    rw [t96J02_presented_finiteIndex_horizontal_step_aux_add]
    exact H.mul_mem hm hn
  neg_mem' := by
    intro m hm
    change t96J02_presented_coordinate (-m) 0 ∈ H
    change t96J02_presented_coordinate m 0 ∈ H at hm
    rw [t96J02_presented_finiteIndex_horizontal_step_aux_neg]
    exact H.inv_mem hm

theorem t96J02_presented_finiteIndex_horizontal_step
    (H : Subgroup T96J02PresentedGroup) (hH : H.FiniteIndex) :
    ∃ p : ℤ, 0 < p ∧
      ∀ m : ℤ, t96J02_presented_coordinate m 0 ∈ H ↔ p ∣ m := by
  let K := t96J02_presented_finiteIndex_horizontal_step_aux_subgroup H
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic K
  have hK_ne : K ≠ ⊥ := by
    intro hzero
    letI : Finite (T96J02PresentedGroup ⧸ H) :=
      Subgroup.finiteIndex_iff_finite_quotient.mp hH
    obtain ⟨i, j, hij, heq⟩ :=
      Finite.exists_ne_map_eq_of_infinite
        (fun n : ℤ ↦ (Quotient.mk''
          (t96J02_presented_coordinate n 0) : T96J02PresentedGroup ⧸ H))
    have hmem : t96J02_presented_coordinate (j - i) 0 ∈ H := by
      have hd : (t96J02_presented_coordinate i 0)⁻¹ *
          t96J02_presented_coordinate j 0 ∈ H :=
        QuotientGroup.leftRel_apply.mp (Quotient.exact' heq)
      rw [show t96J02_presented_coordinate (j - i) 0 =
          (t96J02_presented_coordinate i 0)⁻¹ *
            t96J02_presented_coordinate j 0 by
        rw [sub_eq_add_neg, add_comm,
          t96J02_presented_finiteIndex_horizontal_step_aux_add,
          t96J02_presented_finiteIndex_horizontal_step_aux_neg]]
      exact hd
    have hz : j - i = 0 := by
      have : j - i ∈ K := hmem
      rw [hzero] at this
      simpa using this
    exact hij (sub_eq_zero.mp hz).symm
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hK_ne
    rw [ha, ha0]
    simp
  refine ⟨(a.natAbs : ℤ), ?_, ?_⟩
  · exact_mod_cast Int.natAbs_pos.mpr ha0
  · intro m
    change m ∈ K ↔ _
    rw [ha]
    rw [AddSubgroup.mem_closure_singleton]
    change (∃ n : ℤ, n * a = m) ↔ (a.natAbs : ℤ) ∣ m
    rw [Int.natAbs_dvd]
    constructor
    · rintro ⟨n, rfl⟩
      exact dvd_mul_left a n
    · rintro ⟨n, rfl⟩
      exact ⟨n, mul_comm n a⟩

/-- The set of vertical exponents occurring in a finite-index subgroup is a
nonzero subgroup `qℤ` of `ℤ`.  This leaf is independent of the horizontal one. -/
def t96J02_presented_finiteIndex_vertical_step_aux_subgroup
    (H : Subgroup T96J02PresentedGroup) : AddSubgroup ℤ where
  carrier := {n | ∃ m : ℤ, t96J02_presented_coordinate m n ∈ H}
  zero_mem' := by
    refine ⟨0, ?_⟩
    change KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
      ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 0⟩ ∈ H
    simpa using H.one_mem
  add_mem' := by
    rintro n k ⟨m, hm⟩ ⟨r, hr⟩
    let x := t96J02_presented_coordinate m n *
      t96J02_presented_coordinate r k
    let s : ℤ := Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).left
    refine ⟨s, ?_⟩
    have hx : x ∈ H := H.mul_mem hm hr
    suffices t96J02_presented_coordinate s (n + k) = x by
      simpa [this] using hx
    apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
    simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply]
    change ⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (n + k)⟩ =
      KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x
    apply SemidirectProduct.ext <;>
      simp [s, x, t96J02_presented_coordinate]
  neg_mem' := by
    rintro n ⟨m, hm⟩
    let x := (t96J02_presented_coordinate m n)⁻¹
    let s : ℤ := Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).left
    refine ⟨s, ?_⟩
    have hx : x ∈ H := H.inv_mem hm
    suffices t96J02_presented_coordinate s (-n) = x by
      simpa [this] using hx
    apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
    simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply]
    change ⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (-n)⟩ =
      KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x
    apply SemidirectProduct.ext <;>
      simp [s, x, t96J02_presented_coordinate]

theorem t96J02_presented_finiteIndex_vertical_step
    (H : Subgroup T96J02PresentedGroup) (hH : H.FiniteIndex) :
    ∃ q : ℤ, 0 < q ∧
      ∀ n : ℤ,
        (∃ m : ℤ, t96J02_presented_coordinate m n ∈ H) ↔ q ∣ n := by
  let K := t96J02_presented_finiteIndex_vertical_step_aux_subgroup H
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic K
  have hK_ne : K ≠ ⊥ := by
    intro hzero
    letI := hH
    obtain ⟨i, j, hij, heq⟩ :=
      Finite.exists_ne_map_eq_of_infinite
        (fun n : ℤ ↦
          (t96J02_presented_coordinate 0 n :
            T96J02PresentedGroup ⧸ H))
    have hmem : (t96J02_presented_coordinate 0 i)⁻¹ *
        t96J02_presented_coordinate 0 j ∈ H :=
      QuotientGroup.eq.mp heq
    let x := (t96J02_presented_coordinate 0 i)⁻¹ *
      t96J02_presented_coordinate 0 j
    let s : ℤ := Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x).left
    have hxcoord : t96J02_presented_coordinate s (j - i) = x := by
      apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
      simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply]
      change ⟨Multiplicative.ofAdd s, Multiplicative.ofAdd (j - i)⟩ =
        KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x
      apply SemidirectProduct.ext <;>
        simp [s, x, t96J02_presented_coordinate, div_eq_mul_inv, mul_comm]
    have hjmi : j - i ∈ K := by
      exact ⟨s, hxcoord.symm ▸ hmem⟩
    rw [hzero] at hjmi
    have hz : j - i = 0 := by simpa using hjmi
    exact hij (sub_eq_zero.mp hz).symm
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hK_ne
    rw [ha, ha0]
    simp
  refine ⟨(a.natAbs : ℤ), ?_, ?_⟩
  · exact_mod_cast Int.natAbs_pos.mpr ha0
  · intro n
    change n ∈ K ↔ _
    rw [ha]
    simp only [AddSubgroup.mem_closure_singleton, Int.natAbs_dvd]
    constructor
    · rintro ⟨k, rfl⟩
      exact dvd_mul_left a k
    · rintro ⟨k, rfl⟩
      exact ⟨k, mul_comm k a⟩

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
  apply le_antisymm
  · intro x hx
    let c : Coordinates :=
      KleinPresentedGroupCoordinateNormalForm.coordinateEquiv x
    let n : ℤ := Multiplicative.toAdd c.right
    have hn_ex : ∃ m : ℤ, t96J02_presented_coordinate m n ∈ H := by
      exact ⟨Multiplicative.toAdd c.left, by
        simpa [c, n, t96J02_presented_coordinate] using hx⟩
    have hn : q ∣ n := (hq n).1 hn_ex
    obtain ⟨k, hk⟩ := hn
    let g := t96J02_presented_coordinate r q
    let y := x * g ^ (-k)
    have hyH : y ∈ H := H.mul_mem hx (H.zpow_mem hr (-k))
    have hy_right :
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv y).right = 1 := by
      change (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv
          (x * g ^ (-k))).right = 1
      change SemidirectProduct.rightHom
          (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv (x * g ^ (-k))) = 1
      rw [map_mul, map_zpow, map_mul, map_zpow]
      simp only [g, t96J02_presented_coordinate, MulEquiv.apply_symm_apply]
      change c.right * (Multiplicative.ofAdd q) ^ (-k) = 1
      rw [← Int.ofAdd_mul]
      change Multiplicative.ofAdd n * Multiplicative.ofAdd (q * (-k)) = 1
      change Multiplicative.ofAdd (n + q * (-k)) = 1
      rw [hk]
      simp
    let m : ℤ := Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv y).left
    have hy_coord : t96J02_presented_coordinate m 0 = y := by
      apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
      apply SemidirectProduct.ext
      · simp [m, t96J02_presented_coordinate]
      · simpa [t96J02_presented_coordinate] using hy_right.symm
    have hm : p ∣ m := (hp m).1 (hy_coord.symm ▸ hyH)
    obtain ⟨a, ha⟩ := hm
    have hy_pow : y = (t96J02_presented_coordinate p 0) ^ a := by
      rw [← hy_coord]
      apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
      rw [map_zpow]
      apply SemidirectProduct.ext
      · simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply]
        have hi := congrArg (fun z : Coordinates => z.left)
          (map_zpow (SemidirectProduct.inl (φ := action))
            (Multiplicative.ofAdd p) a)
        change Multiplicative.ofAdd m =
          (SemidirectProduct.inl (φ := action) (Multiplicative.ofAdd p) ^ a).left
        change (Multiplicative.ofAdd p) ^ a =
          (SemidirectProduct.inl (φ := action) (Multiplicative.ofAdd p) ^ a).left at hi
        calc
          Multiplicative.ofAdd m = (Multiplicative.ofAdd p) ^ a := by simpa [ha]
          _ = _ := hi
      · simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply]
        have hi := congrArg (fun z : Coordinates => z.right)
          (map_zpow (SemidirectProduct.inl (φ := action))
            (Multiplicative.ofAdd p) a)
        change 1 =
          (SemidirectProduct.inl (φ := action) (Multiplicative.ofAdd p) ^ a).right
        change 1 =
          (SemidirectProduct.inl (φ := action) (Multiplicative.ofAdd p) ^ a).right at hi
        exact hi
    have hp_cl : t96J02_presented_coordinate p 0 ∈
        Subgroup.closure ({t96J02_presented_coordinate p 0,
          t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hg_cl : g ∈ Subgroup.closure
        ({t96J02_presented_coordinate p 0,
          t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) := by
      exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))
    have hy_cl : y ∈ Subgroup.closure
        ({t96J02_presented_coordinate p 0,
          t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) := by
      rw [hy_pow]
      exact Subgroup.zpow_mem _ hp_cl a
    have hrecover : x = y * g ^ k := by
      simp [y]
    rw [hrecover]
    exact Subgroup.mul_mem _ hy_cl (Subgroup.zpow_mem _ hg_cl k)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with (rfl | hx)
    · exact (hp p).2 (dvd_refl p)
    · rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hr

/-- If the vertical step is even, the two normal-form generators commute and
give a rank-two free abelian group. -/
theorem t96J02_presented_finiteIndex_even_classify
    (H : Subgroup T96J02PresentedGroup) (p q r : ℤ)
    (hp : 0 < p) (hq : 0 < q) (heven : Even q)
    (hgen : H = Subgroup.closure
      ({t96J02_presented_coordinate p 0,
        t96J02_presented_coordinate r q} : Set T96J02PresentedGroup)) :
    Nonempty (H ≃* T96J02TorusGroup) := by
  sorry

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

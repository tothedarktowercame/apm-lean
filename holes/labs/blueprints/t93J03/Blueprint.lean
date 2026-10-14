import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.KleinOrbitQuotientHomeomorph
import ConstructionTargets.KleinSquareDiskCutAndPaste

/-! # Blueprint for t93J03

The two large geometric inputs are isolated from the generic covering-lift and
embedding arguments.  In particular, the cyclic-cover lemma exposes the exact
subgroup equality needed by Mathlib's lifting criterion.
-/

open ConstructionTargets.StatementSurfaceModels Set
noncomputable section

namespace T93J03

def a : FreeGroup Bool := FreeGroup.of false
def b : FreeGroup Bool := FreeGroup.of true

def relations : Set (FreeGroup Bool) := {b⁻¹ * a * b * a}
abbrev PresentedKleinGroup := PresentedGroup relations

def generatorA : PresentedKleinGroup := PresentedGroup.of false

def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ γ : Path x x, (∀ t, γ t ∈ U) → Path.Homotopic γ (Path.refl x)

def inclusion (X : Set KleinBottle) : C(X, KleinBottle) :=
  ⟨Subtype.val, continuous_subtype_val⟩

end T93J03
open T93J03

noncomputable abbrev T93J03KleinPlaneQuotient :=
  MulAction.orbitRel.Quotient
    KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ)

noncomputable abbrev T93J03KleinPlaneOrigin : T93J03KleinPlaneQuotient :=
  Quotient.mk _ (0, 0)

/-- The deck-group calculation at the canonical orbit of the origin. -/
theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_coordinates
    (g : KleinPresentedGroupCoordinateModel.PresentedKleinGroup) (p q : ℝ × ℝ)
    (h : g • p = q) :
    (((Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 : ℤ) : ℝ) =
        q.2 - p.2) ∧
    (((Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).1 : ℤ) : ℝ) =
        q.1 - ((Multiplicative.toAdd
          (KleinPresentedGroupCoordinateModel.action
            (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2
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

theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_cast
    {A : Type*} [TopologicalSpace A] {K : Set A} (hK : IsCompact K)
    (f : A → ℝ) (hf : Continuous f) :
    {z : KleinPresentedGroupCoordinateModel.ZMul |
      ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}.Finite := by
  let S : Set KleinPresentedGroupCoordinateModel.ZMul :=
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

theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_vertical
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {n : KleinPresentedGroupCoordinateModel.ZMul |
      ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}.Finite := by
  apply t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_cast (hK.prod hL)
  fun_prop

theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_horizontal
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L)
    (n : KleinPresentedGroupCoordinateModel.ZMul) :
    {m : KleinPresentedGroupCoordinateModel.ZMul |
      ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.1 -
        ((Multiplicative.toAdd (KleinPresentedGroupCoordinateModel.action n
          (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) '' (K ×ˢ L)}.Finite := by
  apply t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_cast (hK.prod hL)
  fun_prop

theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_actors
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {g : KleinPresentedGroupCoordinateModel.PresentedKleinGroup |
      ((g • ·) '' K ∩ L).Nonempty}.Finite := by
  let V : Set KleinPresentedGroupCoordinateModel.ZMul :=
    {n | ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
    (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}
  let H : KleinPresentedGroupCoordinateModel.ZMul →
      Set KleinPresentedGroupCoordinateModel.ZMul := fun n => {m |
    ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.1 -
        ((Multiplicative.toAdd (KleinPresentedGroupCoordinateModel.action n
          (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) '' (K ×ˢ L)}
  have hV : V.Finite :=
    t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_vertical hK hL
  have hH : ∀ n, (H n).Finite := fun n =>
    t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_horizontal hK hL n
  have hPairs : (⋃ n ∈ V, H n ×ˢ
      ({n} : Set KleinPresentedGroupCoordinateModel.ZMul)).Finite :=
    hV.biUnion fun n _ => (hH n).prod (Set.finite_singleton n)
  apply (hPairs.preimage
    KleinPresentedGroupCoordinateNormalForm.coordinatePairEquiv.injective.injOn).subset
  intro g hg
  obtain ⟨q, ⟨p, hp, hgp⟩, hq⟩ := hg
  have heq := t93J03_kleinPlaneQuotient_pi1_origin_aux_coordinates g p q hgp
  apply Set.mem_iUnion₂.mpr
  refine ⟨(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2, ?_, ?_⟩
  · exact ⟨⟨p, q⟩, ⟨hp, hq⟩, heq.1.symm⟩
  · change (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).1 ∈
        H (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 ∧
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 ∈
        ({(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2} :
          Set KleinPresentedGroupCoordinateModel.ZMul)
    exact ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, heq.2.symm⟩, Set.mem_singleton _⟩

theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_continuous
    (g : KleinPresentedGroupCoordinateModel.PresentedKleinGroup) :
    Continuous (fun p : ℝ × ℝ => g • p) := by
  change Continuous (fun p : ℝ × ℝ => KleinPlaneAffineAction.coordinateAct
    (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g) p)
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    (continuous_const.add continuous_snd)

theorem t93J03_kleinPlaneQuotient_pi1_origin_aux_free
    (g : KleinPresentedGroupCoordinateModel.PresentedKleinGroup) (p : ℝ × ℝ)
    (h : g • p = p) : g = 1 := by
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

theorem t93J03_kleinPlaneQuotient_pi1_origin :
    Nonempty
      (FundamentalGroup T93J03KleinPlaneQuotient T93J03KleinPlaneOrigin ≃*
        PresentedKleinGroup) := by
  letI : ContinuousConstSMul
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) :=
    ⟨t93J03_kleinPlaneQuotient_pi1_origin_aux_continuous⟩
  letI : ProperlyDiscontinuousSMul
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) :=
    ⟨fun hK hL =>
      t93J03_kleinPlaneQuotient_pi1_origin_aux_finite_actors hK hL⟩
  exact
    ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      t93J03_kleinPlaneQuotient_pi1_origin_aux_free (0, 0)

/-- Move the deck-group calculation to every point of the orbit quotient.
The origin calculation is an explicit hypothesis so this seat is parallel. -/
theorem t93J03_kleinPlaneQuotient_pi1_every_basepoint
    (h₀ : Nonempty
      (FundamentalGroup T93J03KleinPlaneQuotient T93J03KleinPlaneOrigin ≃*
        PresentedKleinGroup)) :
    ∀ q : T93J03KleinPlaneQuotient,
      Nonempty
        (FundamentalGroup T93J03KleinPlaneQuotient q ≃*
          PresentedKleinGroup) := by
  intro q
  obtain ⟨e₀⟩ := h₀
  exact
    ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        q T93J03KleinPlaneOrigin).trans e₀⟩

theorem t93J03_kleinPlaneQuotient_homeomorph_aux_sameOrbit
    (p q : ℝ × ℝ) :
    KleinSquareEqvGenToCases.SameOrbit p q ↔
      MulAction.orbitRel
        KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) p q := by
  change q ∈ MulAction.orbit
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup p ↔
    p ∈ MulAction.orbit
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup q
  exact MulAction.mem_orbit_symm

noncomputable def t93J03_kleinPlaneQuotient_homeomorph_aux_planeOrbitRel :
    ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient ≃ₜ
      T93J03KleinPlaneQuotient where
  toFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound
      ((t93J03_kleinPlaneQuotient_homeomorph_aux_sameOrbit p q).mp h)
  invFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound
      ((t93J03_kleinPlaneQuotient_homeomorph_aux_sameOrbit p q).mpr h)
  left_inv := by rintro ⟨p⟩; rfl
  right_inv := by rintro ⟨p⟩; rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

/-- LIBRARY (polygon cut-and-paste, shared with t96J02 and the Fmoves
foundation): the Mathlib-side plane orbit quotient is the frozen disk-polygon
Klein bottle.  t96J02 proves the same fact through its T2 / EqvGen /
closed-square leaves plus `kleinSquarePolygonQuotient_homeomorph_diskPolygon`;
port that chain here once it closes. -/
theorem t93J03_kleinPlaneQuotient_homeomorph_aux_planeOrbit :
    Nonempty (ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient ≃ₜ
      KleinBottle) := by
  sorry

/-- The explicit affine orbit quotient is the frozen polygon model of the
Klein bottle. -/
theorem t93J03_kleinPlaneQuotient_homeomorph :
    Nonempty (T93J03KleinPlaneQuotient ≃ₜ KleinBottle) := by
  obtain ⟨e⟩ := t93J03_kleinPlaneQuotient_homeomorph_aux_planeOrbit
  exact ⟨t93J03_kleinPlaneQuotient_homeomorph_aux_planeOrbitRel.symm.trans e⟩

/-- Transport an all-basepoint fundamental-group calculation across a
homeomorphism.  Both substantive conclusions are hypotheses, so this seat is
independent of the Klein-specific geometry. -/
noncomputable def t93J03_pi1_every_basepoint_of_homeomorph_aux_equiv
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

theorem t93J03_pi1_every_basepoint_of_homeomorph
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
    (e : X ≃ₜ Y)
    (hX : ∀ x : X, Nonempty (FundamentalGroup X x ≃* G)) :
    ∀ y : Y, Nonempty (FundamentalGroup Y y ≃* G) := by
  intro y
  obtain ⟨eX⟩ := hX (e.symm y)
  let E := (t93J03_pi1_every_basepoint_of_homeomorph_aux_equiv
    e (e.symm y)).symm.trans eX
  rw [e.apply_symm_apply y] at E
  exact ⟨E⟩

/-- The fundamental group of the frozen Klein polygon is its standard
presented group.  This is a sorry-free assembly of the four leaves above. -/
theorem t93J03_kleinBottle_pi1_every_basepoint :
    ∀ k : KleinBottle,
      Nonempty (FundamentalGroup KleinBottle k ≃* PresentedKleinGroup) := by
  obtain ⟨e⟩ := t93J03_kleinPlaneQuotient_homeomorph
  exact t93J03_pi1_every_basepoint_of_homeomorph e
    (t93J03_kleinPlaneQuotient_pi1_every_basepoint
      t93J03_kleinPlaneQuotient_pi1_origin)

/-- **LIBRARY.** The subgroup generated by `a` is realized by a planar
covering.  The last equality is deliberately stated at the transported
basepoint, exactly in the form used by the lifting criterion. -/
theorem t93J03_cyclicCover_zpowers_generatorA
    (k : KleinBottle)
    (e : FundamentalGroup KleinBottle k ≃* PresentedKleinGroup) :
    ∃ (C : Type) (_ : TopologicalSpace C) (p : C → KleinBottle)
      (jC : C(C, ℝ × ℝ)) (c : C)
      (hp : IsCoveringMap p) (hpc : p c = k),
      Topology.IsEmbedding jC ∧
      (FundamentalGroup.mapOfEq
          ⟨p, hp.continuous⟩ hpc).range =
        Subgroup.comap e.toMonoidHom (Subgroup.zpowers generatorA) := by
  sorry

/-- Apply the standard covering-space lifting criterion after rewriting its
subgroup condition with the cyclic cover's computed range. -/
theorem t93J03_coveringLift_of_subgroup_le
    {C : Type} [TopologicalSpace C] {p : C → KleinBottle}
    (hp : IsCoveringMap p) (c : C) {k : KleinBottle}
    (hpc : p c = k)
    (e : FundamentalGroup KleinBottle k ≃* PresentedKleinGroup)
    (hcover :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range =
        Subgroup.comap e.toMonoidHom (Subgroup.zpowers generatorA))
    (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X]
    (x : X) (hx : (x : KleinBottle) = k)
    (hX : ∀ g ∈ (FundamentalGroup.mapOfEq (inclusion X) hx).range,
      e g ∈ Subgroup.zpowers generatorA) :
    ∃ l : C(X, C), p ∘ l = inclusion X := by
  cases hx
  have hle :
      (FundamentalGroup.map (inclusion X) x).range ≤
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range := by
    rintro g ⟨y, rfl⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective y
    rw [hcover]
    apply hX
    refine ⟨FundamentalGroup.fromPath (.mk γ), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    congr
  obtain ⟨l, ⟨_, hl⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts_of_range_le hpc hle
  exact ⟨l, hl⟩

/-- A lift of a subspace inclusion is an embedding (embedding cancellation),
and composing it with the planar embedding of the cover stays an embedding. -/
theorem t93J03_lift_isEmbedding_assembly
    {C : Type} [TopologicalSpace C] {p : C → KleinBottle}
    (hp : Continuous p) (jC : C(C, ℝ × ℝ))
    (hjC : Topology.IsEmbedding jC)
    (X : Set KleinBottle) (l : C(X, C))
    (hl : p ∘ l = inclusion X) :
    ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j := by
  have hl' : Topology.IsEmbedding l := by
    apply Topology.IsEmbedding.of_comp l.continuous hp
    rw [hl]
    exact Topology.IsEmbedding.subtypeVal
  exact ⟨jC.comp l, hjC.comp hl'⟩

theorem apm_t93j03 :
    ∀ k : KleinBottle, ∃ e : FundamentalGroup KleinBottle k ≃* PresentedKleinGroup,
      ∀ (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X],
      SemilocallySimplyConnected X → ∀ (x : X) (hx : (x : KleinBottle) = k),
      (∀ g ∈ (FundamentalGroup.mapOfEq (inclusion X) hx).range,
        e g ∈ Subgroup.zpowers generatorA) →
      ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j := by
  intro k
  obtain ⟨e⟩ := t93J03_kleinBottle_pi1_every_basepoint k
  refine ⟨e, ?_⟩
  intro X _ _ _ x hx hX
  obtain ⟨C, topC, p, jC, c, hp, hpc, hjC, hcover⟩ :=
    t93J03_cyclicCover_zpowers_generatorA k e
  letI : TopologicalSpace C := topC
  obtain ⟨l, hl⟩ :=
    t93J03_coveringLift_of_subgroup_le hp c hpc e hcover X x hx hX
  exact t93J03_lift_isEmbedding_assembly hp.continuous jC hjC X l hl

#print axioms apm_t93j03

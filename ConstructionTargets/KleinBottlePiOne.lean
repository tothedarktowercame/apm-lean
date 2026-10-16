import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.KleinOrbitQuotientHomeomorph
import ConstructionTargets.KleinSquareDiskCutAndPaste

/-! # π₁ of the Klein bottle at every basepoint

Banked from the closed t93J03 (its Main, sections before the cyclic cover) by
claude-14 2026-10-16 for the t95J03 blueprint.  The group is the coordinate
model's `PresentedKleinGroup = ⟨a, b | b⁻¹ a b a⟩`
(`KleinPresentedGroupCoordinateModel`, with `coordinateEquiv` to `ℤ ⋊ ℤ`). -/

open ConstructionTargets.StatementSurfaceModels Set
noncomputable section

namespace ConstructionTargets.KleinBottlePiOne

open KleinPresentedGroupCoordinateModel

noncomputable abbrev KleinPlaneQuotient :=
  MulAction.orbitRel.Quotient
    KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ)

noncomputable abbrev KleinPlaneOrigin : KleinPlaneQuotient :=
  Quotient.mk _ (0, 0)

/-- The deck-group calculation at the canonical orbit of the origin. -/
theorem kleinPlaneQuotient_pi1_origin_aux_coordinates
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

theorem kleinPlaneQuotient_pi1_origin_aux_finite_cast
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

theorem kleinPlaneQuotient_pi1_origin_aux_finite_vertical
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {n : KleinPresentedGroupCoordinateModel.ZMul |
      ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}.Finite := by
  apply kleinPlaneQuotient_pi1_origin_aux_finite_cast (hK.prod hL)
  fun_prop

theorem kleinPlaneQuotient_pi1_origin_aux_finite_horizontal
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L)
    (n : KleinPresentedGroupCoordinateModel.ZMul) :
    {m : KleinPresentedGroupCoordinateModel.ZMul |
      ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.1 -
        ((Multiplicative.toAdd (KleinPresentedGroupCoordinateModel.action n
          (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) '' (K ×ˢ L)}.Finite := by
  apply kleinPlaneQuotient_pi1_origin_aux_finite_cast (hK.prod hL)
  fun_prop

theorem kleinPlaneQuotient_pi1_origin_aux_finite_actors
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
    kleinPlaneQuotient_pi1_origin_aux_finite_vertical hK hL
  have hH : ∀ n, (H n).Finite := fun n =>
    kleinPlaneQuotient_pi1_origin_aux_finite_horizontal hK hL n
  have hPairs : (⋃ n ∈ V, H n ×ˢ
      ({n} : Set KleinPresentedGroupCoordinateModel.ZMul)).Finite :=
    hV.biUnion fun n _ => (hH n).prod (Set.finite_singleton n)
  apply (hPairs.preimage
    KleinPresentedGroupCoordinateNormalForm.coordinatePairEquiv.injective.injOn).subset
  intro g hg
  obtain ⟨q, ⟨p, hp, hgp⟩, hq⟩ := hg
  have heq := kleinPlaneQuotient_pi1_origin_aux_coordinates g p q hgp
  apply Set.mem_iUnion₂.mpr
  refine ⟨(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2, ?_, ?_⟩
  · exact ⟨⟨p, q⟩, ⟨hp, hq⟩, heq.1.symm⟩
  · change (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).1 ∈
        H (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 ∧
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2 ∈
        ({(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2} :
          Set KleinPresentedGroupCoordinateModel.ZMul)
    exact ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, heq.2.symm⟩, Set.mem_singleton _⟩

theorem kleinPlaneQuotient_pi1_origin_aux_continuous
    (g : KleinPresentedGroupCoordinateModel.PresentedKleinGroup) :
    Continuous (fun p : ℝ × ℝ => g • p) := by
  change Continuous (fun p : ℝ × ℝ => KleinPlaneAffineAction.coordinateAct
    (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g) p)
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    (continuous_const.add continuous_snd)

theorem kleinPlaneQuotient_pi1_origin_aux_free
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

theorem kleinPlaneQuotient_pi1_origin :
    Nonempty
      (FundamentalGroup KleinPlaneQuotient KleinPlaneOrigin ≃*
        PresentedKleinGroup) := by
  letI : ContinuousConstSMul
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) :=
    ⟨kleinPlaneQuotient_pi1_origin_aux_continuous⟩
  letI : ProperlyDiscontinuousSMul
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) :=
    ⟨fun hK hL =>
      kleinPlaneQuotient_pi1_origin_aux_finite_actors hK hL⟩
  exact
    ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      kleinPlaneQuotient_pi1_origin_aux_free (0, 0)

/-- Move the deck-group calculation to every point of the orbit quotient.
The origin calculation is an explicit hypothesis so this seat is parallel. -/
theorem kleinPlaneQuotient_pi1_every_basepoint
    (h₀ : Nonempty
      (FundamentalGroup KleinPlaneQuotient KleinPlaneOrigin ≃*
        PresentedKleinGroup)) :
    ∀ q : KleinPlaneQuotient,
      Nonempty
        (FundamentalGroup KleinPlaneQuotient q ≃*
          PresentedKleinGroup) := by
  intro q
  obtain ⟨e₀⟩ := h₀
  exact
    ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        q KleinPlaneOrigin).trans e₀⟩

theorem kleinPlaneQuotient_homeomorph_aux_sameOrbit
    (p q : ℝ × ℝ) :
    KleinSquareEqvGenToCases.SameOrbit p q ↔
      MulAction.orbitRel
        KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) p q := by
  change q ∈ MulAction.orbit
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup p ↔
    p ∈ MulAction.orbit
      KleinPresentedGroupCoordinateModel.PresentedKleinGroup q
  exact MulAction.mem_orbit_symm

noncomputable def kleinPlaneQuotient_homeomorph_aux_planeOrbitRel :
    ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient ≃ₜ
      KleinPlaneQuotient where
  toFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound
      ((kleinPlaneQuotient_homeomorph_aux_sameOrbit p q).mp h)
  invFun := Quotient.lift (fun p => Quotient.mk _ p) fun p q h =>
    Quotient.sound
      ((kleinPlaneQuotient_homeomorph_aux_sameOrbit p q).mpr h)
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
theorem kleinPlaneQuotient_homeomorph_aux_planeOrbit :
    Nonempty (ConstructionTargets.KleinOrbitQuotientHomeomorph.PlaneOrbitQuotient ≃ₜ
      KleinBottle) := by
  letI : ContinuousConstSMul KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) :=
    ⟨kleinPlaneQuotient_pi1_origin_aux_continuous⟩
  letI : ProperlyDiscontinuousSMul KleinPresentedGroupCoordinateModel.PresentedKleinGroup
      (ℝ × ℝ) :=
    ⟨fun hK hL => kleinPlaneQuotient_pi1_origin_aux_finite_actors hK hL⟩
  letI : T2Space KleinPlaneQuotient :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
      (Γ := KleinPresentedGroupCoordinateModel.PresentedKleinGroup) (T := ℝ × ℝ)
  exact KleinSquareDiskCutAndPaste.planeOrbitQuotient_homeomorph_kleinBottle
    kleinPlaneQuotient_homeomorph_aux_planeOrbitRel.symm.t2Space

/-- The explicit affine orbit quotient is the frozen polygon model of the
Klein bottle. -/
theorem kleinPlaneQuotient_homeomorph :
    Nonempty (KleinPlaneQuotient ≃ₜ KleinBottle) := by
  obtain ⟨e⟩ := kleinPlaneQuotient_homeomorph_aux_planeOrbit
  exact ⟨kleinPlaneQuotient_homeomorph_aux_planeOrbitRel.symm.trans e⟩

/-- Transport an all-basepoint fundamental-group calculation across a
homeomorphism.  Both substantive conclusions are hypotheses, so this seat is
independent of the Klein-specific geometry. -/
noncomputable def pi1_every_basepoint_of_homeomorph_aux_equiv
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

theorem pi1_every_basepoint_of_homeomorph
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
    (e : X ≃ₜ Y)
    (hX : ∀ x : X, Nonempty (FundamentalGroup X x ≃* G)) :
    ∀ y : Y, Nonempty (FundamentalGroup Y y ≃* G) := by
  intro y
  obtain ⟨eX⟩ := hX (e.symm y)
  let E := (pi1_every_basepoint_of_homeomorph_aux_equiv
    e (e.symm y)).symm.trans eX
  rw [e.apply_symm_apply y] at E
  exact ⟨E⟩

/-- The fundamental group of the frozen Klein polygon is its standard
presented group.  This is a sorry-free assembly of the four leaves above. -/
theorem kleinBottle_pi1_every_basepoint :
    ∀ k : KleinBottle,
      Nonempty (FundamentalGroup KleinBottle k ≃* PresentedKleinGroup) := by
  obtain ⟨e⟩ := kleinPlaneQuotient_homeomorph
  exact pi1_every_basepoint_of_homeomorph e
    (kleinPlaneQuotient_pi1_every_basepoint
      kleinPlaneQuotient_pi1_origin)

end ConstructionTargets.KleinBottlePiOne

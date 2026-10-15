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
  letI : ContinuousConstSMul T96J02PresentedGroup (ℝ × ℝ) :=
    ⟨t96J02_kleinPlaneQuotient_pi1_origin_aux_continuous⟩
  letI : ProperlyDiscontinuousSMul T96J02PresentedGroup (ℝ × ℝ) :=
    ⟨fun hK hL =>
      t96J02_kleinPlaneQuotient_pi1_origin_aux_finite_actors hK hL⟩
  letI : T2Space T96J02KleinPlaneQuotient :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
      (Γ := T96J02PresentedGroup) (T := ℝ × ℝ)
  exact t96J02_kleinPlaneQuotient_homeomorph_aux_planeOrbitRel.symm.t2Space

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
theorem t96J02_kleinSquare_orbit_iff_eqvGen_aux_bounds {p q : ℝ × ℝ}
    (h : Relation.EqvGen KleinSquareBoundaryRelation.SquareRel p q) :
    KleinPlaneActionSquareOrbitClassification.InSquare p ↔
      KleinPlaneActionSquareOrbitClassification.InSquare q := by
  induction h with
  | rel p q h =>
      rcases h with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
      all_goals constructor <;> intro _ <;>
        exact KleinSquareEdgeOrientation.inSquare_squareEdge _ t
  | refl p => exact Iff.rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem t96J02_kleinSquare_orbit_iff_eqvGen_aux_lift
    {p q : ℝ × ℝ}
    (h : Relation.EqvGen KleinSquareBoundaryRelation.SquareRel p q)
    (hp : KleinPlaneActionSquareOrbitClassification.InSquare p)
    (hq : KleinPlaneActionSquareOrbitClassification.InSquare q) :
    Relation.EqvGen T96J02ClosedSquareRel ⟨p, hp⟩ ⟨q, hq⟩ := by
  induction h with
  | rel p q h =>
      exact Relation.EqvGen.rel _ _ h
  | refl p => exact Relation.EqvGen.refl _
  | symm p q h ih => exact Relation.EqvGen.symm _ _ (ih hq hp)
  | trans p q r h₁ h₂ ih₁ ih₂ =>
      have hq' := (t96J02_kleinSquare_orbit_iff_eqvGen_aux_bounds h₁).mp hp
      exact Relation.EqvGen.trans _ ⟨q, hq'⟩ _ (ih₁ hp hq') (ih₂ hq' hq)

theorem t96J02_kleinSquare_orbit_iff_eqvGen_aux_forget
    {p q : T96J02ClosedSquare}
    (h : Relation.EqvGen T96J02ClosedSquareRel p q) :
    Relation.EqvGen KleinSquareBoundaryRelation.SquareRel p.1 q.1 := by
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ h
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem t96J02_kleinSquare_orbit_iff_eqvGen
    (p q : T96J02ClosedSquare) :
    ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv.closedSquareOrbitSetoid.r p q ↔
      Relation.EqvGen T96J02ClosedSquareRel p q := by
  constructor
  · intro h
    apply t96J02_kleinSquare_orbit_iff_eqvGen_aux_lift
    exact KleinSquareCasesToEqvGen.cases_eqvGen p.2 q.2
      ((KleinPlaneActionSquareOrbitClassification.sameOrbit_iff_cases p.2 q.2).mp h)
  · intro h
    exact (KleinPlaneActionSquareOrbitClassification.sameOrbit_iff_cases p.2 q.2).mpr
      (KleinSquareEqvGenToCases.eqvGen_cases p.2 q.2
        (t96J02_kleinSquare_orbit_iff_eqvGen_aux_forget h))

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
  let f : ConstructionTargets.KleinOrbitQuotientHomeomorph.ClosedSquareOrbitQuotient →
      T96J02SquarePolygonQuotient :=
    Quotient.lift (fun p => Quotient.mk _ p) (fun p q hpq =>
      Quotient.sound ((hrel p q).mp hpq))
  let g : T96J02SquarePolygonQuotient →
      ConstructionTargets.KleinOrbitQuotientHomeomorph.ClosedSquareOrbitQuotient :=
    Quotient.lift (fun p => Quotient.mk _ p) (fun p q hpq =>
      Quotient.sound ((hrel p q).mpr hpq))
  refine ⟨{
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_
  }⟩
  · rintro ⟨p⟩
    rfl
  · rintro ⟨p⟩
    rfl
  · apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  · apply Continuous.quotient_lift
    exact continuous_coinduced_rng

/-! ## Cut-and-paste: square `b a b a⁻¹` versus disk `a a b b` (design 2026-10-14)

The disk is carried onto the ℓ¹ diamond `|re| + |im| ≤ 1` by the `I`-equivariant
radial chart `z ↦ (‖z‖ / ℓ¹ z) • z`.  The four disk arcs become the four sides, and
both disk pairings become `w ↦ I * w` (first-quadrant side to second, third to
fourth).  The diamond is cut along the imaginary axis: the left half goes affinely
onto the lower-right triangle `v ≤ u` of the square (`t96J02_cut_L`, vertices
`-I, I, -1 ↦ (0,0), (1,0), (1,1)`), the right half onto the upper-left triangle
(`t96J02_cut_R`, vertices `1, I, -I ↦ (0,0), (0,1), (1,1)`).  The cut becomes the
bottom/top pairing `(t,0) ~ (1-t,1)`, the disk `a` pairing becomes `(0,s) ~ (1,s)`,
and the disk `b` pairing lands on the square's diagonal, where the two halves meet.
`t96J02_paste_L/R` are the affine inverses.  The clamps are the identity on every
point actually used; they only make the raw maps total. -/

section T96J02CutAndPaste
open ConstructionTargets.Surfaces

noncomputable def t96J02_cut_l1 (w : ℂ) : ℝ := |w.re| + |w.im|

noncomputable def t96J02_cut_chart (z : ℂ) : ℂ :=
  if z = 0 then 0 else ((‖z‖ / t96J02_cut_l1 z : ℝ) : ℂ) * z

noncomputable def t96J02_cut_chartInv (w : ℂ) : ℂ :=
  if w = 0 then 0 else ((t96J02_cut_l1 w / ‖w‖ : ℝ) : ℂ) * w

noncomputable def t96J02_cut_L (w : ℂ) : ℝ × ℝ := (1/2 - w.re/2 + w.im/2, -w.re)
noncomputable def t96J02_cut_R (w : ℂ) : ℝ × ℝ := (1/2 - w.re/2 - w.im/2, 1 - w.re)
noncomputable def t96J02_paste_L (p : ℝ × ℝ) : ℂ := ⟨-p.2, 2 * p.1 - 1 - p.2⟩
noncomputable def t96J02_paste_R (p : ℝ × ℝ) : ℂ := ⟨1 - p.2, p.2 - 2 * p.1⟩

noncomputable def t96J02_cut_clampSquare (p : ℝ × ℝ) : T96J02ClosedSquare :=
  ⟨(max 0 (min 1 p.1), max 0 (min 1 p.2)), by
    refine ⟨le_max_left _ _, ?_, le_max_left _ _, ?_⟩ <;>
      exact max_le zero_le_one (min_le_left _ _)⟩

noncomputable def t96J02_cut_clampDisk (z : ℂ) : Disk :=
  ⟨((1 / max 1 ‖z‖ : ℝ) : ℂ) * z, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    exact le_max_right _ _⟩

noncomputable def t96J02_cut_raw (z : Disk) : T96J02ClosedSquare :=
  if (t96J02_cut_chart z).re ≤ 0 then t96J02_cut_clampSquare (t96J02_cut_L (t96J02_cut_chart z))
  else t96J02_cut_clampSquare (t96J02_cut_R (t96J02_cut_chart z))

noncomputable def t96J02_paste_raw (p : T96J02ClosedSquare) : Disk :=
  t96J02_cut_clampDisk (t96J02_cut_chartInv
    (if p.1.2 ≤ p.1.1 then t96J02_paste_L p.1 else t96J02_paste_R p.1))

lemma t96J02_cut_l1_smul (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    t96J02_cut_l1 ((c : ℂ) * z) = c * t96J02_cut_l1 z := by
  simp [t96J02_cut_l1, abs_mul, abs_of_nonneg hc, mul_add]

lemma t96J02_cut_l1_pos {z : ℂ} (hz : z ≠ 0) : 0 < t96J02_cut_l1 z := by
  unfold t96J02_cut_l1
  by_contra h
  push_neg at h
  have h1 : |z.re| = 0 := le_antisymm (by linarith [abs_nonneg z.im]) (abs_nonneg _)
  have h2 : |z.im| = 0 := le_antisymm (by linarith [abs_nonneg z.re]) (abs_nonneg _)
  exact hz (Complex.ext (by simpa using h1) (by simpa using h2))

lemma t96J02_cut_l1_chart (z : ℂ) : t96J02_cut_l1 (t96J02_cut_chart z) = ‖z‖ := by
  unfold t96J02_cut_chart
  split_ifs with hz
  · simp [hz, t96J02_cut_l1]
  · rw [t96J02_cut_l1_smul _ (div_nonneg (norm_nonneg _) (t96J02_cut_l1_pos hz).le), div_mul_cancel₀ _ (t96J02_cut_l1_pos hz).ne']

lemma t96J02_cut_norm_chartInv (w : ℂ) : ‖t96J02_cut_chartInv w‖ = t96J02_cut_l1 w := by
  unfold t96J02_cut_chartInv
  split_ifs with hw
  · simp [hw, t96J02_cut_l1]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (t96J02_cut_l1_pos hw).le (norm_nonneg _)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hw)]

lemma t96J02_cut_chart_pos (z : ℂ) :
    ∃ c : ℝ, 0 < c ∧ t96J02_cut_chart z = (c : ℂ) * z := by
  unfold t96J02_cut_chart
  split_ifs with hz
  · exact ⟨1, one_pos, by simp [hz]⟩
  · exact ⟨_, div_pos (norm_pos_iff.mpr hz) (t96J02_cut_l1_pos hz), rfl⟩

lemma t96J02_cut_chartInv_pos (w : ℂ) :
    ∃ c : ℝ, 0 < c ∧ t96J02_cut_chartInv w = (c : ℂ) * w := by
  unfold t96J02_cut_chartInv
  split_ifs with hw
  · exact ⟨1, one_pos, by simp [hw]⟩
  · exact ⟨_, div_pos (t96J02_cut_l1_pos hw) (norm_pos_iff.mpr hw), rfl⟩

lemma t96J02_cut_l1_I (z : ℂ) : t96J02_cut_l1 (Complex.I * z) = t96J02_cut_l1 z := by
  simp [t96J02_cut_l1, add_comm]

lemma t96J02_cut_chart_I (z : ℂ) :
    t96J02_cut_chart (Complex.I * z) = Complex.I * t96J02_cut_chart z := by
  unfold t96J02_cut_chart
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg (mul_ne_zero Complex.I_ne_zero hz), if_neg hz, t96J02_cut_l1_I]
    simp; ring

lemma t96J02_cut_chartInv_I (w : ℂ) :
    t96J02_cut_chartInv (Complex.I * w) = Complex.I * t96J02_cut_chartInv w := by
  unfold t96J02_cut_chartInv
  by_cases hw : w = 0
  · simp [hw]
  · rw [if_neg (mul_ne_zero Complex.I_ne_zero hw), if_neg hw, t96J02_cut_l1_I]
    simp; ring

lemma t96J02_cut_chartInv_chart (z : ℂ) :
    t96J02_cut_chartInv (t96J02_cut_chart z) = z := by
  by_cases hz : z = 0
  · simp [t96J02_cut_chart, t96J02_cut_chartInv, hz]
  have hc : t96J02_cut_chart z ≠ 0 := by
    obtain ⟨c, hc, h⟩ := t96J02_cut_chart_pos z
    rw [h]; exact mul_ne_zero (by exact_mod_cast hc.ne') hz
  have hn : ‖t96J02_cut_chart z‖ = ‖z‖ ^ 2 / t96J02_cut_l1 z := by
    rw [t96J02_cut_chart, if_neg hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (t96J02_cut_l1_pos hz).le)]; ring
  rw [t96J02_cut_chartInv, if_neg hc, t96J02_cut_l1_chart, hn, t96J02_cut_chart, if_neg hz,
    ← mul_assoc, ← Complex.ofReal_mul]
  have h1 := norm_pos_iff.mpr hz
  have h2 := t96J02_cut_l1_pos hz
  have : ‖z‖ / (‖z‖ ^ 2 / t96J02_cut_l1 z) * (‖z‖ / t96J02_cut_l1 z) = 1 := by
    field_simp
  rw [this]; simp

lemma t96J02_cut_chart_chartInv (w : ℂ) :
    t96J02_cut_chart (t96J02_cut_chartInv w) = w := by
  by_cases hw : w = 0
  · simp [t96J02_cut_chart, t96J02_cut_chartInv, hw]
  have hc : t96J02_cut_chartInv w ≠ 0 := by
    obtain ⟨c, hc, h⟩ := t96J02_cut_chartInv_pos w
    rw [h]; exact mul_ne_zero (by exact_mod_cast hc.ne') hw
  have hl : t96J02_cut_l1 (t96J02_cut_chartInv w) = t96J02_cut_l1 w ^ 2 / ‖w‖ := by
    rw [t96J02_cut_chartInv, if_neg hw,
      t96J02_cut_l1_smul _ (div_nonneg (t96J02_cut_l1_pos hw).le (norm_nonneg _))]; ring
  rw [t96J02_cut_chart, if_neg hc, t96J02_cut_norm_chartInv, hl, t96J02_cut_chartInv, if_neg hw,
    ← mul_assoc, ← Complex.ofReal_mul]
  have h1 := norm_pos_iff.mpr hw
  have h2 := t96J02_cut_l1_pos hw
  have : t96J02_cut_l1 w / (t96J02_cut_l1 w ^ 2 / ‖w‖) * (t96J02_cut_l1 w / ‖w‖) = 1 := by
    field_simp
  rw [this]; simp

lemma t96J02_cut_edge_succ (t : Set.Icc (0 : ℝ) 1) :
    (edgePoint 4 1 t : ℂ) = Complex.I * edgePoint 4 0 t ∧
      (edgePoint 4 3 t : ℂ) = Complex.I * edgePoint 4 2 t := by
  have hI : Complex.exp (Complex.I * (Real.pi / 2 : ℝ)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  have hmul : ∀ w, Complex.I * Complex.exp w =
      Complex.exp (Complex.I * (Real.pi / 2 : ℝ) + w) := by
    intro w; rw [Complex.exp_add, hI]
  constructor <;>
  · simp only [edgePoint]
    rw [hmul]
    congr 1
    push_cast
    ring

/-- The two quadrant edges of the disk, by membership. -/
lemma t96J02_cut_edge_zero_iff (z : Disk) :
    (∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 0 t) ↔
      ‖(z : ℂ)‖ = 1 ∧ 0 ≤ (z : ℂ).re ∧ 0 ≤ (z : ℂ).im := by
  sorry

lemma t96J02_cut_edge_two_iff (z : Disk) :
    (∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 2 t) ↔
      ‖(z : ℂ)‖ = 1 ∧ (z : ℂ).re ≤ 0 ∧ (z : ℂ).im ≤ 0 := by
  sorry

lemma t96J02_cut_chart_continuous : Continuous t96J02_cut_chart := by
  sorry

lemma t96J02_cut_chartInv_continuous : Continuous t96J02_cut_chartInv := by
  sorry

/-- The four polygon vertices `1, I, -1, -I` of the `aabb` disk are one class. -/
lemma t96J02_cut_disk_vertices (x y : Disk)
    (hx : (x : ℂ) = 1 ∨ (x : ℂ) = Complex.I ∨ (x : ℂ) = -1 ∨ (x : ℂ) = -Complex.I)
    (hy : (y : ℂ) = 1 ∨ (y : ℂ) = Complex.I ∨ (y : ℂ) = -1 ∨ (y : ℂ) = -Complex.I) :
    surfaceQuotient false 2 x = surfaceQuotient false 2 y := by
  sorry

/-- The four corners of the square are one class. -/
lemma t96J02_cut_square_corners (p q : T96J02ClosedSquare)
    (hp : p.1 = (0, 0) ∨ p.1 = (1, 0) ∨ p.1 = (0, 1) ∨ p.1 = (1, 1))
    (hq : q.1 = (0, 0) ∨ q.1 = (1, 0) ∨ q.1 = (0, 1) ∨ q.1 = (1, 1)) :
    (Quotient.mk _ p : T96J02SquarePolygonQuotient) = Quotient.mk _ q := by
  sorry

lemma t96J02_cut_continuous (hchart : Continuous t96J02_cut_chart) :
    Continuous (fun z : Disk =>
      (Quotient.mk _ (t96J02_cut_raw z) : T96J02SquarePolygonQuotient)) := by
  sorry

lemma t96J02_paste_continuous (hinv : Continuous t96J02_cut_chartInv)
    (hedge2 : ∀ z : Disk, ‖(z : ℂ)‖ = 1 → (z : ℂ).re ≤ 0 → (z : ℂ).im ≤ 0 →
      ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 2 t) :
    Continuous (fun p : T96J02ClosedSquare =>
      surfaceQuotient false 2 (t96J02_paste_raw p)) := by
  sorry

-- BEGIN SEAT AREA
lemma t96J02_cut_rel
    (hedge0 : ∀ t : Set.Icc (0 : ℝ) 1, ‖(edgePoint 4 0 t : ℂ)‖ = 1 ∧
      0 ≤ (edgePoint 4 0 t : ℂ).re ∧ 0 ≤ (edgePoint 4 0 t : ℂ).im)
    (hedge2 : ∀ t : Set.Icc (0 : ℝ) 1, ‖(edgePoint 4 2 t : ℂ)‖ = 1 ∧
      (edgePoint 4 2 t : ℂ).re ≤ 0 ∧ (edgePoint 4 2 t : ℂ).im ≤ 0)
    (hcorners : ∀ p q : T96J02ClosedSquare,
      (p.1 = (0, 0) ∨ p.1 = (1, 0) ∨ p.1 = (0, 1) ∨ p.1 = (1, 1)) →
      (q.1 = (0, 0) ∨ q.1 = (1, 0) ∨ q.1 = (0, 1) ∨ q.1 = (1, 1)) →
      (Quotient.mk _ p : T96J02SquarePolygonQuotient) = Quotient.mk _ q)
    (x y : Disk) (h : SurfaceRel false 2 x y) :
    (Quotient.mk _ (t96J02_cut_raw x) : T96J02SquarePolygonQuotient) =
      Quotient.mk _ (t96J02_cut_raw y) := by
  rw [KleinSurfaceRelNormalForm.surfaceRel_false_two_iff] at h
  rcases h with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · let x : Disk := edgePoint 4 0 t
    let y : Disk := edgePoint 4 1 t
    change (Quotient.mk _ (t96J02_cut_raw x) : T96J02SquarePolygonQuotient) =
      Quotient.mk _ (t96J02_cut_raw y)
    let w : ℂ := t96J02_cut_chart x
    have hy : (y : ℂ) = Complex.I * x :=
      (t96J02_cut_edge_succ t).1
    have hwI : t96J02_cut_chart y = Complex.I * w := by
      rw [hy, t96J02_cut_chart_I]
    obtain ⟨c, hc, hw⟩ := t96J02_cut_chart_pos (x : ℂ)
    have hx := hedge0 t
    have hwr : 0 ≤ w.re := by
      change 0 ≤ (t96J02_cut_chart x).re
      rw [hw]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]; exact mul_nonneg hc.le hx.2.1
    have hwi : 0 ≤ w.im := by
      change 0 ≤ (t96J02_cut_chart x).im
      rw [hw]; simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]; exact mul_nonneg hc.le hx.2.2
    have hsum : w.re + w.im = 1 := by
      have := t96J02_cut_l1_chart (x : ℂ)
      rw [hx.1] at this
      simpa [w, t96J02_cut_l1, abs_of_nonneg hwr, abs_of_nonneg hwi] using this
    have hwdef : t96J02_cut_chart x = w := rfl
    by_cases hz : w.re = 0
    · have hi : w.im = 1 := by linarith
      apply hcorners
      · exact Or.inr (Or.inl (by
        simp [t96J02_cut_raw, hwdef, hwr, t96J02_cut_L,
          t96J02_cut_clampSquare, hz, hi] <;> norm_num))
      · exact Or.inr (Or.inr (Or.inr (by
          simp [t96J02_cut_raw, hwdef, hwI, t96J02_cut_L,
            t96J02_cut_clampSquare, hz, hi] <;> norm_num)))
    · have hwr' : 0 < w.re := lt_of_le_of_ne hwr (Ne.symm hz)
      have hwi1 : w.im ≤ 1 := by linarith
      have hwr1 : w.re ≤ 1 := by linarith
      apply Quotient.sound
      apply Relation.EqvGen.rel
      left
      let s : Set.Icc (0 : ℝ) 1 := ⟨w.im, hwi, by linarith⟩
      have he0 : (2 : ℝ)⁻¹ - w.re / 2 - w.im / 2 = 0 := by linarith
      have he1 : (2 : ℝ)⁻¹ - -w.im / 2 + w.re / 2 = 1 := by linarith
      refine ⟨s, ?_, ?_⟩
      · simp [t96J02_cut_raw, hwdef, hwr, t96J02_cut_L, t96J02_cut_R,
          t96J02_cut_clampSquare, not_le.mpr hwr', hsum, hwi, hwi1, hwr1, he0, s]
        simp [KleinSquareEdgeOrientation.squareEdge]
        linarith
      · simp [t96J02_cut_raw, hwdef, hwI, t96J02_cut_R,
          t96J02_cut_clampSquare, hwi, hwi1, hwr', hwr1, hsum, s,
          t96J02_cut_L, he1]
        simp [KleinSquareEdgeOrientation.squareEdge]
  · let x : Disk := edgePoint 4 2 t
    let y : Disk := edgePoint 4 3 t
    change (Quotient.mk _ (t96J02_cut_raw x) : T96J02SquarePolygonQuotient) =
      Quotient.mk _ (t96J02_cut_raw y)
    let w : ℂ := t96J02_cut_chart x
    have hy : (y : ℂ) = Complex.I * x :=
      (t96J02_cut_edge_succ t).2
    have hwI : t96J02_cut_chart y = Complex.I * w := by
      rw [hy, t96J02_cut_chart_I]
    obtain ⟨c, hc, hw⟩ := t96J02_cut_chart_pos (x : ℂ)
    have hx := hedge2 t
    have hwr : w.re ≤ 0 := by
      change (t96J02_cut_chart x).re ≤ 0
      rw [hw]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]; exact mul_nonpos_of_nonneg_of_nonpos hc.le hx.2.1
    have hwi : w.im ≤ 0 := by
      change (t96J02_cut_chart x).im ≤ 0
      rw [hw]; simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]; exact mul_nonpos_of_nonneg_of_nonpos hc.le hx.2.2
    have hsum : w.re + w.im = -1 := by
      have := t96J02_cut_l1_chart (x : ℂ)
      rw [hx.1] at this
      simp [w, t96J02_cut_l1, abs_of_nonpos hwr, abs_of_nonpos hwi] at this
      linarith
    have hwdef : t96J02_cut_chart x = w := rfl
    by_cases hz : w.im = 0
    · have hr : w.re = -1 := by linarith
      apply hcorners
      · exact Or.inr (Or.inr (Or.inr (by
          simp [t96J02_cut_raw, hwdef, hwr, t96J02_cut_L,
            t96J02_cut_clampSquare, hz, hr] <;> norm_num)))
      · left
        simp [t96J02_cut_raw, hwdef, hwI, t96J02_cut_L,
          t96J02_cut_clampSquare, hz, hr] <;> norm_num
    · have hwi' : w.im < 0 := lt_of_le_of_ne hwi hz
      have hnr0 : 0 ≤ -w.re := by linarith
      have hnr1 : -w.re ≤ 1 := by linarith
      have hib0 : 0 ≤ 1 + w.im := by linarith
      have hib1 : 1 + w.im ≤ 1 := by linarith
      congr 1
      apply Subtype.ext
      simp [t96J02_cut_raw, hwdef, hwI, hwr, not_le.mpr hwi', t96J02_cut_L,
        t96J02_cut_R, t96J02_cut_clampSquare, hsum, hnr0, hnr1, hib0, hib1]
      constructor
      · congr 2 <;> ring
      · linarith
-- END SEAT AREA

lemma t96J02_paste_rel
    (hedge0 : ∀ z : Disk, ‖(z : ℂ)‖ = 1 → 0 ≤ (z : ℂ).re → 0 ≤ (z : ℂ).im →
      ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 0 t)
    (hedge2 : ∀ z : Disk, ‖(z : ℂ)‖ = 1 → (z : ℂ).re ≤ 0 → (z : ℂ).im ≤ 0 →
      ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 2 t)
    (hvertices : ∀ x y : Disk,
      ((x : ℂ) = 1 ∨ (x : ℂ) = Complex.I ∨ (x : ℂ) = -1 ∨ (x : ℂ) = -Complex.I) →
      ((y : ℂ) = 1 ∨ (y : ℂ) = Complex.I ∨ (y : ℂ) = -1 ∨ (y : ℂ) = -Complex.I) →
      surfaceQuotient false 2 x = surfaceQuotient false 2 y)
    (p q : T96J02ClosedSquare) (h : T96J02ClosedSquareRel p q) :
    surfaceQuotient false 2 (t96J02_paste_raw p) =
      surfaceQuotient false 2 (t96J02_paste_raw q) := by
  sorry

lemma t96J02_paste_cut
    (hedge2 : ∀ z : Disk, ‖(z : ℂ)‖ = 1 → (z : ℂ).re ≤ 0 → (z : ℂ).im ≤ 0 →
      ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 2 t)
    (x : Disk) :
    surfaceQuotient false 2 (t96J02_paste_raw (t96J02_cut_raw x)) =
      surfaceQuotient false 2 x := by
  sorry

lemma t96J02_cut_paste (p : T96J02ClosedSquare) :
    (Quotient.mk _ (t96J02_cut_raw (t96J02_paste_raw p)) : T96J02SquarePolygonQuotient) =
      Quotient.mk _ p := by
  sorry

/-- The genuine polygon-move bridge: the opposite-edge square presentation
and the frozen adjacent-arc disk presentation have homeomorphic quotient
spaces.  This cannot be induced by a homeomorphism of the two carriers; a
proof needs a cut-and-paste map defined only after passage to the quotient. -/
theorem t96J02_kleinSquarePolygonQuotient_homeomorph_diskPolygon :
    Nonempty (T96J02SquarePolygonQuotient ≃ₜ KleinBottle) := by
  have hedge0 := t96J02_cut_edge_zero_iff
  have hedge2 := t96J02_cut_edge_two_iff
  have hcut := t96J02_cut_continuous t96J02_cut_chart_continuous
  have hpaste := t96J02_paste_continuous t96J02_cut_chartInv_continuous
    (fun z h1 h2 h3 => (hedge2 z).mpr ⟨h1, h2, h3⟩)
  have hcr := t96J02_cut_rel (fun t => (hedge0 _).mp ⟨t, rfl⟩)
    (fun t => (hedge2 _).mp ⟨t, rfl⟩) t96J02_cut_square_corners
  have hpr := t96J02_paste_rel (fun z h1 h2 h3 => (hedge0 z).mpr ⟨h1, h2, h3⟩)
    (fun z h1 h2 h3 => (hedge2 z).mpr ⟨h1, h2, h3⟩) t96J02_cut_disk_vertices
  have hpc := t96J02_paste_cut (fun z h1 h2 h3 => (hedge2 z).mpr ⟨h1, h2, h3⟩)
  let f : T96J02SquarePolygonQuotient → KleinBottle :=
    Quotient.lift (fun p => surfaceQuotient false 2 (t96J02_paste_raw p)) (by
      intro p q h
      induction h with
      | rel p q h => exact hpr p q h
      | refl p => rfl
      | symm p q _ ih => exact ih.symm
      | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  let g : KleinBottle → T96J02SquarePolygonQuotient :=
    Quotient.lift (fun z => (Quotient.mk _ (t96J02_cut_raw z) : T96J02SquarePolygonQuotient)) (by
      intro x y h
      induction h with
      | rel x y h => exact hcr x y h
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  refine ⟨Homeomorph.mk ⟨f, g, ?_, ?_⟩ ?_ ?_⟩
  · rintro ⟨p⟩
    exact t96J02_cut_paste p
  · rintro ⟨x⟩
    exact hpc x
  · exact Continuous.quotient_lift hpaste _
  · exact Continuous.quotient_lift hcut _

end T96J02CutAndPaste

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

/-- If the vertical step is odd, conjugation by its lift inverts the
horizontal generator, and normal forms give another Klein group. -/
theorem t96J02_presented_finiteIndex_odd_classify_aux_action
    (q : ℤ) (hq : Odd q) (x : ZMul) :
    action (Multiplicative.ofAdd q) x = x⁻¹ := by
  obtain ⟨k, rfl⟩ := hq
  change (inversion ^ (2 * k + 1)) x = x⁻¹
  rw [zpow_add_one, zpow_mul]
  have hi : inversion ^ (2 : ℤ) = 1 := by
    ext y
    change inversion (inversion y) = y
    simp [inversion]
  rw [hi, one_zpow]
  rfl

theorem t96J02_presented_finiteIndex_odd_classify_aux_action_symm
    (q : ℤ) (hq : Odd q) (x : ZMul) :
    (action (Multiplicative.ofAdd q)).symm x = x⁻¹ := by
  apply (action (Multiplicative.ofAdd q)).injective
  rw [MulEquiv.apply_symm_apply,
    t96J02_presented_finiteIndex_odd_classify_aux_action q hq]
  simp

theorem t96J02_presented_finiteIndex_odd_classify_aux_right_zpow
    (a b : ZMul) (n : ℤ) :
    Multiplicative.toAdd ((⟨a, b⟩ : Coordinates) ^ n).right =
      n * Multiplicative.toAdd b := by
  have h := congrArg Multiplicative.toAdd
    (map_zpow (SemidirectProduct.rightHom : Coordinates →* ZMul)
      (⟨a, b⟩ : Coordinates) n)
  simpa [mul_comm] using h

theorem t96J02_presented_finiteIndex_odd_classify_aux_inl_zpow
    (a : ZMul) (n : ℤ) :
    Multiplicative.toAdd
        ((SemidirectProduct.inl a : Coordinates) ^ n).left =
      n * Multiplicative.toAdd a := by
  calc
    Multiplicative.toAdd
        ((SemidirectProduct.inl a : Coordinates) ^ n).left =
        Multiplicative.toAdd (a ^ n) := by
          exact congrArg (fun z : Coordinates => Multiplicative.toAdd z.left)
            (map_zpow (SemidirectProduct.inl : ZMul →* Coordinates) a n).symm
    _ = n * Multiplicative.toAdd a := by simp

noncomputable def t96J02_presented_finiteIndex_odd_classify_aux_map
    (p q r : ℤ) (hq : Odd q) :
    T96J02PresentedGroup →* T96J02PresentedGroup :=
  PresentedGroup.toGroup (f := fun i => if i then
      t96J02_presented_coordinate r q else
      t96J02_presented_coordinate p 0) (by
    intro w hw
    change w ∈ ({(FreeGroup.of true)⁻¹ * FreeGroup.of false *
      FreeGroup.of true * FreeGroup.of false} : Set (FreeGroup Bool)) at hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    simp
    apply KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.injective
    apply SemidirectProduct.ext
    · simp [t96J02_presented_coordinate,
        t96J02_presented_finiteIndex_odd_classify_aux_action_symm, hq]
    · simp [t96J02_presented_coordinate])

theorem t96J02_presented_finiteIndex_odd_classify
    (H : Subgroup T96J02PresentedGroup) (p q r : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hodd : Odd q)
    (hgen : H = Subgroup.closure
      ({t96J02_presented_coordinate p 0,
        t96J02_presented_coordinate r q} : Set T96J02PresentedGroup)) :
    Nonempty (H ≃* T96J02PresentedGroup) := by
  let f := t96J02_presented_finiteIndex_odd_classify_aux_map p q r hodd
  have hfA : f generatorA = t96J02_presented_coordinate p 0 := by
    exact PresentedGroup.toGroup.of _
  have hfB : f generatorB = t96J02_presented_coordinate r q := by
    exact PresentedGroup.toGroup.of _
  have hf_inj : Function.Injective f := by
    intro x y hxy
    obtain ⟨⟨xm, xn⟩, hx, _⟩ :=
      KleinPresentedGroupCoordinateNormalForm.uniqueNormalForm x
    obtain ⟨⟨ym, yn⟩, hy, _⟩ :=
      KleinPresentedGroupCoordinateNormalForm.uniqueNormalForm y
    rw [hx, hy] at hxy
    simp only [map_mul, map_zpow] at hxy
    rw [hfA, hfB] at hxy
    have hrgt := congrArg (fun z => Multiplicative.toAdd
      ((SemidirectProduct.rightHom : Coordinates →* ZMul)
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv z))) hxy
    have hn : Multiplicative.toAdd xn = Multiplicative.toAdd yn := by
      simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply,
        map_mul, map_zpow] at hrgt
      simp [t96J02_presented_finiteIndex_odd_classify_aux_right_zpow] at hrgt
      rcases hrgt with h | h
      · exact congrArg Multiplicative.toAdd h
      · omega
    have hn' : xn = yn := Multiplicative.toAdd.injective hn
    subst yn
    have ha : (t96J02_presented_coordinate p 0) ^ Multiplicative.toAdd xm =
        (t96J02_presented_coordinate p 0) ^ Multiplicative.toAdd ym := by
      exact mul_right_cancel hxy
    have hlft := congrArg (fun z => Multiplicative.toAdd
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv z).left) ha
    have hm : Multiplicative.toAdd xm = Multiplicative.toAdd ym := by
      simp only [t96J02_presented_coordinate, MulEquiv.apply_symm_apply,
        map_zpow] at hlft
      change Multiplicative.toAdd
          ((SemidirectProduct.inl (Multiplicative.ofAdd p) : Coordinates) ^
            Multiplicative.toAdd xm).left =
        Multiplicative.toAdd
          ((SemidirectProduct.inl (Multiplicative.ofAdd p) : Coordinates) ^
            Multiplicative.toAdd ym).left at hlft
      rw [t96J02_presented_finiteIndex_odd_classify_aux_inl_zpow,
        t96J02_presented_finiteIndex_odd_classify_aux_inl_zpow] at hlft
      exact mul_right_cancel₀ (ne_of_gt hp) hlft
    have hm' : xm = ym := Multiplicative.toAdd.injective hm
    subst ym
    exact hx.trans hy.symm
  have hrange : MonoidHom.range f = H := by
    apply le_antisymm
    · rw [hgen]
      rintro _ ⟨x, rfl⟩
      have hpre : (⊤ : Subgroup T96J02PresentedGroup) ≤
          (Subgroup.closure
            ({t96J02_presented_coordinate p 0,
              t96J02_presented_coordinate r q} : Set T96J02PresentedGroup)).comap f := by
        rw [← PresentedGroup.closure_range_of]
        apply Subgroup.closure_le _ |>.2
        rintro _ ⟨i, rfl⟩
        cases i
        · exact (show f generatorA ∈ Subgroup.closure
              ({t96J02_presented_coordinate p 0,
                t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) by
            rw [hfA]
            exact Subgroup.subset_closure (by simp))
        · exact (show f generatorB ∈ Subgroup.closure
              ({t96J02_presented_coordinate p 0,
                t96J02_presented_coordinate r q} : Set T96J02PresentedGroup) by
            rw [hfB]
            exact Subgroup.subset_closure (by simp))
      exact hpre trivial
    · rw [hgen]
      apply Subgroup.closure_le _ |>.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [← hfA]
        exact ⟨generatorA, rfl⟩
      · rw [← hfB]
        exact ⟨generatorB, rfl⟩
  let g : T96J02PresentedGroup →* H :=
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

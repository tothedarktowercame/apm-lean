import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceGroupBetti
import ConstructionTargets.KleinBottlePiOne
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.CoveringDegree
import ConstructionTargets.T99J01ComponentSheetBounds
import ConstructionTargets.CoveringPathComponentSurjective
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.PolygonSurfacePiOne

open Set

inductive T95J03ClosedSurface
  | orientable (genus : ℕ)
  | nonorientable (genus : PNat)
  deriving DecidableEq

def t95J03Torus : T95J03ClosedSurface := .orientable 1
def t95J03KleinBottle : T95J03ClosedSurface := .nonorientable 2

open ConstructionTargets.Surfaces

/-- A concrete representative of every classification coordinate.  Genus zero
in the orientable family is the two-sphere, not the zero-edge polygon (a disk).
There is no nonorientable genus-zero constructor. -/
noncomputable def T95J03SurfaceSpace : T95J03ClosedSurface → TopCat
  | .orientable 0 =>
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  | .orientable (g + 1) => TopCat.of (Surface true (g + 1))
  | .nonorientable g => TopCat.of (Surface false g)

def T95J03IsKFoldCover (k : ℕ) (E X : TopCat.{0}) (p : E → X) : Prop :=
  IsCoveringMap p ∧ ∀ x : X, Nat.card {e : E // p e = x} = k

def T95J03SharesKFoldCover (k : ℕ) (F G : T95J03ClosedSurface) : Prop :=
  ∃ (E K : TopCat.{0}) (p : E → T95J03SurfaceSpace F)
      (q : K → T95J03SurfaceSpace G),
    T95J03IsKFoldCover k E (T95J03SurfaceSpace F) p ∧
    T95J03IsKFoldCover k K (T95J03SurfaceSpace G) q ∧
    Nonempty (E ≃ₜ K)


/-! # Blueprint (claude-14, revision 2026-10-16)

The registered statement above is unchanged (byte-identical to `Main.lean`).
Route: π₁ and first rational Betti numbers, no Euler characteristic
(`BLUEPRINT.md`).  Leaves are the `lemma … := by sorry` below; everything else
is a sorry-free assembly. -/

open ConstructionTargets ConstructionTargets.SurfaceGroupBetti ConstructionTargets.CoveringDegree
open ConstructionTargets.T99J01ComponentSheetBounds ConstructionTargets.PolygonSurfacePiOne
open KleinPresentedGroupCoordinateModel

abbrev T95J03Torus := UnitAddCircle × UnitAddCircle

/-! ## Covering-space leaves (generic) -/

/-- **Leaf C1.**  For any covering (total space possibly disconnected), the
image of `π₁(E, e)` has index the number of fibre points in the path component
of `e`.

Route.  Copy `CoveringMonodromyCosets.coveringFiberEquivCosets`: the stabilizer
of `e` under monodromy is the image (proof there does not use connectedness);
the orbit of `e` is `ComponentFiber p e` (a path in `E` from `e` to `e'`
projects to a loop whose monodromy sends `e` to `e'` by uniqueness of lifts;
conversely a monodromy image is the endpoint of a lift, so it is joined to
`e`).  Orbit–stabilizer, `Subgroup.index_eq_card`.  About 60–120 lines. -/
/- Monodromy action of `π₁(X, p e)` on the fibre over `p e` (no
connectedness of `E` needed). -/
@[reducible]
noncomputable def t95J03_componentFiberCard_eq_index_auxAction {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    (e : E) :
    MulAction (FundamentalGroup X (p e)) (p ⁻¹' {p e}) where
  smul γ e' := cov.monodromy γ e'
  one_smul e' := by simpa using congrFun cov.monodromy_refl e'
  mul_smul γ γ' e' := cov.monodromy_trans_apply γ' γ e'

/-- The stabilizer of `e` under monodromy is the image of `π₁(E, e)`. -/
theorem t95J03_componentFiberCard_eq_index_aux_stab {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) (e : E) :
    {γ : FundamentalGroup X (p e) | cov.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩} =
      (coveringInducedFundamentalGroupMap cov e).range := by
  ext γ
  constructor
  · intro hγ
    change cov.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩ at hγ
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    let lift := cov.liftPath γ e (by simp)
    have hend : lift 1 = e := by
      simpa [IsCoveringMap.monodromy, lift] using congrArg Subtype.val hγ
    let δ : Path e e := ⟨lift, cov.liftPath_zero _ _ _, hend⟩
    refine ⟨FundamentalGroup.fromPath (.mk δ), ?_⟩
    change FundamentalGroup.map ⟨p, cov.continuous⟩ e
      (FundamentalGroup.fromPath (.mk δ)) = _
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    congr 1
    ext t
    exact congrFun (cov.liftPath_lifts γ e (by simp)) t
  · rintro ⟨δ, rfl⟩
    change cov.monodromy (FundamentalGroup.map ⟨p, cov.continuous⟩ e δ) ⟨e, rfl⟩ = ⟨e, rfl⟩
    exact cov.monodromy_map δ

/-- The monodromy orbit of `e` is exactly the fibre of the path component
of `e`. -/
theorem t95J03_componentFiberCard_eq_index_aux_orbit {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) (e : E) :
    {x : p ⁻¹' {p e} | ∃ γ : FundamentalGroup X (p e), cov.monodromy γ ⟨e, rfl⟩ = x} =
      {x : p ⁻¹' {p e} | Joined e (x : E)} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨γ, rfl⟩
    induction γ using Path.Homotopic.Quotient.ind with
    | mk γ =>
      exact ⟨⟨cov.liftPath γ e (by simp), cov.liftPath_zero γ e (by simp), rfl⟩⟩
  · intro hj
    have he' : p ↑(x : E) = p e := x.2
    let δ : Path e ↑(x : E) := hj.somePath
    let δp : Path.Homotopic.Quotient (p e) (p e) :=
      ((Path.Homotopic.Quotient.mk δ).map ⟨p, cov.continuous⟩).cast
        rfl he'.symm
    exact ⟨FundamentalGroup.fromPath δp, by
      change cov.monodromy δp ⟨e, rfl⟩ = x
      apply Subtype.ext
      simpa [δp, IsCoveringMap.monodromy, Path.Homotopic.Quotient.cast] using
        congrArg Subtype.val (cov.monodromy_map (.mk δ))⟩

lemma t95J03_componentFiberCard_eq_index {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) (e : E) :
    Nat.card (ComponentFiber p e) = (coveringInducedFundamentalGroupMap cov e).range.index := by
  letI := t95J03_componentFiberCard_eq_index_auxAction cov e
  have hstab : MulAction.stabilizer (FundamentalGroup X (p e))
      (⟨e, rfl⟩ : p ⁻¹' {p e}) = (coveringInducedFundamentalGroupMap cov e).range := by
    ext γ
    simp only [MulAction.mem_stabilizer_iff]
    exact (Set.ext_iff.mp (t95J03_componentFiberCard_eq_index_aux_stab cov e)) γ
  have horbit : MulAction.orbit (FundamentalGroup X (p e))
      (⟨e, rfl⟩ : p ⁻¹' {p e}) = {x : p ⁻¹' {p e} | Joined e (x : E)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact (Set.ext_iff.mp (t95J03_componentFiberCard_eq_index_aux_orbit cov e)) x
  have orbitEquiv :
      MulAction.orbit (FundamentalGroup X (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) ≃
        FundamentalGroup X (p e) ⧸ (coveringInducedFundamentalGroupMap cov e).range :=
    (MulAction.orbitEquivQuotientStabilizer _ _).trans (Subgroup.quotientEquivOfEq hstab)
  have e2 : {x : p ⁻¹' {p e} // Joined e (x : E)} ≃
      {x : E // x ∈ p ⁻¹' {p e} ∧ Joined e x} :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr
    (orbitEquiv.symm.trans ((Equiv.setCongr horbit).trans e2)).symm

/-- **Leaf C2.**  The number of sheets of a path component does not depend on
the chosen point of the component.

Route.  A path `γ : e ⟶ e'` projects to `δ = p ∘ γ : p e ⟶ p e'`; lifting `δ`
from every point of the fibre over `p e` (`IsCoveringMap.liftPath`) gives a
bijection of fibres (inverse: lift `δ.symm`), and the lift from `x` joins `x`
to its image, so it restricts to `ComponentFiber p e ≃ ComponentFiber p e'`.
About 60–120 lines. -/
-- Endpoint of the lift of `γ.map p` starting at `x` (with `p x = p e`).
noncomputable def t95J03_componentFiberCard_joined_aux_end {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') (x : E) (hx : p x = p e) : E :=
  cov.liftPath (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source]) 1

lemma t95J03_componentFiberCard_joined_aux_end_mem {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') {x : E} (hx : p x = p e) :
    p (t95J03_componentFiberCard_joined_aux_end cov γ x hx) = p e' := by
  have h := cov.liftPath_lifts (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source])
  have h1 := congrFun h 1
  simpa using h1

/-- The lift of `γ.map p` starting at `x`, as a path. -/
noncomputable def t95J03_componentFiberCard_joined_aux_joinPath {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') {x : E} (hx : p x = p e) :
    Path x (t95J03_componentFiberCard_joined_aux_end cov γ x hx) where
  toFun t := cov.liftPath (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source]) t
  continuous_toFun := (cov.liftPath (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source])).continuous
  source' := cov.liftPath_zero (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source])
  target' := rfl

/-- Lifting there and back along a path returns the starting point. -/
lemma t95J03_componentFiberCard_joined_aux_cancel {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') {x : E} (hx : p x = p e) :
    t95J03_componentFiberCard_joined_aux_end cov γ.symm
      (t95J03_componentFiberCard_joined_aux_end cov γ x hx)
      (t95J03_componentFiberCard_joined_aux_end_mem cov γ hx) = x := by
  have hc : Continuous p := cov.continuous
  have hL0 : cov.liftPath (γ.map hc).toContinuousMap x (by simp [hx, Path.source]) 0 = x :=
    cov.liftPath_zero (γ.map hc).toContinuousMap x (by simp [hx, Path.source])
  have hlifts : ∀ t, p (cov.liftPath (γ.map hc).toContinuousMap x
      (by simp [hx, Path.source]) t) = p (γ t) := by
    intro t
    have h := cov.liftPath_lifts (γ.map hc).toContinuousMap x (by simp [hx, Path.source])
    exact congrFun h t
  set ρ : Path x (t95J03_componentFiberCard_joined_aux_end cov γ x hx) :=
    t95J03_componentFiberCard_joined_aux_joinPath cov γ hx with hρ
  -- the reversed lift lifts the reversed base path, pointwise
  have hsymm : ∀ t : unitInterval,
      p (t95J03_componentFiberCard_joined_aux_joinPath cov γ hx (unitInterval.symm t))
        = p (γ.symm t) := by
    intro t
    have h := hlifts (unitInterval.symm t)
    rw [Path.symm_apply]
    exact h
  have hcomp : p ∘ ρ.symm.toContinuousMap = (γ.symm.map hc).toContinuousMap := by
    funext t
    exact hsymm t
  have hstart : ρ.symm.toContinuousMap 0 =
      t95J03_componentFiberCard_joined_aux_end cov γ x hx := by
    simp
  -- uniqueness of path lifts
  have hEq : ρ.symm.toContinuousMap = cov.liftPath (γ.symm.map hc).toContinuousMap
      (t95J03_componentFiberCard_joined_aux_end cov γ x hx)
      (by simp [t95J03_componentFiberCard_joined_aux_end_mem cov γ hx, Path.source]) :=
    (cov.eq_liftPath_iff' _).mpr ⟨hcomp, hstart⟩
  have h1 := DFunLike.congr_fun hEq 1
  have h2 : ρ.symm 1 = x := by
    show ρ (unitInterval.symm 1) = x
    rw [unitInterval.symm_one]
    exact hL0
  simp only [t95J03_componentFiberCard_joined_aux_end]
  exact h1.symm.trans h2

/-- The bijection of component fibres along a path, by path lifting. -/
noncomputable def t95J03_componentFiberCard_joined_aux_equiv {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') : ComponentFiber p e ≃ ComponentFiber p e' where
  toFun x := ⟨t95J03_componentFiberCard_joined_aux_end cov γ x.1 x.2.1,
    t95J03_componentFiberCard_joined_aux_end_mem cov γ x.2.1,
    ⟨(γ.symm.trans x.2.2.some).trans
      (t95J03_componentFiberCard_joined_aux_joinPath cov γ x.2.1)⟩⟩
  invFun y := ⟨t95J03_componentFiberCard_joined_aux_end cov γ.symm y.1 y.2.1,
    t95J03_componentFiberCard_joined_aux_end_mem cov γ.symm y.2.1,
    ⟨(γ.trans y.2.2.some).trans
      (t95J03_componentFiberCard_joined_aux_joinPath cov γ.symm y.2.1)⟩⟩
  left_inv x := Subtype.ext
    (t95J03_componentFiberCard_joined_aux_cancel cov γ x.2.1)
  right_inv y := Subtype.ext (by
    simpa [Path.symm_symm] using
      t95J03_componentFiberCard_joined_aux_cancel cov γ.symm y.2.1)

lemma t95J03_componentFiberCard_joined {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) {e e' : E}
    (h : Joined e e') :
    Nat.card (ComponentFiber p e) = Nat.card (ComponentFiber p e') := by
  exact Nat.card_congr (t95J03_componentFiberCard_joined_aux_equiv cov h.some)

/-- **Leaf C3.**  Two `k`-sheeted covers on one total space cannot have strictly
more sheets for the second on every component.

Route.  Fix `x : X`, `y : Y`, fibres `A = p⁻¹ x`, `B = q⁻¹ y` (`k` points each).
For `a ∈ A`, its class in `A` under `Joined` is `ComponentFiber p a`; the
component of `a` meets `B` (`CoveringPathComponentSurjective`) in
`ComponentFiber q b` for some `b`, whose card equals that of
`ComponentFiber q a` (`t95J03_componentFiberCard_joined`).  Summing over the
classes of `A`: `k = Σ |A ∩ C| < Σ |B ∩ C| ≤ |B| = k`.  About 100–200 lines. -/
-- Joined-invariance of the component-fibre cardinality (C2 route)

noncomputable def t95J03_sheets_lt_absurd_aux_end {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') (x : E) (hx : p x = p e) : E :=
  cov.liftPath (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source]) 1

lemma t95J03_sheets_lt_absurd_aux_end_mem {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') {x : E} (hx : p x = p e) :
    p (t95J03_sheets_lt_absurd_aux_end cov γ x hx) = p e' := by
  have h := cov.liftPath_lifts (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source])
  have h1 := congrFun h 1
  simpa using h1

/-- The lift of `γ.map p` starting at `x`, as a path. -/
noncomputable def t95J03_sheets_lt_absurd_aux_joinPath {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') {x : E} (hx : p x = p e) :
    Path x (t95J03_sheets_lt_absurd_aux_end cov γ x hx) where
  toFun t := cov.liftPath (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source]) t
  continuous_toFun := (cov.liftPath (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source])).continuous
  source' := cov.liftPath_zero (γ.map cov.continuous).toContinuousMap x
    (by simp [hx, Path.source])
  target' := rfl

/-- Lifting there and back along a path returns the starting point. -/
lemma t95J03_sheets_lt_absurd_aux_cancel {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') {x : E} (hx : p x = p e) :
    t95J03_sheets_lt_absurd_aux_end cov γ.symm
      (t95J03_sheets_lt_absurd_aux_end cov γ x hx)
      (t95J03_sheets_lt_absurd_aux_end_mem cov γ hx) = x := by
  have hc : Continuous p := cov.continuous
  have hL0 : cov.liftPath (γ.map hc).toContinuousMap x (by simp [hx, Path.source]) 0 = x :=
    cov.liftPath_zero (γ.map hc).toContinuousMap x (by simp [hx, Path.source])
  have hlifts : ∀ t, p (cov.liftPath (γ.map hc).toContinuousMap x
      (by simp [hx, Path.source]) t) = p (γ t) := by
    intro t
    have h := cov.liftPath_lifts (γ.map hc).toContinuousMap x (by simp [hx, Path.source])
    exact congrFun h t
  set ρ : Path x (t95J03_sheets_lt_absurd_aux_end cov γ x hx) :=
    t95J03_sheets_lt_absurd_aux_joinPath cov γ hx with hρ
  have hsymm : ∀ t : unitInterval,
      p (t95J03_sheets_lt_absurd_aux_joinPath cov γ hx (unitInterval.symm t))
        = p (γ.symm t) := by
    intro t
    have h := hlifts (unitInterval.symm t)
    rw [Path.symm_apply]
    exact h
  have hcomp : p ∘ ρ.symm.toContinuousMap = (γ.symm.map hc).toContinuousMap := by
    funext t
    exact hsymm t
  have hstart : ρ.symm.toContinuousMap 0 =
      t95J03_sheets_lt_absurd_aux_end cov γ x hx := by
    simp
  have hEq : ρ.symm.toContinuousMap = cov.liftPath (γ.symm.map hc).toContinuousMap
      (t95J03_sheets_lt_absurd_aux_end cov γ x hx)
      (by simp [t95J03_sheets_lt_absurd_aux_end_mem cov γ hx, Path.source]) :=
    (cov.eq_liftPath_iff' _).mpr ⟨hcomp, hstart⟩
  have h1 := DFunLike.congr_fun hEq 1
  have h2 : ρ.symm 1 = x := by
    show ρ (unitInterval.symm 1) = x
    rw [unitInterval.symm_one]
    exact hL0
  simp only [t95J03_sheets_lt_absurd_aux_end]
  exact h1.symm.trans h2

/-- The bijection of component fibres along a path, by path lifting. -/
noncomputable def t95J03_sheets_lt_absurd_aux_liftEquiv {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p)
    {e e' : E} (γ : Path e e') : ComponentFiber p e ≃ ComponentFiber p e' where
  toFun x := ⟨t95J03_sheets_lt_absurd_aux_end cov γ x.1 x.2.1,
    t95J03_sheets_lt_absurd_aux_end_mem cov γ x.2.1,
    ⟨(γ.symm.trans x.2.2.some).trans
      (t95J03_sheets_lt_absurd_aux_joinPath cov γ x.2.1)⟩⟩
  invFun y := ⟨t95J03_sheets_lt_absurd_aux_end cov γ.symm y.1 y.2.1,
    t95J03_sheets_lt_absurd_aux_end_mem cov γ.symm y.2.1,
    ⟨(γ.trans y.2.2.some).trans
      (t95J03_sheets_lt_absurd_aux_joinPath cov γ.symm y.2.1)⟩⟩
  left_inv x := Subtype.ext
    (t95J03_sheets_lt_absurd_aux_cancel cov γ x.2.1)
  right_inv y := Subtype.ext (by
    simpa [Path.symm_symm] using
      t95J03_sheets_lt_absurd_aux_cancel cov γ.symm y.2.1)

lemma t95J03_sheets_lt_absurd_aux_card {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) {e e' : E}
    (h : Joined e e') :
    Nat.card (ComponentFiber p e) = Nat.card (ComponentFiber p e') :=
  Nat.card_congr (t95J03_sheets_lt_absurd_aux_liftEquiv cov h.some)

-- Fibre setoids by `Joined` (C4 route)

def t95J03_sheets_lt_absurd_aux_setoid {E Z : Type*} [TopologicalSpace E]
    [TopologicalSpace Z] (r : E → Z) (z : Z) : Setoid {e : E // r e = z} where
  r a b := Joined b.val a.val
  iseqv := ⟨fun a => Joined.refl a.val, fun h => Joined.symm h,
    fun h1 h2 => Joined.trans h2 h1⟩

lemma t95J03_sheets_lt_absurd_aux_mk_eq {E Z : Type*} [TopologicalSpace E]
    [TopologicalSpace Z] (r : E → Z) (z : Z) (a b : {e : E // r e = z}) :
    Quotient.mk (t95J03_sheets_lt_absurd_aux_setoid r z) a
        = Quotient.mk (t95J03_sheets_lt_absurd_aux_setoid r z) b ↔
      Joined (b : E) (a : E) := by
  constructor
  · intro h; exact Quotient.eq.1 h
  · intro h; exact Quotient.sound h

/-- A fibre-class of the setoid is a component fibre (as an equiv, for cards). -/
def t95J03_sheets_lt_absurd_aux_classEquiv {E Z : Type*} [TopologicalSpace E]
    [TopologicalSpace Z] (r : E → Z) (z : Z) (b : {e : E // r e = z}) :
    {x : {e : E // r e = z} // Quotient.mk (t95J03_sheets_lt_absurd_aux_setoid r z) x
        = Quotient.mk (t95J03_sheets_lt_absurd_aux_setoid r z) b} ≃
      ComponentFiber r (b : E) where
  toFun x := by
    refine ⟨x.1.1, ?_, ?_⟩
    · rw [x.1.2]; exact b.2.symm
    · exact (t95J03_sheets_lt_absurd_aux_mk_eq r z x.1 b).1 x.2
  invFun w := by
    refine ⟨⟨w.1, ?_⟩, ?_⟩
    · rw [w.2.1]; exact b.2
    · exact (t95J03_sheets_lt_absurd_aux_mk_eq r z _ b).2 w.2.2
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

lemma t95J03_sheets_lt_absurd_aux_filter_card {α : Type*} [Fintype α] (pr : α → Prop)
    [DecidablePred pr] :
    Finset.card (Finset.filter pr (Finset.univ : Finset α))
      = Nat.card {a : α // pr a} := by
  classical
  have e : {a : α // pr a} ≃
      {x : α // x ∈ (Finset.univ.filter pr : Finset α)} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [Finset.mem_filter])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

-- The main counting argument

lemma t95J03_sheets_lt_absurd {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y]
    {p : E → X} {q : E → Y} {k : ℕ} (hp : IsKSheetedCover p k) (hq : IsKSheetedCover q k)
    (hk : 0 < k)
    (hlt : ∀ e, Nat.card (ComponentFiber p e) < Nat.card (ComponentFiber q e)) : False := by
  classical
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  haveI : Finite {e : E // p e = x₀} := hp.finite_fiber x₀
  haveI : Fintype {e : E // p e = x₀} := Fintype.ofFinite _
  have hAcard : Fintype.card {e : E // p e = x₀} = k := by
    have h := hp.card_fiber x₀
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hcard0 : 0 < (Finset.univ : Finset {e : E // p e = x₀}).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨e₀, he₀⟩ : Nonempty {e : E // p e = x₀} :=
    Fintype.card_pos_iff.mp (by rw [← Finset.card_univ]; omega)
  set y₀ := q e₀ with hy₀
  haveI : Finite {e : E // q e = y₀} := hq.finite_fiber y₀
  haveI : Fintype {e : E // q e = y₀} := Fintype.ofFinite _
  have hBcard : Fintype.card {e : E // q e = y₀} = k := by
    have h := hq.card_fiber y₀
    rw [Nat.card_eq_fintype_card] at h
    exact h
  let SA := t95J03_sheets_lt_absurd_aux_setoid p x₀
  let SB := t95J03_sheets_lt_absurd_aux_setoid q y₀
  haveI := Classical.decEq (Quotient SA)
  haveI := Classical.decEq (Quotient SB)
  set f : {e : E // p e = x₀} → Quotient SA := fun a => Quotient.mk SA a with hf
  set g : {e : E // q e = y₀} → Quotient SB := fun b => Quotient.mk SB b with hg
  have bex : ∀ a : {e : E // p e = x₀}, ∃ b : {e : E // q e = y₀},
      Joined (a : E) (b : E) := by
    intro a
    obtain ⟨w, hw⟩ := CoveringPathComponentSurjective.componentProjection_surjective
      hq.isCoveringMap (a : E) y₀
    exact ⟨⟨(w : E), hw⟩, w.2⟩
  choose ψ hψ using bex
  set ψc : {e : E // p e = x₀} → Quotient SB := fun a => Quotient.mk SB (ψ a) with hψc
  have hψconst : ∀ a a' : {e : E // p e = x₀}, f a = f a' → ψc a = ψc a' := by
    intro a a' h
    have hA : Joined (a' : E) (a : E) := (t95J03_sheets_lt_absurd_aux_mk_eq p x₀ a a').1 h
    have hchain : Joined (↑(ψ a') : E) (↑(ψ a) : E) :=
      ((Joined.symm (hψ a')).trans hA).trans (hψ a)
    exact (t95J03_sheets_lt_absurd_aux_mk_eq q y₀ (ψ a) (ψ a')).2 hchain
  set ι : Quotient SA → Quotient SB := fun c => ψc c.out with hι
  have hιinj : ∀ c₁ c₂ : Quotient SA, ι c₁ = ι c₂ → c₁ = c₂ := by
    intro c₁ c₂ h
    have hqj : Joined (ψ c₂.out : E) (ψ c₁.out : E) :=
      (t95J03_sheets_lt_absurd_aux_mk_eq q y₀ (ψ c₁.out) (ψ c₂.out)).1 h
    have hchain : Joined (c₁.out : E) (c₂.out : E) :=
      ((hψ c₁.out).trans (Joined.symm hqj)).trans (Joined.symm (hψ c₂.out))
    have hmk : (Quotient.mk SA c₁.out : Quotient SA) = Quotient.mk SA c₂.out :=
      Quotient.sound (Joined.symm hchain)
    rw [Quotient.out_eq, Quotient.out_eq] at hmk
    exact hmk
  set univA := (Finset.univ : Finset {e : E // p e = x₀}) with hunivA
  set univB := (Finset.univ : Finset {e : E // q e = y₀}) with hunivB
  have htermA : ∀ a : {e : E // p e = x₀},
      (univA.filter (fun x => f x = f a)).card
        = Nat.card (ComponentFiber p (a : E)) := by
    intro a
    rw [t95J03_sheets_lt_absurd_aux_filter_card]
    exact Nat.card_congr (t95J03_sheets_lt_absurd_aux_classEquiv p x₀ a)
  have htermB : ∀ a : {e : E // p e = x₀},
      (univB.filter (fun b => g b = ι (f a))).card
        = Nat.card (ComponentFiber q (a : E)) := by
    intro a
    have hic : ι (f a) = ψc a :=
      (show ι (f a) = ψc (Quotient.out (f a)) from rfl).trans
        (hψconst _ _ (Quotient.out_eq (f a)))
    have hfilter : (univB.filter (fun b => g b = ι (f a))).card
        = (univB.filter (fun b => g b = ψc a)).card := by
      simp only [hic]
    rw [hfilter, t95J03_sheets_lt_absurd_aux_filter_card]
    have hcard := Nat.card_congr (t95J03_sheets_lt_absurd_aux_classEquiv q y₀ (ψ a))
    rw [← t95J03_sheets_lt_absurd_aux_card hq.isCoveringMap (hψ a)] at hcard
    exact hcard
  have hstrict : ∀ c ∈ univA.image f,
      (univA.filter (fun a => f a = c)).card
        < (univB.filter (fun b => g b = ι c)).card := by
    intro c hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hc
    rw [htermA a, htermB a]
    exact hlt _
  have hsplitA : univA.card
      = ∑ c ∈ univA.image f, (univA.filter (fun a => f a = c)).card :=
    Finset.card_eq_sum_card_image f univA
  have hsumA : ∑ c ∈ univA.image f, (univA.filter (fun a => f a = c)).card = k := by
    rw [← hsplitA, Finset.card_univ]
    exact hAcard
  have hne : ∃ c ∈ univA.image f,
      (univA.filter (fun a => f a = c)).card
        < (univB.filter (fun b => g b = ι c)).card := by
    refine ⟨f ⟨e₀, he₀⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    obtain ⟨a, _, hfa⟩ := Finset.mem_image.1
      (Finset.mem_image_of_mem f (Finset.mem_univ ⟨e₀, he₀⟩))
    rw [← hfa, htermA a, htermB a]
    exact hlt _
  have h1 : k < ∑ c ∈ univA.image f, (univB.filter (fun b => g b = ι c)).card := by
    rw [← hsumA]
    exact Finset.sum_lt_sum (fun c hc => (hstrict c hc).le) hne
  have hinj : ∀ c ∈ univA.image f, ∀ c' ∈ univA.image f, ι c = ι c' → c = c' :=
    fun c _ c' _ h => hιinj c c' h
  have hreindex : ∑ c ∈ univA.image f, (univB.filter (fun b => g b = ι c)).card
      = ∑ d ∈ (univA.image f).image ι, (univB.filter (fun b => g b = d)).card := by
    rw [Finset.sum_image hinj]
  have hsub : (univA.image f).image ι ⊆ univB.image g := by
    intro d hd
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hd
    refine Finset.mem_image.2 ⟨ψ c.out, Finset.mem_univ _, ?_⟩
    rfl
  have h2 : ∑ d ∈ (univA.image f).image ι, (univB.filter (fun b => g b = d)).card
      ≤ ∑ d ∈ univB.image g, (univB.filter (fun b => g b = d)).card :=
    Finset.sum_le_sum_of_subset hsub
  have hsplitB : univB.card
      = ∑ d ∈ univB.image g, (univB.filter (fun b => g b = d)).card :=
    Finset.card_eq_sum_card_image g univB
  have h3 : ∑ d ∈ univB.image g, (univB.filter (fun b => g b = d)).card = k := by
    rw [← hsplitB, Finset.card_univ]
    exact hBcard
  have h4 := hreindex.trans_le h2
  omega

/-- **Leaf C4.**  If every component has an even number of sheets, so does the
cover.

Route.  Partition the fibre over a point `y` by `Joined` (an equivalence
relation); the class of `b` is `ComponentFiber q b` (same base point `q b = y`).
`Finset.card_eq_sum_card_fiberwise` / `Setoid.IsPartition`; a sum of evens is
even.  About 50–100 lines. -/
-- Setoid on the fibre over y by `Joined`.  The relation argument is reversed
-- (`r a b := Joined b a`) so that `Quotient.eq` unfolds `mk x = mk b` into
-- `Joined b x`, exactly the second component of `ComponentFiber q b`.
def t95J03_even_sheets_aux_setoid {E Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] (q : E → Y) (y : Y) : Setoid {e : E // q e = y} where
  r a b := Joined b.val a.val
  iseqv := ⟨fun a => Joined.refl a.val, fun h => Joined.symm h,
    fun h1 h2 => Joined.trans h2 h1⟩

-- mk x = mk b unfolds to `Joined b x` (the reversed relation pays off here).
lemma t95J03_even_sheets_aux_mk_eq {E Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] (q : E → Y) (y : Y) (a b : {e : E // q e = y}) :
    Quotient.mk (t95J03_even_sheets_aux_setoid q y) a
        = Quotient.mk (t95J03_even_sheets_aux_setoid q y) b ↔
      Joined (b : E) (a : E) := by
  constructor
  · intro h; exact Quotient.eq.1 h
  · intro h; exact Quotient.sound h

-- A fibre-class of the setoid is a component fibre (as an equiv, for cards).
def t95J03_even_sheets_aux_equiv {E Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] (q : E → Y) (y : Y) (b : {e : E // q e = y}) :
    {x : {e : E // q e = y} // Quotient.mk (t95J03_even_sheets_aux_setoid q y) x
        = Quotient.mk (t95J03_even_sheets_aux_setoid q y) b} ≃
      ComponentFiber q (b : E) where
  toFun x := by
    refine ⟨x.1.1, ?_, ?_⟩
    · rw [x.1.2]; exact b.2.symm
    · exact (t95J03_even_sheets_aux_mk_eq q y x.1 b).1 x.2
  invFun w := by
    refine ⟨⟨w.1, ?_⟩, ?_⟩
    · rw [w.2.1]; exact b.2
    · exact (t95J03_even_sheets_aux_mk_eq q y _ b).2 w.2.2
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

-- Filter card equals the subtype card (instance-chained via `card_coe`).
lemma t95J03_even_sheets_aux_filter_card {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    Finset.card (Finset.filter p (Finset.univ : Finset α))
      = Nat.card {a : α // p a} := by
  classical
  have e : {a : α // p a} ≃
      {x : α // x ∈ (Finset.univ.filter p : Finset α)} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [Finset.mem_filter])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

-- Each class of the partition has an even number of elements.
lemma t95J03_even_sheets_aux_class_even {E Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] {q : E → Y} {y : Y} [Fintype {e : E // q e = y}]
    (heven : ∀ e, Even (Nat.card (ComponentFiber q e))) (b : {e : E // q e = y}) :
    Even (Nat.card {a : {e : E // q e = y} // Quotient.mk
      (t95J03_even_sheets_aux_setoid q y) a
        = Quotient.mk (t95J03_even_sheets_aux_setoid q y) b}) := by
  rw [Nat.card_congr (t95J03_even_sheets_aux_equiv q y b)]
  exact heven _

lemma t95J03_even_sheets {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [Nonempty Y] {q : E → Y} {k : ℕ} (hq : IsKSheetedCover q k)
    (heven : ∀ e, Even (Nat.card (ComponentFiber q e))) : Even k := by
  classical
  obtain ⟨y⟩ := ‹Nonempty Y›
  haveI : Finite {e : E // q e = y} := hq.finite_fiber y
  haveI : Fintype {e : E // q e = y} := Fintype.ofFinite _
  haveI := Classical.decEq (Quotient (t95J03_even_sheets_aux_setoid q y))
  set f : {e : E // q e = y} → Quotient (t95J03_even_sheets_aux_setoid q y) :=
    fun a => Quotient.mk (t95J03_even_sheets_aux_setoid q y) a with hf
  have hsplit : (Finset.univ : Finset {e : E // q e = y}).card
      = ∑ c ∈ Finset.image f Finset.univ,
        Finset.card (Finset.filter (fun a => f a = c) Finset.univ) :=
    Finset.card_eq_sum_card_image f Finset.univ
  have heach : ∀ c ∈ Finset.image f Finset.univ,
      Even (Finset.card (Finset.filter (fun a => f a = c) Finset.univ)) := by
    intro c hc
    obtain ⟨b, rfl⟩ := Quotient.exists_rep c
    simp only [hf]
    rw [t95J03_even_sheets_aux_filter_card]
    exact t95J03_even_sheets_aux_class_even heven b
  rw [← hq.card_fiber y, Nat.card_eq_fintype_card]
  show Even (Finset.univ.card)
  rw [hsplit]
  exact even_iff_two_dvd.2
    (Finset.dvd_sum fun c hc => even_iff_two_dvd.1 (heach c hc))

/-- **Leaf C5.**  Precomposing with a homeomorphism keeps a `k`-sheeted cover.
Route: `IsCoveringMap.comp_homeomorph`-style (or local trivializations
pulled back); fibres `φ⁻¹` biject.  About 20–50 lines. -/
lemma t95J03_isKSheeted_comp_homeomorph {E E' X : Type*} [TopologicalSpace E]
    [TopologicalSpace E'] [TopologicalSpace X] {q : E' → X} {k : ℕ}
    (hq : IsKSheetedCover q k) (φ : E ≃ₜ E') : IsKSheetedCover (q ∘ φ) k := by
  refine ⟨hq.isCoveringMap.comp_homeomorph φ, fun x => ?_, fun x => ?_⟩
  · have h : {e : E' // q e = x} ≃ {e : E // (q ∘ φ) e = x} :=
      ⟨fun e => ⟨φ.symm e, by simpa [Function.comp] using e.2⟩,
       fun e => ⟨φ e, by simpa [Function.comp] using e.2⟩,
       fun e => by simp, fun e => by simp⟩
    exact @Finite.of_equiv _ _ (hq.finite_fiber x) h
  · have h : {e : E' // q e = x} ≃ {e : E // (q ∘ φ) e = x} :=
      ⟨fun e => ⟨φ.symm e, by simpa [Function.comp] using e.2⟩,
       fun e => ⟨φ e, by simpa [Function.comp] using e.2⟩,
       fun e => by simp, fun e => by simp⟩
    rw [← Nat.card_congr h]
    exact hq.card_fiber x

/-- **Leaf C6.**  Postcomposing with a homeomorphism keeps a `k`-sheeted cover.
About 20–50 lines. -/
lemma t95J03_homeomorph_comp_isKSheeted {E X Y : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace Y] {p : E → X} {k : ℕ}
    (hp : IsKSheetedCover p k) (ψ : X ≃ₜ Y) : IsKSheetedCover (ψ ∘ p) k := by
  constructor
  · exact hp.isCoveringMap.homeomorph_comp ψ
  · intro y
    have hfin : Finite {e : E // p e = ψ.symm y} := hp.finite_fiber _
    have hequiv : {e : E // (ψ ∘ p) e = y} ≃ {e : E // p e = ψ.symm y} :=
      { toFun := fun e => ⟨e.1, by
          simpa using congrArg (⇑ψ.symm) e.property⟩
        invFun := fun e => ⟨e.1, by
          show ψ (p e) = y
          rw [e.property, ψ.apply_symm_apply]⟩
        left_inv := by intro e; simp
        right_inv := by intro e; simp }
    exact @Finite.of_equiv _ _ hfin hequiv.symm
  intro y
  have hfin : Finite {e : E // p e = ψ.symm y} := hp.finite_fiber _
  have hequiv : {e : E // (ψ ∘ p) e = y} ≃ {e : E // p e = ψ.symm y} :=
    { toFun := fun e => ⟨e.1, by
        simpa using congrArg (⇑ψ.symm) e.property⟩
      invFun := fun e => ⟨e.1, by
        show ψ (p e) = y
        rw [e.property, ψ.apply_symm_apply]⟩
      left_inv := by intro e; simp
      right_inv := by intro e; simp }
  rw [Nat.card_congr hequiv, hp.card_fiber]

/-- **Leaf C7.**  `m` disjoint copies of a `d`-sheeted cover form a
`(d * m)`-sheeted cover.  Route: covering by
`ProductEvenlyCoveredTrivialization.isCoveringMap_productMap`-style argument
or directly (evenly covered sets pull back, fibre `≃ fibre × Fin m`).
About 40–90 lines. -/
lemma t95J03_isKSheeted_prod_fin {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} {d : ℕ} (hp : IsKSheetedCover p d) (m : ℕ) :
    IsKSheetedCover (fun x : E × Fin m => p x.1) (d * m) := by
  have equiv : ∀ b : X, {e : E × Fin m // p e.1 = b} ≃ {e : E // p e = b} × Fin m :=
    fun b =>
      { toFun e := ⟨⟨e.1.1, e.2⟩, e.1.2⟩
        invFun z := ⟨(z.1, z.2), z.1.2⟩
        left_inv := by intro e; simp
        right_inv := by intro z; simp }
  constructor
  · intro x
    obtain ⟨hfib, U, hxU, hU, hfU, H, hH⟩ := hp.isCoveringMap x
    haveI := hfib
    refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := ↥(p ⁻¹' {x}) × Fin m)
      ⟨inferInstance, U, hxU, hU, hfU.preimage continuous_fst, ?_, ?_⟩
    · let H' : ((fun x : E × Fin m => p x.1) ⁻¹' U) ≃ₜ U × (↥(p ⁻¹' {x}) × Fin m) :=
        { toFun y := ⟨(H ⟨y.1.1, y.2⟩).1, ((H ⟨y.1.1, y.2⟩).2, y.1.2)⟩
          invFun z := ⟨(H.symm ⟨z.1, z.2.1⟩, z.2.2), (H.symm ⟨z.1, z.2.1⟩).2⟩
          left_inv := by intro z; ext <;> simp
          right_inv := by intro z; ext <;> simp
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      exact H'
    · intro y; simp [hH]
  · intro b
    haveI : Finite {e : E // p e = b} := hp.finite_fiber b
    exact Finite.of_equiv _ (equiv b).symm
  · intro b
    rw [Nat.card_congr (equiv b), Nat.card_prod, Nat.card_fin, hp.card_fiber b]

/-- **Leaf C8.**  The identity is a one-sheeted cover.  About 10–30 lines. -/
lemma t95J03_id_isKSheeted (X : Type*) [TopologicalSpace X] :
    IsKSheetedCover (id : X → X) 1 := by
  constructor
  · intro x
    letI : Subsingleton ((id : X → X) ⁻¹' {x}) :=
      ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    refine ⟨inferInstance, Set.univ, Set.mem_univ x, isOpen_univ, isOpen_univ, ?_, ?_⟩
    · exact
        { toFun := fun z ↦ (⟨z.1, Set.mem_univ _⟩, ⟨x, rfl⟩)
          invFun := fun z ↦ ⟨z.1.1, Set.mem_univ _⟩
          left_inv := fun _ ↦ rfl
          right_inv := by
            intro z
            apply Prod.ext
            · rfl
            · exact Subsingleton.elim _ _
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
    · intro z
      rfl
  · intro x
    letI : Subsingleton {e : X // id e = x} :=
      ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    exact Finite.of_subsingleton
  · intro x
    letI : Subsingleton {e : X // id e = x} :=
      ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    letI : Nonempty {e : X // id e = x} := ⟨⟨x, rfl⟩⟩
    exact Nat.card_unique

/-! ## Surfaces: models, covers, groups -/

/-- **S1 (proved; ported from the t98A01 blueprint 2026-10-17).**  The standard orientable pairing data of genus `g` has `2g`
edge orbits (same leaf as `t98A01_orientable_data_card`).

Route.  Mirror of `SurfaceGroupBetti.standard_nonorientable_data` (card part)
with `orientableOrbitLabel g : Fin (4g) → Fin g × Bool`
(`orientableOrbitLabel_pair`).  About 40–100 lines. -/
lemma t95J03_orientable_data_card (g : ℕ) (hg : 0 < g) :
    Nat.card (PairingOrbit (standardPairingData true g hg).pair) = 2 * g := by
  change Nat.card (PairingOrbit (orientablePair g)) = 2 * g
  rw [Nat.card_congr (orientableOrbitEquiv g)]
  simp [Nat.card_eq_fintype_card, mul_comm]

/-- **Leaf S2 (LIBRARY-sized).**  The polygon torus is the product torus.

Route.  `z ↦ L (klein_cut_chart z)` where `klein_cut_chart`
(`KleinSquareDiskCutAndPaste`, a homeomorphism of the closed disk onto the
`ℓ¹` ball sending the arc of edge `j` to the side between `i^j` and `i^{j+1}`,
commuting with multiplication by `I`) and `L` is the linear map sending the
lattice `⟨(1,1), (-1,1)⟩` to `ℤ²`, followed by `ℝ² → (ℝ/ℤ)²`.  `SurfaceRel true 1`
glues edge `0` at `t` to edge `2` at `1 - t`: the chart images differ by
`(1, 1)` (check: `e^{iθ}` and `e^{i(3π/2 - θ)}` have `ℓ¹` normalizations
differing by `(1,1)`), similarly edges `1, 3` by `(-1, 1)`; so the map descends.
It is a continuous bijection from the compact quotient to a Hausdorff space
(`Continuous.homeoOfEquivCompactToT2`).  Injectivity: two disk points with the
same image are equal, or are boundary points related by the gluings (corners:
all four vertices map to `0`).  Split if needed: descends / injective /
surjective / assembly.  250–500 lines. -/
-- ROUTE PLAN (accumulated from 4 observed episodes, 2026-10-17; START HERE, do not re-derive):
-- MAP: t95J03_torus_bridge_aux_f z = ((coe (((chart z).re + (chart z).im)/2), coe (((chart z).re - (chart z).im)/2)) : T95J03Torus)
--   chart = klein_cut_chart (ConstructionTargets/KleinSquareDiskCutAndPaste.lean, reached via KleinBottlePiOne import; NOT in Surfaces.lean; reference fully qualified - only namespaces ConstructionTargets + SurfaceGroupBetti are open).
--   The /2 scaling is ESSENTIAL for injectivity: |A| <= 1/2 forces A - A' in {-1,0,1}.
-- API CORRECTION (episode 3): `toUnitAddCircle` does NOT exist in this Mathlib. UnitAddCircle = AddCircle (1 : R); use the coercion (x : UnitAddCircle); equality: QuotientAddGroup.eq gives coe x = coe y <-> exists n : Z, x - y = n; continuity of coercion: AddCircle.continuous_mk' 1.
-- CONTINUITY: klein_cut_chart_continuous exists (banked, verified by grep); components are continuous maps into UnitAddCircle via coercion continuity.
-- DESCENT: Quotient.lift aux_f h with h : forall x y, EqvGen (SurfaceRel true 1) x y -> aux_f x = aux_f y; EqvGen induction: refl/symm/trans trivial; step = the two edge-pair helper lemmas below.
-- EDGE IDENTITIES (paper-verified twice; a = pi*t/2, s = cos a + sin a; chart of e^{i theta} on unit circle = (cos/s, sin/s)):
--   edgePoint 4 j t = exp(I * (pi/2) * (j + t)). Glue: edge j at t ~ edge (j+2) at (1 - t).
--   Edge0@t: L = (1/2, (cos a - sin a)/(2*s)); Edge2@(1-t): L = (-1/2, (cos a - sin a)/(2*s)) -> differ by exactly (1,0).
--   Edge1@t: L = ((cos a - sin a)/(2*s), -1/2); Edge3@(1-t): L = ((cos a - sin a)/(2*s), 1/2) -> differ by exactly (0,1).
--   (episode 2 corrected its own sign error: edge1 second coord is -1/2, cross-checked.)
--   KEY SIMPLIFICATION: glued partner of a boundary point z is -(I * conj z) (ring-level, no trig); flip lemma: I * conj x = exp(I * (pi/2 - Complex.arg x)) for x != 0. Rotation identities: edge1 t = I * edge0 t, edge3 s = -I * edge0 s.
-- INJECTIVITY (the bulk): F z = F z' -> coe-difference d in Z^2 with coords in [-1/2,1/2], so d in {-1,0,1}^2; case split, by symmetry d in {(1,0),(0,1),(1,1),(1,-1)} + mirrors.
--   Case (0,1) WORKED (episode 3): w = (c+1/2, c-1/2), u := c+1/2 in [0,1] -> z = (u, u-1)/r (edge3), z' = (u-1, u)/r (edge1); I*z and -I*z' first-quadrant.
--   Case (1,1): forces diamond vertices w=(1,0), w'=(-1,0); corner chains: 1 = edge0@0 ~ edge2@1 = chart(-i) = (0,-1); -i = edge3@0 ~ edge1@1 = -1. Case (1,-1): w=(0,-1), w'=(0,1); chain analysis OPEN.
--   Master lemma plan: first-quadrant unit x -> exists t in [0,1], x = edge0 t AND I * conj x = edge0 (1-t); arg-free parametrization t := (2/pi) * Real.arcsin x.im (cos(pi*t/2) = x.re from unit norm).
-- SURJECTIVITY: Quotient.induction + lemma exists rep in Icc (-1/2) (1/2) (shift by round/floor).
-- FINISH: continuous bijection, Disk quotient compact, UnitAddCircle^2 T2 -> Continuous.homeoOfEquivCompactToT2.
-- Size estimate ~300-500 lines; helpers MUST be named t95J03_torus_bridge_aux*; no wrapping namespace.
-- TODO ORDER: (1) aux defs (chart coordinate functions, aux_f, aux_f_continuous); (2) the two edge-pair descent helpers; (3) descent + continuity of the quotient map; (4) surjectivity; (5) injectivity cases ((0,1) done on paper, (1,0) symmetric, (1,1) corner chains sketched, (1,-1) OPEN); (6) homeoOfEquiv finish; (7) #print axioms check.

lemma t95J03_torus_bridge_aux_chart_neg (w : ℂ) :
    KleinSquareDiskCutAndPaste.klein_cut_chart (-w) =
      -KleinSquareDiskCutAndPaste.klein_cut_chart w := by
  by_cases hw : w = 0
  · simp [hw, KleinSquareDiskCutAndPaste.klein_cut_chart]
  · have hnw : -w ≠ 0 := by simp [hw]
    have h2 : KleinSquareDiskCutAndPaste.klein_cut_l1 (-w) =
        KleinSquareDiskCutAndPaste.klein_cut_l1 w := by
      unfold KleinSquareDiskCutAndPaste.klein_cut_l1
      simp [Complex.neg_re, Complex.neg_im]
    have h3 : ‖-w‖ = ‖w‖ := norm_neg _
    unfold KleinSquareDiskCutAndPaste.klein_cut_chart
    rw [if_neg hnw, if_neg hw, h2, h3]
    push_cast
    ring

open KleinSquareDiskCutAndPaste

lemma t95J03_torus_bridge_aux_chart_I (w : ℂ) :
    klein_cut_chart (Complex.I * w) = Complex.I * klein_cut_chart w := by
  by_cases hw : w = 0
  · simp [hw, klein_cut_chart]
  · have hnw : Complex.I * w ≠ 0 := by simpa using hw
    have h1 : (Complex.I * w).re = -w.im ∧ (Complex.I * w).im = w.re := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have h2 : klein_cut_l1 (Complex.I * w) = klein_cut_l1 w := by
      unfold klein_cut_l1; rw [h1.1, h1.2, abs_neg]; ring
    have h3 : ‖Complex.I * w‖ = ‖w‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    unfold klein_cut_chart
    rw [if_neg hnw, if_neg hw, h2, h3]
    push_cast
    ring

lemma t95J03_torus_bridge_aux_chart_exp_coords (θ : ℝ) :
    (klein_cut_chart (Complex.exp (Complex.I * θ))).re =
      Real.cos θ / (|Real.cos θ| + |Real.sin θ|) ∧
    (klein_cut_chart (Complex.exp (Complex.I * θ))).im =
      Real.sin θ / (|Real.cos θ| + |Real.sin θ|) := by
  have h0 : Complex.exp (Complex.I * θ) ≠ 0 := Complex.exp_ne_zero _
  have hrw : klein_cut_chart (Complex.exp (Complex.I * θ)) =
      ((‖Complex.exp (Complex.I * θ)‖ / klein_cut_l1 (Complex.exp (Complex.I * θ)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * θ) := by
    rw [klein_cut_chart, if_neg h0]
  have hn : ‖Complex.exp (Complex.I * θ)‖ = 1 := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im]; norm_num
  have hc : (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ ∧
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hl : klein_cut_l1 (Complex.exp (Complex.I * θ)) =
      |Real.cos θ| + |Real.sin θ| := by
    rw [klein_cut_l1, hc.1, hc.2]
  have hpos : (0 : ℝ) < |Real.cos θ| + |Real.sin θ| := by
    by_contra h
    push_neg at h
    have hn1 : 0 ≤ |Real.sin θ| := abs_nonneg _
    have hn2 : 0 ≤ |Real.cos θ| := abs_nonneg _
    have hc0 : Real.cos θ = 0 ∧ Real.sin θ = 0 := by
      constructor <;> apply abs_eq_zero.mp <;> linarith
    have := Real.sin_sq_add_cos_sq θ
    rw [hc0.1, hc0.2] at this
    norm_num at this
  have he : Complex.exp (Complex.I * (θ : ℂ)) =
      ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  constructor
  · rw [hrw, hn, hl, he]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    field_simp
    ring
  · rw [hrw, hn, hl, he]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    field_simp
    ring

lemma t95J03_torus_bridge_aux_edge_exp (j : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (edgePoint 4 j t : ℂ) = Complex.exp (Complex.I * (Real.pi / 2 * ((j : ℝ) + t.1))) := by
  simp only [edgePoint, Subtype.coe_mk]
  congr 1
  push_cast
  ring

-- ## AddCircle coercion API

lemma t95J03_torus_bridge_aux_coe_eq_of_int {x y : ℝ} {n : ℤ} (h : x - y = n) :
    (x : UnitAddCircle) = (y : UnitAddCircle) := by
  have h2 : ((x - y : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by rw [h]; simp⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at h2
  exact h2

lemma t95J03_torus_bridge_aux_int_of_coe_eq {x y : ℝ}
    (h : (x : UnitAddCircle) = (y : UnitAddCircle)) : ∃ n : ℤ, x - y = n := by
  have h2 : ((x - y : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]; exact sub_eq_zero.mpr h
  rw [AddCircle.coe_eq_zero_iff] at h2
  obtain ⟨n, hn⟩ := h2
  exact ⟨n, by rw [← hn]; simp⟩

lemma t95J03_torus_bridge_aux_continuous_coe :
    Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk' 1

-- ## The map to the torus

noncomputable def t95J03_torus_bridge_aux_f (z : ℂ) : T95J03Torus :=
  Prod.mk (((((klein_cut_chart z).re + (klein_cut_chart z).im) / 2 : ℝ) : UnitAddCircle))
    (((((klein_cut_chart z).re - (klein_cut_chart z).im) / 2 : ℝ) : UnitAddCircle))

lemma t95J03_torus_bridge_aux_f_continuous : Continuous t95J03_torus_bridge_aux_f := by
  unfold t95J03_torus_bridge_aux_f
  exact Continuous.prodMk
    (t95J03_torus_bridge_aux_continuous_coe.comp
      (((Complex.continuous_re.comp klein_cut_chart_continuous).add
        (Complex.continuous_im.comp klein_cut_chart_continuous)).div
        continuous_const (by intro _; norm_num)))
    (t95J03_torus_bridge_aux_continuous_coe.comp
      (((Complex.continuous_re.comp klein_cut_chart_continuous).sub
        (Complex.continuous_im.comp klein_cut_chart_continuous)).div
        continuous_const (by intro _; norm_num)))

lemma t95J03_torus_bridge_aux_exp_coords (θ : ℝ) :
    (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))).re = Real.cos θ ∧
    (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))).im = Real.sin θ := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma t95J03_torus_bridge_aux_exp_norm (θ : ℝ) :
    ‖Complex.exp (Complex.I * ((θ : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]

lemma t95J03_torus_bridge_aux_chart_quadrant (w : ℂ)
    (h1 : ‖w‖ = 1) (h2 : 0 ≤ w.re) (h3 : 0 ≤ w.im) :
    (klein_cut_chart w).re = w.re / (w.re + w.im) ∧
    (klein_cut_chart w).im = w.im / (w.re + w.im) := by
  have hw : w ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hne : w.re + w.im ≠ 0 := by
    intro h
    have h4 : w.re = 0 := le_antisymm (by
      have := add_nonneg h2 h3; rw [h] at this; linarith) h2
    have h5 : w.im = 0 := le_antisymm (by
      have := add_nonneg h2 h3; rw [h] at this; linarith) h3
    exact hw (by apply Complex.ext <;> simp [h4, h5])
  have hl : klein_cut_l1 w = w.re + w.im := by
    unfold klein_cut_l1; rw [abs_of_nonneg h2, abs_of_nonneg h3]
  have hrw : klein_cut_chart w = ((1 / (w.re + w.im) : ℝ) : ℂ) * w := by
    rw [klein_cut_chart, if_neg hw, h1, hl]
  constructor
  · rw [hrw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  · rw [hrw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

lemma t95J03_torus_bridge_aux_edge0_facts (t : Set.Icc (0 : ℝ) 1) :
    ‖(edgePoint 4 0 t : ℂ)‖ = 1 ∧
    (edgePoint 4 0 t : ℂ).re = Real.cos (Real.pi / 2 * (t : ℝ)) ∧
    (edgePoint 4 0 t : ℂ).im = Real.sin (Real.pi / 2 * (t : ℝ)) := by
  obtain ⟨hc1, hc2⟩ := t95J03_torus_bridge_aux_exp_coords (Real.pi / 2 * (t : ℝ))
  have hn := t95J03_torus_bridge_aux_exp_norm (Real.pi / 2 * (t : ℝ))
  have heq : (edgePoint 4 0 t : ℂ) =
      Complex.exp (Complex.I * ((Real.pi / 2 * (t : ℝ) : ℝ) : ℂ)) := by
    rw [t95J03_torus_bridge_aux_edge_exp]
    congr 1
    norm_num
  rw [heq]
  exact ⟨hn, hc1, hc2⟩

lemma t95J03_torus_bridge_aux_edge2_as_neg (u : Set.Icc (0 : ℝ) 1) :
    (edgePoint 4 2 u : ℂ) =
      -(Complex.exp (Complex.I * ((Real.pi / 2 * (u : ℝ) : ℝ)))) := by
  have hIpi : Complex.exp (Complex.I * (Real.pi : ℝ)) = -1 := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Real.cos_pi, Real.sin_pi]
  have hmul : ∀ w : ℂ, -(Complex.exp w) =
      Complex.exp (Complex.I * (Real.pi : ℝ)) * Complex.exp w := by
    intro w; rw [hIpi]; ring
  simp only [edgePoint, Subtype.coe_mk]
  rw [hmul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma t95J03_torus_bridge_aux_edge2_facts (u : Set.Icc (0 : ℝ) 1) :
    ‖(edgePoint 4 2 u : ℂ)‖ = 1 ∧
    (edgePoint 4 2 u : ℂ).re = -Real.cos (Real.pi / 2 * (u : ℝ)) ∧
    (edgePoint 4 2 u : ℂ).im = -Real.sin (Real.pi / 2 * (u : ℝ)) := by
  obtain ⟨hc1, hc2⟩ := t95J03_torus_bridge_aux_exp_coords (Real.pi / 2 * (u : ℝ))
  have hn := t95J03_torus_bridge_aux_exp_norm (Real.pi / 2 * (u : ℝ))
  have heq : (edgePoint 4 2 u : ℂ) =
      -(Complex.exp (Complex.I * ((Real.pi / 2 * (u : ℝ) : ℝ) : ℂ))) :=
    t95J03_torus_bridge_aux_edge2_as_neg u
  rw [heq, Complex.neg_re, Complex.neg_im]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_neg]; exact hn
  · rw [hc1]
  · rw [hc2]

lemma t95J03_torus_bridge_aux_pair02 (t : Set.Icc (0 : ℝ) 1) :
    t95J03_torus_bridge_aux_f (edgePoint 4 0 t : ℂ) =
      t95J03_torus_bridge_aux_f
        (edgePoint 4 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : ℂ) := by
  have hb0 : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) t.2.1
    · exact mul_le_of_le_one_right (by positivity) (by have := t.2.2; linarith)
  have hb1 : 0 ≤ Real.pi / 2 * (1 - (t : ℝ)) ∧
      Real.pi / 2 * (1 - (t : ℝ)) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) (by have := t.2.1; have := t.2.2; linarith)
    · exact mul_le_of_le_one_right (by positivity)
        (by have := t.2.1; have := t.2.2; linarith)
  have hb : Real.pi / 2 * (1 - (t : ℝ)) = Real.pi / 2 - Real.pi / 2 * (t : ℝ) := by
    ring_nf
  have hcosβ : Real.cos (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.sin (Real.pi / 2 * (t : ℝ)) ∧
      Real.sin (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.cos (Real.pi / 2 * (t : ℝ)) := by
    rw [hb, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    exact ⟨rfl, rfl⟩
  obtain ⟨hn0, hr0, hi0⟩ := t95J03_torus_bridge_aux_edge0_facts t
  obtain ⟨hn2, hr2, hi2⟩ :=
    t95J03_torus_bridge_aux_edge2_facts
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1)
  have hs0 : Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    have hcc : 0 ≤ Real.cos (Real.pi / 2 * (t : ℝ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩
    have hss : 0 ≤ Real.sin (Real.pi / 2 * (t : ℝ)) :=
      Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩
    have h1 := Real.cos_sq_add_sin_sq (Real.pi / 2 * (t : ℝ))
    intro h
    have hc0 : Real.cos (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    have hs0' : Real.sin (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    rw [hc0, hs0'] at h1
    norm_num at h1
  have hsβ : Real.cos (Real.pi / 2 * (1 - (t : ℝ))) +
      Real.sin (Real.pi / 2 * (1 - (t : ℝ))) ≠ 0 := by
    rw [hcosβ.1, hcosβ.2]; simpa [add_comm] using hs0
  have hsc : Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    rw [add_comm]; exact hs0
  -- chart coordinates on the two edges
  obtain ⟨hc0r, hc0i⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (edgePoint 4 0 t : ℂ) hn0
    (by rw [hr0]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩)
    (by rw [hi0]; exact Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩)
  have hneg : klein_cut_chart (edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ) =
      -(klein_cut_chart
        (-(edgePoint 4 2
          (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))) := by
    rw [t95J03_torus_bridge_aux_chart_neg]
    try simp
  obtain ⟨hcmr, hcmi⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (-(edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))
    (by rw [norm_neg]; exact hn2)
    (by rw [Complex.neg_re, hr2, neg_neg]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb1.2⟩)
    (by rw [Complex.neg_im, hi2, neg_neg]; exact Real.sin_nonneg_of_mem_Icc ⟨hb1.1, by linarith [Real.pi_pos]⟩)
  -- assemble
  simp only [t95J03_torus_bridge_aux_f, Prod.mk.injEq]
  rw [hneg, Complex.neg_re, Complex.neg_im]
  rw [hc0r, hc0i, hcmr, hcmi]
  rw [Complex.neg_re, Complex.neg_im, hr0, hi0, hr2, hi2]
  rw [hcosβ.1, hcosβ.2]
  simp only [neg_neg]
  constructor
  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := 1) ?_
    field_simp [hs0, hsc]
    have hE : 2 * ((Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ))) *
        (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))⁻¹) = 2 := by
      rw [mul_inv_cancel₀ hs0, mul_one]
    linear_combination (norm := ring_nf) hE
  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := 0) ?_
    push_cast
    ring_nf

lemma t95J03_torus_bridge_aux_pair13 (t : Set.Icc (0 : ℝ) 1) :
    t95J03_torus_bridge_aux_f (edgePoint 4 1 t : ℂ) =
      t95J03_torus_bridge_aux_f
        (edgePoint 4 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : ℂ) := by
  have hs1 := klein_cut_edge_succ t
  have hs2 := klein_cut_edge_succ
    (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1)
  have hb0 : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) t.2.1
    · exact mul_le_of_le_one_right (by positivity) (by have := t.2.2; linarith)
  have hb1 : 0 ≤ Real.pi / 2 * (1 - (t : ℝ)) ∧
      Real.pi / 2 * (1 - (t : ℝ)) ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) (by have := t.2.1; have := t.2.2; linarith)
    · exact mul_le_of_le_one_right (by positivity)
        (by have := t.2.1; have := t.2.2; linarith)
  have hcosβ : Real.cos (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.sin (Real.pi / 2 * (t : ℝ)) ∧
      Real.sin (Real.pi / 2 * (1 - (t : ℝ))) =
      Real.cos (Real.pi / 2 * (t : ℝ)) := by
    have hb : Real.pi / 2 * (1 - (t : ℝ)) = Real.pi / 2 - Real.pi / 2 * (t : ℝ) := by
      ring_nf
    rw [hb, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    exact ⟨rfl, rfl⟩
  obtain ⟨hn0, hr0, hi0⟩ := t95J03_torus_bridge_aux_edge0_facts t
  obtain ⟨hn2, hr2, hi2⟩ := t95J03_torus_bridge_aux_edge2_facts
    (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1)
  have hs0 : Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    have hcc : 0 ≤ Real.cos (Real.pi / 2 * (t : ℝ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩
    have hss : 0 ≤ Real.sin (Real.pi / 2 * (t : ℝ)) :=
      Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩
    have h1 := Real.cos_sq_add_sin_sq (Real.pi / 2 * (t : ℝ))
    intro h
    have hc0 : Real.cos (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    have hs0' : Real.sin (Real.pi / 2 * (t : ℝ)) = 0 := by linarith
    rw [hc0, hs0'] at h1
    norm_num at h1
  have hsc : Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)) ≠ 0 := by
    rw [add_comm]; exact hs0
  obtain ⟨hc0r, hc0i⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (edgePoint 4 0 t : ℂ) hn0
    (by rw [hr0]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb0.2⟩)
    (by rw [hi0]; exact Real.sin_nonneg_of_mem_Icc ⟨hb0.1, by linarith [Real.pi_pos]⟩)
  obtain ⟨hcmr, hcmi⟩ := t95J03_torus_bridge_aux_chart_quadrant
    (-(edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))
    (by rw [norm_neg]; exact hn2)
    (by rw [Complex.neg_re, hr2, neg_neg]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb1.2⟩)
    (by rw [Complex.neg_im, hi2, neg_neg]; exact Real.sin_nonneg_of_mem_Icc ⟨hb1.1, by linarith [Real.pi_pos]⟩)
  simp only [t95J03_torus_bridge_aux_f, Prod.mk.injEq]
  rw [hs1.1, hs2.2, t95J03_torus_bridge_aux_chart_I, t95J03_torus_bridge_aux_chart_I]
  have he2c : klein_cut_chart (edgePoint 4 2
      (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ) =
      -(klein_cut_chart
        (-(edgePoint 4 2
          (⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0 : ℝ) 1) : ℂ))) := by
    rw [t95J03_torus_bridge_aux_chart_neg]
    try simp
  rw [he2c, mul_neg]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_neg]
  rw [hc0r, hc0i, hcmr, hcmi, Complex.neg_re, Complex.neg_im,
    hr0, hi0, hr2, hi2, hcosβ.1, hcosβ.2]
  norm_num
  constructor
  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := 0) ?_
    push_cast
    ring_nf

  · refine t95J03_torus_bridge_aux_coe_eq_of_int (n := -1) ?_
    have hB1 : (-(Real.sin (Real.pi / 2 * (t : ℝ)) /
        (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))) -
        Real.cos (Real.pi / 2 * (t : ℝ)) /
        (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))) = -1 := by
      have hI1 : (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ))) *
          (Real.cos (Real.pi / 2 * (t : ℝ)) + Real.sin (Real.pi / 2 * (t : ℝ)))⁻¹ = 1 :=
        mul_inv_cancel₀ hs0
      linear_combination (norm := ring_nf) -1 * hI1
    have hB3 : (Real.cos (Real.pi / 2 * (t : ℝ)) /
        (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ))) +
        Real.sin (Real.pi / 2 * (t : ℝ)) /
        (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)))) = 1 := by
      have hI2 : (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ))) *
          (Real.sin (Real.pi / 2 * (t : ℝ)) + Real.cos (Real.pi / 2 * (t : ℝ)))⁻¹ = 1 :=
        mul_inv_cancel₀ hsc
      linear_combination (norm := ring_nf) hI2
    rw [hB1, hB3]
    push_cast
    norm_num

lemma t95J03_torus_bridge_aux_descent (x y : Disk)
    (h : SurfaceRel true 1 x y) :
    t95J03_torus_bridge_aux_f (x : ℂ) = t95J03_torus_bridge_aux_f (y : ℂ) := by
  unfold SurfaceRel at h
  simp only [if_true] at h
  obtain ⟨j, hj, t, hcase⟩ := h
  have hj0 : j = 0 := Nat.lt_one_iff.mp hj
  subst hj0
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · norm_num at h1 h2
    rw [h1, h2]
    exact t95J03_torus_bridge_aux_pair02 t
  · norm_num at h1 h2
    rw [h1, h2]
    exact t95J03_torus_bridge_aux_pair13 t

lemma t95J03_torus_bridge_aux_sound (x y : Disk)
    (h : Relation.EqvGen (SurfaceRel true 1) x y) :
    t95J03_torus_bridge_aux_f (x : ℂ) = t95J03_torus_bridge_aux_f (y : ℂ) := by
  induction h with
  | refl => rfl
  | symm _ _ h' ih => exact ih.symm
  | trans _ _ _ h1 h2 ih1 ih2 => exact ih1.trans ih2
  | rel x y hrel => exact t95J03_torus_bridge_aux_descent x y hrel

noncomputable def t95J03_torus_bridge_aux_lift : Surface true 1 → T95J03Torus :=
  Quotient.lift (fun z : Disk => t95J03_torus_bridge_aux_f (z : ℂ))
    (fun x y h => t95J03_torus_bridge_aux_sound x y h)

lemma t95J03_torus_bridge_aux_lift_continuous : Continuous t95J03_torus_bridge_aux_lift := by
  unfold t95J03_torus_bridge_aux_lift
  exact Continuous.quotient_lift
    (t95J03_torus_bridge_aux_f_continuous.comp continuous_subtype_val)
    (fun a b h => t95J03_torus_bridge_aux_sound a b h)

lemma t95J03_torus_bridge_aux_abs_le (x y : ℝ) :
    |x + y| + |x - y| ≤ 2 * max |x| |y| := by
  have hA : |x + y| ^ 2 = (x + y) ^ 2 := sq_abs _
  have hB : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
  have hAB : |x + y| * |x - y| = |x ^ 2 - y ^ 2| := by
    rw [← abs_mul]
    congr 1
    ring
  by_cases hc : x ^ 2 ≤ y ^ 2
  · have hmy : |x ^ 2 - y ^ 2| = -(x ^ 2 - y ^ 2) := abs_of_nonpos (by linarith)
    have hm : max |x| |y| = |y| := by
      refine max_eq_right ?_
      by_cases hle : |x| ≤ |y|
      · exact hle
      · exfalso
        push_neg at hle
        have hprod : (|x| - |y|) * (|x| + |y|) = |x| ^ 2 - |y| ^ 2 := by ring
        have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
        have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
        have hpp : 0 < (|x| - |y|) * (|x| + |y|) := by
          nlinarith [hle, abs_nonneg x, abs_nonneg y]
        linarith
    have hexp : (|x + y| + |x - y|) ^ 2 = 4 * y ^ 2 := by
      have e1 : (|x + y| + |x - y|) ^ 2 =
          (|x + y|) ^ 2 + (|x - y|) ^ 2 + 2 * (|x + y| * |x - y|) := by ring
      rw [e1, hA, hB, hAB, hmy]
      ring
    have hsq : (|x + y| + |x - y|) ^ 2 ≤ (2 * max |x| |y|) ^ 2 := by
      rw [hm]
      have h4 : (2 * |y|) ^ 2 = 4 * y ^ 2 := by rw [show (2 * |y|) ^ 2 = 4 * |y| ^ 2 from by ring, sq_abs y]
      rw [h4, hexp]
    have hnn2 : 0 ≤ 2 * max |x| |y| := by positivity
    nlinarith [hsq, hnn2]
  · have hmy : |x ^ 2 - y ^ 2| = x ^ 2 - y ^ 2 := abs_of_nonneg (by linarith)
    have hm : max |x| |y| = |x| := by
      refine max_eq_left ?_
      by_cases hle : |y| ≤ |x|
      · exact hle
      · exfalso
        push_neg at hle
        have hprod : (|y| - |x|) * (|y| + |x|) = |y| ^ 2 - |x| ^ 2 := by ring
        have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
        have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
        have hpp : 0 < (|y| - |x|) * (|y| + |x|) := by
          nlinarith [hle, abs_nonneg x, abs_nonneg y]
        linarith
    have hexp : (|x + y| + |x - y|) ^ 2 = 4 * x ^ 2 := by
      have e1 : (|x + y| + |x - y|) ^ 2 =
          (|x + y|) ^ 2 + (|x - y|) ^ 2 + 2 * (|x + y| * |x - y|) := by ring
      rw [e1, hA, hB, hAB, hmy]
      ring
    have hsq : (|x + y| + |x - y|) ^ 2 ≤ (2 * max |x| |y|) ^ 2 := by
      rw [hm]
      have h4 : (2 * |x|) ^ 2 = 4 * x ^ 2 := by rw [show (2 * |x|) ^ 2 = 4 * |x| ^ 2 from by ring, sq_abs x]
      rw [h4, hexp]
    have hnn2 : 0 ≤ 2 * max |x| |y| := by positivity
    nlinarith [hsq, hnn2]

lemma t95J03_torus_bridge_aux_rep (x : UnitAddCircle) :
    ∃ r : ℝ, r ∈ Set.Icc (-(1 / 2)) (1 / 2) ∧ (r : UnitAddCircle) = x := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨c - (Int.floor (c + 1 / 2) : ℤ), ⟨?_, ?_⟩, ?_⟩
  · have hf1 : ((Int.floor (c + 1 / 2) : ℤ) : ℝ) ≤ c + 1 / 2 := Int.floor_le _
    linarith
  · have hf2 : c + 1 / 2 < (((Int.floor (c + 1 / 2) : ℤ) : ℝ) + 1) := by
      have := Int.lt_floor_add_one (c + 1 / 2)
      push_cast at this
      linarith
    linarith
  · rw [← hc]
    exact t95J03_torus_bridge_aux_coe_eq_of_int (n := -(Int.floor (c + 1 / 2) : ℤ))
      (by push_cast; simp)

lemma t95J03_torus_bridge_aux_lift_surjective :
    Function.Surjective t95J03_torus_bridge_aux_lift := by
  intro p
  obtain ⟨a, b⟩ := p
  obtain ⟨ra, hra, hca⟩ := t95J03_torus_bridge_aux_rep a
  obtain ⟨rb, hrb, hcb⟩ := t95J03_torus_bridge_aux_rep b
  have hra1 : -(1 / 2) ≤ ra := hra.1
  have hra2 : ra ≤ 1 / 2 := hra.2
  have hrb1 : -(1 / 2) ≤ rb := hrb.1
  have hrb2 : rb ≤ 1 / 2 := hrb.2
  have hra' : |ra| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hrb' : |rb| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hl1 : |ra + rb| + |ra - rb| ≤ 1 := by
    have h1 := t95J03_torus_bridge_aux_abs_le ra rb
    have h2 : max |ra| |rb| ≤ 1 / 2 := by
      exact max_le hra' hrb'
    have : 2 * max |ra| |rb| ≤ 1 := by linarith
    linarith
  set w : ℂ := ⟨ra + rb, ra - rb⟩ with hw
  have hball : klein_cut_chartInv w ∈ (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_closedBall, dist_zero_right, klein_cut_norm_chartInv, klein_cut_l1]
    show |ra + rb| + |ra - rb| ≤ 1
    exact hl1
  refine ⟨Quotient.mk _ ⟨klein_cut_chartInv w, hball⟩, ?_⟩
  have hc : klein_cut_chart (klein_cut_chartInv w) = w := klein_cut_chart_chartInv w
  have hxr : (klein_cut_chart (klein_cut_chartInv w)).re = ra + rb := by rw [hc]
  have hxi : (klein_cut_chart (klein_cut_chartInv w)).im = ra - rb := by rw [hc]
  rw [t95J03_torus_bridge_aux_lift, Quotient.lift_mk]
  have hval : t95J03_torus_bridge_aux_f (klein_cut_chartInv w) = Prod.mk a b := by
    show Prod.mk _ _ = Prod.mk a b
    have hrw1 : ((ra + rb) + (ra - rb)) / 2 = ra := by ring
    have hrw2 : ((ra + rb) - (ra - rb)) / 2 = rb := by ring
    rw [hxr, hxi, hrw1, hrw2]
    rw [Prod.mk.injEq]
    exact ⟨hca, hcb⟩
  exact hval

-- ## Injectivity

lemma t95J03_torus_bridge_aux_chart_bound (z : Disk) :
    |(klein_cut_chart (z : ℂ)).re| ≤ 1 ∧ |(klein_cut_chart (z : ℂ)).im| ≤ 1 := by
  have hn : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hl : |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| = ‖(z : ℂ)‖ :=
    klein_cut_l1_chart _
  have hre := abs_nonneg (klein_cut_chart (z : ℂ)).re
  have him := abs_nonneg (klein_cut_chart (z : ℂ)).im
  constructor <;> linarith

-- ## Injectivity: helper lemmas

lemma t95J03_torus_bridge_aux_exp_corner :
    (edgePoint 4 0 ⟨(0 : ℝ), by norm_num⟩ : ℂ) = 1 ∧
    (edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ : ℂ) = -Complex.I ∧
    (edgePoint 4 1 ⟨(0 : ℝ), by norm_num⟩ : ℂ) = Complex.I ∧
    (edgePoint 4 3 ⟨(1 : ℝ), by norm_num⟩ : ℂ) = 1 ∧
    (edgePoint 4 1 ⟨(1 : ℝ), by norm_num⟩ : ℂ) = -1 ∧
    (edgePoint 4 3 ⟨(0 : ℝ), by norm_num⟩ : ℂ) = -Complex.I := by
  have hI : Complex.exp (Complex.I * (((Real.pi : ℝ) : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hIpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    rw [mul_comm]; exact Complex.exp_pi_mul_I
  have hstep3 : Complex.exp (Complex.I * (((Real.pi : ℝ) : ℂ) / 2 * 3)) = -Complex.I := by
    rw [show ((Real.pi : ℝ) : ℂ) / 2 * 3 =
        ((Real.pi : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) / 2 from by
      field_simp
      ring]
    rw [mul_add, Complex.exp_add]
    rw [show Complex.I * ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I from mul_comm _ _,
      Complex.exp_pi_mul_I, hI]
    norm_num
  have hbridge : ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) / 2 := by
    rw [Complex.ofReal_div]
    norm_num
  constructor
  · rw [t95J03_torus_bridge_aux_edge_exp]
    norm_num
    try simp
  · constructor
    · rw [t95J03_torus_bridge_aux_edge_exp]
      norm_num
      rw [hstep3]
    · constructor
      · rw [(klein_cut_edge_succ ⟨(0 : ℝ), by norm_num⟩).1]
        rw [t95J03_torus_bridge_aux_edge_exp]
        norm_num
        try rw [Complex.exp_zero]
        try simp
      · constructor
        · rw [(klein_cut_edge_succ ⟨(1 : ℝ), by norm_num⟩).2]
          rw [t95J03_torus_bridge_aux_edge_exp]
          norm_num
          rw [hstep3]
          norm_num
        · constructor
          · rw [(klein_cut_edge_succ ⟨(1 : ℝ), by norm_num⟩).1]
            rw [t95J03_torus_bridge_aux_edge_exp]
            norm_num
            rw [hI]
            norm_num
          · rw [(klein_cut_edge_succ ⟨(0 : ℝ), by norm_num⟩).2]
            rw [t95J03_torus_bridge_aux_edge_exp]
            norm_num
            rw [hIpi]
            norm_num

lemma t95J03_torus_bridge_aux_angle_of_sin {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hb : 0 ≤ b) (hb2 : b ≤ Real.pi / 2) (h : Real.sin (b - a) = 0) : a = b := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  push_cast at hk
  have hbd1 : b - a ≤ Real.pi / 2 := by linarith [hb2, ha]
  have hbd2 : -(Real.pi / 2) ≤ b - a := by linarith [ha2, hb]
  have hk0 : k = 0 := by
    by_contra h0
    by_cases hh : 1 ≤ k
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hh
      nlinarith [Real.pi_pos, hk, hbd1]
    · have hk' : k ≤ -1 := by omega
      have h1 : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
      nlinarith [Real.pi_pos, hk, hbd2]
  rw [hk0] at hk
  push_cast at hk
  linarith

lemma t95J03_torus_bridge_aux_g_inj {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hb : 0 ≤ b) (hb2 : b ≤ Real.pi / 2)
    (h : Real.cos a - Real.sin a = Real.cos b - Real.sin b) : a = b := by
  have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ha2⟩
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ⟨ha, by linarith [Real.pi_pos]⟩
  have hcb : 0 ≤ Real.cos b := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb2⟩
  have hsb : 0 ≤ Real.sin b := Real.sin_nonneg_of_mem_Icc ⟨hb, by linarith [Real.pi_pos]⟩
  have h1 := Real.cos_sq_add_sin_sq a
  have h2 := Real.cos_sq_add_sin_sq b
  have hsq : (Real.cos a + Real.sin a) ^ 2 = (Real.cos b + Real.sin b) ^ 2 := by
    have e1 : (Real.cos a + Real.sin a) ^ 2 + (Real.cos a - Real.sin a) ^ 2 =
        2 * (Real.cos a ^ 2 + Real.sin a ^ 2) := by ring
    have e2 : (Real.cos b + Real.sin b) ^ 2 + (Real.cos b - Real.sin b) ^ 2 =
        2 * (Real.cos b ^ 2 + Real.sin b ^ 2) := by ring
    rw [h1] at e1
    rw [h2] at e2
    have hPQ : (Real.cos a - Real.sin a) ^ 2 = (Real.cos b - Real.sin b) ^ 2 := by rw [h]
    linarith [e1, e2, hPQ]
  have hS : Real.cos a + Real.sin a = Real.cos b + Real.sin b := by
    have hprod : (Real.cos a + Real.sin a - (Real.cos b + Real.sin b)) *
        (Real.cos a + Real.sin a + (Real.cos b + Real.sin b)) = 0 := by
      have e3 : (Real.cos a + Real.sin a - (Real.cos b + Real.sin b)) *
          (Real.cos a + Real.sin a + (Real.cos b + Real.sin b)) =
          (Real.cos a + Real.sin a) ^ 2 - (Real.cos b + Real.sin b) ^ 2 := by ring
      rw [e3, hsq]
      ring
    have hsumpos : 0 < Real.cos a + Real.sin a + (Real.cos b + Real.sin b) := by
      by_contra hc0
      push_neg at hc0
      have e1 : Real.cos a + Real.sin a = 0 := by linarith [hca, hsa, hcb, hsb, hc0]
      have e2 : Real.cos b + Real.sin b = 0 := by linarith [hca, hsa, hcb, hsb, hc0]
      have hza : Real.cos a = 0 := by nlinarith [hca, hsa, e1]
      have hzb : Real.sin a = 0 := by nlinarith [hca, hsa, e1]
      rw [hza, hzb] at h1
      norm_num at h1
    nlinarith [hprod, hsumpos]
  have hcc : Real.cos a = Real.cos b := by linarith
  have hss : Real.sin a = Real.sin b := by linarith
  refine t95J03_torus_bridge_aux_angle_of_sin ha ha2 hb hb2 ?_
  rw [Real.sin_sub, hcc, hss]
  ring

lemma t95J03_torus_bridge_aux_val_inj {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hb : 0 ≤ b) (hb2 : b ≤ Real.pi / 2)
    (hne1 : Real.cos a + Real.sin a ≠ 0) (hne2 : Real.cos b + Real.sin b ≠ 0)
    (h : (Real.cos a - Real.sin a) / (Real.cos a + Real.sin a) =
      (Real.cos b - Real.sin b) / (Real.cos b + Real.sin b)) : a = b := by
  have hcross : (Real.cos a - Real.sin a) * (Real.cos b + Real.sin b) =
      (Real.cos b - Real.sin b) * (Real.cos a + Real.sin a) :=
    (div_eq_div_iff hne1 hne2).mp h
  refine t95J03_torus_bridge_aux_angle_of_sin ha ha2 hb hb2 ?_
  rw [Real.sin_sub]
  have e : (Real.cos a - Real.sin a) * (Real.cos b + Real.sin b) -
      (Real.cos b - Real.sin b) * (Real.cos a + Real.sin a) =
      2 * (Real.sin b * Real.cos a - Real.cos b * Real.sin a) := by ring
  have h2 : 2 * (Real.sin b * Real.cos a - Real.cos b * Real.sin a) = 0 := by
    linarith [hcross, e]
  linarith

lemma t95J03_torus_bridge_aux_edge1_of (z : ℂ) (h1 : ‖z‖ = 1) (hre : z.re ≤ 0)
    (him : 0 ≤ z.im) : ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 1 t := by
  have hw : ‖-(Complex.I * z)‖ = 1 := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    exact h1
  have hwr : (-(Complex.I * z)).re = z.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hwi : (-(Complex.I * z)).im = -z.re := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]
  have hball : (-(Complex.I * z)) ∈ (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw.le
  have hwz : ‖((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ)‖ = 1 := hw
  have hwrz : 0 ≤ ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).re := by
    show 0 ≤ (-(Complex.I * z)).re
    rw [hwr]
    exact him
  have hwiz : 0 ≤ ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).im := by
    show 0 ≤ (-(Complex.I * z)).im
    rw [hwi]
    exact neg_nonneg.mpr hre
  obtain ⟨t, ht⟩ := (klein_cut_edge_zero_iff (⟨-(Complex.I * z), hball⟩ : Disk)).mpr
    ⟨hwz, hwrz, hwiz⟩
  refine ⟨t, ?_⟩
  have hte : -(Complex.I * z) = (edgePoint 4 0 t : ℂ) := Subtype.ext_iff.mp ht
  have hzI : z = Complex.I * (-(Complex.I * z)) := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]
  rw [hzI, hte, (klein_cut_edge_succ t).1]

lemma t95J03_torus_bridge_aux_edge3_of (z : ℂ) (h1 : ‖z‖ = 1) (hre : 0 ≤ z.re)
    (him : z.im ≤ 0) : ∃ t : Set.Icc (0 : ℝ) 1, z = edgePoint 4 3 t := by
  have hw : ‖-(Complex.I * z)‖ = 1 := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    exact h1
  have hwr : (-(Complex.I * z)).re = z.im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]
  have hwi : (-(Complex.I * z)).im = -z.re := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]
  have hball : (-(Complex.I * z)) ∈ (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw.le
  have hwz : ‖((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ)‖ = 1 := hw
  have hwrz : ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).re ≤ 0 := by
    show (-(Complex.I * z)).re ≤ 0
    rw [hwr]
    exact him
  have hwiz : ((⟨-(Complex.I * z), hball⟩ : Disk) : ℂ).im ≤ 0 := by
    show (-(Complex.I * z)).im ≤ 0
    rw [hwi]
    exact neg_nonpos.mpr hre
  obtain ⟨t, ht⟩ := (klein_cut_edge_two_iff (⟨-(Complex.I * z), hball⟩ : Disk)).mpr
    ⟨hwz, hwrz, hwiz⟩
  refine ⟨t, ?_⟩
  have hte : -(Complex.I * z) = (edgePoint 4 2 t : ℂ) := Subtype.ext_iff.mp ht
  have hzI : z = Complex.I * (-(Complex.I * z)) := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]
  rw [hzI, hte, (klein_cut_edge_succ t).2]

lemma t95J03_torus_bridge_aux_chart_self {z : ℂ} (h : ‖z‖ = 1)
    (hl : klein_cut_l1 z = 1) : klein_cut_chart z = z := by
  rw [klein_cut_chart, if_neg (by
    intro hz
    rw [hz] at h
    simp at h), h, hl]
  norm_num

lemma t95J03_torus_bridge_aux_signs {x y : ℝ} (h : x + y = 1) (hl : |x| + |y| ≤ 1) :
    0 ≤ x ∧ 0 ≤ y := by
  constructor
  · by_contra h0
    push_neg at h0
    have hy1 : 1 < y := by linarith
    have hya : 1 < |y| := by
      have := le_abs_self y
      linarith
    have hx1 : 0 ≤ |x| := abs_nonneg x
    linarith
  · by_contra h0
    push_neg at h0
    have hx1 : 1 < x := by linarith
    have hxa : 1 < |x| := by
      have := le_abs_self x
      linarith
    have hy1 : 0 ≤ |y| := abs_nonneg y
    linarith

set_option maxHeartbeats 2000000 in
/-- The n = 1 core: first-coordinate offset exactly 1. -/
lemma t95J03_torus_bridge_aux_inj_caseA (z z' : Disk) (m : ℤ)
    (hA : ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im) / (2 : ℝ) = 1 / 2)
    (hA' : ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im) / (2 : ℝ) = -(1 / 2))
    (hm : ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im) / 2 -
        ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im) / (2 : ℝ) = m)
    (hm1 : m = 1 ∨ m = -1 ∨ m = 0) :
    Relation.EqvGen (SurfaceRel true 1) z z' := by
  push_cast at hm
  norm_num at hm
  -- chart coordinate notation
  set x := (klein_cut_chart (z : ℂ)).re with hxdef
  set y := (klein_cut_chart (z : ℂ)).im with hydef
  set x' := (klein_cut_chart (z' : ℂ)).re with hx'def
  set y' := (klein_cut_chart (z' : ℂ)).im with hy'def
  have hsum : x + y = 1 := by rw [hxdef, hydef] at hA; linarith
  have hsum' : x' + y' = -1 := by rw [hx'def, hy'def] at hA'; linarith
  have hnormz : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hnormz' : ‖(z' : ℂ)‖ ≤ 1 := by
    have h := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hc0 := klein_cut_l1_chart (z : ℂ)
  unfold klein_cut_l1 at hc0
  rw [← hxdef, ← hydef] at hc0
  have hl1 : |x| + |y| ≤ 1 := by rw [hc0]; exact hnormz
  have hs := t95J03_torus_bridge_aux_signs hsum hl1
  have hl1eq : |x| + |y| = 1 := by
    rw [abs_of_nonneg hs.1, abs_of_nonneg hs.2]
    linarith
  have hnz : ‖(z : ℂ)‖ = 1 := by rw [← hc0, hl1eq]
  have hc0' := klein_cut_l1_chart (z' : ℂ)
  unfold klein_cut_l1 at hc0'
  rw [← hx'def, ← hy'def] at hc0'
  have hl1' : |x'| + |y'| ≤ 1 := by rw [hc0']; exact hnormz'
  have hs' : x' ≤ 0 ∧ y' ≤ 0 := by
    have hn : (-x') + (-y') = 1 := by linarith
    have hl : |-x'| + |-y'| ≤ 1 := by rw [abs_neg, abs_neg]; exact hl1'
    obtain ⟨h1, h2⟩ := t95J03_torus_bridge_aux_signs hn hl
    exact ⟨neg_nonneg.mp h1, neg_nonneg.mp h2⟩
  have hl1eq' : |x'| + |y'| = 1 := by
    rw [abs_of_nonpos hs'.1, abs_of_nonpos hs'.2]
    linarith
  have hnz' : ‖(z' : ℂ)‖ = 1 := by rw [← hc0', hl1eq']
  have hc := t95J03_torus_bridge_aux_exp_corner
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    have hle1 := le_abs_self a
    have hle2 := le_abs_self b
    have hle3 := neg_abs_le a
    have hle4 := neg_abs_le b
    rw [abs_le]
    constructor <;> linarith
  rcases hm1 with rfl | rfl | rfl
  · -- m = 1 : z = 1, z' = -1
    have hd : x - y - (x' - y') = 2 := by linarith
    have hbd1 : x - y ≤ 1 := by
      have := htri x y
      have hx' := abs_nonneg x
      have hy' := abs_nonneg y
      nlinarith [hl1eq]
    have hbd2 : x' - y' ≥ -1 := by
      have := htri x' y'
      have hx' := abs_nonneg x'
      have hy' := abs_nonneg y'
      nlinarith [hl1eq']
    have hx1 : x = 1 ∧ y = 0 := by constructor <;> linarith
    have hx1' : x' = -1 ∧ y' = 0 := by constructor <;> linarith
    have hcz1 : klein_cut_chart (z : ℂ) = 1 := by
      apply Complex.ext
      · rw [← hxdef, hx1.1]; norm_num
      · rw [← hydef, hx1.2]; norm_num
    have hcz1' : klein_cut_chart (z' : ℂ) = -1 := by
      apply Complex.ext
      · rw [← hx'def, hx1'.1]; norm_num
      · rw [← hy'def, hx1'.2]; norm_num
    have hz1 : (z : ℂ) = 1 := by
      rw [← klein_cut_chartInv_chart (z : ℂ), hcz1]
      simp [klein_cut_chartInv, klein_cut_l1]
    have hz1' : (z' : ℂ) = -1 := by
      rw [← klein_cut_chartInv_chart (z' : ℂ), hcz1']
      simp [klein_cut_chartInv, klein_cut_l1]
    set w : Disk := edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ with hwdef
    have hwv : (w : ℂ) = -Complex.I := hc.2.1
    have he0 : z = edgePoint 4 0 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1]; exact hc.1.symm)
    have he2 : w = edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ := by rw [hwdef]
    have he1 : z' = edgePoint 4 1 ⟨(1 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1']; exact hc.2.2.2.2.1.symm)
    have he3 : w = edgePoint 4 3 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hwdef, hwv]; exact hc.2.2.2.2.2.symm)
    have r1 : Relation.EqvGen (SurfaceRel true 1) z w :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) z w (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inl ⟨by rw [he0]; try norm_num, by rw [he2]; try norm_num⟩)
    have rinner : Relation.EqvGen (SurfaceRel true 1) z' w :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) z' w (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(1 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inr ⟨by rw [he1]; try norm_num, by rw [he3]; try norm_num⟩)
    have r2 : Relation.EqvGen (SurfaceRel true 1) w z' :=
      @Relation.EqvGen.symm _ (SurfaceRel true 1) z' w rinner
    exact @Relation.EqvGen.trans _ (SurfaceRel true 1) z w z' r1 r2
  · -- m = -1 : z = i, z' = -i
    have hd : x - y - (x' - y') = -2 := by linarith
    have hbd1 : x - y ≥ -1 := by
      have := htri x y
      have hx' := abs_nonneg x
      have hy' := abs_nonneg y
      nlinarith [hl1eq]
    have hbd2 : x' - y' ≤ 1 := by
      have := htri x' y'
      have hx' := abs_nonneg x'
      have hy' := abs_nonneg y'
      nlinarith [hl1eq']
    have hx0 : x = 0 ∧ y = 1 := by constructor <;> linarith
    have hx0' : x' = 0 ∧ y' = -1 := by constructor <;> linarith
    have hcz1 : klein_cut_chart (z : ℂ) = Complex.I := by
      apply Complex.ext
      · rw [← hxdef, hx0.1]; norm_num
      · rw [← hydef, hx0.2]; norm_num
    have hcz1' : klein_cut_chart (z' : ℂ) = -Complex.I := by
      apply Complex.ext
      · rw [← hx'def, hx0'.1]; norm_num
      · rw [← hy'def, hx0'.2]; norm_num
    have hz1 : (z : ℂ) = Complex.I := by
      rw [← klein_cut_chartInv_chart (z : ℂ), hcz1]
      simp [klein_cut_chartInv, klein_cut_l1]
    have hz1' : (z' : ℂ) = -Complex.I := by
      rw [← klein_cut_chartInv_chart (z' : ℂ), hcz1']
      simp [klein_cut_chartInv, klein_cut_l1]
    set w : Disk := edgePoint 4 3 ⟨(1 : ℝ), by norm_num⟩ with hwdef
    have hwv : (w : ℂ) = 1 := hc.2.2.2.1
    have he1 : z = edgePoint 4 1 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1]; exact hc.2.2.1.symm)
    have he3 : w = edgePoint 4 3 ⟨(1 : ℝ), by norm_num⟩ := by rw [hwdef]
    have he0 : w = edgePoint 4 0 ⟨(0 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hwdef, hwv]; exact hc.1.symm)
    have he2 : z' = edgePoint 4 2 ⟨(1 : ℝ), by norm_num⟩ :=
      Subtype.ext (by rw [hz1']; exact hc.2.1.symm)
    have r1 : Relation.EqvGen (SurfaceRel true 1) z w :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) z w (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inr ⟨by rw [he1]; try norm_num, by rw [he3]; try norm_num⟩)
    have r2' : Relation.EqvGen (SurfaceRel true 1) w z' :=
      @Relation.EqvGen.rel _ (SurfaceRel true 1) w z' (by
        unfold SurfaceRel
        refine ⟨0, by norm_num, ⟨(⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1), ?_⟩⟩
        exact Or.inl ⟨by rw [he0]; try norm_num, by rw [he2]; try norm_num⟩)
    exact @Relation.EqvGen.trans _ (SurfaceRel true 1) z w z' r1 r2'
  · -- m = 0 : the main case
    have hd : x - y = x' - y' := by linarith
    have hxy' : x' = -y ∧ y' = -x := by constructor <;> linarith
    obtain ⟨c, hc0, hcq⟩ := klein_cut_chartInv_pos (klein_cut_chart (z : ℂ))
    have hzc : (z : ℂ) = ((c : ℝ) : ℂ) * (klein_cut_chart (z : ℂ)) :=
      (klein_cut_chartInv_chart (z : ℂ)).symm.trans hcq
    have hzre : (z : ℂ).re = c * x := by
      rw [hzc]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hxdef]
    have hzim : (z : ℂ).im = c * y := by
      rw [hzc]
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hydef]
    have hcnnc : 0 ≤ c := hc0.le
    obtain ⟨t, ht⟩ := (klein_cut_edge_zero_iff z).mpr
      ⟨hnz, by rw [hzre]; exact mul_nonneg hcnnc hs.1,
        by rw [hzim]; exact mul_nonneg hcnnc hs.2⟩
    obtain ⟨c', hc0', hcq'⟩ := klein_cut_chartInv_pos (klein_cut_chart (z' : ℂ))
    have hzc' : (z' : ℂ) = ((c' : ℝ) : ℂ) * (klein_cut_chart (z' : ℂ)) :=
      (klein_cut_chartInv_chart (z' : ℂ)).symm.trans hcq'
    have hzre' : (z' : ℂ).re = c' * x' := by
      rw [hzc']
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hx'def]
    have hzim' : (z' : ℂ).im = c' * y' := by
      rw [hzc']
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hy'def]
    have hc'nn : 0 ≤ c' := hc0'.le
    obtain ⟨u, hu⟩ := (klein_cut_edge_two_iff z').mpr
      ⟨hnz', by rw [hzre']; nlinarith [mul_nonneg hc'nn (neg_nonneg.mpr hs'.1)],
        by rw [hzim']; nlinarith [mul_nonneg hc'nn (neg_nonneg.mpr hs'.2)]⟩
    -- trigonometric parameters
    have hαb : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 :=
      ⟨mul_nonneg (by positivity) t.2.1,
        mul_le_of_le_one_right (by positivity) t.2.2⟩
    have hβb : 0 ≤ Real.pi / 2 * (u : ℝ) ∧ Real.pi / 2 * (u : ℝ) ≤ Real.pi / 2 :=
      ⟨mul_nonneg (by positivity) u.2.1,
        mul_le_of_le_one_right (by positivity) u.2.2⟩
    set α : ℝ := Real.pi / 2 * (t : ℝ) with hαdef
    set β : ℝ := Real.pi / 2 * (u : ℝ) with hβdef
    have hcα : 0 ≤ Real.cos α :=
      Real.cos_nonneg_of_mem_Icc ⟨by have := hαb.1; linarith [Real.pi_pos],
        by have := hαb.2; linarith [Real.pi_pos]⟩
    have hsα : 0 ≤ Real.sin α :=
      Real.sin_nonneg_of_mem_Icc ⟨hαb.1, by have := hαb.2; linarith [Real.pi_pos]⟩
    have hcβ : 0 ≤ Real.cos β :=
      Real.cos_nonneg_of_mem_Icc ⟨by have := hβb.1; linarith [Real.pi_pos],
        by have := hβb.2; linarith [Real.pi_pos]⟩
    have hsβ : 0 ≤ Real.sin β :=
      Real.sin_nonneg_of_mem_Icc ⟨hβb.1, by have := hβb.2; linarith [Real.pi_pos]⟩
    have hne1 : Real.cos α + Real.sin α ≠ 0 := by
      intro hh
      have h1 : Real.cos α = 0 := by nlinarith [hcα, hsα, hh]
      have h2 : Real.sin α = 0 := by nlinarith [hcα, hsα, hh]
      have h3 := Real.cos_sq_add_sin_sq α
      rw [h1, h2] at h3
      norm_num at h3
    have hne2 : Real.cos β + Real.sin β ≠ 0 := by
      intro hh
      have h1 : Real.cos β = 0 := by nlinarith [hcβ, hsβ, hh]
      have h2 : Real.sin β = 0 := by nlinarith [hcβ, hsβ, hh]
      have h3 := Real.cos_sq_add_sin_sq β
      rw [h1, h2] at h3
      norm_num at h3
    have hf0 := t95J03_torus_bridge_aux_edge0_facts t
    have hzrecos : (z : ℂ).re = Real.cos α := by rw [hαdef, ht]; exact hf0.2.1
    have hzimcos : (z : ℂ).im = Real.sin α := by rw [hαdef, ht]; exact hf0.2.2
    have hcs : klein_cut_l1 (z : ℂ) = Real.cos α + Real.sin α := by
      rw [klein_cut_l1, hzrecos, hzimcos, abs_of_nonneg hcα, abs_of_nonneg hsα]
    have hf2 := t95J03_torus_bridge_aux_edge2_facts u
    have hz'recos : (z' : ℂ).re = -Real.cos β := by rw [hβdef, hu]; exact hf2.2.1
    have hz'imcos : (z' : ℂ).im = -Real.sin β := by rw [hβdef, hu]; exact hf2.2.2
    have hcs' : klein_cut_l1 (z' : ℂ) = Real.cos β + Real.sin β := by
      rw [klein_cut_l1, hz'recos, hz'imcos, abs_neg, abs_neg,
        abs_of_nonneg hcβ, abs_of_nonneg hsβ]
    have hz0 : (z : ℂ) ≠ 0 := by
      intro hh
      rw [hh] at hnz
      simp at hnz
    have hz0' : (z' : ℂ) ≠ 0 := by
      intro hh
      rw [hh] at hnz'
      simp at hnz'
    have hchz : klein_cut_chart (z : ℂ) =
        ((1 / (Real.cos α + Real.sin α) : ℝ) : ℂ) * (z : ℂ) := by
      rw [klein_cut_chart, if_neg hz0, hnz, hcs]
    have hchz' : klein_cut_chart (z' : ℂ) =
        ((1 / (Real.cos β + Real.sin β) : ℝ) : ℂ) * (z' : ℂ) := by
      rw [klein_cut_chart, if_neg hz0', hnz', hcs']
    have hxα : x = Real.cos α / (Real.cos α + Real.sin α) := by
      rw [hxdef, hchz]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzrecos]
      field_simp
      try ring
    have hyα : y = Real.sin α / (Real.cos α + Real.sin α) := by
      rw [hydef, hchz]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzimcos]
      field_simp
      try ring
    have hx'β : x' = -Real.cos β / (Real.cos β + Real.sin β) := by
      rw [hx'def, hchz']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz'recos]
      field_simp
      try ring
    have hy'β : y' = -Real.sin β / (Real.cos β + Real.sin β) := by
      rw [hy'def, hchz']
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz'imcos]
      field_simp
      try ring
    have hvalα : (Real.cos α - Real.sin α) / (Real.cos α + Real.sin α) = x - y := by
      rw [hxα, hyα, div_sub_div_same]
    have hvalβ : (Real.cos (Real.pi / 2 - β) - Real.sin (Real.pi / 2 - β)) /
        (Real.cos (Real.pi / 2 - β) + Real.sin (Real.pi / 2 - β)) = x' - y' := by
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hx'β, hy'β,
        div_sub_div_same, add_comm (Real.sin β) (Real.cos β)]
      ring
    have hpb : 0 ≤ Real.pi / 2 - β ∧ Real.pi / 2 - β ≤ Real.pi / 2 :=
      ⟨by linarith, by linarith⟩
    have hpbne : Real.cos (Real.pi / 2 - β) + Real.sin (Real.pi / 2 - β) ≠ 0 := by
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
      simpa [add_comm] using hne2
    have hπ : Real.pi / 2 - β = α :=
      t95J03_torus_bridge_aux_val_inj hpb.1 hpb.2 hαb.1 hαb.2 hpbne hne1
        (by rw [hvalα, hvalβ]
            linarith [hd])
    have hut : (u : ℝ) = 1 - (t : ℝ) := by
      have hkey : (Real.pi / 2) * ((u : ℝ) + (t : ℝ)) = Real.pi / 2 := by
        rw [mul_add]
        rw [← hβdef, ← hαdef, ← hπ]
        ring
      have hsum1 : (u : ℝ) + (t : ℝ) = 1 := by
        have h2 : (Real.pi / 2) * ((u : ℝ) + (t : ℝ)) = (Real.pi / 2) * 1 := by
          rw [hkey]
          ring
        exact mul_left_cancel₀ (by positivity : (Real.pi / 2 : ℝ) ≠ 0) h2
      linarith
    have he2 : z' = edgePoint 4 2 ⟨1 - (t : ℝ),
        by have := t.2.1; have := t.2.2; constructor <;> linarith⟩ := by
      rw [hu, show u = ⟨1 - (t : ℝ),
        by have := t.2.1; have := t.2.2; constructor <;> linarith⟩ from Subtype.ext hut]
    exact @Relation.EqvGen.rel _ (SurfaceRel true 1) z z'
      ⟨0, by norm_num, ⟨t, Or.inl ⟨by rw [ht]; try norm_num, by rw [he2]; try norm_num⟩⟩⟩

set_option maxHeartbeats 2000000 in
/-- The m = 1 core: second-coordinate offset exactly 1. -/
lemma t95J03_torus_bridge_aux_inj_caseB (z z' : Disk)
    (hA : ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im) / (2 : ℝ) =
      ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im) / 2)
    (hB : ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im) / (2 : ℝ) = 1 / 2)
    (hB' : ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im) / (2 : ℝ) = -(1 / 2)) :
    Relation.EqvGen (SurfaceRel true 1) z z' := by
  set x := (klein_cut_chart (z : ℂ)).re with hxdef
  set y := (klein_cut_chart (z : ℂ)).im with hydef
  set x' := (klein_cut_chart (z' : ℂ)).re with hx'def
  set y' := (klein_cut_chart (z' : ℂ)).im with hy'def
  have hsub : x - y = 1 := by rw [hxdef, hydef] at hB; linarith
  have hsub' : x' - y' = -1 := by rw [hx'def, hy'def] at hB'; linarith
  have hAeq : x + y = x' + y' := by rw [hxdef, hydef, hx'def, hy'def] at hA; linarith
  have hnormz : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hnormz' : ‖(z' : ℂ)‖ ≤ 1 := by
    have h := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hc0 := klein_cut_l1_chart (z : ℂ)
  unfold klein_cut_l1 at hc0
  rw [← hxdef, ← hydef] at hc0
  have hl1 : |x| + |y| ≤ 1 := by rw [hc0]; exact hnormz
  have hs : 0 ≤ x ∧ y ≤ 0 := by
    have hn : x + (-y) = 1 := by linarith
    have hl : |x| + |-y| ≤ 1 := by rw [abs_neg]; exact hl1
    obtain ⟨h1, h2⟩ := t95J03_torus_bridge_aux_signs hn hl
    exact ⟨h1, neg_nonneg.mp h2⟩
  have hl1eq : |x| + |y| = 1 := by
    rw [abs_of_nonneg hs.1, abs_of_nonpos hs.2]
    linarith
  have hnz : ‖(z : ℂ)‖ = 1 := by rw [← hc0, hl1eq]
  have hc0' := klein_cut_l1_chart (z' : ℂ)
  unfold klein_cut_l1 at hc0'
  rw [← hx'def, ← hy'def] at hc0'
  have hl1' : |x'| + |y'| ≤ 1 := by rw [hc0']; exact hnormz'
  have hs' : x' ≤ 0 ∧ 0 ≤ y' := by
    have hn : y' + (-x') = 1 := by linarith
    have hl : |y'| + |-x'| ≤ 1 := by rw [abs_neg]; linarith
    obtain ⟨h1, h2⟩ := t95J03_torus_bridge_aux_signs hn hl
    exact ⟨neg_nonneg.mp h2, h1⟩
  have hl1eq' : |x'| + |y'| = 1 := by
    rw [abs_of_nonpos hs'.1, abs_of_nonneg hs'.2]
    linarith
  have hnz' : ‖(z' : ℂ)‖ = 1 := by rw [← hc0', hl1eq']
  -- z on edge 3, z' on edge 1
  obtain ⟨c, hc0p, hcq⟩ := klein_cut_chartInv_pos (klein_cut_chart (z : ℂ))
  have hzc : (z : ℂ) = ((c : ℝ) : ℂ) * (klein_cut_chart (z : ℂ)) :=
    (klein_cut_chartInv_chart (z : ℂ)).symm.trans hcq
  have hzre : (z : ℂ).re = c * x := by
    rw [hzc]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hxdef]
  have hzim : (z : ℂ).im = c * y := by
    rw [hzc]
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hydef]
  have hcnn : 0 ≤ c := hc0p.le
  obtain ⟨t, ht⟩ := t95J03_torus_bridge_aux_edge3_of (z : ℂ) hnz
    (by rw [hzre]; exact mul_nonneg hcnn hs.1)
    (by rw [hzim]; nlinarith [mul_nonneg hcnn (neg_nonneg.mpr hs.2)])
  obtain ⟨c', hc0p', hcq'⟩ := klein_cut_chartInv_pos (klein_cut_chart (z' : ℂ))
  have hzc' : (z' : ℂ) = ((c' : ℝ) : ℂ) * (klein_cut_chart (z' : ℂ)) :=
    (klein_cut_chartInv_chart (z' : ℂ)).symm.trans hcq'
  have hzre' : (z' : ℂ).re = c' * x' := by
    rw [hzc']
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hx'def]
  have hzim' : (z' : ℂ).im = c' * y' := by
    rw [hzc']
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hy'def]
  have hcnn' : 0 ≤ c' := hc0p'.le
  obtain ⟨s, hs1⟩ := t95J03_torus_bridge_aux_edge1_of (z' : ℂ) hnz'
    (by rw [hzre']; nlinarith [mul_nonneg hcnn' (neg_nonneg.mpr hs'.1)])
    (by rw [hzim']; exact mul_nonneg hcnn' hs'.2)
  -- trigonometric parameters
  have hδb : 0 ≤ Real.pi / 2 * (t : ℝ) ∧ Real.pi / 2 * (t : ℝ) ≤ Real.pi / 2 :=
    ⟨mul_nonneg (by positivity) t.2.1, mul_le_of_le_one_right (by positivity) t.2.2⟩
  have hσb : 0 ≤ Real.pi / 2 * (s : ℝ) ∧ Real.pi / 2 * (s : ℝ) ≤ Real.pi / 2 :=
    ⟨mul_nonneg (by positivity) s.2.1, mul_le_of_le_one_right (by positivity) s.2.2⟩
  set δ : ℝ := Real.pi / 2 * (t : ℝ) with hδdef
  set σ : ℝ := Real.pi / 2 * (s : ℝ) with hσdef
  have hcδ : 0 ≤ Real.cos δ :=
    Real.cos_nonneg_of_mem_Icc ⟨by have := hδb.1; linarith [Real.pi_pos],
      by have := hδb.2; linarith [Real.pi_pos]⟩
  have hsδ : 0 ≤ Real.sin δ :=
    Real.sin_nonneg_of_mem_Icc ⟨hδb.1, by have := hδb.2; linarith [Real.pi_pos]⟩
  have hcσ : 0 ≤ Real.cos σ :=
    Real.cos_nonneg_of_mem_Icc ⟨by have := hσb.1; linarith [Real.pi_pos],
      by have := hσb.2; linarith [Real.pi_pos]⟩
  have hsσ : 0 ≤ Real.sin σ :=
    Real.sin_nonneg_of_mem_Icc ⟨hσb.1, by have := hσb.2; linarith [Real.pi_pos]⟩
  have hneδ : Real.cos δ + Real.sin δ ≠ 0 := by
    intro hh
    have h1 : Real.cos δ = 0 := by nlinarith [hcδ, hsδ, hh]
    have h2 : Real.sin δ = 0 := by nlinarith [hcδ, hsδ, hh]
    have h3 := Real.cos_sq_add_sin_sq δ
    rw [h1, h2] at h3
    norm_num at h3
  have hneσ : Real.cos σ + Real.sin σ ≠ 0 := by
    intro hh
    have h1 : Real.cos σ = 0 := by nlinarith [hcσ, hsσ, hh]
    have h2 : Real.sin σ = 0 := by nlinarith [hcσ, hsσ, hh]
    have h3 := Real.cos_sq_add_sin_sq σ
    rw [h1, h2] at h3
    norm_num at h3
  -- coordinates of z (edge 3 = I * edge 2) and z' (edge 1 = I * edge 0)
  have hw := klein_cut_edge_succ t
  have hf2 := t95J03_torus_bridge_aux_edge2_facts t
  have hz3 : (z : ℂ) = Complex.I * ((edgePoint 4 2 t : ℂ)) := by
    rw [ht]
    exact hw.2
  have hw' := klein_cut_edge_succ s
  have hf0 := t95J03_torus_bridge_aux_edge0_facts s
  have hz1' : (z' : ℂ) = Complex.I * ((edgePoint 4 0 s : ℂ)) := by
    rw [hs1]
    exact hw'.1
  have hzreδ : (z : ℂ).re = Real.sin δ := by
    rw [hz3]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, hδdef, hf2.2.2]
    push_cast
    ring
  have hzimδ : (z : ℂ).im = -Real.cos δ := by
    rw [hz3]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, hδdef, hf2.2.1]
    push_cast
    ring
  have hzre'σ : (z' : ℂ).re = -Real.sin σ := by
    rw [hz1']
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, hσdef, hf0.2.2]
    push_cast
    ring
  have hzim'σ : (z' : ℂ).im = Real.cos σ := by
    rw [hz1']
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, hσdef, hf0.2.1]
    push_cast
    ring
  have hcs : klein_cut_l1 (z : ℂ) = Real.cos δ + Real.sin δ := by
    rw [klein_cut_l1, hzreδ, hzimδ, abs_neg, abs_of_nonneg hsδ, abs_of_nonneg hcδ]
    ring
  have hcs' : klein_cut_l1 (z' : ℂ) = Real.cos σ + Real.sin σ := by
    rw [klein_cut_l1, hzre'σ, hzim'σ, abs_neg, abs_of_nonneg hsσ,
      abs_of_nonneg hcσ]
    ring
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hh
    rw [hh] at hnz
    simp at hnz
  have hz0' : (z' : ℂ) ≠ 0 := by
    intro hh
    rw [hh] at hnz'
    simp at hnz'
  have hchz : klein_cut_chart (z : ℂ) =
      ((1 / (Real.cos δ + Real.sin δ) : ℝ) : ℂ) * (z : ℂ) := by
    rw [klein_cut_chart, if_neg hz0, hnz, hcs]
  have hchz' : klein_cut_chart (z' : ℂ) =
      ((1 / (Real.cos σ + Real.sin σ) : ℝ) : ℂ) * (z' : ℂ) := by
    rw [klein_cut_chart, if_neg hz0', hnz', hcs']
  have hxδ : x = Real.sin δ / (Real.cos δ + Real.sin δ) := by
    rw [hxdef, hchz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzreδ]
    field_simp
    try ring
  have hyδ : y = -Real.cos δ / (Real.cos δ + Real.sin δ) := by
    rw [hydef, hchz]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzimδ]
    field_simp
    try ring
  have hx'σ : x' = -Real.sin σ / (Real.cos σ + Real.sin σ) := by
    rw [hx'def, hchz']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzre'σ]
    field_simp
    try ring
  have hy'σ : y' = Real.cos σ / (Real.cos σ + Real.sin σ) := by
    rw [hy'def, hchz']
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzim'σ]
    field_simp
    try ring
  have hvalδ : (Real.cos δ - Real.sin δ) / (Real.cos δ + Real.sin δ) = -(x + y) := by
    rw [hxδ, hyδ]
    field_simp
    ring
  have hvalσ : (Real.cos (Real.pi / 2 - σ) - Real.sin (Real.pi / 2 - σ)) /
      (Real.cos (Real.pi / 2 - σ) + Real.sin (Real.pi / 2 - σ)) = -(x' + y') := by
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hx'σ, hy'σ,
      add_comm (Real.sin σ) (Real.cos σ)]
    field_simp
    ring
  have hpb : 0 ≤ Real.pi / 2 - σ ∧ Real.pi / 2 - σ ≤ Real.pi / 2 :=
    ⟨by linarith, by linarith⟩
  have hpbne : Real.cos (Real.pi / 2 - σ) + Real.sin (Real.pi / 2 - σ) ≠ 0 := by
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    simpa [add_comm] using hneσ
  have hπ : Real.pi / 2 - σ = δ :=
    t95J03_torus_bridge_aux_val_inj hpb.1 hpb.2 hδb.1 hδb.2 hpbne hneδ
      (by rw [hvalδ, hvalσ]
          linarith)
  have hts : (t : ℝ) = 1 - (s : ℝ) := by
    have hkey : (Real.pi / 2) * ((t : ℝ) + (s : ℝ)) = Real.pi / 2 := by
      rw [mul_add]
      rw [← hδdef, ← hσdef, ← hπ]
      ring
    have hsum1 : (t : ℝ) + (s : ℝ) = 1 := by
      have h2 : (Real.pi / 2) * ((t : ℝ) + (s : ℝ)) = (Real.pi / 2) * 1 := by
        rw [hkey]
        ring
      exact mul_left_cancel₀ (by positivity : (Real.pi / 2 : ℝ) ≠ 0) h2
    linarith
  have hts' : t = ⟨1 - (s : ℝ),
      by have := s.2.1; have := s.2.2; constructor <;> linarith⟩ := Subtype.ext hts
  have he3 : z = edgePoint 4 3 ⟨1 - (s : ℝ),
      by have := s.2.1; have := s.2.2; constructor <;> linarith⟩ := by
    apply Subtype.ext
    rw [ht, hts']
  have res : Relation.EqvGen (SurfaceRel true 1) z' z :=
    @Relation.EqvGen.rel _ (SurfaceRel true 1) z' z
      ⟨0, by norm_num, ⟨s, Or.inr ⟨by apply Subtype.ext; rw [hs1]; try norm_num,
        by rw [he3]; try norm_num⟩⟩⟩
  exact @Relation.EqvGen.symm _ (SurfaceRel true 1) z' z res

set_option maxHeartbeats 1000000 in
lemma t95J03_torus_bridge_aux_inj_core (z z' : Disk)
    (h : t95J03_torus_bridge_aux_f (z : ℂ) = t95J03_torus_bridge_aux_f (z' : ℂ)) :
    Relation.EqvGen (SurfaceRel true 1) z z' := by
  simp only [t95J03_torus_bridge_aux_f, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨n, hn⟩ := t95J03_torus_bridge_aux_int_of_coe_eq h1
  obtain ⟨m, hm⟩ := t95J03_torus_bridge_aux_int_of_coe_eq h2
  set A := ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im) / 2 with hAdef
  set A' := ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im) / 2 with hA'def
  set B := ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im) / 2 with hBdef
  set B' := ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im) / 2 with hB'def
  have hnorm : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hnorm' : ‖(z' : ℂ)‖ ≤ 1 := by
    have h := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hsumz : |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| ≤ 1 := by
    have hc := klein_cut_l1_chart (z : ℂ)
    unfold klein_cut_l1 at hc
    linarith
  have hsumz' : |(klein_cut_chart (z' : ℂ)).re| + |(klein_cut_chart (z' : ℂ)).im| ≤ 1 := by
    have hc := klein_cut_l1_chart (z' : ℂ)
    unfold klein_cut_l1 at hc
    linarith
  have hAne : |A| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im| ≤
        |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hAdef, abs_le]
    constructor <;> nlinarith [htri, hsumz, le_abs_self ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im), neg_abs_le ((klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im)]
  have hAne' : |A'| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im| ≤
        |(klein_cut_chart (z' : ℂ)).re| + |(klein_cut_chart (z' : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z' : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z' : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z' : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z' : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hA'def, abs_le]
    constructor <;> nlinarith [htri, hsumz', le_abs_self ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im), neg_abs_le ((klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im)]
  have hBne : |B| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im| ≤
        |(klein_cut_chart (z : ℂ)).re| + |(klein_cut_chart (z : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hBdef, abs_le]
    constructor <;> nlinarith [htri, hsumz, le_abs_self ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im), neg_abs_le ((klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im)]
  have hBne' : |B'| ≤ 1 / 2 := by
    have htri : |(klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im| ≤
        |(klein_cut_chart (z' : ℂ)).re| + |(klein_cut_chart (z' : ℂ)).im| := by
      have hx := le_abs_self (klein_cut_chart (z' : ℂ)).re
      have hy := le_abs_self (klein_cut_chart (z' : ℂ)).im
      have hnx := neg_abs_le (klein_cut_chart (z' : ℂ)).re
      have hny := neg_abs_le (klein_cut_chart (z' : ℂ)).im
      rw [abs_le]
      constructor <;> linarith
    rw [hB'def, abs_le]
    constructor <;> nlinarith [htri, hsumz', le_abs_self ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im), neg_abs_le ((klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im)]
  obtain ⟨hAlo, hAhi⟩ := abs_le.1 hAne
  obtain ⟨hA'lo, hA'hi⟩ := abs_le.1 hAne'
  obtain ⟨hBlo, hBhi⟩ := abs_le.1 hBne
  obtain ⟨hB'lo, hB'hi⟩ := abs_le.1 hBne'
  have hmR : (m : ℝ) = B - B' := by push_cast; linarith
  have hnR : (n : ℝ) = A - A' := by push_cast; linarith
  have hmlo : (-(1:ℝ)) ≤ B - B' := by linarith
  have hmhi : B - B' ≤ (1:ℝ) := by linarith
  have hnlo : (-(1:ℝ)) ≤ A - A' := by linarith
  have hnhi : A - A' ≤ (1:ℝ) := by linarith
  have hmC : m = 1 ∨ m = -1 ∨ m = 0 := by
    have hc1 : ((-1:ℤ):ℝ) ≤ (m:ℝ) := by rw [hmR]; push_cast; linarith
    have hc2 : ((m:ℝ)) ≤ ((1:ℤ):ℝ) := by rw [hmR]; push_cast; linarith
    have i1 : (-1:ℤ) ≤ m := by exact_mod_cast hc1
    have i2 : m ≤ (1:ℤ) := by exact_mod_cast hc2
    omega
  have hnC : n = 1 ∨ n = -1 ∨ n = 0 := by
    have hc1 : ((-1:ℤ):ℝ) ≤ (n:ℝ) := by rw [hnR]; push_cast; linarith
    have hc2 : ((n:ℝ)) ≤ ((1:ℤ):ℝ) := by rw [hnR]; push_cast; linarith
    have i1 : (-1:ℤ) ≤ n := by exact_mod_cast hc1
    have i2 : n ≤ (1:ℤ) := by exact_mod_cast hc2
    omega
  rcases hnC with rfl | rfl | rfl
  · push_cast at hn
    norm_num at hn
    -- n = 1
    have hA1 : A = 1 / 2 := by linarith
    have hA1' : A' = -(1 / 2) := by linarith
    rw [hAdef] at hA1
    rw [hA'def] at hA1'
    rw [hBdef, hB'def] at hm
    exact t95J03_torus_bridge_aux_inj_caseA z z' m hA1 hA1' hm hmC
  · push_cast at hn
    norm_num at hn
    -- n = -1 : swap
    apply Relation.EqvGen.symm
    have hA1 : A' - A = 1 := by linarith
    have hA1' : A = -(1 / 2) := by linarith
    have hA2 : A' = 1 / 2 := by linarith
    rw [hA'def] at hA2
    rw [hAdef] at hA1'
    have hm' : B' - B = (-(m : ℤ) : ℤ) := by
      push_cast
      have := hm
      push_cast at *
      linarith
    rw [hB'def, hBdef] at hm'
    have hmc : (-m) = 1 ∨ (-m) = -1 ∨ (-m) = 0 := by omega
    exact t95J03_torus_bridge_aux_inj_caseA z' z (-m) hA2 hA1' hm' hmc
  · push_cast at hn
    norm_num at hn
    -- n = 0
    have hAeq : A = A' := by linarith
    rcases hmC with rfl | rfl | rfl
    · push_cast at hm
      norm_num at hm
      -- m = 1
      have hB1 : B = 1 / 2 := by linarith
      have hB1' : B' = -(1 / 2) := by linarith
      rw [hAdef, hA'def] at hAeq
      rw [hBdef] at hB1
      rw [hB'def] at hB1'
      exact t95J03_torus_bridge_aux_inj_caseB z z' hAeq hB1 hB1'
    · push_cast at hm
      norm_num at hm
      -- m = -1 : swap
      apply Relation.EqvGen.symm
      have hAeq' : A' = A := by linarith
      have hB1 : B' = 1 / 2 := by linarith
      have hB1' : B = -(1 / 2) := by linarith
      rw [hA'def, hAdef] at hAeq'
      rw [hB'def] at hB1
      rw [hBdef] at hB1'
      exact t95J03_torus_bridge_aux_inj_caseB z' z hAeq' hB1 hB1'
    · push_cast at hm
      norm_num at hm
      -- both zero : z = z'
      have hBeq : B = B' := by linarith
      have hre : (klein_cut_chart (z : ℂ)).re + (klein_cut_chart (z : ℂ)).im =
          (klein_cut_chart (z' : ℂ)).re + (klein_cut_chart (z' : ℂ)).im := by
        rw [hAdef, hA'def] at hAeq
        linarith
      have him : (klein_cut_chart (z : ℂ)).re - (klein_cut_chart (z : ℂ)).im =
          (klein_cut_chart (z' : ℂ)).re - (klein_cut_chart (z' : ℂ)).im := by
        rw [hBdef, hB'def] at hBeq
        linarith
      have hchart : klein_cut_chart (z : ℂ) = klein_cut_chart (z' : ℂ) := by
        have e1 : (klein_cut_chart (z : ℂ)).re = (klein_cut_chart (z' : ℂ)).re := by linarith
        have e2 : (klein_cut_chart (z : ℂ)).im = (klein_cut_chart (z' : ℂ)).im := by linarith
        exact Complex.ext e1 e2
      have hzz' : z = z' := by
        apply Subtype.ext
        have h1 : (z : ℂ) = klein_cut_chartInv (klein_cut_chart (z : ℂ)) :=
          (klein_cut_chartInv_chart _).symm
        have h2 : (z' : ℂ) = klein_cut_chartInv (klein_cut_chart (z' : ℂ)) :=
          (klein_cut_chartInv_chart _).symm
        rw [h1, h2, hchart]
      rw [hzz']
      exact Relation.EqvGen.refl z'

lemma t95J03_torus_bridge_aux_lift_injective :
    Function.Injective t95J03_torus_bridge_aux_lift := by
  intro qa qb hq
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective qa
  obtain ⟨z', rfl⟩ := Quotient.mk_surjective qb
  rw [t95J03_torus_bridge_aux_lift, Quotient.lift_mk, Quotient.lift_mk] at hq
  exact Quotient.sound (t95J03_torus_bridge_aux_inj_core z z' hq)

lemma t95J03_torus_bridge : Nonempty (Surface true 1 ≃ₜ T95J03Torus) := by
  haveI : CompactSpace (Surface true 1) := by
    have hcomp : IsCompact (Set.univ : Set (Surface true 1)) := by
      rw [← Set.range_eq_univ.2 (surjective_surfaceQuotient true 1)]
      have h := (isCompact_univ.image (continuous_surfaceQuotient true 1) :
        IsCompact (surfaceQuotient true 1 '' Set.univ))
      rwa [Set.image_univ] at h
    exact isCompact_univ_iff.mp hcomp
  have hbij : Function.Bijective t95J03_torus_bridge_aux_lift :=
    ⟨t95J03_torus_bridge_aux_lift_injective, t95J03_torus_bridge_aux_lift_surjective⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective t95J03_torus_bridge_aux_lift hbij)
    (t95J03_torus_bridge_aux_lift_continuous : Continuous
      (Equiv.ofBijective t95J03_torus_bridge_aux_lift hbij))⟩

/-- **Leaf S3 (layer 2: uses S2).**  `π₁` of the torus is commutative.

Route.  Transport along `t95J03_torus_bridge`
(`SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph`); then either
`FundamentalGroupProduct.fundamentalGroupProdMulEquiv` and `π₁(AddCircle)`
commutative (≅ ℤ via `CircleUniversalCover`/`AddCircle` covering by `ℝ`), or
Eckmann–Hilton for the topological group `T95J03Torus`.  About 60–200 lines. -/
lemma t95J03_torus_pi1_comm (x : Surface true 1)
    (a b : FundamentalGroup (Surface true 1) x) : a * b = b * a := by
  obtain ⟨h⟩ := t95J03_torus_bridge
  let τ : T95J03Torus ≃ₜ T95J03Torus := Homeomorph.addRight (-(h x))
  have hτ : τ (h x) = (0 : T95J03Torus) := by
    simp [τ]
  let e₁ := SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph h x
  let e₂ : FundamentalGroup T95J03Torus (h x) ≃*
      FundamentalGroup T95J03Torus (0 : T95J03Torus) := by
    rw [← hτ]
    exact SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph τ (h x)
  let e₃ := ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv
    (0 : UnitAddCircle) (0 : UnitAddCircle)
  let c : UnitAddCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have hc : c 0 = (1 : Circle) := by
    simp [c, AddCircle.homeomorphCircle_apply]
  let e₄ : FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ :=
    (SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph c 0).trans (by
      rw [hc]
      exact ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt)
  let e := ((e₁.trans e₂).trans e₃).trans (e₄.prodCongr e₄)
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- **Leaf S4.**  An abelian finite-index subgroup of the Klein group has even
index.

Route.  Coordinates `coordinateEquiv : PresentedKleinGroup ≃* ℤ ⋊ ℤ`
(`b` acts on `a` by inversion).  Finite index gives `a^m ∈ H` with `m ≥ 1`
(two of the cosets `a^i H`, `i ≤ index`, coincide).  If `h ∈ H` has odd
`ℤ`-coordinate, `h a^m h⁻¹ = a^{-m} ≠ a^m` (`a` has infinite order), contradicting
commutativity.  So `H ≤ ker (second coordinate mod 2)`, a subgroup of index 2,
and `index H = 2 * relindex` (`Subgroup.relindex_mul_index`).
About 100–180 lines. -/
def t95J03_klein_index_even_aux_orientation : PresentedKleinGroup →*
    MulAut ZMul :=
  (action.comp SemidirectProduct.rightHom).comp
    KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.toMonoidHom

lemma t95J03_klein_index_even_aux_inv_sq : inversion ^ 2 = 1 := by
  ext x
  change (x⁻¹)⁻¹ = x
  simp

lemma t95J03_klein_index_even_aux_A_pow_left (n : ℕ) :
    (A ^ n).left = Multiplicative.ofAdd (n : ℤ) := by
  calc
    (A ^ n).left = (SemidirectProduct.inl
        (Multiplicative.ofAdd 1 ^ n) : Coordinates).left := by
      simpa [A] using congrArg SemidirectProduct.left
        (map_pow (SemidirectProduct.inl : ZMul →* Coordinates)
          (Multiplicative.ofAdd 1) n).symm
    _ = Multiplicative.ofAdd (n : ℤ) := by
      apply Multiplicative.toAdd.injective
      rw [SemidirectProduct.left_inl, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
      simp

lemma t95J03_klein_index_even_aux_fix (z : ZMul) (n : ℕ) (hn : 0 < n)
    (hfix : action z (Multiplicative.ofAdd (n : ℤ)) = Multiplicative.ofAdd (n : ℤ)) :
    action z = 1 := by
  rcases Int.even_or_odd' (Multiplicative.toAdd z) with ⟨k, hk | hk⟩
  · rw [show action z = inversion ^ Multiplicative.toAdd z by simp [action], hk,
      zpow_mul]
    have h2 : inversion ^ (2 : ℤ) = 1 := by
      rw [zpow_ofNat]; exact t95J03_klein_index_even_aux_inv_sq
    rw [h2, one_zpow]
  · exfalso
    have hip : (inversion ^ 2) ^ k = 1 := by
      calc
        (inversion ^ 2) ^ k = (1 : MulAut ZMul) ^ k := congrArg
          (fun u : MulAut ZMul => u ^ k) t95J03_klein_index_even_aux_inv_sq
        _ = 1 := one_zpow k
    have ha : action z = inversion := by
      calc
        action z = (inversion ^ 2) ^ k * inversion := by
          simp only [show action z = inversion ^ Multiplicative.toAdd z by simp [action], hk,
            zpow_add_one, zpow_mul]
          rfl
        _ = inversion := by simpa [hip]
    rw [ha] at hfix
    have hf := congrArg Multiplicative.toAdd hfix
    simp [inversion] at hf
    omega

lemma t95J03_klein_index_even_aux_le (H : Subgroup PresentedKleinGroup)
    (hfin : H.index ≠ 0) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    H ≤ t95J03_klein_index_even_aux_orientation.ker := by
  intro h hh
  obtain ⟨n, hn, -, han⟩ := H.exists_pow_mem_of_index_ne_zero hfin generatorA
  have hc := hcomm h hh (generatorA ^ n) han
  have hc' := congrArg KleinPresentedGroupCoordinateNormalForm.coordinateEquiv hc
  have hfix : action (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv h).2
      (Multiplicative.ofAdd (n : ℤ)) = Multiplicative.ofAdd (n : ℤ) := by
    have := congrArg SemidirectProduct.left hc'
    have hapow := t95J03_klein_index_even_aux_A_pow_left n
    have hbpow : (A ^ n).right = 1 := by simp [A, ← map_pow]
    have heq : (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv h).left *
        action (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv h).right
          (Multiplicative.ofAdd (n : ℤ)) =
        Multiplicative.ofAdd (n : ℤ) *
          (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv h).left := by
      simpa [hapow, hbpow] using this
    rw [mul_comm (Multiplicative.ofAdd (n : ℤ))] at heq
    exact mul_left_cancel heq
  exact t95J03_klein_index_even_aux_fix _ n hn hfix

lemma t95J03_klein_index_even (H : Subgroup PresentedKleinGroup) (hfin : H.index ≠ 0)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : Even H.index := by
  let K := t95J03_klein_index_even_aux_orientation.ker
  have hHK : H ≤ K := t95J03_klein_index_even_aux_le H hfin hcomm
  have hindex : K.index = 2 := by
    rw [Subgroup.index_ker]
    have hrange : t95J03_klein_index_even_aux_orientation.range =
        Subgroup.zpowers inversion := by
      rw [← Subgroup.range_zpowersHom]
      apply le_antisymm
      · rintro x ⟨g, rfl⟩
        refine ⟨(KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).2, ?_⟩
        change action (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).right =
          t95J03_klein_index_even_aux_orientation g
        rw [show t95J03_klein_index_even_aux_orientation g =
          action (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g).right by rfl]
      · rintro x ⟨z, rfl⟩
        refine ⟨KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
          (SemidirectProduct.inr z), ?_⟩
        rw [show t95J03_klein_index_even_aux_orientation
          (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
            (SemidirectProduct.inr z)) = action z by simp [t95J03_klein_index_even_aux_orientation]]
        simp [action]
    rw [hrange, Nat.card_zpowers]
    apply orderOf_eq_prime
    · ext z
      change (z⁻¹)⁻¹ = z
      simp
    · intro heq
      have := DFunLike.congr_fun heq (Multiplicative.ofAdd (1 : ℤ))
      have := congrArg Multiplicative.toAdd this
      norm_num [inversion] at this
  rw [← H.relIndex_mul_index hHK, hindex]
  exact ⟨H.relIndex K, by omega⟩

/-- **Leaf S5.**  `(x, y) ↦ (n x, y)` is an `n`-sheeted cover of the torus
(same as t98A01's `t98A01_torusFive_isNfoldCover` with `5 → n`).

Route.  `AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero`,
`ProductEvenlyCoveredTrivialization.isCoveringMap_productMap` with the identity;
fibres are cosets of the `n`-torsion `{j/n}`.  About 60–150 lines. -/
lemma t95J03_torusNsmul_isKSheeted_aux_id :
    IsCoveringMap (id : UnitAddCircle → UnitAddCircle) := by
  intro x
  letI : Subsingleton ((id : UnitAddCircle → UnitAddCircle) ⁻¹' {x}) :=
    ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  refine ⟨inferInstance, Set.univ, Set.mem_univ x, isOpen_univ, isOpen_univ, ?_, ?_⟩
  · exact
      { toFun := fun z ↦ (⟨z.1, Set.mem_univ _⟩, ⟨x, rfl⟩)
        invFun := fun z ↦ ⟨z.1.1, Set.mem_univ _⟩
        left_inv := fun _ ↦ rfl
        right_inv := by
          intro z
          apply Prod.ext
          · rfl
          · exact Subsingleton.elim _ _
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
  · intro z
    rfl

noncomputable def t95J03_torusNsmul_isKSheeted_aux_kernel_equiv (n : ℕ) (hn : 0 < n) :
    Fin n ≃ (nsmulAddMonoidHom (α := UnitAddCircle) n).ker := by
  let f : Fin n → (nsmulAddMonoidHom (α := UnitAddCircle) n).ker := fun j ↦
    ⟨((j : ℝ) / (n : ℝ) : UnitAddCircle), (AddCircle.nsmul_eq_zero_iff hn).2
      ⟨j, j.isLt, by simp⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      have hc : ((i : ℝ) / (n : ℝ) : UnitAddCircle) =
          ((j : ℝ) / (n : ℝ) : UnitAddCircle) :=
        congrArg Subtype.val hij
      have hi : (i : ℝ) / n ∈ Set.Ico (0 : ℝ) (0 + 1) := by
        constructor
        · positivity
        · simpa using (div_lt_one (by positivity : (0 : ℝ) < n)).2 (by exact_mod_cast i.isLt)
      have hj : (j : ℝ) / n ∈ Set.Ico (0 : ℝ) (0 + 1) := by
        constructor
        · positivity
        · simpa using (div_lt_one (by positivity : (0 : ℝ) < n)).2 (by exact_mod_cast j.isLt)
      have hr := (AddCircle.coe_eq_coe_iff_of_mem_Ico hi hj).1 hc
      exact_mod_cast ((div_left_inj' (by positivity : (n : ℝ) ≠ 0)).mp hr)
    · intro k
      obtain ⟨m, hm, hmk⟩ := (AddCircle.nsmul_eq_zero_iff hn).1 k.2
      refine ⟨⟨m, hm⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using hmk
  exact Equiv.ofBijective f hf

lemma t95J03_torusNsmul_isKSheeted_aux_kernel_card (n : ℕ) (hn : 0 < n) :
    Nat.card ((nsmulAddMonoidHom (α := UnitAddCircle) n).ker) = n := by
  rw [← Nat.card_congr (t95J03_torusNsmul_isKSheeted_aux_kernel_equiv n hn), Nat.card_fin]

lemma t95J03_torusNsmul_isKSheeted_aux_product {f : UnitAddCircle → UnitAddCircle}
    (hf : IsCoveringMap f) : IsCoveringMap (fun x : T95J03Torus ↦ (f x.1, x.2)) := by
  rintro ⟨x, y⟩
  rcases hf x with ⟨hdiscI, U, hxU, hU, hfU, Hf, hHf⟩
  rcases t95J03_torusNsmul_isKSheeted_aux_id y with
    ⟨hdiscJ, V, hyV, hV, hgV, Hg, hHg⟩
  letI : DiscreteTopology (f ⁻¹' {x}) := hdiscI
  letI : DiscreteTopology ((id : UnitAddCircle → UnitAddCircle) ⁻¹' {y}) := hdiscJ
  have h : IsEvenlyCovered (fun z : T95J03Torus ↦ (f z.1, z.2)) (x, y)
      ((f ⁻¹' {x}) × ((id : UnitAddCircle → UnitAddCircle) ⁻¹' {y})) := by
    refine ⟨inferInstance, U ×ˢ V, ⟨hxU, hyV⟩, hU.prod hV, ?_, ?_, ?_⟩
    · simpa using hfU.prod hgV
    · exact
        { toFun := fun p ↦
            (⟨((Hf ⟨p.1.1, p.2.1⟩).1.1, (Hg ⟨p.1.2, p.2.2⟩).1.1),
               (Hf ⟨p.1.1, p.2.1⟩).1.2, (Hg ⟨p.1.2, p.2.2⟩).1.2⟩,
             ((Hf ⟨p.1.1, p.2.1⟩).2, (Hg ⟨p.1.2, p.2.2⟩).2))
          invFun := fun q ↦
            ⟨((Hf.symm (⟨q.1.1.1, q.1.2.1⟩, q.2.1)).1,
               (Hg.symm (⟨q.1.1.2, q.1.2.2⟩, q.2.2)).1), by
              exact ⟨(Hf.symm (⟨q.1.1.1, q.1.2.1⟩, q.2.1)).2,
                (Hg.symm (⟨q.1.1.2, q.1.2.2⟩, q.2.2)).2⟩⟩
          left_inv := by
            intro p
            apply Subtype.ext
            exact Prod.ext
              (congrArg Subtype.val (Hf.symm_apply_apply ⟨p.1.1, p.2.1⟩))
              (congrArg Subtype.val (Hg.symm_apply_apply ⟨p.1.2, p.2.2⟩))
          right_inv := by
            intro q
            apply Prod.ext
            · apply Subtype.ext
              exact Prod.ext
                (congrArg (fun z ↦ z.1.1) (Hf.apply_symm_apply _))
                (congrArg (fun z ↦ z.1.1) (Hg.apply_symm_apply _))
            · exact Prod.ext
                (congrArg (fun z ↦ z.2) (Hf.apply_symm_apply _))
                (congrArg (fun z ↦ z.2) (Hg.apply_symm_apply _))
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
    · intro p
      exact Prod.ext (hHf ⟨p.1.1, p.2.1⟩) (hHg ⟨p.1.2, p.2.2⟩)
  let H : (f ⁻¹' {x}) × ((id : UnitAddCircle → UnitAddCircle) ⁻¹' {y}) ≃ₜ
      (fun z : T95J03Torus ↦ (f z.1, z.2)) ⁻¹' {(x, y)} :=
    { toFun := fun p ↦ ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
      invFun := fun p ↦
        (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact h.of_fiber_homeomorph H

lemma t95J03_torusNsmul_isKSheeted (n : ℕ) (hn : 0 < n) :
    IsKSheetedCover (fun x : T95J03Torus => (n • x.1, x.2)) n := by
  letI : NeZero n := ⟨hn.ne'⟩
  let hc := AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) n
  constructor
  · exact t95J03_torusNsmul_isKSheeted_aux_product hc.isCoveringMap
  · intro b
    let ek : (nsmulAddMonoidHom (α := UnitAddCircle) n).ker ≃
        {e : T95J03Torus // (n • e.1, e.2) = b} := by
      let a₀ := (hc.surjective b.1).choose
      have ha₀ := (hc.surjective b.1).choose_spec
      change n • a₀ = b.1 at ha₀
      exact
        { toFun := fun k ↦ ⟨(k.1 + a₀, b.2), by
            apply Prod.ext
            · change n • (k.1 + a₀) = b.1
              have hk : n • k.1 = 0 := k.2
              rw [nsmul_add, hk, ha₀, zero_add]
            · rfl⟩
          invFun := fun x ↦ ⟨x.1.1 - a₀, by
            change n • (x.1.1 - a₀) = 0
            rw [nsmul_sub, ha₀]
            have hx := congrArg Prod.fst x.2
            change n • x.1.1 = b.1 at hx
            rw [hx, sub_self]⟩
          left_inv := by intro k; apply Subtype.ext; exact add_sub_cancel_right k.1 a₀
          right_inv := by
            intro x
            apply Subtype.ext
            exact Prod.ext (sub_add_cancel x.1.1 a₀) (congrArg Prod.snd x.2).symm }
    have hkfin : Finite ((nsmulAddMonoidHom (α := UnitAddCircle) n).ker) :=
      Finite.of_equiv (Fin n) (t95J03_torusNsmul_isKSheeted_aux_kernel_equiv n hn)
    letI := hkfin
    exact Finite.of_equiv _ ek
  · intro b
    obtain ⟨a₀, ha₀⟩ := hc.surjective b.1
    change n • a₀ = b.1 at ha₀
    let e : {x : T95J03Torus // (n • x.1, x.2) = b} ≃
        (nsmulAddMonoidHom (α := UnitAddCircle) n).ker :=
      { toFun := fun x ↦ ⟨x.1.1 - a₀, by
          change n • (x.1.1 - a₀) = 0
          rw [nsmul_sub, ha₀]
          have hx := congrArg Prod.fst x.2
          change n • x.1.1 = b.1 at hx
          rw [hx, sub_self]⟩
        invFun := fun k ↦ ⟨(k.1 + a₀, b.2), by
          have hk : n • k.1 = 0 := k.2
          apply Prod.ext
          · change n • (k.1 + a₀) = b.1
            rw [nsmul_add, hk, ha₀, zero_add]
          · rfl⟩
        left_inv := by
          intro x
          apply Subtype.ext
          exact Prod.ext (sub_add_cancel x.1.1 a₀) (congrArg Prod.snd x.2).symm
        right_inv := by
          intro k
          apply Subtype.ext
          exact add_sub_cancel_right k.1 a₀ }
    rw [Nat.card_congr e]
    exact t95J03_torusNsmul_isKSheeted_aux_kernel_card n hn

/-! Banked from lemma-1's S6 partial (2026-10-18). -/
noncomputable def t95J03_klein_doubleCover_aux_tau :
    T95J03Torus → T95J03Torus :=
  fun x => (-x.1, x.2 + (1 / 2 : ℝ))

lemma t95J03_klein_doubleCover_aux_tau_sq (x : T95J03Torus) :
    t95J03_klein_doubleCover_aux_tau
      (t95J03_klein_doubleCover_aux_tau x) = x := by
  apply Prod.ext
  · simp [t95J03_klein_doubleCover_aux_tau]
  · change x.2 + (1 / 2 : ℝ) + (1 / 2 : ℝ) = x.2
    have hh : ((1 / 2 : ℝ) : UnitAddCircle) + ((1 / 2 : ℝ) : UnitAddCircle) = 0 := by
      rw [← AddCircle.coe_add]; norm_num
    rw [add_assoc, hh, add_zero]

lemma t95J03_klein_doubleCover_aux_tau_ne (x : T95J03Torus) :
    t95J03_klein_doubleCover_aux_tau x ≠ x := by
  intro h
  have h2 := congrArg Prod.snd h
  change x.2 + (1 / 2 : ℝ) = x.2 at h2
  have hz : ((1 / 2 : ℝ) : UnitAddCircle) = 0 := by
    simpa using congrArg (fun y => -x.2 + y) h2
  rw [QuotientAddGroup.eq_zero_iff] at hz
  obtain ⟨z, hz⟩ := hz
  have : (1 / 2 : ℝ) = (z : ℝ) := by simpa using hz.symm
  have : (2 : ℤ) * z = 1 := by exact_mod_cast (show (2 : ℝ) * (z : ℝ) = 1 by linarith)
  omega

lemma t95J03_klein_doubleCover_aux_tau_continuous :
    Continuous t95J03_klein_doubleCover_aux_tau := by
  unfold t95J03_klein_doubleCover_aux_tau
  fun_prop

/-- **Leaf S6a (split 2026-10-18).**  A continuous fixed-point-free involution of
a Hausdorff space gives a 2-sheeted covering onto its orbit quotient.

Route.  Separate `x` and `τ x` by disjoint opens `U ∋ x`, `V ∋ τ x`; then
`W = U ∩ τ⁻¹ V` satisfies `W ∩ τ W = ∅`.  The quotient map is open (the
saturation of an open `O` is `O ∪ τ⁻¹ O`, `τ` being a homeomorphism, its own
inverse), so `W` is evenly covered by `W ⊔ τ W`.  The fibre over `[x]` is
`{x, τ x}`, two distinct points; `EqvGen` of `y = τ x` relates exactly
`y = x ∨ y = τ x` because `τ` is an involution.  About 80–160 lines. -/
lemma t95J03_klein_doubleCover_aux_involution_cover {X : Type*} [TopologicalSpace X]
    [T2Space X] (τ : X → X) (hτ : Continuous τ) (hinv : ∀ x, τ (τ x) = x)
    (hfree : ∀ x, τ x ≠ x) :
    IsKSheetedCover (Quotient.mk (Relation.EqvGen.setoid fun x y : X => y = τ x)) 2 := by
  sorry

/-- **Leaf S6b (split 2026-10-18).**  The torus maps onto the Klein plane
quotient with fibres exactly the `τ`-orbits.

Route.  `f (u, v) = [(ũ, 2 ṽ)]` for lifts `ũ, ṽ ∈ ℝ`: well defined because
`(ũ + 1, 2ṽ)` and `(ũ, 2ṽ + 2)` lie in the same orbit (the generators `a`
and `b²`).  Continuity: lift through `ℝ × ℝ → T95J03Torus` (a quotient map,
product of `AddCircle` quotient maps, open).  Surjective: `[(x, y)] = f (x, y/2)`.
`f (τ z) = f z` since `(-ũ, 2ṽ + 1)` is the image under `b`.  Conversely
`f z = f w` means `(ũ', 2ṽ') = (m + (-1)ⁿ ũ, n + 2ṽ)`; `n` even gives `w = z`,
`n` odd gives `w = τ z`.  Use `KleinPresentedGroupCoordinateModel` for the
action formula.  About 100–200 lines. -/
-- BEGIN SEAT AREA
-- exploratory helpers
noncomputable def t95J03_klein_doubleCover_aux_planeMap_aux_raw (p : ℝ × ℝ) :
    ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient :=
  Quotient.mk'' (p.1, 2 * p.2)

lemma t95J03_klein_doubleCover_aux_planeMap_aux_action_even (k : ℤ) :
    KleinPresentedGroupCoordinateModel.action (Multiplicative.ofAdd (2 * k))
      (Multiplicative.ofAdd 1) = Multiplicative.ofAdd 1 := by
  change (KleinPresentedGroupCoordinateModel.inversion ^ (2 * k))
    (Multiplicative.ofAdd 1) = Multiplicative.ofAdd 1
  rw [zpow_mul]
  have hi : KleinPresentedGroupCoordinateModel.inversion ^ (2 : ℤ) = 1 := by
    ext z
    change z⁻¹⁻¹ = z
    simp
  rw [hi, one_zpow]
  rfl

lemma t95J03_klein_doubleCover_aux_planeMap_aux_action_odd (k : ℤ) :
    KleinPresentedGroupCoordinateModel.action (Multiplicative.ofAdd (2 * k + 1))
      (Multiplicative.ofAdd 1) = Multiplicative.ofAdd (-1) := by
  rw [show Multiplicative.ofAdd (2 * k + 1) =
      Multiplicative.ofAdd (2 * k) * Multiplicative.ofAdd 1 by simp]
  rw [map_mul]
  change KleinPresentedGroupCoordinateModel.action (Multiplicative.ofAdd (2 * k))
    (KleinPresentedGroupCoordinateModel.action (Multiplicative.ofAdd 1)
      (Multiplicative.ofAdd 1)) = _
  rw [KleinPresentedGroupCoordinateModel.action_one, map_inv,
    t95J03_klein_doubleCover_aux_planeMap_aux_action_even]
  rfl

lemma t95J03_klein_doubleCover_aux_planeMap_aux_raw_eq (p q : ℝ × ℝ) :
    t95J03_klein_doubleCover_aux_planeMap_aux_raw p =
        t95J03_klein_doubleCover_aux_planeMap_aux_raw q ↔
      ∃ m n : ℤ, 2 * p.2 = (n : ℝ) + 2 * q.2 ∧
        p.1 = (m : ℝ) +
          ((Multiplicative.toAdd (KleinPresentedGroupCoordinateModel.action
            (Multiplicative.ofAdd n) (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * q.1 := by
  rw [t95J03_klein_doubleCover_aux_planeMap_aux_raw,
    t95J03_klein_doubleCover_aux_planeMap_aux_raw, Quotient.eq'',
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    let c := KleinPresentedGroupCoordinateNormalForm.coordinateEquiv g
    change KleinPlaneAffineAction.coordinateAct c (q.1, 2 * q.2) =
      (p.1, 2 * p.2) at hg
    refine ⟨Multiplicative.toAdd c.1, Multiplicative.toAdd c.2, ?_, ?_⟩
    · simpa [KleinPlaneAffineAction.coordinateAct] using (congrArg Prod.snd hg).symm
    · simpa [KleinPlaneAffineAction.coordinateAct] using (congrArg Prod.fst hg).symm
  · rintro ⟨m, n, hy, hx⟩
    refine ⟨KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm
      ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd n⟩, ?_⟩
    change KleinPlaneAffineAction.coordinateAct
      (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv
        (KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.symm _))
      (q.1, 2 * q.2) = (p.1, 2 * p.2)
    rw [KleinPresentedGroupCoordinateNormalForm.coordinateEquiv.apply_symm_apply]
    ext <;> simp [KleinPlaneAffineAction.coordinateAct]
    · exact hx.symm
    · exact hy.symm

noncomputable def t95J03_klein_doubleCover_aux_planeMap_aux_y (x : ℝ) :
    UnitAddCircle → ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient :=
  Quotient.lift (fun y : ℝ => t95J03_klein_doubleCover_aux_planeMap_aux_raw (x, y)) (by
    intro y y' h
    have hc : (y : UnitAddCircle) = (y' : UnitAddCircle) := Quotient.sound h
    obtain ⟨k, hk⟩ := t95J03_torus_bridge_aux_int_of_coe_eq hc
    apply (t95J03_klein_doubleCover_aux_planeMap_aux_raw_eq (x, y) (x, y')).2
    refine ⟨0, 2 * k, ?_, ?_⟩
    · push_cast; linarith
    · rw [t95J03_klein_doubleCover_aux_planeMap_aux_action_even]
      simp)

lemma t95J03_klein_doubleCover_aux_planeMap_aux_y_coe (x y : ℝ) :
    t95J03_klein_doubleCover_aux_planeMap_aux_y x (y : UnitAddCircle) =
      t95J03_klein_doubleCover_aux_planeMap_aux_raw (x, y) := rfl

noncomputable def t95J03_klein_doubleCover_aux_planeMap_aux_f :
    T95J03Torus → ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient :=
  fun z => (Quotient.lift (fun x : ℝ => t95J03_klein_doubleCover_aux_planeMap_aux_y x) (by
    intro x x' h
    funext y
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      have hc : (x : UnitAddCircle) = (x' : UnitAddCircle) := Quotient.sound h
      obtain ⟨k, hk⟩ := t95J03_torus_bridge_aux_int_of_coe_eq hc
      change t95J03_klein_doubleCover_aux_planeMap_aux_y x (y : UnitAddCircle) =
        t95J03_klein_doubleCover_aux_planeMap_aux_y x' (y : UnitAddCircle)
      rw [t95J03_klein_doubleCover_aux_planeMap_aux_y_coe,
        t95J03_klein_doubleCover_aux_planeMap_aux_y_coe]
      apply (t95J03_klein_doubleCover_aux_planeMap_aux_raw_eq (x, y) (x', y)).2
      refine ⟨k, 0, by norm_num, ?_⟩
      simp [KleinPresentedGroupCoordinateModel.action,
        KleinPresentedGroupCoordinateModel.inversion]
      linarith)) z.1 z.2

lemma t95J03_klein_doubleCover_aux_planeMap_aux_f_coe (x y : ℝ) :
    t95J03_klein_doubleCover_aux_planeMap_aux_f
      ((x : UnitAddCircle), (y : UnitAddCircle)) =
      t95J03_klein_doubleCover_aux_planeMap_aux_raw (x, y) := rfl

lemma t95J03_klein_doubleCover_aux_planeMap :
    ∃ f : T95J03Torus → ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient, Continuous f ∧ Function.Surjective f ∧
      ∀ z w, f z = f w ↔ (w = z ∨ w = t95J03_klein_doubleCover_aux_tau z) := by
  refine ⟨t95J03_klein_doubleCover_aux_planeMap_aux_f, ?_, ?_, ?_⟩
  · let π : ℝ → UnitAddCircle := fun x => (x : UnitAddCircle)
    have hq : Topology.IsQuotientMap (Prod.map π π) :=
      (QuotientAddGroup.isOpenQuotientMap_mk.prodMap
        QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap
    rw [hq.continuous_iff]
    have hr : Continuous t95J03_klein_doubleCover_aux_planeMap_aux_raw :=
      continuous_quotient_mk'.comp
        (continuous_fst.prodMk (continuous_const.mul continuous_snd))
    convert hr using 1
  · intro a
    induction a using Quotient.inductionOn' with
    | _ p =>
      refine ⟨((p.1 : UnitAddCircle), ((p.2 / 2 : ℝ) : UnitAddCircle)), ?_⟩
      rw [t95J03_klein_doubleCover_aux_planeMap_aux_f_coe]
      unfold t95J03_klein_doubleCover_aux_planeMap_aux_raw
      congr 1
      apply Prod.ext
      · simp
      · dsimp; ring
  · rintro ⟨zx, zy⟩ ⟨wx, wy⟩
    induction zx using QuotientAddGroup.induction_on with
    | _ x =>
      induction zy using QuotientAddGroup.induction_on with
      | _ y =>
        induction wx using QuotientAddGroup.induction_on with
        | _ u =>
          induction wy using QuotientAddGroup.induction_on with
          | _ v =>
            rw [t95J03_klein_doubleCover_aux_planeMap_aux_f_coe,
              t95J03_klein_doubleCover_aux_planeMap_aux_f_coe]
            constructor
            · intro h
              obtain ⟨m, n, hy, hx⟩ :=
                (t95J03_klein_doubleCover_aux_planeMap_aux_raw_eq (x, y) (u, v)).1 h
              obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
              · left
                apply Prod.ext
                · apply t95J03_torus_bridge_aux_coe_eq_of_int (n := -m)
                  rw [t95J03_klein_doubleCover_aux_planeMap_aux_action_even] at hx
                  simp at hx
                  push_cast
                  linarith
                · apply t95J03_torus_bridge_aux_coe_eq_of_int (n := -k)
                  push_cast at hy
                  push_cast
                  linarith
              · right
                apply Prod.ext
                · change (u : UnitAddCircle) = (-x : UnitAddCircle)
                  apply t95J03_torus_bridge_aux_coe_eq_of_int (n := m)
                  rw [t95J03_klein_doubleCover_aux_planeMap_aux_action_odd] at hx
                  simp at hx
                  linarith
                · change (v : UnitAddCircle) =
                    (y : UnitAddCircle) + ((1 / 2 : ℝ) : UnitAddCircle)
                  rw [← AddCircle.coe_add]
                  apply t95J03_torus_bridge_aux_coe_eq_of_int (n := -k - 1)
                  push_cast at hy
                  push_cast
                  linarith
            · rintro (h | h)
              · rw [← t95J03_klein_doubleCover_aux_planeMap_aux_f_coe,
                  ← t95J03_klein_doubleCover_aux_planeMap_aux_f_coe]
                exact congrArg t95J03_klein_doubleCover_aux_planeMap_aux_f h.symm
              · have h1 := congrArg Prod.fst h
                have h2 := congrArg Prod.snd h
                change (u : UnitAddCircle) = (-x : UnitAddCircle) at h1
                change (v : UnitAddCircle) =
                  (y : UnitAddCircle) + ((1 / 2 : ℝ) : UnitAddCircle) at h2
                obtain ⟨m, hm⟩ := t95J03_torus_bridge_aux_int_of_coe_eq h1
                rw [← AddCircle.coe_add] at h2
                obtain ⟨k, hk⟩ := t95J03_torus_bridge_aux_int_of_coe_eq h2
                apply (t95J03_klein_doubleCover_aux_planeMap_aux_raw_eq
                  (x, y) (u, v)).2
                refine ⟨m, -2 * k - 1, ?_, ?_⟩
                · push_cast; linarith
                · have ha : -2 * k - 1 = 2 * (-k - 1) + 1 := by ring
                  rw [ha, t95J03_klein_doubleCover_aux_planeMap_aux_action_odd]
                  simp
                  linarith
-- END SEAT AREA

/-- **Leaf S6c (split 2026-10-18).**  A continuous surjection from a compact
space onto a Hausdorff space, whose fibres are the `τ`-orbits, induces a
homeomorphism from the orbit quotient.

Route.  `f` is constant on `EqvGen`-classes (each generator step is in a
fibre), so it descends to `Quotient.lift`; injective by `hfib`; continuous by
`continuous_quot_lift`; the quotient of a compact space is compact; use
`Continuous.homeoOfEquivCompactToT2`.  About 30–70 lines. -/
lemma t95J03_klein_doubleCover_aux_quotient_homeomorph {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (τ : X → X) (f : X → Y) (hf : Continuous f) (hs : Function.Surjective f)
    (hfib : ∀ z w, f z = f w ↔ (w = z ∨ w = τ z)) :
    Nonempty (Quotient (Relation.EqvGen.setoid fun x y : X => y = τ x) ≃ₜ Y) := by
  let r : X → X → Prop := fun x y => y = τ x
  have hrespect : ∀ x y, Relation.EqvGen r x y → f x = f y := by
    intro x y hxy
    induction hxy with
    | rel x y h => exact (hfib x y).2 (Or.inr h)
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  let g : Quotient (Relation.EqvGen.setoid r) → Y :=
    Quotient.lift f hrespect
  have hg_cont : Continuous g := continuous_quot_lift hrespect hf
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨Quotient.mk _ x, rfl⟩
  have hg_inj : Function.Injective g := by
    intro q q' hqq'
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective q'
    change f x = f y at hqq'
    rcases (hfib x y).1 hqq' with h | h
    · simpa [h]
    · exact Quotient.sound (Relation.EqvGen.rel x y h)
  have hg_bij : Function.Bijective g := ⟨hg_inj, hg_surj⟩
  letI : CompactSpace (Quotient (Relation.EqvGen.setoid r)) := by
    apply isCompact_univ_iff.mp
    rw [← Set.range_eq_univ.2 Quotient.mk_surjective]
    simpa only [Set.image_univ] using
      (isCompact_univ.image
        (continuous_quotient_mk' (s := Relation.EqvGen.setoid r)))
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective g hg_bij)
    (show Continuous (Equiv.ofBijective g hg_bij) from hg_cont)⟩

/-- **Leaf S6.**  The torus double-covers the Klein bottle.

Route.  Use `KleinBottlePiOne.kleinPlaneQuotient_homeomorph :
KleinPlaneQuotient ≃ₜ KleinBottle` (orbit space of `ℝ²` under
`(m, n) • (x, y) = (m + (-1)ⁿ x, n + y)`).  The subgroup of even `n` acts by the
translations `ℤ × 2ℤ`; define `T95J03Torus → KleinPlaneQuotient`,
`(u, v) ↦ [(ũ, 2 ṽ)]` (well defined: `a` and `b²`).  It is the quotient of the
torus by the free involution `τ (u, v) = (-u, v + 1/2)` (image of `b`), hence a
2-sheeted covering (finite free action on a Hausdorff space:
`isCoveringMap_quotientMk_of_properlyDiscontinuousSMul`), and the induced map
`T95J03Torus ⧸ τ → KleinPlaneQuotient` is a continuous bijection compact → T2.
Fibre `{(u, v), τ(u, v)}`, distinct.  150–350 lines. -/
lemma t95J03_klein_doubleCover :
    ∃ π : T95J03Torus → Surface false 2, IsKSheetedCover π 2 := by
  obtain ⟨f, hfc, hfs, hfib⟩ := t95J03_klein_doubleCover_aux_planeMap
  letI : ContinuousConstSMul KleinPresentedGroupCoordinateModel.PresentedKleinGroup (ℝ × ℝ) :=
    ⟨ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_pi1_origin_aux_continuous⟩
  letI : ProperlyDiscontinuousSMul KleinPresentedGroupCoordinateModel.PresentedKleinGroup
      (ℝ × ℝ) :=
    ⟨fun hK hL =>
      ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_pi1_origin_aux_finite_actors hK hL⟩
  letI : T2Space ConstructionTargets.KleinBottlePiOne.KleinPlaneQuotient :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
      (Γ := KleinPresentedGroupCoordinateModel.PresentedKleinGroup) (T := ℝ × ℝ)
  obtain ⟨e⟩ := t95J03_klein_doubleCover_aux_quotient_homeomorph
    t95J03_klein_doubleCover_aux_tau f hfc hfs hfib
  obtain ⟨k⟩ := ConstructionTargets.KleinBottlePiOne.kleinPlaneQuotient_homeomorph
  have hc := t95J03_klein_doubleCover_aux_involution_cover t95J03_klein_doubleCover_aux_tau
    t95J03_klein_doubleCover_aux_tau_continuous t95J03_klein_doubleCover_aux_tau_sq
    t95J03_klein_doubleCover_aux_tau_ne
  exact ⟨_, t95J03_homeomorph_comp_isKSheeted hc (e.trans k)⟩

/-! ## Assemblies -/

theorem t95J03_isKSheeted_of_kfold {k : ℕ} (hk : 0 < k) {E X : TopCat.{0}} {p : E → X}
    (h : T95J03IsKFoldCover k E X p) : IsKSheetedCover p k where
  isCoveringMap := h.1
  finite_fiber b := Nat.finite_of_card_ne_zero (by rw [h.2 b]; omega)
  card_fiber b := h.2 b

theorem t95J03_kfold_of_isKSheeted {k : ℕ} {E X : TopCat.{0}} {p : E → X}
    (h : IsKSheetedCover p k) : T95J03IsKFoldCover k E X p :=
  ⟨h.isCoveringMap, h.card_fiber⟩

/-- `π₁(E, e)` is a subgroup of `π₁(X, p e)` of index the component's sheets. -/
theorem t95J03_pi1_subgroup {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) (e : E) :
    ∃ H : Subgroup (FundamentalGroup X (p e)),
      H.index = Nat.card (ComponentFiber p e) ∧ Nonempty (FundamentalGroup E e ≃* H) :=
  ⟨_, (t95J03_componentFiberCard_eq_index cov e).symm,
    ⟨MonoidHom.ofInjective (coveringInducedFundamentalGroupMap_injective cov e)⟩⟩

/-- Rank bounds transported through a one-relator presentation. -/
theorem t95J03_b1_bounds {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ} (hn : 0 < n)
    (r : FreeGroup (Fin n))
    (eX : FundamentalGroup X x ≃* FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _))
    (H : Subgroup (FundamentalGroup X x)) {d : ℕ} (hd : 0 < d) (hH : H.index = d) :
    (n - 1) * d + 1 ≤ b1 H + d ∧
      ((∃ φ : Additive (FreeGroup (Fin n)) →+ ℚ, φ (Additive.ofMul r) ≠ 0) →
        b1 H + 1 ≤ (n - 1) * d + 1) := by
  let G' := FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))
  let H' : Subgroup G' := H.map (eX : FundamentalGroup X x →* G')
  have hidx : H'.index = d := (Subgroup.index_map_equiv H eX).trans hH
  have hb : b1 H = b1 H' := b1_congr (H.equivMapOfInjective _ eX.injective)
  rw [hb]
  exact b1_finiteIndex_bounds n d hn hd r H' hidx

theorem t95J03_orientable_presentation (g : ℕ) (hg : 0 < g) (x : Surface true g) :
    ∃ r : FreeGroup (Fin (2 * g)),
      Nonempty (FundamentalGroup (Surface true g) x ≃*
        FreeGroup (Fin (2 * g)) ⧸ Subgroup.normalClosure ({r} : Set _)) := by
  let P := standardPairingData true g hg
  let h := standardPairingData_space_homeomorph true g hg
  have hcard := t95J03_orientable_data_card g hg
  obtain ⟨r, ⟨eP⟩, -⟩ := polygon_presentation P (h.symm x)
  let c : FreeGroup (Fin (Nat.card (PairingOrbit P.pair))) ≃* FreeGroup (Fin (2 * g)) :=
    FreeGroup.freeGroupCongr (finCongr hcard)
  refine ⟨c r, ⟨?_⟩⟩
  have hx : h (h.symm x) = x := h.apply_symm_apply x
  exact ((SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph h.symm x).trans eP).trans
    (quotientSingletonCongr c r)

/-- Against the Klein bottle: `1 ≤ b₁(π₁(E, e)) ≤` the sheets of `e`'s component. -/
theorem t95J03_klein_side {E : Type*} [TopologicalSpace E] {q : E → Surface false 2} {k : ℕ}
    (hq : IsKSheetedCover q k) (e : E) :
    1 ≤ b1 (FundamentalGroup E e) ∧
      b1 (FundamentalGroup E e) ≤ Nat.card (ComponentFiber q e) := by
  obtain ⟨H, hH, ⟨eH⟩⟩ := t95J03_pi1_subgroup hq.isCoveringMap e
  obtain ⟨r, ⟨eK⟩, hr⟩ := surface_presentation 2 (by norm_num) (q e)
  have hd := componentFiberCard_pos hq e
  obtain ⟨hlow, hup⟩ := t95J03_b1_bounds (by norm_num) r eK H hd hH
  have hup' := hup hr
  rw [b1_congr eH]
  constructor <;> omega

/-- Against a surface with an `n`-generator one-relator group:
`(n - 2) d + 1 ≤ b₁(π₁(E, e))`. -/
theorem t95J03_base_side {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} {k n : ℕ} (hp : IsKSheetedCover p k) (hn : 0 < n) (e : E)
    (hpres : ∃ r : FreeGroup (Fin n), Nonempty (FundamentalGroup X (p e) ≃*
        FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _))) :
    (n - 1) * Nat.card (ComponentFiber p e) + 1 ≤
      b1 (FundamentalGroup E e) + Nat.card (ComponentFiber p e) := by
  obtain ⟨H, hH, ⟨eH⟩⟩ := t95J03_pi1_subgroup hp.isCoveringMap e
  obtain ⟨r, ⟨eX⟩⟩ := hpres
  rw [b1_congr eH]
  exact (t95J03_b1_bounds hn r eX H (componentFiberCard_pos hp e) hH).1

/-- Excluding a base whose sheets are forced strictly below the Klein sheets. -/
theorem t95J03_exclude_large {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace X] {p : E → X} {q : E → Surface false 2} {k n : ℕ}
    (hp : IsKSheetedCover p k) (hq : IsKSheetedCover q k) (hk : 0 < k) (hn : 3 ≤ n)
    (hpres : ∀ x : X, ∃ r : FreeGroup (Fin n), Nonempty (FundamentalGroup X x ≃*
        FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _))) : False := by
  haveI : PathConnectedSpace (Surface false 2) := surface_pathConnected false 2
  refine t95J03_sheets_lt_absurd hp hq hk fun e => ?_
  have hb := t95J03_base_side hp (by omega) e (hpres (p e))
  have hK := (t95J03_klein_side hq e).2
  have hd := componentFiberCard_pos hp e
  have : (n - 1) * Nat.card (ComponentFiber p e) ≥ 2 * Nat.card (ComponentFiber p e) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- A component whose `π₁` has `b₁ = 0` cannot also cover the Klein bottle. -/
theorem t95J03_exclude_b1_zero {E : Type*} [TopologicalSpace E]
    {q : E → Surface false 2} {k : ℕ}
    (hq : IsKSheetedCover q k) (e : E) (hzero : b1 (FundamentalGroup E e) = 0) : False := by
  have := (t95J03_klein_side hq e).1
  omega

theorem t95J03_exists_point {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Nonempty X] {p : E → X} {k : ℕ} (hp : IsKSheetedCover p k) (hk : 0 < k) : Nonempty E := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have h := hp.card_fiber x
  haveI := hp.finite_fiber x
  have : 0 < Nat.card {e : E // p e = x} := by omega
  obtain ⟨⟨e, -⟩⟩ := (Nat.card_pos_iff.mp this).1
  exact ⟨e⟩

theorem t95J03_b1_zero_of_subsingleton (G : Type*) [Group G] [Subsingleton G] : b1 G = 0 := by
  haveI : Subsingleton (Additive G) := inferInstanceAs (Subsingleton G)
  haveI : Subsingleton (Additive G →+ ℚ) := ⟨fun φ ψ => AddMonoidHom.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact Module.finrank_zero_of_subsingleton

/-- Classification: a surface sharing a `k`-fold cover with the Klein bottle is
the torus (then `k` is even) or the Klein bottle. -/
theorem t95J03_classify (k : ℕ) (hk : 0 < k) (F : T95J03ClosedSurface)
    (hF : T95J03SharesKFoldCover k F t95J03KleinBottle) :
    (F = t95J03Torus ∧ Even k) ∨ F = t95J03KleinBottle := by
  obtain ⟨E, K', p, q, hp, hq, ⟨φ⟩⟩ := hF
  have hp' := t95J03_isKSheeted_of_kfold hk hp
  have hq0 := t95J03_isKSheeted_of_kfold hk hq
  have hq' : IsKSheetedCover (q ∘ φ) k := t95J03_isKSheeted_comp_homeomorph hq0 φ
  change IsKSheetedCover (q ∘ φ : E → Surface false 2) k at hq'
  cases F with
  | orientable g =>
    rcases g with _ | _ | g
    · -- the sphere
      change E → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 at p
      replace hp' : IsKSheetedCover (B := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        p k := hp'
      haveI : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
        SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 2 le_rfl
      obtain ⟨e⟩ := t95J03_exists_point hp' hk
      obtain ⟨H, -, ⟨eH⟩⟩ := t95J03_pi1_subgroup hp'.isCoveringMap e
      haveI : Subsingleton (FundamentalGroup (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (p e)) := by
        change Subsingleton (Path.Homotopic.Quotient _ _)
        infer_instance
      haveI : Subsingleton (FundamentalGroup E e) := ⟨fun a b => eH.injective
        (Subtype.ext (Subsingleton.elim _ _))⟩
      exact (t95J03_exclude_b1_zero hq' e
        (t95J03_b1_zero_of_subsingleton (FundamentalGroup E e))).elim
    · -- the torus: every component has an even number of Klein sheets
      left
      refine ⟨rfl, ?_⟩
      change E → Surface true 1 at p
      replace hp' : IsKSheetedCover (B := Surface true 1) p k := hp'
      haveI : Nonempty (Surface false 2) := ⟨surfaceQuotient false 2 ⟨0, by simp⟩⟩
      refine t95J03_even_sheets hq' fun e => ?_
      obtain ⟨HT, -, ⟨eT⟩⟩ := t95J03_pi1_subgroup hp'.isCoveringMap e
      obtain ⟨HK, hHK, ⟨eK⟩⟩ := t95J03_pi1_subgroup hq'.isCoveringMap e
      obtain ⟨ek⟩ := KleinBottlePiOne.kleinBottle_pi1_every_basepoint ((q ∘ φ) e)
      let H' : Subgroup PresentedKleinGroup :=
        HK.map (ek : FundamentalGroup (Surface false 2) ((q ∘ φ) e) →* PresentedKleinGroup)
      have hidx : H'.index = Nat.card (ComponentFiber (q ∘ φ) e) :=
        (Subgroup.index_map_equiv HK ek).trans hHK
      suffices hev : Even H'.index by rwa [hidx] at hev
      refine t95J03_klein_index_even H'
        (by rw [hidx]; exact (componentFiberCard_pos hq' e).ne') ?_
      have hcommE : ∀ u v : FundamentalGroup E e, u * v = v * u := by
        intro u v
        have h : ((eT (u * v) : HT) : FundamentalGroup (Surface true 1) (p e)) =
            ((eT (v * u) : HT) : FundamentalGroup (Surface true 1) (p e)) := by
          rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
          exact t95J03_torus_pi1_comm _ _ _
        exact eT.injective (Subtype.ext h)
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      have hHK : (⟨u, hu⟩ : HK) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨u, hu⟩ := by
        have h2 := congrArg eK (hcommE (eK.symm ⟨u, hu⟩) (eK.symm ⟨v, hv⟩))
        simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
      have huv : u * v = v * u := congrArg Subtype.val hHK
      change ek u * ek v = ek v * ek u
      rw [← map_mul, ← map_mul, huv]
    · -- orientable genus `g + 2`: `n = 2g + 4 ≥ 3` generators
      change E → Surface true (g + 2) at p
      replace hp' : IsKSheetedCover (B := Surface true (g + 2)) p k := hp'
      haveI : PathConnectedSpace (Surface true (g + 2)) := surface_pathConnected true (g + 2)
      exact (t95J03_exclude_large hp' hq' hk (n := 2 * (g + 2)) (by omega)
        (fun x => t95J03_orientable_presentation (g + 2) (by omega) x)).elim
  | nonorientable g =>
    change E → Surface false g at p
    replace hp' : IsKSheetedCover (B := Surface false g) p k := hp'
    haveI : Nonempty (Surface false g) := ⟨surfaceQuotient false g ⟨0, by simp⟩⟩
    haveI : PathConnectedSpace (Surface false g) := surface_pathConnected false g
    rcases Nat.lt_or_ge (g : ℕ) 3 with hlt | hge
    · have hg := g.pos
      have h12 : (g : ℕ) = 1 ∨ (g : ℕ) = 2 := by omega
      rcases h12 with h1 | h2
      · -- the projective plane: `b₁ = 0`
        obtain ⟨e⟩ := t95J03_exists_point hp' hk
        obtain ⟨H, hH, ⟨eH⟩⟩ := t95J03_pi1_subgroup hp'.isCoveringMap e
        obtain ⟨r, ⟨eX⟩, hr⟩ := surface_presentation g g.pos (p e)
        have hd := componentFiberCard_pos hp' e
        have hup := (t95J03_b1_bounds g.pos r eX H hd hH).2 hr
        have h0 : (g : ℕ) - 1 = 0 := by omega
        rw [h0] at hup
        rw [← b1_congr eH] at hup
        exact (t95J03_exclude_b1_zero hq' e (by omega)).elim
      · right
        exact congrArg T95J03ClosedSurface.nonorientable (PNat.eq h2)
    · exact (t95J03_exclude_large hp' hq' hk (n := g) hge
        (fun x => (surface_presentation g g.pos x).imp fun _ h => h.1)).elim

/-- Membership: the Klein bottle always, the torus for even `k`. -/
theorem t95J03_realize (k : ℕ) (hk : 0 < k) (F : T95J03ClosedSurface)
    (hF : F = t95J03KleinBottle ∨ (F = t95J03Torus ∧ Even k)) :
    T95J03SharesKFoldCover k F t95J03KleinBottle := by
  rcases hF with rfl | ⟨rfl, m, rfl⟩
  · refine ⟨TopCat.of (Surface false 2 × Fin k), TopCat.of (Surface false 2 × Fin k),
      fun x => x.1, fun x => x.1, ?_, ?_, ⟨Homeomorph.refl _⟩⟩ <;>
    · apply t95J03_kfold_of_isKSheeted
      simpa using t95J03_isKSheeted_prod_fin (t95J03_id_isKSheeted (Surface false 2)) k
  · obtain ⟨b⟩ := t95J03_torus_bridge
    obtain ⟨π, hπ⟩ := t95J03_klein_doubleCover
    refine ⟨TopCat.of (T95J03Torus × Fin m), TopCat.of (T95J03Torus × Fin m),
      fun x => b.symm ((2 • x.1.1, x.1.2)), fun x => π x.1, ?_, ?_, ⟨Homeomorph.refl _⟩⟩
    · apply t95J03_kfold_of_isKSheeted
      have h := t95J03_isKSheeted_prod_fin
        (t95J03_homeomorph_comp_isKSheeted (t95J03_torusNsmul_isKSheeted 2 (by norm_num))
          b.symm) m
      rw [show 2 * m = m + m by ring] at h
      exact h
    · apply t95J03_kfold_of_isKSheeted
      have h := t95J03_isKSheeted_prod_fin hπ m
      rw [show 2 * m = m + m by ring] at h
      exact h

theorem apm_t95j03 (k : ℕ) (hk : 1 < k) :
    {F | T95J03SharesKFoldCover k F t95J03KleinBottle} =
      if Even k then {t95J03Torus, t95J03KleinBottle}
      else {t95J03KleinBottle} := by
  have hk0 : 0 < k := by omega
  ext F
  constructor
  · intro hF
    rcases t95J03_classify k hk0 F hF with ⟨rfl, hev⟩ | rfl
    · simp [hev]
    · split_ifs <;> simp
  · intro hF
    apply t95J03_realize k hk0 F
    split_ifs at hF with hev
    · rcases hF with rfl | rfl
      · exact Or.inr ⟨rfl, hev⟩
      · exact Or.inl rfl
    · exact Or.inl hF

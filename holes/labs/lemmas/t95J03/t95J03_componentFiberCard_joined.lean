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
-- BEGIN SEAT AREA

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
-- END SEAT AREA

/-- **Leaf C3.**  Two `k`-sheeted covers on one total space cannot have strictly
more sheets for the second on every component.

Route.  Fix `x : X`, `y : Y`, fibres `A = p⁻¹ x`, `B = q⁻¹ y` (`k` points each).
For `a ∈ A`, its class in `A` under `Joined` is `ComponentFiber p a`; the
component of `a` meets `B` (`CoveringPathComponentSurjective`) in
`ComponentFiber q b` for some `b`, whose card equals that of
`ComponentFiber q a` (`t95J03_componentFiberCard_joined`).  Summing over the
classes of `A`: `k = Σ |A ∩ C| < Σ |B ∩ C| ≤ |B| = k`.  About 100–200 lines. -/
lemma t95J03_sheets_lt_absurd {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y]
    {p : E → X} {q : E → Y} {k : ℕ} (hp : IsKSheetedCover p k) (hq : IsKSheetedCover q k)
    (hk : 0 < k)
    (hlt : ∀ e, Nat.card (ComponentFiber p e) < Nat.card (ComponentFiber q e)) : False := by
  sorry

/-- **Leaf C4.**  If every component has an even number of sheets, so does the
cover.

Route.  Partition the fibre over a point `y` by `Joined` (an equivalence
relation); the class of `b` is `ComponentFiber q b` (same base point `q b = y`).
`Finset.card_eq_sum_card_fiberwise` / `Setoid.IsPartition`; a sum of evens is
even.  About 50–100 lines. -/
lemma t95J03_even_sheets {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [Nonempty Y] {q : E → Y} {k : ℕ} (hq : IsKSheetedCover q k)
    (heven : ∀ e, Even (Nat.card (ComponentFiber q e))) : Even k := by
  sorry

/-- **Leaf C5.**  Precomposing with a homeomorphism keeps a `k`-sheeted cover.
Route: `IsCoveringMap.comp_homeomorph`-style (or local trivializations
pulled back); fibres `φ⁻¹` biject.  About 20–50 lines. -/
lemma t95J03_isKSheeted_comp_homeomorph {E E' X : Type*} [TopologicalSpace E]
    [TopologicalSpace E'] [TopologicalSpace X] {q : E' → X} {k : ℕ}
    (hq : IsKSheetedCover q k) (φ : E ≃ₜ E') : IsKSheetedCover (q ∘ φ) k := by
  sorry

/-- **Leaf C6.**  Postcomposing with a homeomorphism keeps a `k`-sheeted cover.
About 20–50 lines. -/
lemma t95J03_homeomorph_comp_isKSheeted {E X Y : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace Y] {p : E → X} {k : ℕ}
    (hp : IsKSheetedCover p k) (ψ : X ≃ₜ Y) : IsKSheetedCover (ψ ∘ p) k := by
  sorry

/-- **Leaf C7.**  `m` disjoint copies of a `d`-sheeted cover form a
`(d * m)`-sheeted cover.  Route: covering by
`ProductEvenlyCoveredTrivialization.isCoveringMap_productMap`-style argument
or directly (evenly covered sets pull back, fibre `≃ fibre × Fin m`).
About 40–90 lines. -/
lemma t95J03_isKSheeted_prod_fin {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} {d : ℕ} (hp : IsKSheetedCover p d) (m : ℕ) :
    IsKSheetedCover (fun x : E × Fin m => p x.1) (d * m) := by
  sorry

/-- **Leaf C8.**  The identity is a one-sheeted cover.  About 10–30 lines. -/
lemma t95J03_id_isKSheeted (X : Type*) [TopologicalSpace X] :
    IsKSheetedCover (id : X → X) 1 := by
  sorry

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
lemma t95J03_torus_bridge : Nonempty (Surface true 1 ≃ₜ T95J03Torus) := by
  sorry

/-- **Leaf S3 (layer 2: uses S2).**  `π₁` of the torus is commutative.

Route.  Transport along `t95J03_torus_bridge`
(`SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph`); then either
`FundamentalGroupProduct.fundamentalGroupProdMulEquiv` and `π₁(AddCircle)`
commutative (≅ ℤ via `CircleUniversalCover`/`AddCircle` covering by `ℝ`), or
Eckmann–Hilton for the topological group `T95J03Torus`.  About 60–200 lines. -/
lemma t95J03_torus_pi1_comm (x : Surface true 1)
    (a b : FundamentalGroup (Surface true 1) x) : a * b = b * a := by
  sorry

/-- **Leaf S4.**  An abelian finite-index subgroup of the Klein group has even
index.

Route.  Coordinates `coordinateEquiv : PresentedKleinGroup ≃* ℤ ⋊ ℤ`
(`b` acts on `a` by inversion).  Finite index gives `a^m ∈ H` with `m ≥ 1`
(two of the cosets `a^i H`, `i ≤ index`, coincide).  If `h ∈ H` has odd
`ℤ`-coordinate, `h a^m h⁻¹ = a^{-m} ≠ a^m` (`a` has infinite order), contradicting
commutativity.  So `H ≤ ker (second coordinate mod 2)`, a subgroup of index 2,
and `index H = 2 * relindex` (`Subgroup.relindex_mul_index`).
About 100–180 lines. -/
lemma t95J03_klein_index_even (H : Subgroup PresentedKleinGroup) (hfin : H.index ≠ 0)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : Even H.index := by
  sorry

/-- **Leaf S5.**  `(x, y) ↦ (n x, y)` is an `n`-sheeted cover of the torus
(same as t98A01's `t98A01_torusFive_isNfoldCover` with `5 → n`).

Route.  `AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero`,
`ProductEvenlyCoveredTrivialization.isCoveringMap_productMap` with the identity;
fibres are cosets of the `n`-torsion `{j/n}`.  About 60–150 lines. -/
lemma t95J03_torusNsmul_isKSheeted (n : ℕ) (hn : 0 < n) :
    IsKSheetedCover (fun x : T95J03Torus => (n • x.1, x.2)) n := by
  sorry

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
  sorry

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

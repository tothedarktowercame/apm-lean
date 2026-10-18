import Mathlib
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Covering.AddCircle
import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonMoves
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.SurfaceGroupBetti
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.ProductEvenlyCoveredTrivialization

/-!
# APM t98A01 — a five-fold surface cover and a connected sum

(a) The fivefold example is the genuine map `(x,y) ↦ (5x,y)` on `(ℝ/ℤ)²`.
The universal clause says that among the repository's closed orientable
surfaces only the torus admits a regular five-sheeted self-cover.

(b) A surface presented by a polygon word `w` is
`PolygonMoves.PolygonSurface w`: the closed disk with its boundary arcs paired
as `w` prescribes (equal signs glue `t ↔ t`, opposite signs `t ↔ 1 - t`).  For
words with disjoint labels, the connected sum of the surfaces of `w₁` and `w₂`
is the surface of the concatenated word `w₁ ++ w₂`: cutting a disk at a vertex
of each polygon and gluing the boundary circles leaves the single polygon
`w₁w₂` (Massey, *Algebraic Topology: An Introduction*, Ch. 1 §7).  `T`, `P`, `K`
are the words `aba⁻¹b⁻¹`, `aa`, `aba⁻¹b`; the statement certifies each against
the repository's standard models `Surface true 1`, `Surface false 1`,
`Surface false 2`.  The canonical form of `K#T#T#P#K#T` is `Surface false 11`
(eleven crosscaps).  The Euler characteristic is the alternating rank sum of
rational singular homology (`HasEulerCharacteristic`), a homeomorphism
invariant.

## Statement repairs

2026-10-16 (claude-14): part (b) previously computed classification data
with the arithmetic function `connectedSum : Bool → ℕ → Bool → ℕ → Bool × ℕ`
(which encodes `T#P ≅ P#P#P`, the substance of the exercise) and certified the
homeomorphism by `Homeomorph.refl`; χ was the formula `2 - g`.  Part (b) is
replaced by the polygon-word connected sum and the rational-homology Euler
characteristic above.  Part (a) is unchanged.

## Encoding questions

Regularity is transitivity of actual deck homeomorphisms on every fiber.
-/

open ConstructionTargets.Surfaces

noncomputable section

abbrev T98A01Torus := UnitAddCircle × UnitAddCircle

def t98A01TorusFiveCover : C(T98A01Torus, T98A01Torus) :=
  ⟨fun p ↦ (5 • p.1, p.2), by fun_prop⟩

def t98A01IsNfoldCover {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B]
    (n : ℕ) (p : E → B) : Prop :=
  IsCoveringMap p ∧ ∀ b : B, Nat.card {e : E // p e = b} = n

def t98A01IsRegularNfoldCover {E B : Type*}
    [TopologicalSpace E] [TopologicalSpace B]
    (n : ℕ) (p : E → B) : Prop :=
  t98A01IsNfoldCover n p ∧
    ∀ x y : E, p x = p y →
      ∃ h : E ≃ₜ E, (∀ z : E, p (h z) = p z) ∧ h x = y

/-- The six summands of `K # T # T # P # K # T`. -/
inductive T98A01Summand
  | K₁ | T₁ | T₂ | P | K₂ | T₃
  deriving DecidableEq

/-- Edge labels: summand `s` uses `(s, false)` (`a`) and `(s, true)` (`b`). -/
abbrev T98A01Edge := T98A01Summand × Bool

/-- `T = a b a⁻¹ b⁻¹`. -/
def t98A01TorusWord (s : T98A01Summand) : List (PolygonMoves.Signed T98A01Edge) :=
  [((s, false), true), ((s, true), true), ((s, false), false), ((s, true), false)]

/-- `P = a a`. -/
def t98A01ProjectiveWord (s : T98A01Summand) : List (PolygonMoves.Signed T98A01Edge) :=
  [((s, false), true), ((s, false), true)]

/-- `K = a b a⁻¹ b`. -/
def t98A01KleinWord (s : T98A01Summand) : List (PolygonMoves.Signed T98A01Edge) :=
  [((s, false), true), ((s, true), true), ((s, false), false), ((s, true), true)]

/-- The word of `K # T # T # P # K # T`. -/
def t98A01SumWord : List (PolygonMoves.Signed T98A01Edge) :=
  t98A01KleinWord .K₁ ++ t98A01TorusWord .T₁ ++ t98A01TorusWord .T₂ ++
    t98A01ProjectiveWord .P ++ t98A01KleinWord .K₂ ++ t98A01TorusWord .T₃

abbrev T98A01SumSurface := PolygonMoves.PolygonSurface t98A01SumWord


/-! # Blueprint (claude-14, 2026-10-16)

Everything above `apm_t98a01` is the proposed statement (`RevisedMain.lean`).
Route: see `BLUEPRINT.md`.  Leaves are the `lemma … := by sorry` below; every
other declaration is a sorry-free assembly. -/

open ConstructionTargets ConstructionTargets.SurfaceGroupBetti
open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology
open ConstructionTargets.RationalLefschetz PolygonMoves

/-! ## (a) The five-fold torus cover -/

lemma t98A01_circleFive_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (5 • · : UnitAddCircle → UnitAddCircle)
      (nsmulAddMonoidHom (α := UnitAddCircle) 5).ker := by
  exact AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 5

lemma t98A01_circleFive_isCoveringMap :
    IsCoveringMap (5 • · : UnitAddCircle → UnitAddCircle) :=
  t98A01_circleFive_isAddQuotientCoveringMap.isCoveringMap

/-- **Leaf (a1).**  `(x, y) ↦ (5x, y)` is a covering with fibres of size 5.

Route.  Covering: `ProductEvenlyCoveredTrivialization.isCoveringMap_productMap`
with `t98A01_circleFive_isCoveringMap` and the identity (a homeomorphism is a
covering, e.g. `Homeomorph.isCoveringMap` / `IsHomeomorph.isCoveringMap`).
Fibre: `{e // (5 e.1, e.2) = (x, y)} ≃ {x' // 5 x' = x}` (second coordinate
forced), and the latter is a coset of the kernel of `nsmul 5` on
`UnitAddCircle` (`t98A01_circleFive_isAddQuotientCoveringMap`, or
`AddCircle` torsion: the kernel is `{j/5 | j < 5}`), of cardinality 5.
About 60–150 lines. -/
lemma t98A01_torusFive_isNfoldCover :
    t98A01IsNfoldCover 5 t98A01TorusFiveCover := by
  sorry

/-- Deck transformations: translate the first coordinate. -/
theorem t98A01_torusFive_deck (x y : T98A01Torus)
    (hxy : t98A01TorusFiveCover x = t98A01TorusFiveCover y) :
    ∃ h : T98A01Torus ≃ₜ T98A01Torus,
      (∀ z, t98A01TorusFiveCover (h z) = t98A01TorusFiveCover z) ∧ h x = y := by
  have h1 : 5 • x.1 = 5 • y.1 := (Prod.ext_iff.mp hxy).1
  have h2 : x.2 = y.2 := (Prod.ext_iff.mp hxy).2
  refine ⟨Homeomorph.addRight ((y.1 - x.1, 0) : T98A01Torus), ?_, ?_⟩
  · intro z
    change ((5 • (z.1 + (y.1 - x.1)), z.2 + 0) : T98A01Torus) = (5 • z.1, z.2)
    rw [smul_add, smul_sub, h1, sub_self, add_zero, add_zero]
  · change ((x.1 + (y.1 - x.1), x.2 + 0) : T98A01Torus) = y
    rw [add_sub_cancel, add_zero, h2]

/-! ## (a) Only the torus: b₁ of surface groups -/

/-- **Leaf (a3).**  The standard orientable pairing data of genus `g` has `2g`
edge orbits.

Route.  Mirror of `SurfaceGroupBetti.standard_nonorientable_data` (`card`
part): `orientableOrbitLabel g : Fin (4g) → Fin g × Bool` is constant exactly
on pairing orbits (`orientableOrbitLabel_pair` in `PolygonSurfacePiOne`), and
is surjective; build `PairingOrbit (standardPairingData true g hg).pair ≃
Fin g × Bool` as for `nonorientableOrbitEquiv`.  About 40–100 lines. -/
lemma t98A01_orientable_data_card (g : ℕ) (hg : 0 < g) :
    Nat.card (PairingOrbit (standardPairingData true g hg).pair) = 2 * g := by
  sorry

/-- **Leaf (a4).**  `Surface true 0` (no edge identifications: the closed disk)
has trivial fundamental group.

Route.  `SurfaceRel true 0` is empty (`j < 0`), so `surfaceQuotient true 0` is
a continuous bijection from the compact disk onto a quotient whose topology is
coinduced: a homeomorphism `Disk ≃ₜ Surface true 0`.  The disk is convex, hence
contractible (`Convex.contractibleSpace` or a straight-line homotopy), hence
`SimplyConnectedSpace`; transport (`SimplyConnectedSpace.ofHomotopyEquiv` /
`Homeomorph`).  About 40–100 lines. -/
lemma t98A01_surfaceTrueZero_pi1_subsingleton (x : Surface true 0) :
    Subsingleton (FundamentalGroup (Surface true 0) x) := by
  sorry

theorem t98A01_b1_oneRelator_bounds (n : ℕ) (r : FreeGroup (Fin n)) :
    n ≤ b1 (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _)) + 1 ∧
      b1 (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _)) ≤ n := by
  obtain ⟨hfd, hb⟩ := b1_freeGroup n
  obtain ⟨hlow, hup, -⟩ := b1_quotient_normalClosure_bounds ({r} : Finset _)
  have hq : b1 (FreeGroup (Fin n) ⧸
        Subgroup.normalClosure ((({r} : Finset (FreeGroup (Fin n))) : Set _))) =
      b1 (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set _)) :=
    b1_congr (QuotientGroup.quotientMulEquivOfEq (by rw [Finset.coe_singleton]))
  simp only [Finset.card_singleton] at hlow
  omega

theorem t98A01_b1_subsingleton (G : Type*) [Group G] [Subsingleton G] : b1 G = 0 := by
  haveI : Subsingleton (Additive G) := inferInstanceAs (Subsingleton G)
  haveI : Subsingleton (Additive G →+ ℚ) := ⟨fun φ ψ => AddMonoidHom.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact Module.finrank_zero_of_subsingleton

theorem t98A01_orientable_presentation (g : ℕ) (hg : 0 < g) (x : Surface true g) :
    ∃ r : FreeGroup (Fin (2 * g)),
      Nonempty (FundamentalGroup (Surface true g) x ≃*
        FreeGroup (Fin (2 * g)) ⧸ Subgroup.normalClosure ({r} : Set _)) := by
  let P := standardPairingData true g hg
  let h := standardPairingData_space_homeomorph true g hg
  have hcard := t98A01_orientable_data_card g hg
  obtain ⟨r, ⟨eP⟩, -⟩ := polygon_presentation P (h.symm x)
  let c : FreeGroup (Fin (Nat.card (PairingOrbit P.pair))) ≃* FreeGroup (Fin (2 * g)) :=
    FreeGroup.freeGroupCongr (finCongr hcard)
  refine ⟨c r, ⟨?_⟩⟩
  have hx : h (h.symm x) = x := h.apply_symm_apply x
  exact ((SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph h.symm x).trans eP).trans
    (quotientSingletonCongr c r)

/-- `b₁(π₁ Σ_g)` lies in `[2g - 1, 2g]` for `g > 0` and is `0` for the disk. -/
theorem t98A01_b1_surfaceTrue (g : ℕ) (x : Surface true g) :
    (g = 0 → b1 (FundamentalGroup (Surface true g) x) = 0) ∧
    (0 < g → 2 * g ≤ b1 (FundamentalGroup (Surface true g) x) + 1 ∧
      b1 (FundamentalGroup (Surface true g) x) ≤ 2 * g) := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    haveI := t98A01_surfaceTrueZero_pi1_subsingleton x
    exact t98A01_b1_subsingleton _
  · intro hg
    obtain ⟨r, ⟨e⟩⟩ := t98A01_orientable_presentation g hg x
    rw [b1_congr e]
    exact t98A01_b1_oneRelator_bounds (2 * g) r

/-- The universal clause of (a): a five-sheeted cover `Σ_g → Σ_h` with
`Σ_g ≅ Σ_h` forces `g = h = 1` (regularity is not needed). -/
theorem t98A01_orientable_cover_genus (g h : ℕ) (p : Surface true g → Surface true h)
    (hp : t98A01IsNfoldCover 5 p) (he : Nonempty (Surface true g ≃ₜ Surface true h)) :
    g = 1 ∧ h = 1 := by
  obtain ⟨hcov, hcard⟩ := hp
  obtain ⟨e⟩ := he
  haveI : PathConnectedSpace (Surface true g) := surface_pathConnected true g
  let e0 : Surface true g :=
    surfaceQuotient true g ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let f := coveringInducedFundamentalGroupMap hcov e0
  have hidx : f.range.index = 5 := by
    rw [← coveringFiberCard_eq_index hcov e0, ← hcard (p e0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Set.mem_singleton_iff))
  have hbE : b1 (FundamentalGroup (Surface true g) e0) =
      b1 (FundamentalGroup (Surface true h) (e e0)) :=
    b1_congr (SurfaceGroupBetti.fundamentalGroupEquivOfHomeomorph e e0)
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · haveI := t98A01_surfaceTrueZero_pi1_subsingleton (p e0)
    have htop : f.range = ⊤ := Subsingleton.elim _ _
    rw [htop, Subgroup.index_top] at hidx
    omega
  obtain ⟨r, ⟨eh⟩⟩ := t98A01_orientable_presentation h hh (p e0)
  let H := f.range.map (eh : FundamentalGroup (Surface true h) (p e0) →*
    FreeGroup (Fin (2 * h)) ⧸ Subgroup.normalClosure ({r} : Set _))
  have hHidx : H.index = 5 := (Subgroup.index_map_equiv f.range eh).trans hidx
  have eH : FundamentalGroup (Surface true g) e0 ≃* H :=
    (MonoidHom.ofInjective (coveringInducedFundamentalGroupMap_injective hcov e0)).trans
      (f.range.equivMapOfInjective _ eh.injective)
  obtain ⟨hlow, -⟩ := b1_finiteIndex_bounds (2 * h) 5 (by omega) (by norm_num) r H hHidx
  rw [← b1_congr eH, hbE] at hlow
  obtain ⟨-, hhb⟩ := t98A01_b1_surfaceTrue h (e e0)
  obtain ⟨hlo_h, hup_h⟩ := hhb hh
  have hh1 : h = 1 := by
    have : (2 * h - 1) * 5 + 1 ≤ 2 * h + 5 := le_trans hlow (by omega)
    omega
  subst hh1
  obtain ⟨hg0, hgb⟩ := t98A01_b1_surfaceTrue g e0
  rcases Nat.eq_zero_or_pos g with hg | hg
  · have := hg0 hg
    omega
  · obtain ⟨hlo_g, -⟩ := hgb hg
    exact ⟨by omega, rfl⟩

/-! ## (b) Word moves -/

/-- **Leaf (b1).**  Torus bridge: `x y x⁻¹ y⁻¹` is the standard torus.

Route.  As `PolygonMoves.crosscapTwo_bridge`: the two relations agree as
relations on `Disk` up to `EqvGen` (`WordRel` pairs positions 0,2 and 1,3 with
opposite signs, so with reversed parameter; `SurfaceRel true 1` pairs
`edgePoint 4 0 t ~ edgePoint 4 2 (1-t)` and `edgePoint 4 1 t ~ edgePoint 4 3 (1-t)`);
then `Quotient.congrRight` and continuity both ways.  About 60–120 lines. -/
lemma t98A01_torus_bridge {L : Type*} [DecidableEq L] (x y : Signed L) (hxy : x.1 ≠ y.1) :
    Nonempty (PolygonSurface [x, y, inv x, inv y] ≃ₜ Surface true 1) := by
  sorry

/-- The word of `g` doubled letters `c₀ c₀ c₁ c₁ ⋯`. -/
def t98A01CrosscapWord {L : Type*} (g : ℕ) (c : Fin g → Signed L) : List (Signed L) :=
  (List.finRange g).flatMap fun i => [c i, c i]

/-- **Leaf (b2).**  Crosscap bridge: `c₀ c₀ c₁ c₁ ⋯ c_{g-1} c_{g-1}` with distinct
labels is `Surface false g`.

Route.  As `PolygonMoves.crosscapTwo_bridge`, for general `g`: position `i` of
the word is `c (i / 2)`; two distinct positions carry the same label iff they
are `2j, 2j + 1`, and then the signs agree, so `WordRel` glues `t ↔ t`, which
is exactly `SurfaceRel false g` (`edgePoint (2g) (2j) t ~ edgePoint (2g) (2j+1) t`).
Length `2g`.  About 80–160 lines. -/
lemma t98A01_crosscap_bridge {L : Type*} [DecidableEq L] (g : ℕ) (hg : 0 < g)
    (c : Fin g → Signed L) (hc : Function.Injective fun i => (c i).1) :
    Nonempty (PolygonSurface (t98A01CrosscapWord g c) ≃ₜ Surface false g) := by
  sorry

/-- **Leaf (b3).**  A Klein block becomes two crosscaps:
`u a b a⁻¹ b t ≅ u a a b⁻¹ b⁻¹ t`.

Route.  Two `PolygonMoves.cutAndPaste` steps (`u x v x t ≅ u x x v⁻¹ t`):
the pair `b` with `u ++ [a]`, `v = [a⁻¹]` gives `u a b b a t`; then the pair `a`
with `v = [b, b]` gives `u a a b⁻¹ b⁻¹ t`.  Side conditions: label freshness
from the hypotheses, `IsPolygonWord` of the middle word (same label counts).
About 80–180 lines. -/
lemma t98A01_kleinBlock {L : Type*} [DecidableEq L] (u t : List (Signed L))
    (a b : Signed L) (hab : a.1 ≠ b.1)
    (ha : a.1 ∉ (u ++ t).map Prod.fst) (hb : b.1 ∉ (u ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [a, b, inv a, b] ++ t)) :
    Nonempty (PolygonSurface (u ++ [a, b, inv a, b] ++ t) ≃ₜ
      PolygonSurface (u ++ [a, a, inv b, inv b] ++ t)) := by
  sorry

/-- **Leaf (b4).**  A handle next to a crosscap becomes two crosscaps:
`u x x a b a⁻¹ b⁻¹ t ≅ u x x b b a a t`.

Route.  Four `cutAndPaste` steps (the first used right-to-left):
`u x x a b a⁻¹ b⁻¹ t ≅ u x a⁻¹ x b a⁻¹ b⁻¹ t` (pair `x`, `v = [a⁻¹]`);
`≅ u x a⁻¹ a⁻¹ b⁻¹ x⁻¹ b⁻¹ t` (pair `a⁻¹`, `u ++ [x]`, `v = [x, b]`);
`≅ u x a⁻¹ a⁻¹ b⁻¹ b⁻¹ x t` (pair `b⁻¹`, `v = [x⁻¹]`);
`≅ u x x b b a a t` (pair `x`, `v = [a⁻¹, a⁻¹, b⁻¹, b⁻¹]`).
Checked by hand: each step is literally `u x v x t ≅ u x x (inverseWord v) t`.
About 120–220 lines. -/
lemma t98A01_handleAbsorb {L : Type*} [DecidableEq L] (u t : List (Signed L))
    (x a b : Signed L) (hxa : x.1 ≠ a.1) (hxb : x.1 ≠ b.1) (hab : a.1 ≠ b.1)
    (hx : x.1 ∉ (u ++ t).map Prod.fst) (ha : a.1 ∉ (u ++ t).map Prod.fst)
    (hb : b.1 ∉ (u ++ t).map Prod.fst)
    (hw : IsPolygonWord (u ++ [x, x, a, b, inv a, inv b] ++ t)) :
    Nonempty (PolygonSurface (u ++ [x, x, a, b, inv a, inv b] ++ t) ≃ₜ
      PolygonSurface (u ++ [x, x, b, b, a, a] ++ t)) := by
  sorry

/-- The eleven crosscap letters of the normal form, in order. -/
def t98A01CrosscapLetters : Fin 11 → Signed T98A01Edge :=
  ![((.K₁, false), true), ((.K₁, true), false), ((.T₁, true), true), ((.T₁, false), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.P, false), true),
    ((.K₂, false), true), ((.K₂, true), false), ((.T₃, true), true), ((.T₃, false), true)]

/-- **Leaf (b5, layer 2: uses b3, b4).**  The normal form of the sum word.

Route.  `K₁` by `t98A01_kleinBlock` (`u = []`); then `T₁`, `T₂` by
`t98A01_handleAbsorb`, each after the crosscap pair just produced
(`x = (K₁,b)⁻¹`, then `x = (T₁,a)`); `P` is already a crosscap; `K₂` by
`t98A01_kleinBlock`; `T₃` by `t98A01_handleAbsorb` with `x = (K₂,b)⁻¹`.
Each step's `u`, `t` are explicit lists; freshness, distinctness and
`IsPolygonWord` are `decide`; list equalities `rfl`/`simp`.  Compose with
`PolygonMoves.homeomorph_trans`.  The result is
`t98A01CrosscapWord 11 t98A01CrosscapLetters` (checked by hand).
About 80–200 lines. -/
lemma t98A01_sum_normalForm :
    Nonempty (T98A01SumSurface ≃ₜ
      PolygonSurface (t98A01CrosscapWord 11 t98A01CrosscapLetters)) := by
  sorry

/-! ## (b) Euler characteristic -/

/-- **Leaf (b6, LIBRARY).**  Rational singular homology has rank equal to the
`ℤ`-rank of integral singular homology (universal coefficients over the flat
`ℤ`-algebra `ℚ`).

Route (split before dispatch, see BLUEPRINT.md): (i) natural chain iso
`C_•(X; ℚ) ≅ (extendScalars ℤ → ℚ)(C_•(X; ℤ))` (chains are coproducts of the
coefficient object, `SSet.singularChainComplexFunctor`; `extendScalars`
preserves coproducts and sends `ℤ` to `ℚ`); (ii) `extendScalars` along
`ℤ → ℚ` is exact (`ℚ` flat / localization) so it preserves homology
(`Functor.PreservesHomology`, `HomologicalComplex.homologyFunctorIso`-style);
(iii) `finrank_ℚ (ℚ ⊗ M) = finrank_ℤ M` for finite `M`
(`Module.finrank_baseChange` / rank of torsion is zero).  400–900 lines. -/
lemma t98A01_rationalHomology_finrank (X : Type) [TopologicalSpace X] (k : ℕ)
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M]
    (e : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) ≅ ModuleCat.of ℤ M) :
    FiniteDimensional ℚ (Homology X k) ∧
      Module.finrank ℚ (Homology X k) = Module.finrank ℤ M := by
  sorry

/-- **Leaf (b7).**  Integral homology ranks of the standard crosscap data:
`attachingBoundary : ℤ → ℤ^g` is `n ↦ n • attachingDegree`, and
`attachingDegree ≠ 0` (`SurfaceGroupBetti.standard_nonorientable_data`), so the
kernel is `0` and the cokernel has rank `g - 1`.

Route.  Kernel: injective since a nonzero vector `d` has `n • d = 0 → n = 0`.
Cokernel: finite (quotient of `Fin`-indexed functions, `Module.Finite`);
rank via `ℚ`-rank–nullity (`Module.finrank` of a quotient by the span of one
nonzero vector), or `rank_quotient_add_rank`.  About 80–200 lines. -/
lemma t98A01_crosscap_homology_ranks (g : ℕ) (hg : 0 < g) :
    Module.Finite ℤ (BoundaryCokernel (standardPairingData false g hg)) ∧
      Module.finrank ℤ (BoundaryCokernel (standardPairingData false g hg)) = g - 1 ∧
      Module.Finite ℤ (BoundaryKernel (standardPairingData false g hg)) ∧
      Module.finrank ℤ (BoundaryKernel (standardPairingData false g hg)) = 0 := by
  sorry

/-- **Leaf (b8, layer 2: uses b6, b7).**  `χ(N_g) = 2 - g`.

Route.  `PolygonSurfaceHomology.polygonQuotient_homology` gives
`H₀ ≅ ℤ`, `H₁ ≅ BoundaryCokernel`, `H₂ ≅ BoundaryKernel`, `H_k = 0` (`k ≥ 3`);
`t98A01_rationalHomology_finrank` (with `M = ℤ`, the cokernel, the kernel, and
`M = PUnit`-style zero for `k ≥ 3`) gives finite dimensions `1, g - 1, 0, 0`;
take `bound = 2`; the trace of the identity is `finrank` (`LinearMap.trace_id`;
`induced (ContinuousMap.id X) k` is the identity by functoriality).
`1 - (g - 1) + 0 = 2 - g` in `ℚ` (`g ≥ 1`).  About 80–160 lines. -/
lemma t98A01_hasEulerCharacteristic_crosscap (g : ℕ) (hg : 0 < g) :
    HasEulerCharacteristic (standardPairingData false g hg).Space (2 - (g : ℚ)) := by
  sorry

/-- **Leaf (b9).**  `HasEulerCharacteristic` is a homeomorphism invariant.

Route.  The homology functor sends the homeomorphism to isomorphisms
`Homology X k ≅ Homology Y k` (`TopCat.isoOfHomeo`, `Functor.mapIso`), giving
linear equivalences: finite dimensionality and subsingletons transfer; the
trace of the identity is `finrank`, preserved (`LinearEquiv.finrank_eq`).
About 60–120 lines. -/
lemma t98A01_hasEulerCharacteristic_of_homeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {v : ℚ} (h : HasEulerCharacteristic Y v) :
    HasEulerCharacteristic X v := by
  sorry

/-! ## Assembly -/

theorem apm_t98a01 :
    t98A01IsRegularNfoldCover 5 t98A01TorusFiveCover ∧
    (∀ (g h : ℕ) (p : Surface true g → Surface true h),
      t98A01IsRegularNfoldCover 5 p →
      Nonempty (Surface true g ≃ₜ Surface true h) →
      eulerCharacteristic true g = 5 * eulerCharacteristic true h ∧
      g = 1 ∧ h = 1) ∧
    Nonempty (PolygonMoves.PolygonSurface (t98A01TorusWord .T₁) ≃ₜ Surface true 1) ∧
    Nonempty (PolygonMoves.PolygonSurface (t98A01ProjectiveWord .P) ≃ₜ
      Surface false 1) ∧
    Nonempty (PolygonMoves.PolygonSurface (t98A01KleinWord .K₁) ≃ₜ Surface false 2) ∧
    Nonempty (T98A01SumSurface ≃ₜ Surface false 11) ∧
    ConstructionTargets.RationalLefschetz.HasEulerCharacteristic T98A01SumSurface (-9) := by
  have hsum : Nonempty (T98A01SumSurface ≃ₜ Surface false 11) :=
    homeomorph_trans t98A01_sum_normalForm
      (t98A01_crosscap_bridge 11 (by norm_num) t98A01CrosscapLetters (by decide))
  refine ⟨⟨t98A01_torusFive_isNfoldCover, t98A01_torusFive_deck⟩, ?_, ?_, ?_, ?_, hsum, ?_⟩
  · intro g h p hp he
    obtain ⟨rfl, rfl⟩ := t98A01_orientable_cover_genus g h p hp.1 he
    exact ⟨by norm_num [eulerCharacteristic], rfl, rfl⟩
  · exact t98A01_torus_bridge ((T98A01Summand.T₁, false), true) ((T98A01Summand.T₁, true), true) (by decide)
  · exact t98A01_crosscap_bridge 1 (by norm_num) ![((T98A01Summand.P, false), true)] (by decide)
  · obtain ⟨e₁⟩ := t98A01_kleinBlock [] [] ((T98A01Summand.K₁, false), true) ((T98A01Summand.K₁, true), true)
      (by decide) (by decide) (by decide) (by unfold IsPolygonWord; decide)
    obtain ⟨e₂⟩ := t98A01_crosscap_bridge 2 (by norm_num)
      ![((T98A01Summand.K₁, false), true), ((T98A01Summand.K₁, true), false)] (by decide)
    exact ⟨e₁.trans e₂⟩
  · obtain ⟨e⟩ := hsum
    have hχ := t98A01_hasEulerCharacteristic_crosscap 11 (by norm_num)
    have h' := t98A01_hasEulerCharacteristic_of_homeomorph
      (e.trans (standardPairingData_space_homeomorph false 11 (by norm_num)).symm) hχ
    norm_num at h'
    exact h'

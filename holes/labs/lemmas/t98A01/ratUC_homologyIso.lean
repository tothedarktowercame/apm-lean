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
import ConstructionTargets.UnitAddCircleFiveTorsionCardinality

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

/-! # Blueprint (claude-14, 2026-10-17)

Everything above is the registered statement block of `Main.lean`, verbatim.
Route: see `BLUEPRINT.md`.  Leaves are the theorems ending in `sorry`.  Every
other declaration below is proved. -/

open CategoryTheory
open ConstructionTargets ConstructionTargets.SurfaceGroupBetti
open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology
open ConstructionTargets.RationalLefschetz

/-! ## Shared polygon normal-form material (`polygonNF_*`)

This section is copied verbatim into the t98A01 and t94J09 blueprints.  The
helpers are proved here.  The one leaf, `polygonNF_crosscap_eqvGen_iff`, ends
in `sorry`.  It states only the relation-level comparison; the homeomorphism
`polygonNF_crosscapBridge` is assembled from it. -/

section PolygonNF

open ConstructionTargets.Surfaces PolygonMoves

/-- Two quotient maps out of the same space with the same fibres have
homeomorphic targets. -/
theorem polygonNF_homeomorph_of_fibres {Z X Y : Type*} [TopologicalSpace Z]
    [TopologicalSpace X] [TopologicalSpace Y] {p : Z → X} {q : Z → Y}
    (hp : Topology.IsQuotientMap p) (hq : Topology.IsQuotientMap q)
    (h : ∀ x y, p x = p y ↔ q x = q y) : Nonempty (X ≃ₜ Y) := by
  let p' : C(Z, X) := ⟨p, hp.continuous⟩
  let q' : C(Z, Y) := ⟨q, hq.continuous⟩
  have hker : Setoid.ker p' = Setoid.ker q' := Setoid.ext fun x y => h x y
  have e₁ := Topology.IsQuotientMap.homeomorph (f := p') hp
  have e₂ := Topology.IsQuotientMap.homeomorph (f := q') hq
  rw [hker] at e₁
  exact ⟨e₁.symm.trans e₂⟩

/-- The disk quotients of two relations with the same equivalence closure are
homeomorphic.  Every polygon surface in the repository is such a quotient. -/
theorem polygonNF_quotient_homeomorph {r s : Disk → Disk → Prop}
    (h : ∀ x y, Relation.EqvGen r x y ↔ Relation.EqvGen s x y) :
    Nonempty (@Homeomorph (Quotient (Relation.EqvGen.setoid r))
      (Quotient (Relation.EqvGen.setoid s))
      (TopologicalSpace.coinduced (fun x : Disk => Quotient.mk _ x) inferInstance)
      (TopologicalSpace.coinduced (fun x : Disk => Quotient.mk _ x) inferInstance)) := by
  letI : TopologicalSpace (Quotient (Relation.EqvGen.setoid r)) :=
    TopologicalSpace.coinduced (fun x : Disk => Quotient.mk _ x) inferInstance
  letI : TopologicalSpace (Quotient (Relation.EqvGen.setoid s)) :=
    TopologicalSpace.coinduced (fun x : Disk => Quotient.mk _ x) inferInstance
  refine polygonNF_homeomorph_of_fibres (p := fun x : Disk => Quotient.mk _ x)
    (q := fun x : Disk => Quotient.mk _ x) ⟨Quotient.mk_surjective, rfl⟩
    ⟨Quotient.mk_surjective, rfl⟩ ?_
  intro x y
  rw [Quotient.eq, Quotient.eq]
  exact h x y

/-- One forward `cutAndPaste` step between two explicitly written words. -/
theorem polygonNF_cutStep {L : Type*} [DecidableEq L] (w w' : List (Signed L))
    (u v t : List (Signed L)) (x : Signed L)
    (hw₀ : w = u ++ [x] ++ v ++ [x] ++ t)
    (hw₁ : w' = u ++ [x, x] ++ inverseWord v ++ t)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst) (hw : IsPolygonWord w) :
    Nonempty (PolygonSurface w ≃ₜ PolygonSurface w') := by
  subst hw₀ hw₁
  exact cutAndPaste u v t x hx hw

/-- One `cutAndPaste` step used from right to left. -/
theorem polygonNF_uncutStep {L : Type*} [DecidableEq L] (w w' : List (Signed L))
    (u v t : List (Signed L)) (x : Signed L)
    (hw₀ : w = u ++ [x, x] ++ inverseWord v ++ t)
    (hw₁ : w' = u ++ [x] ++ v ++ [x] ++ t)
    (hx : x.1 ∉ (u ++ v ++ t).map Prod.fst) (hw : IsPolygonWord w') :
    Nonempty (PolygonSurface w ≃ₜ PolygonSurface w') := by
  subst hw₀ hw₁
  obtain ⟨e⟩ := cutAndPaste u v t x hx hw
  exact ⟨e.symm⟩

/-- One `inversePairCancellation` step between explicitly written words. -/
theorem polygonNF_cancelStep {L : Type*} [DecidableEq L] (w w' : List (Signed L))
    (u v : List (Signed L)) (x : Signed L)
    (hw₀ : w = u ++ [x, inv x] ++ v) (hw₁ : w' = u ++ v)
    (hx : x.1 ∉ (u ++ v).map Prod.fst) (hrest : IsPolygonWord w') :
    Nonempty (PolygonSurface w ≃ₜ PolygonSurface w') := by
  subst hw₀ hw₁
  exact inversePairCancellation u v x hx hrest

/-- The crosscap word `c₀ c₀ c₁ c₁ ⋯ c_{g-1} c_{g-1}`. -/
def polygonNF_crosscapWord {L : Type*} (g : ℕ) (c : Fin g → Signed L) :
    List (Signed L) :=
  (List.finRange g).flatMap fun i => [c i, c i]

/-- The handle word `a₀ b₀ a₀⁻¹ b₀⁻¹ ⋯ a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹`. -/
def polygonNF_handleWord {L : Type*} (g : ℕ) (a b : Fin g → Signed L) :
    List (Signed L) :=
  (List.finRange g).flatMap fun i => [a i, b i, inv (a i), inv (b i)]

/-- **Shared leaf `polygonNF_crosscap_eqvGen_iff`.**  With distinct labels,
the crosscap word generates the same equivalence relation on the disk as the
standard model `SurfaceRel false g`.

Route.  As `PolygonMoves.crosscapTwo_bridge_aux_eqv`, for general `g`.  The
word has length `2g`; position `i` carries `c (i / 2)`
(`List.getElem_flatMap`-style lemma, or induction on `g` with
`List.finRange_succ`).  By injectivity, two distinct positions carry the same
label iff they are `2j, 2j+1` (either order).  Both carry the same sign, so
`WordRel` glues `t ↦ t`.  That is literally
`edgePoint (2g) (2j) t ~ edgePoint (2g) (2j+1) t`.  The reversed order is the
symmetric generator.  Degenerate case `g = 0`: both relations are empty.
About 80–160 lines. -/
lemma polygonNF_crosscap_eqvGen_iff_aux_length {L : Type*} (g : ℕ)
    (c : Fin g → Signed L) : (polygonNF_crosscapWord g c).length = 2 * g := by
  simp [polygonNF_crosscapWord, List.length_flatMap]
  omega

lemma polygonNF_crosscap_eqvGen_iff_aux_flat_get {A B : Type*}
    (f : A → B) (xs : List A) (i : ℕ) :
    (xs.flatMap fun a => [f a, f a])[i]? = Option.map f xs[i / 2]? := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          cases i with
          | zero => simp
          | succ k =>
              have hd : (k + 2) / 2 = k / 2 + 1 := by omega
              simpa [hd] using ih k

lemma polygonNF_crosscap_eqvGen_iff_aux_get {L : Type*} (g : ℕ)
    (c : Fin g → Signed L) (i : Fin (polygonNF_crosscapWord g c).length) :
    (polygonNF_crosscapWord g c).get i =
      c ⟨i.1 / 2, by
        have hi := i.2
        have hlen := polygonNF_crosscap_eqvGen_iff_aux_length g c
        omega⟩ := by
  rw [List.get_eq_getElem]
  have h := polygonNF_crosscap_eqvGen_iff_aux_flat_get c (List.finRange g) i
  have hf : i.1 < ((List.finRange g).flatMap (fun a => [c a, c a])).length := by
    simpa [polygonNF_crosscapWord] using i.2
  rw [List.getElem?_eq_getElem hf] at h
  have hi : i.1 / 2 < (List.finRange g).length := by
    simp only [List.length_finRange]
    have hlen := polygonNF_crosscap_eqvGen_iff_aux_length g c
    omega
  rw [List.getElem?_eq_getElem hi] at h
  simpa [polygonNF_crosscapWord] using Option.some.inj h

lemma polygonNF_crosscap_eqvGen_iff_aux_surface_to_word {L : Type*}
    [DecidableEq L] (g : ℕ) (c : Fin g → Signed L) {x y : Disk}
    (h : SurfaceRel false g x y) : WordRel (polygonNF_crosscapWord g c) x y := by
  simp only [SurfaceRel, Bool.false_eq_true, if_false] at h
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  have hlen := polygonNF_crosscap_eqvGen_iff_aux_length g c
  let i₀ : Fin (polygonNF_crosscapWord g c).length := ⟨2 * j, by omega⟩
  let i₁ : Fin (polygonNF_crosscapWord g c).length := ⟨2 * j + 1, by omega⟩
  have hget₀ : (polygonNF_crosscapWord g c).get i₀ = c ⟨j, hj⟩ := by
    rw [polygonNF_crosscap_eqvGen_iff_aux_get]
    congr 1
    apply Fin.ext
    simp [i₀]
  have hget₁ : (polygonNF_crosscapWord g c).get i₁ = c ⟨j, hj⟩ := by
    rw [polygonNF_crosscap_eqvGen_iff_aux_get]
    congr 1
    apply Fin.ext
    simp [i₁]
    omega
  refine ⟨i₀, i₁, ?_, t, ?_, ?_, ?_⟩
  · intro he
    have := congrArg Fin.val he
    simp [i₀, i₁] at this
  · rw [hget₀, hget₁]
  · simp [i₀, hlen]
  · rw [hget₀, hget₁]
    simp [i₁, hlen]

lemma polygonNF_crosscap_eqvGen_iff_aux_word_to_surface {L : Type*}
    [DecidableEq L] (g : ℕ) (c : Fin g → Signed L)
    (hc : Function.Injective fun i => (c i).1) {x y : Disk}
    (h : WordRel (polygonNF_crosscapWord g c) x y) :
    Relation.EqvGen (SurfaceRel false g) x y := by
  rcases h with ⟨i, j, hij, t, hlabel, rfl, rfl⟩
  rw [polygonNF_crosscap_eqvGen_iff_aux_get,
    polygonNF_crosscap_eqvGen_iff_aux_get] at hlabel ⊢
  have hidx := hc hlabel
  have hq : i.1 / 2 = j.1 / 2 := by
    exact Fin.val_eq_of_eq hidx
  have hsign : (c ⟨i.1 / 2, by
      have hlen := polygonNF_crosscap_eqvGen_iff_aux_length g c
      omega⟩).2 = (c ⟨j.1 / 2, by
      have hlen := polygonNF_crosscap_eqvGen_iff_aux_length g c
      omega⟩).2 := congrArg (fun k => (c k).2) hidx
  have hlen := polygonNF_crosscap_eqvGen_iff_aux_length g c
  have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  have hjg : j.1 / 2 < g := by omega
  have hig : i.1 / 2 < g := by omega
  have hpairs :
      (i.1 = 2 * (i.1 / 2) ∧ j.1 = 2 * (i.1 / 2) + 1) ∨
      (j.1 = 2 * (i.1 / 2) ∧ i.1 = 2 * (i.1 / 2) + 1) := by
    omega
  rcases hpairs with hp | hp
  · have hr : SurfaceRel false g
        (edgePoint (polygonNF_crosscapWord g c).length i t)
        (edgePoint (polygonNF_crosscapWord g c).length j t) := by
      simp only [SurfaceRel, Bool.false_eq_true, if_false]
      refine ⟨i.1 / 2, hig, t, ?_, ?_⟩
      · congr 1 <;> omega
      · congr 1 <;> omega
    simp only [hsign, if_true]
    exact Relation.EqvGen.rel _ _ hr
  · have hr : SurfaceRel false g
        (edgePoint (polygonNF_crosscapWord g c).length j t)
        (edgePoint (polygonNF_crosscapWord g c).length i t) := by
      simp only [SurfaceRel, Bool.false_eq_true, if_false]
      refine ⟨i.1 / 2, hig, t, ?_, ?_⟩
      · congr 1 <;> omega
      · congr 1 <;> omega
    simp only [hsign, if_true]
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hr)

theorem polygonNF_crosscap_eqvGen_iff {L : Type*} [DecidableEq L] (g : ℕ)
    (c : Fin g → Signed L) (hc : Function.Injective fun i => (c i).1)
    (x y : Disk) :
    Relation.EqvGen (WordRel (polygonNF_crosscapWord g c)) x y ↔
      Relation.EqvGen (SurfaceRel false g) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact polygonNF_crosscap_eqvGen_iff_aux_word_to_surface g c hc h
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h =>
        exact Relation.EqvGen.rel _ _
          (polygonNF_crosscap_eqvGen_iff_aux_surface_to_word g c h)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Crosscap bridge: the crosscap word with distinct labels presents
`Surface false g`. -/
theorem polygonNF_crosscapBridge {L : Type*} [DecidableEq L] (g : ℕ)
    (c : Fin g → Signed L) (hc : Function.Injective fun i => (c i).1) :
    Nonempty (PolygonSurface (polygonNF_crosscapWord g c) ≃ₜ Surface false g) :=
  polygonNF_quotient_homeomorph (polygonNF_crosscap_eqvGen_iff g c hc)

end PolygonNF

section PolygonNFHandle

open ConstructionTargets.Surfaces PolygonMoves

/-- **Family leaf `polygonNF_handle_eqvGen_iff`** (t98A01 here;
later t94J04, t00A02).  With `2g` distinct labels, the handle word generates
the same equivalence relation on the disk as the standard model
`SurfaceRel true g`.

Route.  Same pattern as the crosscap leaf.  Position `4j + r` carries
`a j, b j, inv (a j), inv (b j)` for `r = 0, 1, 2, 3`.  The only same-label
pairs are `{4j, 4j+2}` and `{4j+1, 4j+3}`, with opposite signs, so `WordRel`
glues `t ↦ 1 - t` (`reverseParameter`).  That is the `tr` of `SurfaceRel true g`.
Degenerate case `g = 0`: both relations are empty.  About 100–200 lines. -/
theorem polygonNF_handle_eqvGen_iff {L : Type*} [DecidableEq L] (g : ℕ)
    (a b : Fin g → Signed L)
    (hab : Function.Injective fun p : Fin g × Bool =>
      if p.2 then (b p.1).1 else (a p.1).1)
    (x y : Disk) :
    Relation.EqvGen (WordRel (polygonNF_handleWord g a b)) x y ↔
      Relation.EqvGen (SurfaceRel true g) x y := by
  sorry

/-- Handle bridge: the handle word with distinct labels presents
`Surface true g`. -/
theorem polygonNF_handleBridge {L : Type*} [DecidableEq L] (g : ℕ)
    (a b : Fin g → Signed L)
    (hab : Function.Injective fun p : Fin g × Bool =>
      if p.2 then (b p.1).1 else (a p.1).1) :
    Nonempty (PolygonSurface (polygonNF_handleWord g a b) ≃ₜ Surface true g) :=
  polygonNF_quotient_homeomorph (polygonNF_handle_eqvGen_iff g a b hab)

end PolygonNFHandle

/-! ## (a) The five-fold torus cover -/

lemma t98A01_circleFive_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (5 • · : UnitAddCircle → UnitAddCircle)
      (nsmulAddMonoidHom (α := UnitAddCircle) 5).ker := by
  exact AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 5

lemma t98A01_circleFive_isCoveringMap :
    IsCoveringMap (5 • · : UnitAddCircle → UnitAddCircle) :=
  t98A01_circleFive_isAddQuotientCoveringMap.isCoveringMap

/-- **Leaf `t98A01_torusFive_isNfoldCover`.**  `(x, y) ↦ (5x, y)` is a covering
with fibres of size 5.

Route.  Covering: banked
`ProductEvenlyCoveredTrivialization.isCoveringMap_productMap` with
`t98A01_circleFive_isCoveringMap` and the identity covering
(`IsCoveringMap.id` or `Homeomorph.refl _ |>.isCoveringMap`); the map is
`productMap (5 • ·) id` by `rfl`.  Fibre over `(x, y)`: the second coordinate
is forced, so the fibre is `{a // 5 • a = x}`.  Pick `a₀` with `5 • a₀ = x`
(`nsmul` is surjective on `AddCircle`, e.g. from the covering map, or
`AddCircle.nsmul_surjective`-style).  Then `a ↦ a - a₀` is a bijection onto
the kernel `UnitAddCircleFiveTorsionCardinality.fiveKernel`, whose card is
banked as `fiveKernel_natCard = 5`.  About 40–100 lines. -/
lemma t98A01_torusFive_isNfoldCover_aux_id :
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

theorem t98A01_torusFive_isNfoldCover :
    t98A01IsNfoldCover 5 t98A01TorusFiveCover := by
  constructor
  · simpa [t98A01TorusFiveCover,
      ConstructionTargets.ProductEvenlyCoveredTrivialization.productMap] using
      ConstructionTargets.ProductEvenlyCoveredTrivialization.isCoveringMap_productMap
        t98A01_circleFive_isCoveringMap t98A01_torusFive_isNfoldCover_aux_id
  · intro b
    obtain ⟨a₀, ha₀⟩ := t98A01_circleFive_isAddQuotientCoveringMap.surjective b.1
    change 5 • a₀ = b.1 at ha₀
    let e : {x : T98A01Torus // t98A01TorusFiveCover x = b} ≃
        UnitAddCircleFiveTorsionCardinality.fiveKernel :=
      { toFun := fun x ↦ ⟨x.1.1 - a₀, by
          change 5 • (x.1.1 - a₀) = 0
          rw [nsmul_sub, ha₀]
          have hx := congrArg Prod.fst x.2
          change 5 • x.1.1 = b.1 at hx
          rw [hx, sub_self]⟩
        invFun := fun k ↦ ⟨(k.1 + a₀, b.2), by
          have hk : 5 • k.1 = 0 := k.2
          apply Prod.ext
          · change 5 • (k.1 + a₀) = b.1
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
    exact UnitAddCircleFiveTorsionCardinality.fiveKernel_natCard

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

/-- The standard orientable pairing data of genus `g` has `2g` edge orbits
(re-indexed by the banked `PolygonSurfacePiOne.orientableOrbitEquiv`). -/
theorem t98A01_orientable_data_card (g : ℕ) (hg : 0 < g) :
    Nat.card (PairingOrbit (standardPairingData true g hg).pair) = 2 * g := by
  change Nat.card (PairingOrbit (orientablePair g)) = 2 * g
  rw [Nat.card_congr (orientableOrbitEquiv g)]
  simp [Nat.card_eq_fintype_card, mul_comm]

/-- **Leaf `t98A01_surfaceTrueZero_pi1_subsingleton`.**  `Surface true 0` (no
edge identifications: the closed disk) has trivial fundamental group.

Route.  `SurfaceRel true 0` is empty (`j < 0`), so `EqvGen` is equality and
`surfaceQuotient true 0` is a continuous bijection from the compact disk onto
a quotient whose topology is coinduced: a homeomorphism `Disk ≃ₜ Surface true 0`
(`polygonNF_homeomorph_of_fibres` with the identity quotient map on `Disk`
gives it directly).  The disk is convex, hence contractible
(`Convex.contractibleSpace`), hence `SimplyConnectedSpace`; transport along the
homeomorphism.  About 40–100 lines. -/
theorem t98A01_surfaceTrueZero_pi1_subsingleton (x : Surface true 0) :
    Subsingleton (FundamentalGroup (Surface true 0) x) := by
  have hrel (a b : Disk) :
      Relation.EqvGen (SurfaceRel true 0) a b ↔ a = b := by
    constructor
    · intro h
      induction h with
      | rel a b hab => simp [SurfaceRel] at hab
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · rintro rfl
      exact Relation.EqvGen.refl _
  have he : Nonempty (Disk ≃ₜ Surface true 0) :=
    polygonNF_homeomorph_of_fibres
      (p := id) (q := surfaceQuotient true 0)
      Topology.IsQuotientMap.id
      ⟨surjective_surfaceQuotient true 0, rfl⟩
      (fun a b => by
        change a = b ↔ Quotient.mk _ a = Quotient.mk _ b
        rw [Quotient.eq]
        change a = b ↔ Relation.EqvGen (SurfaceRel true 0) a b
        exact (hrel a b).symm)
  letI : ContractibleSpace Disk :=
    Convex.contractibleSpace (convex_closedBall (0 : ℂ) 1)
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let e := Classical.choice he
  letI : ContractibleSpace (Surface true 0) := e.symm.contractibleSpace
  letI : SimplyConnectedSpace (Surface true 0) :=
    SimplyConnectedSpace.ofContractible _
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

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


/-! ## (b) Rational homology from integral homology (universal coefficients)

`HasEulerCharacteristic` uses rational singular homology.  The banked polygon
homology (`PolygonSurfaceHomology.polygonQuotient_homology`) is integral.  The
three leaves below pass from `ℤ` to `ℚ` by extension of scalars.  They are
general homological algebra, not polygon-specific, and serve every rational
Euler-characteristic consumer. -/

/-- Extension of scalars `ℤ → ℚ` on module categories. -/
abbrev ratUC_F : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (algebraMap ℤ ℚ)

abbrev ratUC_chainsZ (X : TopCat.{0}) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

abbrev ratUC_chainsQ (X : TopCat.{0}) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    (ModuleCat.of ℚ ℚ)).obj X

/-- **Leaf `ratUC_chainIso` (UC i).**  Rational singular chains are the
extension of scalars of integral singular chains.

Route.  Both complexes are `alternatingFaceMapComplex` of the simplicial
object `n ↦ ∐_{σ : SingularSimplex X n} R`
(`SSet.singularChainComplexFunctor`).  `AlgebraicTopology.map_alternatingFaceMapComplex`
commutes `F.mapHomologicalComplex` past `alternatingFaceMapComplex`, so it
suffices to give an iso of simplicial objects
`F ∘ (∐ ℤ) ≅ ∐ ℚ`.  `ratUC_F` is a left adjoint
(`ModuleCat.extendRestrictScalarsAdj`), so it preserves coproducts
(`PreservesCoproduct.iso`), and `F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ`
(`TensorProduct.lid`-style).  Naturality in the simplicial index: face maps
are `Sigma.map'` along reindexing, which commute with the coproduct
comparison (`Sigma.hom_ext`).  If `ratUC_F.Additive` is needed it follows from
the adjunction (`Adjunction.left_adjoint_additive`-style, or
`Functor.additive_of_preservesBinaryBiproducts`).  About 100–220 lines. -/
theorem ratUC_chainIso (X : TopCat.{0}) :
    Nonempty ((ratUC_F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (ratUC_chainsZ X) ≅ ratUC_chainsQ X) := by
  sorry

/-- **Leaf `ratUC_homologyIso` (UC ii).**  Extension of scalars to `ℚ`
commutes with homology of any chain complex of abelian groups.

Route.  `ℚ` is a flat `ℤ`-module (`Module.Flat` of a localization, or
torsion-free over a PID), so `ratUC_F` is exact.  An exact functor between
abelian categories preserves homology
(`Functor.preservesHomology_of_map_exact` in
`Mathlib/CategoryTheory/Abelian/Exact.lean`).  Then
`ShortComplex.mapHomologyIso` applied to `K.sc k` gives the iso, since
`((F.mapHomologicalComplex _).obj K).sc k = (K.sc k).map F` up to `Iso.refl`.
About 60–150 lines. -/
-- BEGIN SEAT AREA
theorem ratUC_homologyIso (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (k : ℕ) :
    Nonempty (((ratUC_F.mapHomologicalComplex _).obj K).homology k ≅
      ratUC_F.obj (K.homology k)) := by
  sorry
-- END SEAT AREA

/-- **Leaf `ratUC_finrank` (UC iii).**  For a finitely generated abelian group
`M`, `ℚ ⊗ M` is finite dimensional of dimension `finrank ℤ M`.

Route.  `ratUC_F.obj M` is `ℚ ⊗[ℤ] M` (`ModuleCat.ExtendScalars.obj'`).
Finite: `Module.Finite.base_change`.  Rank: write `M ≃ ℤ^r × T` with `T`
finite (`Module.equiv_free_prod_directSum`, structure theorem over a PID);
`ℚ ⊗ T = 0` because `T` is torsion; `ℚ ⊗ ℤ^r ≅ ℚ^r`
(`Module.finrank_baseChange`).  `Module.finrank ℤ M = r` because torsion has
rank zero over a domain.  Alternatively `IsLocalizedModule` with
`Module.finrank_of_isLocalizedModule_of_free`-style lemmas.  Degenerate case
`M = 0`: both sides are `0`.  About 60–150 lines. -/
theorem ratUC_finrank (M : Type) [AddCommGroup M] [Module.Finite ℤ M] :
    FiniteDimensional ℚ (ratUC_F.obj (ModuleCat.of ℤ M)) ∧
      Module.finrank ℚ (ratUC_F.obj (ModuleCat.of ℤ M)) = Module.finrank ℤ M := by
  sorry

/-- Layer 2 (uses UC i–iii): rational homology rank from an integral
computation. -/
theorem ratUC_rationalHomology_finrank (X : Type) [TopologicalSpace X] (k : ℕ)
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M]
    (e : SpaceH X k ≅ ModuleCat.of ℤ M) :
    FiniteDimensional ℚ (Homology X k) ∧
      Module.finrank ℚ (Homology X k) = Module.finrank ℤ M := by
  obtain ⟨c⟩ := ratUC_chainIso (TopCat.of X)
  obtain ⟨h⟩ := ratUC_homologyIso (ratUC_chainsZ (TopCat.of X)) k
  have i : Homology X k ≅ ratUC_F.obj (ModuleCat.of ℤ M) :=
    (HomologicalComplex.homologyFunctor _ _ k).mapIso c.symm ≪≫ h ≪≫ ratUC_F.mapIso e
  let l := i.toLinearEquiv
  obtain ⟨hfd, hr⟩ := ratUC_finrank M
  exact ⟨LinearEquiv.finiteDimensional l.symm, l.finrank_eq.trans hr⟩

/-! ## (b) Euler characteristic of the standard surfaces (`polygonNF_*` family) -/

/-- The identity acts on rational homology with trace equal to its rank. -/
theorem polygonNF_trace_induced_id (X : Type) [TopologicalSpace X] (k : ℕ)
    [FiniteDimensional ℚ (Homology X k)] :
    LinearMap.trace ℚ (Homology X k) (induced (ContinuousMap.id X) k).hom =
      Module.finrank ℚ (Homology X k) := by
  have h : induced (ContinuousMap.id X) k = 𝟙 _ := by
    simp only [induced]
    exact CategoryTheory.Functor.map_id _ _
  rw [h, ModuleCat.hom_id, LinearMap.trace_id]

/-- `HasEulerCharacteristic` from finite ranks: the trace of the identity is
the rank. -/
theorem polygonNF_hasEulerCharacteristic_of_finrank (X : Type) [TopologicalSpace X]
    (hfd : ∀ k, FiniteDimensional ℚ (Homology X k)) (bound : ℕ)
    (hz : ∀ k, bound < k → Module.finrank ℚ (Homology X k) = 0) (v : ℚ)
    (hv : ∑ k ∈ Finset.range (bound + 1),
      (-1 : ℚ) ^ k * (Module.finrank ℚ (Homology X k) : ℚ) = v) :
    HasEulerCharacteristic X v := by
  refine ⟨hfd, bound, fun k hk => ?_, ?_⟩
  · haveI := hfd k
    exact Module.finrank_zero_iff.mp (hz k hk)
  · rw [← hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := hfd k
    rw [polygonNF_trace_induced_id]

/-- `HasEulerCharacteristic` is a homeomorphism invariant. -/
theorem polygonNF_hasEulerCharacteristic_of_homeomorph {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {v : ℚ}
    (h : HasEulerCharacteristic Y v) : HasEulerCharacteristic X v := by
  obtain ⟨hfd, bound, hsub, hv⟩ := h
  let l : ∀ k, Homology X k ≃ₗ[ℚ] Homology Y k := fun k =>
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo e)).toLinearEquiv
  have hfdX : ∀ k, FiniteDimensional ℚ (Homology X k) := fun k => by
    haveI := hfd k
    exact LinearEquiv.finiteDimensional (l k).symm
  refine polygonNF_hasEulerCharacteristic_of_finrank X hfdX bound (fun k hk => ?_) v ?_
  · haveI := hsub k hk
    rw [(l k).finrank_eq]
    exact Module.finrank_zero_of_subsingleton
  · rw [← hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := hfd k
    rw [polygonNF_trace_induced_id, (l k).finrank_eq]

/-- **Family leaf `polygonNF_standard_boundary_ranks`** (t98A01 here; later
any χ consumer).  Integral ranks of the cellular boundary `ℤ → ℤ^{edges}` of
the standard pairing data.  Orientable: the degree is `0` (each handle orbit
has one `true` and one `false` edge, `handleSign`), so the kernel is `ℤ` and
the cokernel is `ℤ^{2g}`.  Nonorientable: the degree is `-2` on every orbit
(banked `SurfaceGroupBetti.standard_nonorientable_data_aux_degree`), so the
kernel is `0` and the cokernel has rank `g - 1`.

Route.  Orbit counts: `orientableOrbitEquiv`, `nonorientableOrbitEquiv`
(both banked).  Orientable: show `attachingDegree = 0` as in
`standard_nonorientable_data_aux_degree` (sum over `orientableCoord`), then
`attachingBoundary = 0`, `ker = ⊤ ≅ ℤ`, cokernel `≅ (Fin g × Bool → ℤ)`.
Nonorientable: `n • d = 0 → n = 0` for `d ≠ 0` gives `ker = ⊥`; the cokernel
of the span of one nonzero vector in `ℤ^g` has rank `g - 1`
(`Submodule.finrank_quotient_add_finrank` over `ℤ`, or pass to `ℚ`).
`Module.Finite` of a quotient of `Fin`-indexed functions is
`Module.Finite.quotient`.  About 80–200 lines. -/
theorem polygonNF_standard_boundary_ranks (o : Bool) (g : ℕ) (hg : 0 < g) :
    Module.Finite ℤ (BoundaryCokernel (standardPairingData o g hg)) ∧
      Module.finrank ℤ (BoundaryCokernel (standardPairingData o g hg)) =
        (if o then 2 * g else g - 1) ∧
      Module.finrank ℤ (BoundaryKernel (standardPairingData o g hg)) =
        (if o then 1 else 0) := by
  sorry

/-- Layer 2 (uses the ranks leaf and UC i–iii): `χ` of the standard pairing
space. -/
theorem polygonNF_hasEulerCharacteristic_pairingSpace (o : Bool) (g : ℕ) (hg : 0 < g) :
    HasEulerCharacteristic (standardPairingData o g hg).Space
      (Surfaces.eulerCharacteristic o g : ℚ) := by
  set P := standardPairingData o g hg
  obtain ⟨⟨h0⟩, ⟨h1⟩, ⟨h2⟩, h3⟩ := polygonQuotient_homology P
  obtain ⟨hfin1, hr1, hr2⟩ := polygonNF_standard_boundary_ranks o g hg
  have r0 := ratUC_rationalHomology_finrank P.Space 0 ℤ h0
  have r1 := ratUC_rationalHomology_finrank P.Space 1 _ h1
  have r2 := ratUC_rationalHomology_finrank P.Space 2 _ h2
  have r3 : ∀ k, 3 ≤ k → FiniteDimensional ℚ (Homology P.Space k) ∧
      Module.finrank ℚ (Homology P.Space k) = 0 := fun k hk => by
    have z := ratUC_rationalHomology_finrank P.Space k PUnit
      ((h3 k hk).iso (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ PUnit)))
    simpa using z
  have hfd : ∀ k, FiniteDimensional ℚ (Homology P.Space k) := by
    intro k
    rcases k with _ | _ | _ | k
    · exact r0.1
    · exact r1.1
    · exact r2.1
    · exact (r3 (k + 3) (by omega)).1
  refine polygonNF_hasEulerCharacteristic_of_finrank _ hfd 2
    (fun k hk => (r3 k hk).2) _ ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [r0.2, r1.2, r2.2, hr1, hr2]
  cases o
  · simp only [Bool.false_eq_true, ↓reduceIte, Surfaces.eulerCharacteristic_nonorientable]
    rw [Module.finrank_self]
    push_cast [Nat.cast_sub hg]
    ring
  · simp only [↓reduceIte, Surfaces.eulerCharacteristic_orientable]
    rw [Module.finrank_self]
    push_cast
    ring

/-- `χ(Surface o g) = eulerCharacteristic o g` in rational singular homology. -/
theorem polygonNF_hasEulerCharacteristic_surface (o : Bool) (g : ℕ) (hg : 0 < g) :
    HasEulerCharacteristic (Surfaces.Surface o g) (Surfaces.eulerCharacteristic o g : ℚ) :=
  polygonNF_hasEulerCharacteristic_of_homeomorph
    (standardPairingData_space_homeomorph o g hg).symm
    (polygonNF_hasEulerCharacteristic_pairingSpace o g hg)

/-! ## (b) The summand words against the standard models -/

theorem t98A01_torusWord_eq :
    t98A01TorusWord .T₁ =
      polygonNF_handleWord 1 ![((.T₁, false), true)] ![((.T₁, true), true)] := by
  decide

theorem t98A01_torus_bridge :
    Nonempty (PolygonMoves.PolygonSurface (t98A01TorusWord .T₁) ≃ₜ Surface true 1) := by
  rw [t98A01_torusWord_eq]
  exact polygonNF_handleBridge 1 _ _ (by decide)

theorem t98A01_projectiveWord_eq :
    t98A01ProjectiveWord .P = polygonNF_crosscapWord 1 ![((.P, false), true)] := by
  decide

theorem t98A01_projective_bridge :
    Nonempty (PolygonMoves.PolygonSurface (t98A01ProjectiveWord .P) ≃ₜ
      Surface false 1) := by
  rw [t98A01_projectiveWord_eq]
  exact polygonNF_crosscapBridge 1 _ (by decide)

/-! ### The Klein word: two cut-and-paste steps -/

/-- `aK₁ bK₁ bK₁ aK₁` -/
def t98A01Klein_nf1 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, true), true), ((.K₁, true), true),
    ((.K₁, false), true)]

/-- Step 1: cut-and-paste on the pair bK₁. -/
theorem t98A01Klein_move1 :
    Nonempty (PolygonMoves.PolygonSurface (t98A01KleinWord .K₁) ≃ₜ
      PolygonMoves.PolygonSurface t98A01Klein_nf1) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true)]
    [((.K₁, false), false)]
    []
    ((.K₁, true), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹` -/
def t98A01Klein_nf2 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false)]

/-- Step 2: cut-and-paste on the pair aK₁. -/
theorem t98A01Klein_move2 :
    Nonempty (PolygonMoves.PolygonSurface t98A01Klein_nf1 ≃ₜ
      PolygonMoves.PolygonSurface t98A01Klein_nf2) :=
  polygonNF_cutStep _ _
    []
    [((.K₁, true), true), ((.K₁, true), true)]
    []
    ((.K₁, false), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)


theorem t98A01_klein_bridge :
    Nonempty (PolygonMoves.PolygonSurface (t98A01KleinWord .K₁) ≃ₜ
      Surface false 2) := by
  have h := PolygonMoves.homeomorph_trans t98A01Klein_move1 t98A01Klein_move2
  have hw : t98A01Klein_nf2 = polygonNF_crosscapWord 2
      ![((.K₁, false), true), ((.K₁, true), false)] := by decide
  rw [hw] at h
  exact PolygonMoves.homeomorph_trans h (polygonNF_crosscapBridge 2 _ (by decide))

/-! ### The sum word: sixteen cut-and-paste steps

`K₁` by two steps (`a b a⁻¹ b ↦ a b b a ↦ a a b⁻¹ b⁻¹`).  Each handle after a
crosscap pair `x x` by four steps (`x x a b a⁻¹ b⁻¹ ↦ x a⁻¹ x b a⁻¹ b⁻¹ ↦
x a⁻¹ a⁻¹ b⁻¹ x⁻¹ b⁻¹ ↦ x a⁻¹ a⁻¹ b⁻¹ b⁻¹ x ↦ x x b b a a`, the first step
right to left): `T₁` after `(bK₁)⁻¹`, `T₂` after `aT₁`.  `P` is already a
crosscap.  `K₂` by two steps, then `T₃` after `(bK₂)⁻¹`.  Every step is the
banked `PolygonMoves.cutAndPaste` between explicitly written words; side
conditions are `decide`.  In the comments `aS`, `bS` are the labels
`(S, false)`, `(S, true)`. -/

/-- `aK₁ bK₁ bK₁ aK₁ aT₁ bT₁ aT₁⁻¹ bT₁⁻¹ aT₂ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf1 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, true), true), ((.K₁, true), true),
    ((.K₁, false), true), ((.T₁, false), true), ((.T₁, true), true),
    ((.T₁, false), false), ((.T₁, true), false), ((.T₂, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 1: cut-and-paste on the pair bK₁. -/
theorem t98A01_move1 :
    Nonempty (PolygonMoves.PolygonSurface t98A01SumWord ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf1) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true)]
    [((.K₁, false), false)]
    [((.T₁, false), true), ((.T₁, true), true), ((.T₁, false), false),
      ((.T₁, true), false), ((.T₂, false), true), ((.T₂, true), true),
      ((.T₂, false), false), ((.T₂, true), false), ((.P, false), true),
      ((.P, false), true), ((.K₂, false), true), ((.K₂, true), true),
      ((.K₂, false), false), ((.K₂, true), true), ((.T₃, false), true),
      ((.T₃, true), true), ((.T₃, false), false), ((.T₃, true), false)]
    ((.K₁, true), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ aT₁ bT₁ aT₁⁻¹ bT₁⁻¹ aT₂ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf2 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, false), true), ((.T₁, true), true),
    ((.T₁, false), false), ((.T₁, true), false), ((.T₂, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 2: cut-and-paste on the pair aK₁. -/
theorem t98A01_move2 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf1 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf2) :=
  polygonNF_cutStep _ _
    []
    [((.K₁, true), true), ((.K₁, true), true)]
    [((.T₁, false), true), ((.T₁, true), true), ((.T₁, false), false),
      ((.T₁, true), false), ((.T₂, false), true), ((.T₂, true), true),
      ((.T₂, false), false), ((.T₂, true), false), ((.P, false), true),
      ((.P, false), true), ((.K₂, false), true), ((.K₂, true), true),
      ((.K₂, false), false), ((.K₂, true), true), ((.T₃, false), true),
      ((.T₃, true), true), ((.T₃, false), false), ((.T₃, true), false)]
    ((.K₁, false), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ aT₁⁻¹ bK₁⁻¹ bT₁ aT₁⁻¹ bT₁⁻¹ aT₂ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf3 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.T₁, false), false), ((.K₁, true), false), ((.T₁, true), true),
    ((.T₁, false), false), ((.T₁, true), false), ((.T₂, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 3: cut-and-paste on bK₁⁻¹, right to left. -/
theorem t98A01_move3 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf2 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf3) :=
  polygonNF_uncutStep _ _
    [((.K₁, false), true), ((.K₁, false), true)]
    [((.T₁, false), false)]
    [((.T₁, true), true), ((.T₁, false), false), ((.T₁, true), false),
      ((.T₂, false), true), ((.T₂, true), true), ((.T₂, false), false),
      ((.T₂, true), false), ((.P, false), true), ((.P, false), true),
      ((.K₂, false), true), ((.K₂, true), true), ((.K₂, false), false),
      ((.K₂, true), true), ((.T₃, false), true), ((.T₃, true), true),
      ((.T₃, false), false), ((.T₃, true), false)]
    ((.K₁, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ aT₁⁻¹ aT₁⁻¹ bT₁⁻¹ bK₁ bT₁⁻¹ aT₂ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf4 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.T₁, false), false), ((.T₁, false), false), ((.T₁, true), false),
    ((.K₁, true), true), ((.T₁, true), false), ((.T₂, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 4: cut-and-paste on the pair aT₁⁻¹. -/
theorem t98A01_move4 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf3 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf4) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false)]
    [((.K₁, true), false), ((.T₁, true), true)]
    [((.T₁, true), false), ((.T₂, false), true), ((.T₂, true), true),
      ((.T₂, false), false), ((.T₂, true), false), ((.P, false), true),
      ((.P, false), true), ((.K₂, false), true), ((.K₂, true), true),
      ((.K₂, false), false), ((.K₂, true), true), ((.T₃, false), true),
      ((.T₃, true), true), ((.T₃, false), false), ((.T₃, true), false)]
    ((.T₁, false), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ aT₁⁻¹ aT₁⁻¹ bT₁⁻¹ bT₁⁻¹ bK₁⁻¹ aT₂ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf5 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.T₁, false), false), ((.T₁, false), false), ((.T₁, true), false),
    ((.T₁, true), false), ((.K₁, true), false), ((.T₂, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 5: cut-and-paste on the pair bT₁⁻¹. -/
theorem t98A01_move5 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf4 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf5) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.T₁, false), false), ((.T₁, false), false)]
    [((.K₁, true), true)]
    [((.T₂, false), true), ((.T₂, true), true), ((.T₂, false), false),
      ((.T₂, true), false), ((.P, false), true), ((.P, false), true),
      ((.K₂, false), true), ((.K₂, true), true), ((.K₂, false), false),
      ((.K₂, true), true), ((.T₃, false), true), ((.T₃, true), true),
      ((.T₃, false), false), ((.T₃, true), false)]
    ((.T₁, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ aT₂ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf6 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 6: cut-and-paste on the pair bK₁⁻¹. -/
theorem t98A01_move6 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf5 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf6) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true)]
    [((.T₁, false), false), ((.T₁, false), false), ((.T₁, true), false),
      ((.T₁, true), false)]
    [((.T₂, false), true), ((.T₂, true), true), ((.T₂, false), false),
      ((.T₂, true), false), ((.P, false), true), ((.P, false), true),
      ((.K₂, false), true), ((.K₂, true), true), ((.K₂, false), false),
      ((.K₂, true), true), ((.T₃, false), true), ((.T₃, true), true),
      ((.T₃, false), false), ((.T₃, true), false)]
    ((.K₁, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₂⁻¹ aT₁ bT₂ aT₂⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf7 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₂, false), false), ((.T₁, false), true),
    ((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 7: cut-and-paste on aT₁, right to left. -/
theorem t98A01_move7 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf6 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf7) :=
  polygonNF_uncutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true)]
    [((.T₂, false), false)]
    [((.T₂, true), true), ((.T₂, false), false), ((.T₂, true), false),
      ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
      ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
      ((.T₃, true), false)]
    ((.T₁, false), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₂⁻¹ aT₂⁻¹ bT₂⁻¹ aT₁⁻¹ bT₂⁻¹ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf8 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₂, false), false), ((.T₂, false), false),
    ((.T₂, true), false), ((.T₁, false), false), ((.T₂, true), false),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 8: cut-and-paste on the pair aT₂⁻¹. -/
theorem t98A01_move8 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf7 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf8) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true)]
    [((.T₁, false), true), ((.T₂, true), true)]
    [((.T₂, true), false), ((.P, false), true), ((.P, false), true),
      ((.K₂, false), true), ((.K₂, true), true), ((.K₂, false), false),
      ((.K₂, true), true), ((.T₃, false), true), ((.T₃, true), true),
      ((.T₃, false), false), ((.T₃, true), false)]
    ((.T₂, false), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₂⁻¹ aT₂⁻¹ bT₂⁻¹ bT₂⁻¹ aT₁ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf9 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₂, false), false), ((.T₂, false), false),
    ((.T₂, true), false), ((.T₂, true), false), ((.T₁, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 9: cut-and-paste on the pair bT₂⁻¹. -/
theorem t98A01_move9 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf8 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf9) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₂, false), false), ((.T₂, false), false)]
    [((.T₁, false), false)]
    [((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
      ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
      ((.T₃, true), false)]
    ((.T₂, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ bK₂ aK₂⁻¹ bK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf10 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 10: cut-and-paste on the pair aT₁. -/
theorem t98A01_move10 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf9 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf10) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true)]
    [((.T₂, false), false), ((.T₂, false), false), ((.T₂, true), false),
      ((.T₂, true), false)]
    [((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, true), true), ((.K₂, false), false), ((.K₂, true), true),
      ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
      ((.T₃, true), false)]
    ((.T₁, false), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ bK₂ bK₂ aK₂ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf11 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, true), true), ((.K₂, true), true), ((.K₂, false), true),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 11: cut-and-paste on the pair bK₂. -/
theorem t98A01_move11 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf10 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf11) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
      ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
      ((.P, false), true), ((.P, false), true), ((.K₂, false), true)]
    [((.K₂, false), false)]
    [((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
      ((.T₃, true), false)]
    ((.K₂, true), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ aK₂ bK₂⁻¹ bK₂⁻¹ aT₃ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf12 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, false), true), ((.K₂, true), false), ((.K₂, true), false),
    ((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 12: cut-and-paste on the pair aK₂. -/
theorem t98A01_move12 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf11 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf12) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
      ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
      ((.P, false), true), ((.P, false), true)]
    [((.K₂, true), true), ((.K₂, true), true)]
    [((.T₃, false), true), ((.T₃, true), true), ((.T₃, false), false),
      ((.T₃, true), false)]
    ((.K₂, false), true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ aK₂ bK₂⁻¹ aT₃⁻¹ bK₂⁻¹ bT₃ aT₃⁻¹ bT₃⁻¹` -/
def t98A01_nf13 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, false), true), ((.K₂, true), false), ((.T₃, false), false),
    ((.K₂, true), false), ((.T₃, true), true), ((.T₃, false), false),
    ((.T₃, true), false)]

/-- Step 13: cut-and-paste on bK₂⁻¹, right to left. -/
theorem t98A01_move13 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf12 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf13) :=
  polygonNF_uncutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
      ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
      ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, false), true)]
    [((.T₃, false), false)]
    [((.T₃, true), true), ((.T₃, false), false), ((.T₃, true), false)]
    ((.K₂, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ aK₂ bK₂⁻¹ aT₃⁻¹ aT₃⁻¹ bT₃⁻¹ bK₂ bT₃⁻¹` -/
def t98A01_nf14 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, false), true), ((.K₂, true), false), ((.T₃, false), false),
    ((.T₃, false), false), ((.T₃, true), false), ((.K₂, true), true),
    ((.T₃, true), false)]

/-- Step 14: cut-and-paste on the pair aT₃⁻¹. -/
theorem t98A01_move14 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf13 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf14) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
      ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
      ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, false), true), ((.K₂, true), false)]
    [((.K₂, true), false), ((.T₃, true), true)]
    [((.T₃, true), false)]
    ((.T₃, false), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ aK₂ bK₂⁻¹ aT₃⁻¹ aT₃⁻¹ bT₃⁻¹ bT₃⁻¹ bK₂⁻¹` -/
def t98A01_nf15 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, false), true), ((.K₂, true), false), ((.T₃, false), false),
    ((.T₃, false), false), ((.T₃, true), false), ((.T₃, true), false),
    ((.K₂, true), false)]

/-- Step 15: cut-and-paste on the pair bT₃⁻¹. -/
theorem t98A01_move15 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf14 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf15) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
      ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
      ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, false), true), ((.K₂, true), false), ((.T₃, false), false),
      ((.T₃, false), false)]
    [((.K₂, true), true)]
    []
    ((.T₃, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `aK₁ aK₁ bK₁⁻¹ bK₁⁻¹ bT₁ bT₁ aT₁ aT₁ bT₂ bT₂ aT₂ aT₂ aP aP aK₂ aK₂ bK₂⁻¹ bK₂⁻¹ bT₃ bT₃ aT₃ aT₃` -/
def t98A01_nf16 : List (PolygonMoves.Signed T98A01Edge) :=
  [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
    ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
    ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
    ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
    ((.K₂, false), true), ((.K₂, true), false), ((.K₂, true), false),
    ((.T₃, true), true), ((.T₃, true), true), ((.T₃, false), true),
    ((.T₃, false), true)]

/-- Step 16: cut-and-paste on the pair bK₂⁻¹. -/
theorem t98A01_move16 :
    Nonempty (PolygonMoves.PolygonSurface t98A01_nf15 ≃ₜ
      PolygonMoves.PolygonSurface t98A01_nf16) :=
  polygonNF_cutStep _ _
    [((.K₁, false), true), ((.K₁, false), true), ((.K₁, true), false),
      ((.K₁, true), false), ((.T₁, true), true), ((.T₁, true), true),
      ((.T₁, false), true), ((.T₁, false), true), ((.T₂, true), true),
      ((.T₂, true), true), ((.T₂, false), true), ((.T₂, false), true),
      ((.P, false), true), ((.P, false), true), ((.K₂, false), true),
      ((.K₂, false), true)]
    [((.T₃, false), false), ((.T₃, false), false), ((.T₃, true), false),
      ((.T₃, true), false)]
    []
    ((.K₂, true), false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)


/-- The eleven crosscap letters of the normal form, in order. -/
def t98A01CrosscapLetters : Fin 11 → PolygonMoves.Signed T98A01Edge :=
  ![((.K₁, false), true), ((.K₁, true), false), ((.T₁, true), true),
    ((.T₁, false), true), ((.T₂, true), true), ((.T₂, false), true),
    ((.P, false), true), ((.K₂, false), true), ((.K₂, true), false),
    ((.T₃, true), true), ((.T₃, false), true)]

theorem t98A01_nf16_eq :
    t98A01_nf16 = polygonNF_crosscapWord 11 t98A01CrosscapLetters := by
  decide

theorem t98A01_sum_normalForm :
    Nonempty (T98A01SumSurface ≃ₜ Surface false 11) := by
  have h := PolygonMoves.homeomorph_trans t98A01_move1 <|
    PolygonMoves.homeomorph_trans t98A01_move2 <|
    PolygonMoves.homeomorph_trans t98A01_move3 <|
    PolygonMoves.homeomorph_trans t98A01_move4 <|
    PolygonMoves.homeomorph_trans t98A01_move5 <|
    PolygonMoves.homeomorph_trans t98A01_move6 <|
    PolygonMoves.homeomorph_trans t98A01_move7 <|
    PolygonMoves.homeomorph_trans t98A01_move8 <|
    PolygonMoves.homeomorph_trans t98A01_move9 <|
    PolygonMoves.homeomorph_trans t98A01_move10 <|
    PolygonMoves.homeomorph_trans t98A01_move11 <|
    PolygonMoves.homeomorph_trans t98A01_move12 <|
    PolygonMoves.homeomorph_trans t98A01_move13 <|
    PolygonMoves.homeomorph_trans t98A01_move14 <|
    PolygonMoves.homeomorph_trans t98A01_move15 t98A01_move16
  rw [t98A01_nf16_eq] at h
  exact PolygonMoves.homeomorph_trans h
    (polygonNF_crosscapBridge 11 t98A01CrosscapLetters (by decide))

theorem t98A01_sum_hasEulerCharacteristic :
    HasEulerCharacteristic T98A01SumSurface (-9) := by
  obtain ⟨e⟩ := t98A01_sum_normalForm
  have h := polygonNF_hasEulerCharacteristic_of_homeomorph e
    (polygonNF_hasEulerCharacteristic_surface false 11 (by norm_num))
  norm_num at h
  exact h

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
  refine ⟨⟨t98A01_torusFive_isNfoldCover, t98A01_torusFive_deck⟩, ?_,
    t98A01_torus_bridge, t98A01_projective_bridge, t98A01_klein_bridge,
    t98A01_sum_normalForm, t98A01_sum_hasEulerCharacteristic⟩
  intro g h p hp he
  obtain ⟨rfl, rfl⟩ := t98A01_orientable_cover_genus g h p hp.1 he
  exact ⟨by norm_num [eulerCharacteristic], rfl, rfl⟩

end

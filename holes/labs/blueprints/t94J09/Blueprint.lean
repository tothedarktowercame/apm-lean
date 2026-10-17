import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonMoves
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.t94J09Closure

/-!
# APM t94J09

## Statement repairs

The harvested TeX includes an old proposed answer claiming a connected sum of
three projective planes, but explicitly warns that computation is not trusted.
It contradicts the problem's stipulated two vertex classes: the resulting CW
structure has `V = 2`, `E = 7`, `F = 1`, hence Euler characteristic `-4` and
non-orientable genus `6`.  The formal conclusion follows the stated gluing
data and therefore classifies the surface as a sum of six projective planes.

## Encoding questions

The signed word determines an actual quotient of the closed disk by its seven
edge pairings. A second quotient realizes the standard polygon
`a₁a₁⋯a₆a₆` for the nonorientable genus-six surface. The conclusion identifies
these spaces by a homeomorphism and computes integral singular homology of the
source quotient, in addition to retaining the cell-count certificate.
-/

open CategoryTheory Set

noncomputable section

/-- The seven edge labels in the polygon. -/
inductive apm_t94J09_Label
  | a | b | c | d | e | f | g
  deriving DecidableEq

/-- An oriented occurrence of a polygon edge. -/
inductive apm_t94J09_SignedLabel
  | pos (x : apm_t94J09_Label)
  | neg (x : apm_t94J09_Label)
  deriving DecidableEq

/-- The edge word `a c d⁻¹ g⁻¹ f e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ f a b`. -/
def apm_t94J09_word : List apm_t94J09_SignedLabel :=
  [.pos .a, .pos .c, .neg .d, .neg .g, .pos .f, .neg .e, .pos .b,
   .neg .c, .neg .d, .neg .g, .neg .e, .pos .f, .pos .a, .pos .b]

/-- The two exceptional corners are those after positions `3` and `9`. -/
def apm_t94J09_vertexClass (i : Fin 14) : Fin 2 :=
  if i.1 = 3 ∨ i.1 = 9 then 1 else 0

/-- Forget the orientation of an edge occurrence. -/
def apm_t94J09_SignedLabel.label : apm_t94J09_SignedLabel → apm_t94J09_Label
  | .pos x | .neg x => x

/-- Number of distinct edge labels in a polygon word. -/
def apm_t94J09_edgeCount (word : List apm_t94J09_SignedLabel) : ℕ :=
  (word.map apm_t94J09_SignedLabel.label).toFinset.card

/-- Number of vertex classes specified by the corner partition. -/
def apm_t94J09_vertexCount {n m : ℕ} (vertexClass : Fin n → Fin m) : ℕ :=
  (Finset.univ.image vertexClass).card

/-- Euler characteristic of the one-face polygonal CW structure. -/
def apm_t94J09_eulerCharacteristic {n m : ℕ}
    (word : List apm_t94J09_SignedLabel)
    (vertexClass : Fin n → Fin m) : ℤ :=
  apm_t94J09_vertexCount vertexClass - apm_t94J09_edgeCount word + 1

/-- Every label occurs once in each orientation, the orientable pairing test. -/
def apm_t94J09_hasOppositeOrientationPairing
    (word : List apm_t94J09_SignedLabel) : Prop :=
  ∀ x : apm_t94J09_Label,
    word.count (.pos x) = 1 ∧ word.count (.neg x) = 1

/-- The genus forced by Euler characteristic in the nonorientable case. -/
def apm_t94J09_nonorientableGenus (chi : ℤ) : ℤ := 2 - chi

abbrev apm_t94J09_Disk := Metric.closedBall (0 : ℂ) 1

/-- Boundary parameter `t` on edge `j` of an `edgeCount`-gon. -/
def apm_t94J09_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t94J09_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_t94J09_reverse (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- The seven edge pairings specified by the signed fourteen-edge word. -/
inductive apm_t94J09_PolygonRel :
    apm_t94J09_Disk → apm_t94J09_Disk → Prop
  | a (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 0 t) (apm_t94J09_edgePoint 14 12 t)
  | b (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 6 t) (apm_t94J09_edgePoint 14 13 t)
  | c (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 1 t)
      (apm_t94J09_edgePoint 14 7 (apm_t94J09_reverse t))
  | d (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 2 t) (apm_t94J09_edgePoint 14 8 t)
  | e (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 5 t) (apm_t94J09_edgePoint 14 10 t)
  | f (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 4 t) (apm_t94J09_edgePoint 14 11 t)
  | g (t) : apm_t94J09_PolygonRel
      (apm_t94J09_edgePoint 14 3 t) (apm_t94J09_edgePoint 14 9 t)

def apm_t94J09_PolygonSurface :=
  Quotient (Relation.EqvGen.setoid apm_t94J09_PolygonRel)

noncomputable instance : TopologicalSpace apm_t94J09_PolygonSurface :=
  TopologicalSpace.coinduced
    (fun x : apm_t94J09_Disk ↦ Quotient.mk _ x) inferInstance

/-- Standard polygon pairings `a₁a₁⋯a₆a₆` for `N₆`. -/
def apm_t94J09_N6Rel (x y : apm_t94J09_Disk) : Prop :=
  ∃ j : ℕ, j < 6 ∧ ∃ t : Set.Icc (0 : ℝ) 1,
    x = apm_t94J09_edgePoint 12 (2 * j) t ∧
    y = apm_t94J09_edgePoint 12 (2 * j + 1) t

def apm_t94J09_N6 :=
  Quotient (Relation.EqvGen.setoid apm_t94J09_N6Rel)

noncomputable instance : TopologicalSpace apm_t94J09_N6 :=
  TopologicalSpace.coinduced
    (fun x : apm_t94J09_Disk ↦ Quotient.mk _ x) inferInstance

/-- The canonical map from the fourteen-gon to its glued surface. -/
def apm_t94J09_polygonQuotient :
    apm_t94J09_Disk → apm_t94J09_PolygonSurface :=
  fun x => Quotient.mk _ x

lemma apm_t94J09_continuous_polygonQuotient :
    Continuous apm_t94J09_polygonQuotient := by
  exact continuous_coinduced_rng

lemma apm_t94J09_surjective_polygonQuotient :
    Function.Surjective apm_t94J09_polygonQuotient := by
  exact Quotient.mk_surjective

/-- The canonical map from the standard twelve-gon to `N₆`. -/
def apm_t94J09_n6Quotient : apm_t94J09_Disk → apm_t94J09_N6 :=
  fun x => Quotient.mk _ x

lemma apm_t94J09_continuous_n6Quotient :
    Continuous apm_t94J09_n6Quotient := by
  exact continuous_coinduced_rng

lemma apm_t94J09_surjective_n6Quotient :
    Function.Surjective apm_t94J09_n6Quotient := by
  exact Quotient.mk_surjective

private lemma apm_t94J09_eqvGen_respects
    {X Z : Type*} {r : X → X → Prop} (f : X → Z)
    (hr : ∀ x y, r x y → f x = f y) {x y : X}
    (hxy : Relation.EqvGen r x y) : f x = f y := by
  induction hxy with
  | rel a b hab => exact hr a b hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Continuous eliminator for the quotient defined by the signed word. -/
noncomputable def apm_t94J09_polygonDesc
    {Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z))
    (hr : ∀ x y, apm_t94J09_PolygonRel x y → f x = f y) :
    C(apm_t94J09_PolygonSurface, Z) :=
  ⟨Quotient.lift f (fun _ _ hxy ↦ apm_t94J09_eqvGen_respects f hr hxy),
    f.continuous.quotient_lift
      (fun _ _ hxy ↦ apm_t94J09_eqvGen_respects f hr hxy)⟩

@[simp] lemma apm_t94J09_polygonDesc_quotient
    {Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z))
    (hr : ∀ x y, apm_t94J09_PolygonRel x y → f x = f y)
    (x : apm_t94J09_Disk) :
    apm_t94J09_polygonDesc f hr (apm_t94J09_polygonQuotient x) = f x := rfl

lemma apm_t94J09_polygonDesc_unique
    {Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z))
    (hr : ∀ x y, apm_t94J09_PolygonRel x y → f x = f y)
    (u : C(apm_t94J09_PolygonSurface, Z))
    (hu : ∀ x, u (apm_t94J09_polygonQuotient x) = f x) :
    u = apm_t94J09_polygonDesc f hr := by
  ext y
  obtain ⟨x, rfl⟩ := apm_t94J09_surjective_polygonQuotient y
  exact hu x

/-- Continuous eliminator for the standard genus-six polygon quotient. -/
noncomputable def apm_t94J09_n6Desc
    {Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z))
    (hr : ∀ x y, apm_t94J09_N6Rel x y → f x = f y) :
    C(apm_t94J09_N6, Z) :=
  ⟨Quotient.lift f (fun _ _ hxy ↦ apm_t94J09_eqvGen_respects f hr hxy),
    f.continuous.quotient_lift
      (fun _ _ hxy ↦ apm_t94J09_eqvGen_respects f hr hxy)⟩

@[simp] lemma apm_t94J09_n6Desc_quotient
    {Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z))
    (hr : ∀ x y, apm_t94J09_N6Rel x y → f x = f y)
    (x : apm_t94J09_Disk) :
    apm_t94J09_n6Desc f hr (apm_t94J09_n6Quotient x) = f x := rfl

lemma apm_t94J09_n6Desc_unique
    {Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z))
    (hr : ∀ x y, apm_t94J09_N6Rel x y → f x = f y)
    (u : C(apm_t94J09_N6, Z))
    (hu : ∀ x, u (apm_t94J09_n6Quotient x) = f x) :
    u = apm_t94J09_n6Desc f hr := by
  ext y
  obtain ⟨x, rfl⟩ := apm_t94J09_surjective_n6Quotient y
  exact hu x

/-- Two relation-respecting disk maps whose composites are identities modulo
the respective relations induce a homeomorphism of the quotient surfaces. -/
noncomputable def apm_t94J09_homeomorphOfDiskMaps
    (p q : C(apm_t94J09_Disk, apm_t94J09_Disk))
    (hp : ∀ x y, apm_t94J09_PolygonRel x y →
      apm_t94J09_n6Quotient (p x) = apm_t94J09_n6Quotient (p y))
    (hq : ∀ x y, apm_t94J09_N6Rel x y →
      apm_t94J09_polygonQuotient (q x) = apm_t94J09_polygonQuotient (q y))
    (hqp : ∀ x, apm_t94J09_polygonQuotient (q (p x)) =
      apm_t94J09_polygonQuotient x)
    (hpq : ∀ x, apm_t94J09_n6Quotient (p (q x)) =
      apm_t94J09_n6Quotient x) :
    apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6 := by
  let pbar : C(apm_t94J09_Disk, apm_t94J09_N6) :=
    ⟨fun x => apm_t94J09_n6Quotient (p x),
      apm_t94J09_continuous_n6Quotient.comp p.continuous⟩
  let qbar : C(apm_t94J09_Disk, apm_t94J09_PolygonSurface) :=
    ⟨fun x => apm_t94J09_polygonQuotient (q x),
      apm_t94J09_continuous_polygonQuotient.comp q.continuous⟩
  let u := apm_t94J09_polygonDesc pbar hp
  let v := apm_t94J09_n6Desc qbar hq
  exact
    { toFun := u
      invFun := v
      continuous_toFun := u.continuous
      continuous_invFun := v.continuous
      left_inv := by
        intro z
        obtain ⟨x, rfl⟩ := apm_t94J09_surjective_polygonQuotient z
        exact hqp x
      right_inv := by
        intro z
        obtain ⟨x, rfl⟩ := apm_t94J09_surjective_n6Quotient z
        exact hpq x }

abbrev apm_t94J09_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t94J09_PolygonSurface))

lemma apm_t94J09_vertexCount_eq :
    apm_t94J09_vertexCount apm_t94J09_vertexClass = 2 := by
  decide

lemma apm_t94J09_edgeCount_eq :
    apm_t94J09_edgeCount apm_t94J09_word = 7 := by
  decide

lemma apm_t94J09_eulerCharacteristic_eq :
    apm_t94J09_eulerCharacteristic apm_t94J09_word
      apm_t94J09_vertexClass = -4 := by
  decide

lemma apm_t94J09_not_oppositeOrientationPairing :
    ¬apm_t94J09_hasOppositeOrientationPairing apm_t94J09_word := by
  intro h
  have ha := h apm_t94J09_Label.a
  simp [apm_t94J09_word] at ha

lemma apm_t94J09_nonorientableGenus_eq :
    apm_t94J09_nonorientableGenus
      (apm_t94J09_eulerCharacteristic apm_t94J09_word
        apm_t94J09_vertexClass) = 6 := by
  decide

/-! # Blueprint (claude-14, 2026-10-17)

Everything above is the registered statement block of `Main.lean`, verbatim.
Route: see `BLUEPRINT.md`.  Leaves are the theorems ending in `sorry`.  Every
other declaration below is proved. -/

open ConstructionTargets ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology

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
theorem polygonNF_crosscap_eqvGen_iff {L : Type*} [DecidableEq L] (g : ℕ)
    (c : Fin g → Signed L) (hc : Function.Injective fun i => (c i).1)
    (x y : Disk) :
    Relation.EqvGen (WordRel (polygonNF_crosscapWord g c)) x y ↔
      Relation.EqvGen (SurfaceRel false g) x y := by
  sorry

/-- Crosscap bridge: the crosscap word with distinct labels presents
`Surface false g`. -/
theorem polygonNF_crosscapBridge {L : Type*} [DecidableEq L] (g : ℕ)
    (c : Fin g → Signed L) (hc : Function.Injective fun i => (c i).1) :
    Nonempty (PolygonSurface (polygonNF_crosscapWord g c) ≃ₜ Surface false g) :=
  polygonNF_quotient_homeomorph (polygonNF_crosscap_eqvGen_iff g c hc)

end PolygonNF

/-! ## The fourteen-edge word as a `PolygonMoves` word -/

/-- Read an oriented occurrence as a `PolygonMoves` signed letter. -/
def t94J09_toSigned : apm_t94J09_SignedLabel → PolygonMoves.Signed apm_t94J09_Label
  | .pos x => (x, true)
  | .neg x => (x, false)

/-- The frozen word `a c d⁻¹ g⁻¹ f e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ f a b`, letter by letter. -/
def t94J09_signedWord : List (PolygonMoves.Signed apm_t94J09_Label) :=
  apm_t94J09_word.map t94J09_toSigned

/-- **Leaf `t94J09_polygonRel_eqvGen_iff`.**  The seven literal generators of
`apm_t94J09_PolygonRel` and the `PolygonMoves.WordRel` of the signed word
generate the same equivalence relation on the disk.

Route.  Both directions by induction on `EqvGen`.  (→) Each of the seven
constructors is one `WordRel` instance: positions `(0,12)`, `(6,13)`,
`(1,7)`, `(2,8)`, `(5,10)`, `(4,11)`, `(3,9)`; only `c` has opposite signs, and
then `WordRel` uses `reverseParameter t`, which equals `apm_t94J09_reverse t`.
`apm_t94J09_edgePoint` and `Surfaces.edgePoint` have the same body (`rfl`).
(←) `WordRel` gives `i ≠ j : Fin 14` with equal labels: `fin_cases i <;>
fin_cases j` and `simp [t94J09_signedWord, apm_t94J09_word]` leaves exactly the
14 ordered pairs above.  The pair `(i, j)` with `i` the larger index is the
symmetric generator.  For `(7,1)` the parameter is reversed twice:
`apm_t94J09_reverse (reverseParameter t) = t` by `Subtype.ext; simp`.  The
closure `ConstructionTargets.t94J09Closure.frozen_boundaryRel_iff_generator`
does the same case split for a sibling relation and is a template.
About 100–200 lines. -/
theorem t94J09_polygonRel_eqvGen_iff (x y : apm_t94J09_Disk) :
    Relation.EqvGen apm_t94J09_PolygonRel x y ↔
      Relation.EqvGen (PolygonMoves.WordRel t94J09_signedWord) x y := by
  sorry

theorem t94J09_bridge :
    Nonempty (apm_t94J09_PolygonSurface ≃ₜ
      PolygonMoves.PolygonSurface t94J09_signedWord) :=
  polygonNF_quotient_homeomorph t94J09_polygonRel_eqvGen_iff

/-! ## Normalization: five cut-and-paste steps and one cancellation

Each step is a banked `PolygonMoves` move (`cutAndPaste` or
`inversePairCancellation`) between explicitly written words.  Side conditions
are closed by `decide`.  The chain was found by a breadth-first search over
the banked moves and is checked here by Lean.  The two vertex classes become
one at the cancellation, which also removes the seventh label. -/

/-- `a a f⁻¹ e g d c b⁻¹ e f⁻¹ g d c⁻¹ b` -/
def t94J09_nf1 : List (PolygonMoves.Signed apm_t94J09_Label) :=
  [(.a, true), (.a, true), (.f, false), (.e, true), (.g, true),
    (.d, true), (.c, true), (.b, false), (.e, true), (.f, false),
    (.g, true), (.d, true), (.c, false), (.b, true)]

/-- Step 1: cut-and-paste on the pair a. -/
theorem t94J09_move1 :
    Nonempty (PolygonMoves.PolygonSurface t94J09_signedWord ≃ₜ
      PolygonMoves.PolygonSurface t94J09_nf1) :=
  polygonNF_cutStep _ _
    []
    [(.c, true), (.d, false), (.g, false), (.f, true), (.e, false),
      (.b, true), (.c, false), (.d, false), (.g, false), (.e, false),
      (.f, true)]
    [(.b, true)]
    (.a, true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ g d c⁻¹ b` -/
def t94J09_nf2 : List (PolygonMoves.Signed apm_t94J09_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.b, true), (.c, false), (.d, false), (.g, false), (.e, false),
    (.g, true), (.d, true), (.c, false), (.b, true)]

/-- Step 2: cut-and-paste on the pair f⁻¹. -/
theorem t94J09_move2 :
    Nonempty (PolygonMoves.PolygonSurface t94J09_nf1 ≃ₜ
      PolygonMoves.PolygonSurface t94J09_nf2) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true)]
    [(.e, true), (.g, true), (.d, true), (.c, true), (.b, false), (.e, true)]
    [(.g, true), (.d, true), (.c, false), (.b, true)]
    (.f, false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g d c b⁻¹ g d c⁻¹ b` -/
def t94J09_nf3 : List (PolygonMoves.Signed apm_t94J09_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.d, true), (.c, true), (.b, false),
    (.g, true), (.d, true), (.c, false), (.b, true)]

/-- Step 3: cut-and-paste on the pair e⁻¹. -/
theorem t94J09_move3 :
    Nonempty (PolygonMoves.PolygonSurface t94J09_nf2 ≃ₜ
      PolygonMoves.PolygonSurface t94J09_nf3) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false)]
    [(.b, true), (.c, false), (.d, false), (.g, false)]
    [(.g, true), (.d, true), (.c, false), (.b, true)]
    (.e, false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b c⁻¹ d⁻¹ d c⁻¹ b` -/
def t94J09_nf4 : List (PolygonMoves.Signed apm_t94J09_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.g, true), (.b, true), (.c, false),
    (.d, false), (.d, true), (.c, false), (.b, true)]

/-- Step 4: cut-and-paste on the pair g. -/
theorem t94J09_move4 :
    Nonempty (PolygonMoves.PolygonSurface t94J09_nf3 ≃ₜ
      PolygonMoves.PolygonSurface t94J09_nf4) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
      (.e, false)]
    [(.d, true), (.c, true), (.b, false)]
    [(.d, true), (.c, false), (.b, true)]
    (.g, true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b b c d⁻¹ d c` -/
def t94J09_nf5 : List (PolygonMoves.Signed apm_t94J09_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.g, true), (.b, true), (.b, true),
    (.c, true), (.d, false), (.d, true), (.c, true)]

/-- Step 5: cut-and-paste on the pair b. -/
theorem t94J09_move5 :
    Nonempty (PolygonMoves.PolygonSurface t94J09_nf4 ≃ₜ
      PolygonMoves.PolygonSurface t94J09_nf5) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
      (.e, false), (.g, true), (.g, true)]
    [(.c, false), (.d, false), (.d, true), (.c, false)]
    []
    (.b, true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b b c c` -/
def t94J09_nf6 : List (PolygonMoves.Signed apm_t94J09_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.g, true), (.b, true), (.b, true),
    (.c, true), (.c, true)]

/-- Step 6: cancel d⁻¹ d. -/
theorem t94J09_move6 :
    Nonempty (PolygonMoves.PolygonSurface t94J09_nf5 ≃ₜ
      PolygonMoves.PolygonSurface t94J09_nf6) :=
  polygonNF_cancelStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
      (.e, false), (.g, true), (.g, true), (.b, true), (.b, true), (.c, true)]
    [(.c, true)]
    (.d, false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- The six crosscap letters of the normal form. -/
def t94J09_crosscapLetters : Fin 6 → PolygonMoves.Signed apm_t94J09_Label :=
  ![(.a, true), (.f, false), (.e, false), (.g, true), (.b, true), (.c, true)]

theorem t94J09_nf6_eq :
    t94J09_nf6 = polygonNF_crosscapWord 6 t94J09_crosscapLetters := by
  decide

theorem t94J09_word_normalForm :
    Nonempty (PolygonMoves.PolygonSurface t94J09_signedWord ≃ₜ
      Surfaces.Surface false 6) := by
  have h := PolygonMoves.homeomorph_trans t94J09_move1 <|
    PolygonMoves.homeomorph_trans t94J09_move2 <|
    PolygonMoves.homeomorph_trans t94J09_move3 <|
    PolygonMoves.homeomorph_trans t94J09_move4 <|
    PolygonMoves.homeomorph_trans t94J09_move5 t94J09_move6
  rw [t94J09_nf6_eq] at h
  exact PolygonMoves.homeomorph_trans h
    (polygonNF_crosscapBridge 6 t94J09_crosscapLetters (by decide))

/-! ## The standard twelve-gon `apm_t94J09_N6` is `Surface false 6` -/

theorem t94J09_surfaceRel_eq_N6Rel :
    Surfaces.SurfaceRel false 6 = apm_t94J09_N6Rel := by
  funext x y
  exact propext Iff.rfl

theorem t94J09_surface_homeomorph_N6 :
    Nonempty (Surfaces.Surface false 6 ≃ₜ apm_t94J09_N6) :=
  polygonNF_quotient_homeomorph fun x y => by rw [t94J09_surfaceRel_eq_N6Rel]

theorem t94J09_normalization :
    Nonempty (apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6) :=
  PolygonMoves.homeomorph_trans t94J09_bridge <|
    PolygonMoves.homeomorph_trans t94J09_word_normalForm
      t94J09_surface_homeomorph_N6

/-! ## Integral homology, transported from the banked `N₆` computation -/

/-- The standard genus-six pairing data present the frozen polygon surface. -/
theorem t94J09_n6Space_homeomorph :
    Nonempty (t94J09Closure.n6PairingData.Space ≃ₜ apm_t94J09_PolygonSurface) := by
  obtain ⟨e⟩ := PolygonMoves.homeomorph_trans t94J09_bridge t94J09_word_normalForm
  exact ⟨(standardPairingData_space_homeomorph false 6 (by omega)).trans e.symm⟩

theorem t94J09_polygon_homology :
    Nonempty (apm_t94J09_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t94J09_H 1 ≅ ModuleCat.of ℤ ((Fin 5 → ℤ) × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t94J09_H k)) := by
  obtain ⟨e⟩ := t94J09_n6Space_homeomorph
  let iso : ∀ k : ℕ, apm_t94J09_H k ≅ H t94J09Closure.n6PairingData k := fun k =>
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e.symm)
  obtain ⟨⟨h0⟩, ⟨h1⟩, h2⟩ := t94J09Closure.n6PolygonHomologyExplicit
  exact ⟨⟨iso 0 ≪≫ h0⟩, ⟨iso 1 ≪≫ h1⟩, fun k hk => (h2 k hk).of_iso (iso k)⟩

/-! ## Assembly -/

theorem apm_t94j09 :
    apm_t94J09_vertexCount apm_t94J09_vertexClass = 2 ∧
    apm_t94J09_edgeCount apm_t94J09_word = 7 ∧
    apm_t94J09_eulerCharacteristic apm_t94J09_word
      apm_t94J09_vertexClass = -4 ∧
    ¬apm_t94J09_hasOppositeOrientationPairing apm_t94J09_word ∧
    apm_t94J09_nonorientableGenus
      (apm_t94J09_eulerCharacteristic apm_t94J09_word
        apm_t94J09_vertexClass) = 6 ∧
    Nonempty (apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6) ∧
    Nonempty (apm_t94J09_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t94J09_H 1 ≅
      ModuleCat.of ℤ ((Fin 5 → ℤ) × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t94J09_H k)) := by
  exact ⟨apm_t94J09_vertexCount_eq, apm_t94J09_edgeCount_eq,
    apm_t94J09_eulerCharacteristic_eq,
    apm_t94J09_not_oppositeOrientationPairing,
    apm_t94J09_nonorientableGenus_eq, t94J09_normalization,
    t94J09_polygon_homology.1, t94J09_polygon_homology.2.1,
    t94J09_polygon_homology.2.2⟩

end

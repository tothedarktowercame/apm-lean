import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonMoves

/-! # Blueprint for APM tunk01 -/

open Set

noncomputable section

inductive apm_tunk01_Label
  | a | b | c | d | e | f | g
  deriving DecidableEq

inductive apm_tunk01_SignedLabel
  | pos (x : apm_tunk01_Label)
  | neg (x : apm_tunk01_Label)
  deriving DecidableEq

def apm_tunk01_word : List apm_tunk01_SignedLabel :=
  [.pos .a, .pos .c, .neg .d, .neg .g, .pos .f, .neg .e, .pos .b,
   .neg .c, .neg .d, .neg .g, .neg .e, .pos .f, .pos .a, .pos .b]

def apm_tunk01_vertexClass (i : Fin 14) : Fin 2 :=
  if i.1 = 3 ∨ i.1 = 9 then 1 else 0

def apm_tunk01_SignedLabel.label : apm_tunk01_SignedLabel → apm_tunk01_Label
  | .pos x | .neg x => x

def apm_tunk01_edgeCount (word : List apm_tunk01_SignedLabel) : ℕ :=
  (word.map apm_tunk01_SignedLabel.label).toFinset.card

def apm_tunk01_vertexCount {n m : ℕ} (vertexClass : Fin n → Fin m) : ℕ :=
  (Finset.univ.image vertexClass).card

def apm_tunk01_eulerCharacteristic {n m : ℕ}
    (word : List apm_tunk01_SignedLabel) (vertexClass : Fin n → Fin m) : ℤ :=
  apm_tunk01_vertexCount vertexClass - apm_tunk01_edgeCount word + 1

def apm_tunk01_hasOppositeOrientationPairing
    (word : List apm_tunk01_SignedLabel) : Prop :=
  ∀ x : apm_tunk01_Label,
    word.count (.pos x) = 1 ∧ word.count (.neg x) = 1

abbrev apm_tunk01_Disk := Metric.closedBall (0 : ℂ) 1

def apm_tunk01_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_tunk01_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_tunk01_reverse (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

inductive apm_tunk01_PolygonRel : apm_tunk01_Disk → apm_tunk01_Disk → Prop
  | a (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 0 t) (apm_tunk01_edgePoint 14 12 t)
  | b (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 6 t) (apm_tunk01_edgePoint 14 13 t)
  | c (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 1 t)
      (apm_tunk01_edgePoint 14 7 (apm_tunk01_reverse t))
  | d (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 2 t) (apm_tunk01_edgePoint 14 8 t)
  | e (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 5 t) (apm_tunk01_edgePoint 14 10 t)
  | f (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 4 t) (apm_tunk01_edgePoint 14 11 t)
  | g (t) : apm_tunk01_PolygonRel
      (apm_tunk01_edgePoint 14 3 t) (apm_tunk01_edgePoint 14 9 t)

def apm_tunk01_PolygonSurface :=
  Quotient (Relation.EqvGen.setoid apm_tunk01_PolygonRel)

noncomputable instance : TopologicalSpace apm_tunk01_PolygonSurface :=
  TopologicalSpace.coinduced
    (fun x : apm_tunk01_Disk ↦ Quotient.mk _ x) inferInstance

def apm_tunk01_N6Rel (x y : apm_tunk01_Disk) : Prop :=
  ∃ j : ℕ, j < 6 ∧ ∃ t : Set.Icc (0 : ℝ) 1,
    x = apm_tunk01_edgePoint 12 (2 * j) t ∧
    y = apm_tunk01_edgePoint 12 (2 * j + 1) t

def apm_tunk01_N6 :=
  Quotient (Relation.EqvGen.setoid apm_tunk01_N6Rel)

noncomputable instance : TopologicalSpace apm_tunk01_N6 :=
  TopologicalSpace.coinduced
    (fun x : apm_tunk01_Disk ↦ Quotient.mk _ x) inferInstance

lemma apm_tunk01_vertexCount_eq :
    apm_tunk01_vertexCount apm_tunk01_vertexClass = 2 := by
  decide

lemma apm_tunk01_edgeCount_eq :
    apm_tunk01_edgeCount apm_tunk01_word = 7 := by
  decide

lemma apm_tunk01_eulerCharacteristic_eq :
    apm_tunk01_eulerCharacteristic apm_tunk01_word
      apm_tunk01_vertexClass = -4 := by
  decide

lemma apm_tunk01_not_oppositeOrientationPairing :
    ¬apm_tunk01_hasOppositeOrientationPairing apm_tunk01_word := by
  intro h
  have ha := h apm_tunk01_Label.a
  simp [apm_tunk01_word] at ha

/-! ## Normalization, ported from the closed t94J09 blueprint (same word, same pairings) -/

open ConstructionTargets ConstructionTargets.PolygonSurfacePiOne

/-! ## Shared polygon normal-form material (`polygonNF_*`)

This section is copied verbatim into the t98A01, t94J09 and tunk01 blueprints.  The
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

/-! ## The fourteen-edge word as a `PolygonMoves` word -/

/-- Read an oriented occurrence as a `PolygonMoves` signed letter. -/
def tunk01_toSigned : apm_tunk01_SignedLabel → PolygonMoves.Signed apm_tunk01_Label
  | .pos x => (x, true)
  | .neg x => (x, false)

/-- The frozen word `a c d⁻¹ g⁻¹ f e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ f a b`, letter by letter. -/
def tunk01_signedWord : List (PolygonMoves.Signed apm_tunk01_Label) :=
  apm_tunk01_word.map tunk01_toSigned

/-- **Leaf `tunk01_polygonRel_eqvGen_iff`.**  The seven literal generators of
`apm_tunk01_PolygonRel` and the `PolygonMoves.WordRel` of the signed word
generate the same equivalence relation on the disk.

Route.  Both directions by induction on `EqvGen`.  (→) Each of the seven
constructors is one `WordRel` instance: positions `(0,12)`, `(6,13)`,
`(1,7)`, `(2,8)`, `(5,10)`, `(4,11)`, `(3,9)`; only `c` has opposite signs, and
then `WordRel` uses `reverseParameter t`, which equals `apm_tunk01_reverse t`.
`apm_tunk01_edgePoint` and `Surfaces.edgePoint` have the same body (`rfl`).
(←) `WordRel` gives `i ≠ j : Fin 14` with equal labels: `fin_cases i <;>
fin_cases j` and `simp [tunk01_signedWord, apm_tunk01_word]` leaves exactly the
14 ordered pairs above.  The pair `(i, j)` with `i` the larger index is the
symmetric generator.  For `(7,1)` the parameter is reversed twice:
`apm_tunk01_reverse (reverseParameter t) = t` by `Subtype.ext; simp`.  The
closure `ConstructionTargets.ConstructionTargets.t94J09Closure.frozen_boundaryRel_iff_generator (t94J09)`
does the same case split for a sibling relation and is a template.
About 100–200 lines. -/
lemma tunk01_polygonRel_eqvGen_iff_aux_forward {x y : apm_tunk01_Disk}
    (h : apm_tunk01_PolygonRel x y) :
    PolygonMoves.WordRel tunk01_signedWord x y := by
  dsimp [tunk01_signedWord, apm_tunk01_word, tunk01_toSigned]
  cases h with
  | a t => exact ⟨0, 12, by decide, t, by decide, rfl, rfl⟩
  | b t => exact ⟨6, 13, by decide, t, by decide, rfl, rfl⟩
  | c t => exact ⟨1, 7, by decide, t, by decide, rfl, rfl⟩
  | d t => exact ⟨2, 8, by decide, t, by decide, rfl, rfl⟩
  | e t => exact ⟨5, 10, by decide, t, by decide, rfl, rfl⟩
  | f t => exact ⟨4, 11, by decide, t, by decide, rfl, rfl⟩
  | g t => exact ⟨3, 9, by decide, t, by decide, rfl, rfl⟩

lemma tunk01_polygonRel_eqvGen_iff_aux_reverse_c (t : Set.Icc (0 : ℝ) 1) :
    Relation.EqvGen apm_tunk01_PolygonRel
      (Surfaces.edgePoint 14 1 (PolygonMoves.reverseParameter t))
      (Surfaces.edgePoint 14 7 t) := by
  apply Relation.EqvGen.rel
  convert apm_tunk01_PolygonRel.c (apm_tunk01_reverse t) using 1 <;>
    ext <;> simp [apm_tunk01_edgePoint, Surfaces.edgePoint,
      apm_tunk01_reverse, PolygonMoves.reverseParameter]

set_option maxHeartbeats 1000000

theorem tunk01_polygonRel_eqvGen_iff (x y : apm_tunk01_Disk) :
    Relation.EqvGen apm_tunk01_PolygonRel x y ↔
      Relation.EqvGen (PolygonMoves.WordRel tunk01_signedWord) x y := by
  constructor
  · intro h
    induction h with
    | rel _ _ hab => exact .rel _ _ (tunk01_polygonRel_eqvGen_iff_aux_forward hab)
    | refl => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | refl => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    | rel _ _ hab =>
      rcases hab with ⟨i, j, hij, t, hlab, rfl, rfl⟩
      fin_cases i <;> fin_cases j <;>
        simp [tunk01_signedWord, apm_tunk01_word, tunk01_toSigned] at hij hlab ⊢
      all_goals (solve
        | simpa only using (tunk01_polygonRel_eqvGen_iff_aux_reverse_c t).symm
        | apply Relation.EqvGen.rel; exact .a t
        | apply Relation.EqvGen.rel; exact .b t
        | apply Relation.EqvGen.rel; exact .c t
        | apply Relation.EqvGen.rel; exact .d t
        | apply Relation.EqvGen.rel; exact .e t
        | apply Relation.EqvGen.rel; exact .f t
        | apply Relation.EqvGen.rel; exact .g t
        | apply Relation.EqvGen.symm; apply Relation.EqvGen.rel; exact .a t
        | apply Relation.EqvGen.symm; apply Relation.EqvGen.rel; exact .b t
        | apply Relation.EqvGen.symm; apply Relation.EqvGen.rel; exact .d t
        | apply Relation.EqvGen.symm; apply Relation.EqvGen.rel; exact .e t
        | apply Relation.EqvGen.symm; apply Relation.EqvGen.rel; exact .f t
        | apply Relation.EqvGen.symm; apply Relation.EqvGen.rel; exact .g t)

set_option maxHeartbeats 200000

theorem tunk01_bridge :
    Nonempty (apm_tunk01_PolygonSurface ≃ₜ
      PolygonMoves.PolygonSurface tunk01_signedWord) :=
  polygonNF_quotient_homeomorph tunk01_polygonRel_eqvGen_iff

/-! ## Normalization: five cut-and-paste steps and one cancellation

Each step is a banked `PolygonMoves` move (`cutAndPaste` or
`inversePairCancellation`) between explicitly written words.  Side conditions
are closed by `decide`.  The chain was found by a breadth-first search over
the banked moves and is checked here by Lean.  The two vertex classes become
one at the cancellation, which also removes the seventh label. -/

/-- `a a f⁻¹ e g d c b⁻¹ e f⁻¹ g d c⁻¹ b` -/
def tunk01_nf1 : List (PolygonMoves.Signed apm_tunk01_Label) :=
  [(.a, true), (.a, true), (.f, false), (.e, true), (.g, true),
    (.d, true), (.c, true), (.b, false), (.e, true), (.f, false),
    (.g, true), (.d, true), (.c, false), (.b, true)]

/-- Step 1: cut-and-paste on the pair a. -/
theorem tunk01_move1 :
    Nonempty (PolygonMoves.PolygonSurface tunk01_signedWord ≃ₜ
      PolygonMoves.PolygonSurface tunk01_nf1) :=
  polygonNF_cutStep _ _
    []
    [(.c, true), (.d, false), (.g, false), (.f, true), (.e, false),
      (.b, true), (.c, false), (.d, false), (.g, false), (.e, false),
      (.f, true)]
    [(.b, true)]
    (.a, true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ g d c⁻¹ b` -/
def tunk01_nf2 : List (PolygonMoves.Signed apm_tunk01_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.b, true), (.c, false), (.d, false), (.g, false), (.e, false),
    (.g, true), (.d, true), (.c, false), (.b, true)]

/-- Step 2: cut-and-paste on the pair f⁻¹. -/
theorem tunk01_move2 :
    Nonempty (PolygonMoves.PolygonSurface tunk01_nf1 ≃ₜ
      PolygonMoves.PolygonSurface tunk01_nf2) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true)]
    [(.e, true), (.g, true), (.d, true), (.c, true), (.b, false), (.e, true)]
    [(.g, true), (.d, true), (.c, false), (.b, true)]
    (.f, false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g d c b⁻¹ g d c⁻¹ b` -/
def tunk01_nf3 : List (PolygonMoves.Signed apm_tunk01_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.d, true), (.c, true), (.b, false),
    (.g, true), (.d, true), (.c, false), (.b, true)]

/-- Step 3: cut-and-paste on the pair e⁻¹. -/
theorem tunk01_move3 :
    Nonempty (PolygonMoves.PolygonSurface tunk01_nf2 ≃ₜ
      PolygonMoves.PolygonSurface tunk01_nf3) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false)]
    [(.b, true), (.c, false), (.d, false), (.g, false)]
    [(.g, true), (.d, true), (.c, false), (.b, true)]
    (.e, false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b c⁻¹ d⁻¹ d c⁻¹ b` -/
def tunk01_nf4 : List (PolygonMoves.Signed apm_tunk01_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.g, true), (.b, true), (.c, false),
    (.d, false), (.d, true), (.c, false), (.b, true)]

/-- Step 4: cut-and-paste on the pair g. -/
theorem tunk01_move4 :
    Nonempty (PolygonMoves.PolygonSurface tunk01_nf3 ≃ₜ
      PolygonMoves.PolygonSurface tunk01_nf4) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
      (.e, false)]
    [(.d, true), (.c, true), (.b, false)]
    [(.d, true), (.c, false), (.b, true)]
    (.g, true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b b c d⁻¹ d c` -/
def tunk01_nf5 : List (PolygonMoves.Signed apm_tunk01_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.g, true), (.b, true), (.b, true),
    (.c, true), (.d, false), (.d, true), (.c, true)]

/-- Step 5: cut-and-paste on the pair b. -/
theorem tunk01_move5 :
    Nonempty (PolygonMoves.PolygonSurface tunk01_nf4 ≃ₜ
      PolygonMoves.PolygonSurface tunk01_nf5) :=
  polygonNF_cutStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
      (.e, false), (.g, true), (.g, true)]
    [(.c, false), (.d, false), (.d, true), (.c, false)]
    []
    (.b, true) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- `a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b b c c` -/
def tunk01_nf6 : List (PolygonMoves.Signed apm_tunk01_Label) :=
  [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
    (.e, false), (.g, true), (.g, true), (.b, true), (.b, true),
    (.c, true), (.c, true)]

/-- Step 6: cancel d⁻¹ d. -/
theorem tunk01_move6 :
    Nonempty (PolygonMoves.PolygonSurface tunk01_nf5 ≃ₜ
      PolygonMoves.PolygonSurface tunk01_nf6) :=
  polygonNF_cancelStep _ _
    [(.a, true), (.a, true), (.f, false), (.f, false), (.e, false),
      (.e, false), (.g, true), (.g, true), (.b, true), (.b, true), (.c, true)]
    [(.c, true)]
    (.d, false) (by decide) (by decide) (by decide)
    (by unfold PolygonMoves.IsPolygonWord; decide)

/-- The six crosscap letters of the normal form. -/
def tunk01_crosscapLetters : Fin 6 → PolygonMoves.Signed apm_tunk01_Label :=
  ![(.a, true), (.f, false), (.e, false), (.g, true), (.b, true), (.c, true)]

theorem tunk01_nf6_eq :
    tunk01_nf6 = polygonNF_crosscapWord 6 tunk01_crosscapLetters := by
  decide

theorem tunk01_word_normalForm :
    Nonempty (PolygonMoves.PolygonSurface tunk01_signedWord ≃ₜ
      Surfaces.Surface false 6) := by
  have h := PolygonMoves.homeomorph_trans tunk01_move1 <|
    PolygonMoves.homeomorph_trans tunk01_move2 <|
    PolygonMoves.homeomorph_trans tunk01_move3 <|
    PolygonMoves.homeomorph_trans tunk01_move4 <|
    PolygonMoves.homeomorph_trans tunk01_move5 tunk01_move6
  rw [tunk01_nf6_eq] at h
  exact PolygonMoves.homeomorph_trans h
    (polygonNF_crosscapBridge 6 tunk01_crosscapLetters (by decide))

/-! ## The standard twelve-gon `apm_tunk01_N6` is `Surface false 6` -/

theorem tunk01_surfaceRel_eq_N6Rel :
    Surfaces.SurfaceRel false 6 = apm_tunk01_N6Rel := by
  funext x y
  exact propext Iff.rfl

theorem tunk01_surface_homeomorph_N6 :
    Nonempty (Surfaces.Surface false 6 ≃ₜ apm_tunk01_N6) :=
  polygonNF_quotient_homeomorph fun x y => by rw [tunk01_surfaceRel_eq_N6Rel]

theorem tunk01_normalization :
    Nonempty (apm_tunk01_PolygonSurface ≃ₜ apm_tunk01_N6) :=
  PolygonMoves.homeomorph_trans tunk01_bridge <|
    PolygonMoves.homeomorph_trans tunk01_word_normalForm
      tunk01_surface_homeomorph_N6

/-! ## Integral homology, transported from the banked `N₆` computation -/

/-- Normalize the concrete fourteen-gon presentation to the standard
twelve-gon presentation of the nonorientable genus-six surface. -/
theorem apm_tunk01_polygon_normalization :
    Nonempty (apm_tunk01_PolygonSurface ≃ₜ apm_tunk01_N6) :=
  tunk01_normalization

/-- The printed polygon is the nonorientable closed surface of genus six. -/
theorem apm_tunk01
    (X : Type*) [TopologicalSpace X]
    (hPresentation : Nonempty (X ≃ₜ apm_tunk01_PolygonSurface)) :
    apm_tunk01_vertexCount apm_tunk01_vertexClass = 2 ∧
    apm_tunk01_edgeCount apm_tunk01_word = 7 ∧
    apm_tunk01_eulerCharacteristic apm_tunk01_word apm_tunk01_vertexClass = -4 ∧
    ¬apm_tunk01_hasOppositeOrientationPairing apm_tunk01_word ∧
    Nonempty (X ≃ₜ apm_tunk01_N6) := by
  rcases hPresentation with ⟨e⟩
  let en : apm_tunk01_PolygonSurface ≃ₜ apm_tunk01_N6 :=
    Classical.choice apm_tunk01_polygon_normalization
  exact ⟨apm_tunk01_vertexCount_eq, apm_tunk01_edgeCount_eq,
    apm_tunk01_eulerCharacteristic_eq,
    apm_tunk01_not_oppositeOrientationPairing,
    ⟨e.trans en⟩⟩

#print axioms apm_tunk01

import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonMoves

/-!
# Finite covers of standard orientable surfaces

This file isolates the two missing polygonal-topology foundations needed by
three finite-cover consumers.  The final theorem is an assembly, not surface
recognition: it passes through a one-polygon `PairingData` obtained by lifting
the standard cell structure and joining the lifted faces along a dual spanning
tree.
-/

open Set
noncomputable section

namespace ConstructionTargets.StandardSurfaceFiniteCover

open Surfaces PolygonSurfacePiOne

/-- A pairing reverses boundary orientation on every paired pair.  With the
sign convention of `boundaryRel`, this is the orientable case. -/
def IsOrientablePairing (P : PairingData) : Prop :=
  ∀ i, P.sign (P.pair i) ≠ P.sign i

/-! ## Polygon complexes

Split of `standardCover_pairingData` (claude-14, 2026-10-24, after the lemma-2
PARTIAL reported that the repository has no multi-polygon interface).  A
`PolygonComplex` is `PairingData` with several faces and no one-vertex
condition.  The proof runs: lift the standard `4g`-gon through the cover
(`_aux_lift`), glue faces along a dual spanning tree one edge at a time
(`_aux_glueStep`), contract a spanning tree of the 1-skeleton one edge at a
time (`_aux_contractStep`), and read off the one-face one-vertex complex as
`PairingData` (`_aux_toPairing`).  Each glue and each contraction removes two
boundary arcs, which gives `4gn - 4(n - 1)` arcs from `n` faces of `4g`. -/

/-- Finitely many polygons with paired boundary sides.  Side `⟨f, i⟩` is arc
`i` of the `sides f`-gon `f`; it is identified with side `pair ⟨f, i⟩`,
preserving the arc parameter when the two signs agree (as in `boundaryRel`). -/
structure PolygonComplex where
  faceCount : ℕ
  sides : Fin faceCount → ℕ
  sides_pos : ∀ f, 0 < sides f
  pair : Equiv.Perm (Σ f : Fin faceCount, Fin (sides f))
  pair_pair : ∀ s, pair (pair s) = s
  pair_ne : ∀ s, pair s ≠ s
  sign : (Σ f : Fin faceCount, Fin (sides f)) → Bool

namespace PolygonComplex

/-- The boundary sides of all faces. -/
abbrev Side (C : PolygonComplex) := Σ f : Fin C.faceCount, Fin (C.sides f)

/-- The parameter on the paired side. -/
def pairedParameter (C : PolygonComplex) (s : C.Side) (t : Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 :=
  if C.sign s = C.sign (C.pair s) then t else reverseIcc t

/-- The generating identifications on the disjoint union of the face disks. -/
def Rel (C : PolygonComplex) (x y : Σ _ : Fin C.faceCount, Disk) : Prop :=
  ∃ s : C.Side, ∃ t : Set.Icc (0 : ℝ) 1,
    x = ⟨s.1, edgePoint (C.sides s.1) s.2 t⟩ ∧
      y = ⟨(C.pair s).1,
        edgePoint (C.sides (C.pair s).1) (C.pair s).2 (C.pairedParameter s t)⟩

/-- The glued surface. -/
def Space (C : PolygonComplex) :=
  Quotient (Relation.EqvGen.setoid C.Rel)

noncomputable instance (C : PolygonComplex) : TopologicalSpace C.Space :=
  TopologicalSpace.coinduced
    (fun x : Σ _ : Fin C.faceCount, Disk =>
      Quotient.mk (Relation.EqvGen.setoid C.Rel) x)
    inferInstance

/-- The number of boundary arcs over all faces. -/
def totalSides (C : PolygonComplex) : ℕ :=
  ∑ f, C.sides f

/-- Every paired pair reverses the parameter: the faces, all oriented
counterclockwise, are glued coherently. -/
def IsOrientable (C : PolygonComplex) : Prop :=
  ∀ s, C.sign (C.pair s) ≠ C.sign s

/-- The face-dual graph (faces, joined when they share a paired side) is
connected. -/
def DualConnected (C : PolygonComplex) : Prop :=
  ∀ f f' : Fin C.faceCount,
    Relation.EqvGen (fun a b => ∃ s : C.Side, s.1 = a ∧ (C.pair s).1 = b) f f'

/-- Corner `⟨f, i⟩` is the initial endpoint of side `⟨f, i⟩`; its terminal
endpoint is the next corner of the same face. -/
def nextCorner (C : PolygonComplex) (s : C.Side) : C.Side :=
  ⟨s.1, ⟨(s.2 + 1) % C.sides s.1, Nat.mod_lt _ (C.sides_pos s.1)⟩⟩

/-- Corners identified by one side pairing: initial with initial when the
parameter is preserved, initial with terminal when it is reversed. -/
def CornerRel (C : PolygonComplex) (a b : C.Side) : Prop :=
  ∃ s : C.Side,
    if C.sign s = C.sign (C.pair s) then
      (a = s ∧ b = C.pair s) ∨ (a = C.nextCorner s ∧ b = C.nextCorner (C.pair s))
    else
      (a = s ∧ b = C.nextCorner (C.pair s)) ∨ (a = C.nextCorner s ∧ b = C.pair s)

/-- The vertices of the complex: corner classes. -/
def Vertex (C : PolygonComplex) :=
  Quotient (Relation.EqvGen.setoid C.CornerRel)

/-- The number of vertices. -/
noncomputable def vertexCount (C : PolygonComplex) : ℕ :=
  Nat.card C.Vertex

end PolygonComplex

open PolygonComplex

/-- Banked by lemma-2 (2026-10-24): the arc count after `n - 1` glues and
`n - 1` contractions. -/
theorem standardCover_pairingData_aux_edgeCount
    (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n) :
    4 * g * n - 4 * (n - 1) = 4 * (n * (g - 1) + 1) := by
  have hsub : n * (g - 1) = n * g - n := by
    rw [Nat.mul_sub_left_distrib]
    simp
  rw [hsub]
  have hcomm : 4 * g * n = 4 * (n * g) := by ring
  rw [hcomm]
  have hn_one : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hng : n ≤ n * g := by
    simpa using Nat.mul_le_mul_left n hg
  omega

theorem standardCover_pairingData_aux_lift_aux_fiberEquiv
    (n : ℕ) (hn : 1 ≤ n) (E B : Type*) (p : E → B)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n) (b : B) :
    Nonempty ({e : E // p e = b} ≃ Fin n) := by
  let F := {e : E // p e = b}
  have hcard : Nat.card F = n := hsheets b
  have hne : Nat.card F ≠ 0 := by omega
  letI : Finite F := Nat.finite_of_card_ne_zero hne
  letI : Fintype F := Fintype.ofFinite F
  refine ⟨Fintype.equivFin F |>.trans (finCongr ?_)⟩
  simpa [Nat.card_eq_fintype_card] using hcard

/-! Split of `_aux_lift` (claude-14, 2026-10-24, after the lemma-2 PARTIAL
that banked `_aux_fiberEquiv`).  Lift the base disk once through each point
over its centre (`_aux_diskLift`), read off which lifted face meets which
along each side (`_aux_sidePairing`), build the complex from that
(`_aux_complex`), and check the three properties that are not by
construction: `_aux_homeomorph`, `_aux_dualConnected`, `_aux_vertexCount`. -/

/-- The centre of the disk. -/
def standardCover_pairingData_aux_lift_aux_center : Disk :=
  ⟨0, by simp⟩

/-- The side pairing of `SurfaceRel true g` on the `4g`-gon:
`4j ↔ 4j + 2` and `4j + 1 ↔ 4j + 3`, with the parameter reversed. -/
def standardCover_pairingData_aux_lift_aux_basePair (g : ℕ) (k : Fin (4 * g)) :
    Fin (4 * g) :=
  ⟨if k.1 % 4 < 2 then k.1 + 2 else k.1 - 2, by have := k.2; split <;> omega⟩

theorem standardCover_pairingData_aux_lift_aux_basePair_basePair (g : ℕ)
    (k : Fin (4 * g)) :
    standardCover_pairingData_aux_lift_aux_basePair g
      (standardCover_pairingData_aux_lift_aux_basePair g k) = k := by
  ext; simp only [standardCover_pairingData_aux_lift_aux_basePair]
  split <;> split <;> omega

theorem standardCover_pairingData_aux_lift_aux_basePair_ne (g : ℕ)
    (k : Fin (4 * g)) :
    standardCover_pairingData_aux_lift_aux_basePair g k ≠ k := by
  intro h; have := congrArg Fin.val h
  simp only [standardCover_pairingData_aux_lift_aux_basePair] at this
  split at this <;> omega

/-- Sides `4j` and `4j + 1` carry sign `true`, their partners `false`. -/
def standardCover_pairingData_aux_lift_aux_baseSign (g : ℕ) (k : Fin (4 * g)) :
    Bool :=
  decide (k.1 % 4 < 2)

theorem standardCover_pairingData_aux_lift_aux_baseSign_basePair (g : ℕ)
    (k : Fin (4 * g)) :
    standardCover_pairingData_aux_lift_aux_baseSign g
        (standardCover_pairingData_aux_lift_aux_basePair g k) ≠
      standardCover_pairingData_aux_lift_aux_baseSign g k := by
  have := k.2
  simp only [standardCover_pairingData_aux_lift_aux_baseSign,
    standardCover_pairingData_aux_lift_aux_basePair, ne_eq, decide_eq_decide]
  split <;> omega

/-- Leaf: the closed disk is simply connected and locally path connected, so
the quotient map lifts uniquely through the cover from any point over the
centre (`IsCoveringMap.existsUnique_continuousMap_lifts`). -/
theorem standardCover_pairingData_aux_lift_aux_diskLift (g : ℕ)
    (E : Type*) [TopologicalSpace E] (p : E → Surface true g) (hp : IsCoveringMap p)
    (e : E)
    (he : p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center) :
    ∃! L : C(Disk, E), p ∘ L = surfaceQuotient true g ∧
      L standardCover_pairingData_aux_lift_aux_center = e := by
  sorry

/-- Leaf: with one lift `L i` of the disk through each point over the centre,
side `k` of face `i` is glued to side `basePair k` of exactly one face
`σ i k`, with the parameter reversed.  (Both sides lift the same path in the
surface, so they agree once they agree at one point; the face is determined
by uniqueness of lifts.) -/
-- BEGIN SEAT AREA
theorem standardCover_pairingData_aux_lift_aux_sidePairing
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e) :
    ∃ σ : Fin n → Fin (4 * g) → Fin n,
      (∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i) ∧
      ∀ i (k : Fin (4 * g)) t, L i (edgePoint (4 * g) k t) =
        L (σ i k) (edgePoint (4 * g)
          (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)) := by
  sorry
-- END SEAT AREA

/-- The lifted complex: `n` copies of the `4g`-gon, side `⟨i, k⟩` glued to
side `⟨σ i k, basePair k⟩`. -/
def standardCover_pairingData_aux_lift_aux_complex (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i) :
    PolygonComplex where
  faceCount := n
  sides _ := 4 * g
  sides_pos _ := by omega
  pair := Function.Involutive.toPerm
    (fun s : (Σ _ : Fin n, Fin (4 * g)) =>
      (⟨σ s.1 s.2, standardCover_pairingData_aux_lift_aux_basePair g s.2⟩ :
        Σ _ : Fin n, Fin (4 * g)))
    (by
      rintro ⟨i, k⟩
      simp only [hσ, standardCover_pairingData_aux_lift_aux_basePair_basePair])
  pair_pair s := by
    rcases s with ⟨i, k⟩
    simp [hσ, standardCover_pairingData_aux_lift_aux_basePair_basePair]
  pair_ne s := by
    rcases s with ⟨i, k⟩
    intro h
    exact standardCover_pairingData_aux_lift_aux_basePair_ne g k
      (congrArg Sigma.snd h |> fun h' => by simpa using h')
  sign s := standardCover_pairingData_aux_lift_aux_baseSign g s.2

/-- Leaf: the lifts assemble to a homeomorphism.  The map
`⟨i, x⟩ ↦ L i x` from the disjoint union of the disks is surjective (every
point of `E` is on some lifted disk), identifies exactly the points that
`Rel` generates (by `hside` and uniqueness of lifts), and is a quotient map. -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (hside : ∀ i (k : Fin (4 * g)) t, L i (edgePoint (4 * g) k t) =
      L (σ i k) (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t))) :
    Nonempty (E ≃ₜ (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Space) := by
  sorry

/-- Leaf: a connected glued space has connected face-dual graph.  The faces
in one dual class form a union of glued disks that is closed and open in
`C.Space`, since every side of such a face is glued to a face of the same
class. -/
theorem standardCover_pairingData_aux_lift_aux_dualConnected (C : PolygonComplex)
    [ConnectedSpace C.Space] : C.DualConnected := by
  sorry

/-- Leaf: the corner classes of the lifted complex correspond to the `n`
points over the image of the corners (all corners of the `4g`-gon are one
point of `Surface true g`).  Corner `⟨i, k⟩` goes to
`L i (edgePoint (4g) k 0)`; `CornerRel` generates exactly the identifications
of this map. -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (hside : ∀ i (k : Fin (4 * g)) t, L i (edgePoint (4 * g) k t) =
      L (σ i k) (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t))) :
    (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).vertexCount = n := by
  sorry

/-- **Lifted cell structure**, assembled from the `_aux_lift_aux_*` leaves
above.  Lift the standard `4g`-gon through the
cover.  The interior of the base disk is simply connected, so it has `n`
disjoint lifts; their closures are the `n` faces, each a `4g`-gon.  The faces
inherit the base pairing, hence orientability.  Path-connectedness of `E`
(via path lifting and `IsCoveringMap.monodromy`) makes the face-dual graph
connected.  The single base vertex has `n` preimages, which are the corner
classes. -/
theorem standardCover_pairingData_aux_lift
    (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n) :
    ∃ C : PolygonComplex, C.faceCount = n ∧ (∀ f, C.sides f = 4 * g) ∧
      C.IsOrientable ∧ C.DualConnected ∧ C.vertexCount = n ∧
      Nonempty (E ≃ₜ C.Space) := by
  set c := standardCover_pairingData_aux_lift_aux_center
  set b := surfaceQuotient true g c
  obtain ⟨eqv⟩ := standardCover_pairingData_aux_lift_aux_fiberEquiv n hn E _ p hsheets b
  have hlift := fun i : Fin n =>
    standardCover_pairingData_aux_lift_aux_diskLift g E p hp (eqv.symm i).1 (eqv.symm i).2
  choose L hL using hlift
  have hfib : ∀ e, p e = b → ∃! i, L i c = e := by
    intro e he
    refine ⟨eqv ⟨e, he⟩, ?_, ?_⟩
    · exact ((hL _).1.2).trans (by simp)
    · intro j hj
      rw [← eqv.apply_symm_apply j]
      congr 1; ext; exact ((hL j).1.2).symm.trans hj
  have hLp : ∀ i, p ∘ L i = surfaceQuotient true g := fun i => (hL i).1.1
  obtain ⟨σ, hσ, hside⟩ :=
    standardCover_pairingData_aux_lift_aux_sidePairing g n hg E p hp hsheets L hLp hfib
  obtain ⟨h⟩ := standardCover_pairingData_aux_lift_aux_homeomorph g n hg E p hp hsheets
    L hLp hfib σ hσ hside
  refine ⟨standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ, rfl,
    fun _ => rfl, ?_, ?_, ?_, ⟨h⟩⟩
  · intro s
    exact standardCover_pairingData_aux_lift_aux_baseSign_basePair g s.2
  · haveI : ConnectedSpace
        (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Space :=
      h.surjective.connectedSpace h.continuous
    exact standardCover_pairingData_aux_lift_aux_dualConnected _
  · exact standardCover_pairingData_aux_lift_aux_vertexCount g n hg E p hp hsheets
      L hLp hfib σ hσ hside

/-- Banked by lemma-3 (2026-10-24): with two faces and a connected dual graph,
some side pairs two distinct faces. -/
theorem standardCover_pairingData_aux_glueStep_aux_crossingSide
    (C : PolygonComplex) (hC : 2 ≤ C.faceCount) (hconn : C.DualConnected) :
    ∃ s : C.Side, s.1 ≠ (C.pair s).1 := by
  let f : Fin C.faceCount := ⟨0, by omega⟩
  let g : Fin C.faceCount := ⟨1, by omega⟩
  by_contra h
  push_neg at h
  have hedge : ∀ a b : Fin C.faceCount,
      (∃ s : C.Side, s.1 = a ∧ (C.pair s).1 = b) → a = b := by
    intro a b hab
    obtain ⟨s, rfl, hs⟩ := hab
    exact (h s).trans hs
  have heqv : ∀ {a b : Fin C.faceCount},
      Relation.EqvGen (fun a b => ∃ s : C.Side,
        s.1 = a ∧ (C.pair s).1 = b) a b → a = b := by
    intro a b hab
    induction hab with
    | rel a b hab => exact hedge a b hab
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hfg : f = g := heqv (hconn f g)
  have : (0 : ℕ) = 1 := congrArg Fin.val hfg
  omega

/-- `C'` is `C` with faces `s.1` and `(C.pair s).1` glued along `s` into the
face `merged`.  `old` sends each face of `C'` to the face of `C` it came from
(`merged` to `s.1`); `toOld` sends each side of `C'` to the side of `C` it came
from, and hits every side except `s` and `C.pair s`.  Unmerged faces keep their
sides in order.  The merged face runs through sides `s.2 + 1, …, s.2 - 1` of
`s.1` and then sides `(C.pair s).2 + 1, …, (C.pair s).2 - 1` of
`(C.pair s).1`, each with its arc parameter kept. -/
structure standardCover_pairingData_aux_glueStep_aux_GlueData
    (C C' : PolygonComplex) (s : C.Side) where
  faceCount_succ : C'.faceCount + 1 = C.faceCount
  merged : Fin C'.faceCount
  old : Fin C'.faceCount → Fin C.faceCount
  old_merged : old merged = s.1
  old_injective : Function.Injective old
  old_ne : ∀ k, old k ≠ (C.pair s).1
  sides_old : ∀ k, k ≠ merged → C'.sides k = C.sides (old k)
  sides_merged : C'.sides merged + 2 = C.sides s.1 + C.sides (C.pair s).1
  toOld : C'.Side → C.Side
  toOld_injective : Function.Injective toOld
  toOld_ne : ∀ t, toOld t ≠ s ∧ toOld t ≠ C.pair s
  toOld_surj : ∀ u, u ≠ s → u ≠ C.pair s → ∃ t, toOld t = u
  toOld_fst : ∀ t : C'.Side, t.1 ≠ merged → (toOld t).1 = old t.1
  toOld_val : ∀ t : C'.Side, t.1 ≠ merged → (toOld t).2.val = t.2.val
  toOld_merged_fst : ∀ m : Fin (C'.sides merged),
    (toOld ⟨merged, m⟩).1 =
      if m.val + 1 < C.sides s.1 then s.1 else (C.pair s).1
  toOld_merged_val : ∀ m : Fin (C'.sides merged),
    (toOld ⟨merged, m⟩).2.val =
      if m.val + 1 < C.sides s.1 then (s.2.val + 1 + m.val) % C.sides s.1
      else ((C.pair s).2.val + 1 + (m.val + 1 - C.sides s.1)) %
        C.sides (C.pair s).1
  pair_toOld : ∀ t, toOld (C'.pair t) = C.pair (toOld t)
  sign_toOld : ∀ t, C'.sign t = C.sign (toOld t)

/-- **Leaf (build the merged complex).** -/
theorem standardCover_pairingData_aux_glueStep_aux_mergeExists
    (C : PolygonComplex) (hsides : ∀ f, 2 ≤ C.sides f) (s : C.Side)
    (hs : s.1 ≠ (C.pair s).1) :
    ∃ C' : PolygonComplex,
      Nonempty (standardCover_pairingData_aux_glueStep_aux_GlueData C C' s) := by
  sorry

/-- **Leaf (arc count).**  Every side of `C` except `s` and `C.pair s` is a
side of `C'`, once. -/
theorem standardCover_pairingData_aux_glueStep_aux_totalSides
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s) :
    C'.totalSides + 2 = C.totalSides := by
  sorry

theorem standardCover_pairingData_aux_glueStep_aux_sides
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hsides : ∀ f, 2 ≤ C.sides f) : ∀ k, 2 ≤ C'.sides k := by
  intro k
  by_cases hk : k = D.merged
  · subst hk
    have h₁ := hsides s.1
    have h₂ := hsides (C.pair s).1
    have := D.sides_merged
    omega
  · rw [D.sides_old k hk]
    exact hsides _

theorem standardCover_pairingData_aux_glueStep_aux_orientable
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) : C'.IsOrientable := by
  intro t
  rw [D.sign_toOld, D.sign_toOld, D.pair_toOld]
  exact hor _

/-- **Leaf (dual graph).**  A dual edge of `C` between faces other than
`s.1, (C.pair s).1` is a dual edge of `C'`; one at `s.1` or `(C.pair s).1`
(other than `s` itself) is a dual edge at `merged`. -/
theorem standardCover_pairingData_aux_glueStep_aux_dualConnected
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hconn : C.DualConnected) : C'.DualConnected := by
  sorry

/-- **Leaf (corners).**  `toOld` induces a bijection of corner classes.  The
four corners at the ends of `s` and `C.pair s` lie in two `C`-classes (by
orientability); in `C'` they are the two junctions of the merged face. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) : C'.vertexCount = C.vertexCount := by
  sorry

/-- **Leaf (two disks glued along an arc).**  The disks of `s.1` and
`(C.pair s).1`, glued along `s` with the parameter reversed, form one disk
whose boundary is the merged face's boundary; all other identifications are
carried by `toOld`. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hsides : ∀ f, 2 ≤ C.sides f) (hor : C.IsOrientable) :
    Nonempty (C.Space ≃ₜ C'.Space) := by
  sorry

/-- **One dual-tree glue.**  With at least two faces and a connected
dual graph, some side pairs two distinct faces.  Gluing those two disks along
that side gives one disk with `a + b - 2` sides; corners, orientability and
dual connectivity are kept.  `2 ≤ sides` excludes two monogons forming a
sphere with no sides left. -/
theorem standardCover_pairingData_aux_glueStep
    (C : PolygonComplex) (hC : 2 ≤ C.faceCount) (hsides : ∀ f, 2 ≤ C.sides f)
    (hconn : C.DualConnected) (hor : C.IsOrientable) :
    ∃ C' : PolygonComplex, C'.faceCount + 1 = C.faceCount ∧
      C'.totalSides + 2 = C.totalSides ∧ C'.vertexCount = C.vertexCount ∧
      C'.IsOrientable ∧ C'.DualConnected ∧ (∀ f, 2 ≤ C'.sides f) ∧
      Nonempty (C.Space ≃ₜ C'.Space) := by
  obtain ⟨s, hs⟩ :=
    standardCover_pairingData_aux_glueStep_aux_crossingSide C hC hconn
  obtain ⟨C', ⟨D⟩⟩ :=
    standardCover_pairingData_aux_glueStep_aux_mergeExists C hsides s hs
  exact ⟨C', D.faceCount_succ,
    standardCover_pairingData_aux_glueStep_aux_totalSides D,
    standardCover_pairingData_aux_glueStep_aux_vertexCount D hor,
    standardCover_pairingData_aux_glueStep_aux_orientable D hor,
    standardCover_pairingData_aux_glueStep_aux_dualConnected D hconn,
    standardCover_pairingData_aux_glueStep_aux_sides D hsides,
    standardCover_pairingData_aux_glueStep_aux_homeomorph D hsides hor⟩

/-- Glue along a whole dual spanning tree: `k` glues on `k + 1` faces. -/
theorem standardCover_pairingData_aux_treeGlue (k : ℕ) :
    ∀ C : PolygonComplex, C.faceCount = k + 1 → (∀ f, 2 ≤ C.sides f) →
      C.DualConnected → C.IsOrientable →
      ∃ C' : PolygonComplex, C'.faceCount = 1 ∧
        C'.totalSides + 2 * k = C.totalSides ∧ C'.vertexCount = C.vertexCount ∧
        C'.IsOrientable ∧ Nonempty (C.Space ≃ₜ C'.Space) := by
  induction k with
  | zero =>
    intro C hk _ _ hor
    exact ⟨C, hk, by simp, rfl, hor, ⟨Homeomorph.refl _⟩⟩
  | succ k ih =>
    intro C hk hs hconn hor
    obtain ⟨C₁, hf₁, ht₁, hv₁, hor₁, hconn₁, hs₁, ⟨e₁⟩⟩ :=
      standardCover_pairingData_aux_glueStep C (by omega) hs hconn hor
    obtain ⟨C₂, hf₂, ht₂, hv₂, hor₂, ⟨e₂⟩⟩ := ih C₁ (by omega) hs₁ hconn₁ hor₁
    exact ⟨C₂, hf₂, by omega, hv₂.trans hv₁, hor₂, ⟨e₁.trans e₂⟩⟩

/-! Split of `_aux_contractStep` (claude-14, 2026-10-24, after the lemma-1
PARTIAL banked `_aux_totalSides_five_le`).  `ContractData C C' s` specifies the
contracted complex without constructing it; `_aux_contractExists` builds one. -/

/-- Banked by lemma-1 (2026-10-24). -/
lemma standardCover_pairingData_aux_contractStep_aux_totalSides_five_le
    (C : PolygonComplex) (hV : 2 ≤ C.vertexCount)
    (hlarge : 2 * C.vertexCount < C.totalSides) :
    5 ≤ C.totalSides := by
  omega

/-- **Leaf (a side with distinct ends).**  In a one-face complex the corners
`⟨0, 0⟩, ⟨0, 1⟩, …` are joined in turn by sides; if every side had both ends
in one class, all corners would be one vertex. -/
theorem standardCover_pairingData_aux_contractStep_aux_distinctEnds
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : 2 ≤ C.vertexCount) :
    ∃ s : C.Side, Quotient.mk (Relation.EqvGen.setoid C.CornerRel) s ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner s) := by
  sorry

/-- `C'` is the one-face complex `C` with sides `s` and `C.pair s` removed
from the boundary.  `toOld` sends each side of `C'` to the side of `C` it came
from, keeps the order of the boundary, and hits every side except `s` and
`C.pair s`.  Pairings and signs are carried unchanged. -/
structure standardCover_pairingData_aux_contractStep_aux_ContractData
    (C C' : PolygonComplex) (s : C.Side) where
  faceCount_eq : C'.faceCount = 1
  totalSides_add_two : C'.totalSides + 2 = C.totalSides
  toOld : C'.Side → C.Side
  toOld_injective : Function.Injective toOld
  toOld_ne : ∀ t, toOld t ≠ s ∧ toOld t ≠ C.pair s
  toOld_surj : ∀ u, u ≠ s → u ≠ C.pair s → ∃ t, toOld t = u
  toOld_lt : ∀ t t' : C'.Side, t.2.val < t'.2.val →
    (toOld t).2.val < (toOld t').2.val
  pair_toOld : ∀ t, toOld (C'.pair t) = C.pair (toOld t)
  sign_toOld : ∀ t, C'.sign t = C.sign (toOld t)

/-- **Leaf (build the contracted complex).**  `C'.sides 0 = C.sides 0 - 2`,
`toOld` the increasing enumeration of the other sides, pairing and sign pulled
back along it (`C.pair` swaps `s` and `C.pair s`, so it preserves the rest). -/
theorem standardCover_pairingData_aux_contractStep_aux_contractExists
    (C : PolygonComplex) (h1 : C.faceCount = 1) (h3 : 3 ≤ C.totalSides)
    (s : C.Side) :
    ∃ C' : PolygonComplex,
      Nonempty (standardCover_pairingData_aux_contractStep_aux_ContractData C C' s) := by
  sorry

theorem standardCover_pairingData_aux_contractStep_aux_orientable
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (hor : C.IsOrientable) : C'.IsOrientable := by
  intro t
  rw [D.sign_toOld, D.sign_toOld, D.pair_toOld]
  exact hor _

/-- **Leaf (corners).**  Map a corner `t` of `C'` to `toOld t`.  The classes
of `s` and `C.nextCorner s` (distinct by `hs`) become one class; every other
class is kept.  At the place where `s` (or `C.pair s`) was removed, the
terminal corner of the side before it now equals the initial corner of the
side after it, which joins the two classes. -/
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides)
    (hs : Quotient.mk (Relation.EqvGen.setoid C.CornerRel) s ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner s))
    (hor : C.IsOrientable) : C'.vertexCount + 1 = C.vertexCount := by
  sorry

/-- **Leaf (collapse an arc).**  Side `s` has distinct ends, so its image in
`C.Space` is an embedded arc; collapsing it (and its partner, the same arc) to
a point gives `C'.Space`.  In the disk: a homeomorphism `Disk → Disk` that
sends side `s` and side `C.pair s` to single boundary points and the other
sides onto the sides of the `(sides - 2)`-gon, compatible with the pairings. -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides)
    (hs : Quotient.mk (Relation.EqvGen.setoid C.CornerRel) s ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner s))
    (hor : C.IsOrientable) : Nonempty (C.Space ≃ₜ C'.Space) := by
  sorry

/-- **One 1-skeleton contraction.**  A one-face complex with at least
two vertices has a side whose endpoints are distinct vertices.  Collapsing
that side and its partner (an embedded arc in the surface) removes two
boundary arcs and merges the two vertices.  `2 * vertexCount < totalSides`
excludes the sphere words, where the contraction would reach zero sides; it
is preserved by the step. -/
theorem standardCover_pairingData_aux_contractStep
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : 2 ≤ C.vertexCount)
    (hlarge : 2 * C.vertexCount < C.totalSides) (hor : C.IsOrientable) :
    ∃ C' : PolygonComplex, C'.faceCount = 1 ∧ C'.totalSides + 2 = C.totalSides ∧
      C'.vertexCount + 1 = C.vertexCount ∧ C'.IsOrientable ∧
      Nonempty (C.Space ≃ₜ C'.Space) := by
  have h5 := standardCover_pairingData_aux_contractStep_aux_totalSides_five_le C hV hlarge
  obtain ⟨s, hs⟩ :=
    standardCover_pairingData_aux_contractStep_aux_distinctEnds C h1 hV
  obtain ⟨C', ⟨D⟩⟩ :=
    standardCover_pairingData_aux_contractStep_aux_contractExists C h1 (by omega) s
  exact ⟨C', D.faceCount_eq, D.totalSides_add_two,
    standardCover_pairingData_aux_contractStep_aux_vertexCount D h1 h5 hs hor,
    standardCover_pairingData_aux_contractStep_aux_orientable D hor,
    standardCover_pairingData_aux_contractStep_aux_homeomorph D h1 h5 hs hor⟩

/-- Contract a spanning tree of the 1-skeleton: `k` contractions on `k + 1`
vertices. -/
theorem standardCover_pairingData_aux_contract (k : ℕ) :
    ∀ C : PolygonComplex, C.faceCount = 1 → C.vertexCount = k + 1 →
      2 * C.vertexCount < C.totalSides → C.IsOrientable →
      ∃ C' : PolygonComplex, C'.faceCount = 1 ∧
        C'.totalSides + 2 * k = C.totalSides ∧ C'.vertexCount = 1 ∧
        C'.IsOrientable ∧ Nonempty (C.Space ≃ₜ C'.Space) := by
  induction k with
  | zero =>
    intro C h1 hV _ hor
    exact ⟨C, h1, by simp, hV, hor, ⟨Homeomorph.refl _⟩⟩
  | succ k ih =>
    intro C h1 hV hlarge hor
    obtain ⟨C₁, hf₁, ht₁, hv₁, hor₁, ⟨e₁⟩⟩ :=
      standardCover_pairingData_aux_contractStep C h1 (by omega) hlarge hor
    obtain ⟨C₂, hf₂, ht₂, hv₂, hor₂, ⟨e₂⟩⟩ :=
      ih C₁ hf₁ (by omega) (by omega) hor₁
    exact ⟨C₂, hf₂, by omega, hv₂, hor₂, ⟨e₁.trans e₂⟩⟩

/-! Split of `_aux_toPairing` (claude-14, 2026-10-24, after a lemma-2 PARTIAL
that banked nothing).  With one face, `C.Side` is `Fin C.totalSides`
(`_aux_sideEquiv`); transport `pair` and `sign` along it (`_aux_pairing`).
`oneVertex` comes from one corner step at a time (`_aux_cornerStep`), and the
homeomorphism is the leaf `_aux_homeomorph`. -/

/-- With one face, its index type is `Unique`. -/
def standardCover_pairingData_aux_toPairing_aux_uniqueFace
    (C : PolygonComplex) (h1 : C.faceCount = 1) : Unique (Fin C.faceCount) where
  default := ⟨0, by omega⟩
  uniq f := Fin.ext (by have := f.2; omega)

/-- With one face, the sides of `C` are `Fin C.totalSides`: side `⟨f, i⟩`
goes to `i`. -/
def standardCover_pairingData_aux_toPairing_aux_sideEquiv
    (C : PolygonComplex) (h1 : C.faceCount = 1) : C.Side ≃ Fin C.totalSides :=
  letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
  (Equiv.uniqueSigma (fun f => Fin (C.sides f))).trans
    (finCongr (by simp [PolygonComplex.totalSides, Fintype.sum_unique]))

/-- The pairing of `C` on `Fin C.totalSides`. -/
abbrev standardCover_pairingData_aux_toPairing_aux_pair
    (C : PolygonComplex) (h1 : C.faceCount = 1) : Equiv.Perm (Fin C.totalSides) :=
  (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1).permCongr C.pair

/-- The signs of `C` on `Fin C.totalSides`. -/
abbrev standardCover_pairingData_aux_toPairing_aux_sign
    (C : PolygonComplex) (h1 : C.faceCount = 1) : Fin C.totalSides → Bool :=
  C.sign ∘ (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1).symm

/-- `C` as `PairingData`, given the one-vertex condition for the transported
pairing. -/
def standardCover_pairingData_aux_toPairing_aux_pairing
    (C : PolygonComplex) (h1 : C.faceCount = 1)
    (hvert : ∀ i j : Fin C.totalSides,
      Relation.EqvGen (boundaryRel C.totalSides
          (standardCover_pairingData_aux_toPairing_aux_pair C h1)
          (standardCover_pairingData_aux_toPairing_aux_sign C h1))
        (polygonVertex C.totalSides i) (polygonVertex C.totalSides j)) :
    PairingData where
  edgeCount := C.totalSides
  edgeCount_pos := Fin.pos_iff_nonempty.mpr
    ⟨standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1
      ⟨⟨0, by omega⟩, ⟨0, C.sides_pos _⟩⟩⟩
  pair := standardCover_pairingData_aux_toPairing_aux_pair C h1
  pair_pair i := by simp [Equiv.permCongr_apply, C.pair_pair]
  pair_ne i h := by
    apply C.pair_ne ((standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1).symm i)
    have := congrArg (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1).symm h
    simpa [Equiv.permCongr_apply] using this
  sign := standardCover_pairingData_aux_toPairing_aux_sign C h1
  oneVertex := hvert

/-- With one vertex class, any two corners are `CornerRel`-connected. -/
theorem standardCover_pairingData_aux_toPairing_aux_cornersRelated
    (C : PolygonComplex) (hV : C.vertexCount = 1) (a b : C.Side) :
    Relation.EqvGen C.CornerRel a b := by
  have hsub : Subsingleton C.Vertex := (Nat.card_eq_one_iff_unique.mp hV).1
  exact Quotient.exact (@Subsingleton.elim C.Vertex hsub
    (Quotient.mk (Relation.EqvGen.setoid C.CornerRel) a) (Quotient.mk _ b))

/-- Leaf: one `CornerRel` step is a chain of boundary identifications of the
corresponding polygon vertices.  Corner `s` is `polygonVertex (e s)`; corner
`nextCorner s` is `edgePoint _ (e s) 1` (by `edgePoint_one_eq_succ_zero`, plus
`edgePoint n n 0 = edgePoint n 0 0` at the wrap-around).  Each case of
`CornerRel` is then one `boundaryRel` step at `t = 0` or `t = 1`. -/
theorem standardCover_pairingData_aux_toPairing_aux_cornerStep
    (C : PolygonComplex) (h1 : C.faceCount = 1) (a b : C.Side)
    (hab : C.CornerRel a b) :
    Relation.EqvGen (boundaryRel C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_pair C h1)
        (standardCover_pairingData_aux_toPairing_aux_sign C h1))
      (polygonVertex C.totalSides (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 a))
      (polygonVertex C.totalSides (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 b)) := by
  sorry

theorem standardCover_pairingData_aux_toPairing_aux_oneVertex
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : C.vertexCount = 1)
    (i j : Fin C.totalSides) :
    Relation.EqvGen (boundaryRel C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_pair C h1)
        (standardCover_pairingData_aux_toPairing_aux_sign C h1))
      (polygonVertex C.totalSides i) (polygonVertex C.totalSides j) := by
  set e := standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1
  have key : ∀ a b, Relation.EqvGen C.CornerRel a b →
      Relation.EqvGen (boundaryRel C.totalSides
          (standardCover_pairingData_aux_toPairing_aux_pair C h1)
          (standardCover_pairingData_aux_toPairing_aux_sign C h1))
        (polygonVertex C.totalSides (e a)) (polygonVertex C.totalSides (e b)) := by
    intro a b h
    induction h with
    | rel a b hab => exact standardCover_pairingData_aux_toPairing_aux_cornerStep C h1 a b hab
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  simpa [e] using key (e.symm i) (e.symm j)
    (standardCover_pairingData_aux_toPairing_aux_cornersRelated C hV _ _)

/-- Leaf: the glued spaces agree.  The map `⟨f, x⟩ ↦ x` from
`Σ _ : Fin C.faceCount, Disk` to `Disk` is a homeomorphism (one face), and it
carries `C.Rel` onto `boundaryRel` of the transported pairing: side `s` of
`C` is arc `e s` of the `totalSides`-gon, and `C.sides f = C.totalSides` for
the one face `f`, so `edgePoint` agrees on both sides.  Descend it and its
inverse through the two quotients. -/
theorem standardCover_pairingData_aux_toPairing_aux_homeomorph
    (C : PolygonComplex) (h1 : C.faceCount = 1)
    (hvert : ∀ i j : Fin C.totalSides,
      Relation.EqvGen (boundaryRel C.totalSides
          (standardCover_pairingData_aux_toPairing_aux_pair C h1)
          (standardCover_pairingData_aux_toPairing_aux_sign C h1))
        (polygonVertex C.totalSides i) (polygonVertex C.totalSides j)) :
    Nonempty (C.Space ≃ₜ
      (standardCover_pairingData_aux_toPairing_aux_pairing C h1 hvert).Space) := by
  sorry

/-- **Read off the pairing.**  A one-face one-vertex complex is
`PairingData`: reindex `Σ f : Fin 1, Fin (sides f)` as `Fin (sides 0)` and
`Σ _ : Fin 1, Disk` as `Disk`.  `oneVertex` comes from `vertexCount = 1`:
corner classes generate the identifications of `polygonVertex`.  Assembled
from the `_aux_toPairing_aux_*` pieces above. -/
theorem standardCover_pairingData_aux_toPairing
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : C.vertexCount = 1)
    (hor : C.IsOrientable) :
    ∃ P : PairingData, IsOrientablePairing P ∧ P.edgeCount = C.totalSides ∧
      Nonempty (C.Space ≃ₜ P.Space) := by
  have hvert := standardCover_pairingData_aux_toPairing_aux_oneVertex C h1 hV
  refine ⟨standardCover_pairingData_aux_toPairing_aux_pairing C h1 hvert, ?_, rfl,
    standardCover_pairingData_aux_toPairing_aux_homeomorph C h1 hvert⟩
  intro i
  set e := standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1
  show C.sign (e.symm (e (C.pair (e.symm i)))) ≠ C.sign (e.symm i)
  rw [Equiv.symm_apply_apply]
  exact hor (e.symm i)

/-- **Lifted polygon complex and dual-tree reduction.**  Lift the standard
`4g`-gon cell structure through the cover.  Its `n` lifted vertices, `2gn`
lifted edges and `n` lifted faces form a connected face-dual complex.
Joining faces along a spanning tree and then contracting a spanning tree of
the 1-skeleton produces one orientable polygon with `4 * (n * (g - 1) + 1)`
sides.  Assembled from the leaves above. -/
theorem standardCover_pairingData
    (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n) :
    ∃ P : PairingData,
      IsOrientablePairing P ∧ P.edgeCount = 4 * (n * (g - 1) + 1) ∧
      Nonempty (E ≃ₜ P.Space) := by
  obtain ⟨C, hf, hs, hor, hconn, hv, ⟨eE⟩⟩ :=
    standardCover_pairingData_aux_lift g n hg hn E p hp hsheets
  have htot : C.totalSides = 4 * g * n := by
    simp only [PolygonComplex.totalSides, hs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, hf]
    ring
  obtain ⟨C₁, hf₁, ht₁, hv₁, hor₁, ⟨e₁⟩⟩ :=
    standardCover_pairingData_aux_treeGlue (n - 1) C (by omega)
      (fun f => by rw [hs f]; omega) hconn hor
  have hgn : n ≤ g * n := Nat.le_mul_of_pos_left n (by omega)
  have htot' : C.totalSides = 4 * (g * n) := by rw [htot]; ring
  obtain ⟨C₂, hf₂, ht₂, hv₂, hor₂, ⟨e₂⟩⟩ :=
    standardCover_pairingData_aux_contract (n - 1) C₁ hf₁ (by omega)
      (by omega) hor₁
  obtain ⟨P, horP, hP, ⟨e₃⟩⟩ :=
    standardCover_pairingData_aux_toPairing C₂ hf₂ hv₂ hor₂
  refine ⟨P, horP, ?_, ⟨eE.trans (e₁.trans (e₂.trans e₃))⟩⟩
  rw [hP, ← standardCover_pairingData_aux_edgeCount g n hg hn]
  omega

/-- Banked by lemma-2 (2026-10-24): the word of `P`, and `P.Space ≃ₜ PolygonSurface (wordOf P)`. -/
def orientablePairing_normalForm_aux_wordOf (P : PairingData) :
    List (PolygonMoves.Signed (PairingOrbit P.pair)) :=
  List.ofFn (fun i : Fin P.edgeCount => (P.orbit i, P.sign i))

local instance orientablePairing_normalForm_aux_orbit_decEq (P : PairingData) :
    DecidableEq (PairingOrbit P.pair) := Classical.decEq _

@[simp] theorem orientablePairing_normalForm_aux_wordOf_length (P : PairingData) :
    (orientablePairing_normalForm_aux_wordOf P).length = P.edgeCount := by
  simp [orientablePairing_normalForm_aux_wordOf]

@[simp] theorem orientablePairing_normalForm_aux_wordOf_get (P : PairingData)
    (i : Fin (orientablePairing_normalForm_aux_wordOf P).length) :
    (orientablePairing_normalForm_aux_wordOf P).get i =
      (P.orbit ⟨i, by simpa using i.2⟩, P.sign ⟨i, by simpa using i.2⟩) := by
  simp [orientablePairing_normalForm_aux_wordOf]

theorem orientablePairing_normalForm_aux_boundary_to_word (P : PairingData)
    {x y : Disk} (hxy : P.Rel x y) :
    PolygonMoves.WordRel (orientablePairing_normalForm_aux_wordOf P) x y := by
  rcases hxy with ⟨i, t, rfl, rfl⟩
  let i' : Fin (orientablePairing_normalForm_aux_wordOf P).length :=
    ⟨i, by simpa using i.2⟩
  let j' : Fin (orientablePairing_normalForm_aux_wordOf P).length :=
    ⟨P.pair i, by simpa using (P.pair i).2⟩
  refine ⟨i', j', ?_, t, ?_, ?_, ?_⟩
  · intro hij
    apply P.pair_ne i
    exact Fin.ext (congrArg Fin.val hij).symm
  · rw [orientablePairing_normalForm_aux_wordOf_get,
      orientablePairing_normalForm_aux_wordOf_get]
    simpa [i', j'] using (P.orbit_pair i).symm
  · simp [i']
  · rw [orientablePairing_normalForm_aux_wordOf_get,
      orientablePairing_normalForm_aux_wordOf_get]
    simp only [orientablePairing_normalForm_aux_wordOf_length]
    simp [i', j', PolygonSurfacePiOne.pairedParameter,
      PolygonMoves.reverseParameter, PolygonSurfacePiOne.reverseIcc]

theorem orientablePairing_normalForm_aux_word_to_boundary (P : PairingData)
    {x y : Disk}
    (hxy : PolygonMoves.WordRel (orientablePairing_normalForm_aux_wordOf P) x y) :
    Relation.EqvGen P.Rel x y := by
  rcases hxy with ⟨i, j, hij, t, hlab, rfl, rfl⟩
  let i' : Fin P.edgeCount := ⟨i, by simpa using i.2⟩
  let j' : Fin P.edgeCount := ⟨j, by simpa using j.2⟩
  have horbit : P.orbit i' = P.orbit j' := by
    rw [orientablePairing_normalForm_aux_wordOf_get,
      orientablePairing_normalForm_aux_wordOf_get] at hlab
    simpa [i', j'] using hlab
  have hj : j' = P.pair i' := by
    rcases (P.orbit_eq_iff i' j').mp horbit with h | h
    · exfalso
      apply hij
      exact Fin.ext (congrArg Fin.val h).symm
    · exact h
  apply Relation.EqvGen.rel
  refine ⟨i', t, ?_, ?_⟩
  · simp [i']
  · rw [orientablePairing_normalForm_aux_wordOf_get,
      orientablePairing_normalForm_aux_wordOf_get]
    simp only [orientablePairing_normalForm_aux_wordOf_length]
    simp [i', j', hj, PolygonSurfacePiOne.pairedParameter,
      PolygonMoves.reverseParameter, PolygonSurfacePiOne.reverseIcc]
    congr 1
    exact congrArg Fin.val hj

theorem orientablePairing_normalForm_aux_eqv (P : PairingData) (x y : Disk) :
    Relation.EqvGen P.Rel x y ↔
      Relation.EqvGen
        (PolygonMoves.WordRel (orientablePairing_normalForm_aux_wordOf P)) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact .rel _ _ (orientablePairing_normalForm_aux_boundary_to_word P h)
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact orientablePairing_normalForm_aux_word_to_boundary P h
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

def orientablePairing_normalForm_aux_bridge_equiv (P : PairingData) :
    P.Space ≃ PolygonMoves.PolygonSurface
      (orientablePairing_normalForm_aux_wordOf P) :=
  Quotient.congrRight (orientablePairing_normalForm_aux_eqv P)

theorem orientablePairing_normalForm_aux_bridge (P : PairingData) :
    Nonempty (P.Space ≃ₜ PolygonMoves.PolygonSurface
      (orientablePairing_normalForm_aux_wordOf P)) := by
  let e := orientablePairing_normalForm_aux_bridge_equiv P
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }⟩
  · apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : Disk => e (Quotient.mk _ x))
    simpa [e, orientablePairing_normalForm_aux_bridge_equiv] using
      (PolygonMoves.continuous_polygonQuotient
        (orientablePairing_normalForm_aux_wordOf P))
  · apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : Disk => e.symm (Quotient.mk _ x))
    simpa [e, orientablePairing_normalForm_aux_bridge_equiv] using
      P.continuous_quotientMap


/-! ## Word-level normalization

Split of `orientablePairing_normalForm` (claude-14, 2026-10-24, after the
lemma-2 PARTIAL banked the bridge above).  The proof runs on words over `ℕ`,
where fresh labels exist: relabel `wordOf P` injectively into `ℕ`
(`_aux_relabel`), check that the result is an orientable one-vertex polygon word
(`_aux_natWord_isPolygonWord`, `_aux_natWord_orientable`,
`_aux_natWord_oneVertex`), normalize it combinatorially by rotations, relabelings
and orientable cut-and-paste steps (`_aux_normalize`), turn each step into a
homeomorphism (`_aux_cutPaste` plus `PolygonMoves.rotation`/`relabelInvert`),
and compare the standard word with `Surface true h` (`_aux_standard`). -/

open PolygonMoves in
/-- **Leaf (injective relabeling).**  `WordRel` only compares labels for
equality, so an injective relabeling gives the same relation on the disk. -/
lemma orientablePairing_normalForm_aux_relabel_aux_wordRel {L L' : Type*}
    [DecidableEq L] [DecidableEq L'] (w : List (Signed L)) (f : L → L')
    (hf : Function.Injective f) :
    WordRel (w.map fun x => (f x.1, x.2)) = WordRel w := by
  funext p q
  apply propext
  let w' := w.map fun x => (f x.1, x.2)
  constructor
  · rintro ⟨i, j, hij, t, hlab, hp, hq⟩
    let i' : Fin w.length := ⟨i.1, by simpa [w'] using i.2⟩
    let j' : Fin w.length := ⟨j.1, by simpa [w'] using j.2⟩
    have hij' : i' ≠ j' := by
      intro h
      exact hij (Fin.ext (by simpa [i', j'] using congrArg Fin.val h))
    have hlab' : (w.get i').1 = (w.get j').1 := by
      apply hf
      simpa [w', i', j'] using hlab
    refine ⟨i', j', hij', t, hlab', ?_, ?_⟩
    · simpa [i', w'] using hp
    · simpa [i', j', w'] using hq
  · rintro ⟨i, j, hij, t, hlab, hp, hq⟩
    let i' : Fin w'.length := ⟨i.1, by simpa [w'] using i.2⟩
    let j' : Fin w'.length := ⟨j.1, by simpa [w'] using j.2⟩
    have hij' : i' ≠ j' := by
      intro h
      exact hij (Fin.ext (by simpa [i', j'] using congrArg Fin.val h))
    have hlab' : (w'.get i').1 = (w'.get j').1 := by
      simpa [w', i', j'] using congrArg f hlab
    refine ⟨i', j', hij', t, hlab', ?_, ?_⟩
    · simpa [i', w'] using hp
    · simpa [i', j', w'] using hq

open PolygonMoves in
theorem orientablePairing_normalForm_aux_relabel {L L' : Type*}
    [DecidableEq L] [DecidableEq L'] (w : List (Signed L)) (f : L → L')
    (hf : Function.Injective f) :
    Nonempty (PolygonSurface w ≃ₜ PolygonSurface (w.map fun x => (f x.1, x.2))) := by
  let w' := w.map fun x => (f x.1, x.2)
  have h : WordRel w' = WordRel w :=
    orientablePairing_normalForm_aux_relabel_aux_wordRel w f hf
  change Nonempty
    (Quotient (Relation.EqvGen.setoid (WordRel w)) ≃ₜ
      Quotient (Relation.EqvGen.setoid (WordRel w')))
  rw [h]
  exact ⟨Homeomorph.refl _⟩

/-- Labels in `ℕ`: an orbit goes to the index of a chosen representative. -/
def orientablePairing_normalForm_aux_enc (P : PairingData) (o : PairingOrbit P.pair) : ℕ :=
  (Quotient.out o : Fin P.edgeCount).val

theorem orientablePairing_normalForm_aux_enc_injective (P : PairingData) :
    Function.Injective (orientablePairing_normalForm_aux_enc P) := by
  intro a b hab
  exact Quotient.out_inj.mp (Fin.ext hab)

/-- The word of `P` with labels in `ℕ`. -/
def orientablePairing_normalForm_aux_natWord (P : PairingData) :
    List (PolygonMoves.Signed ℕ) :=
  (orientablePairing_normalForm_aux_wordOf P).map
    fun x => (orientablePairing_normalForm_aux_enc P x.1, x.2)

/-- Two distinct arcs with the same label carry opposite signs. -/
def orientablePairing_normalForm_aux_WordOrientable {L : Type*}
    (w : List (PolygonMoves.Signed L)) : Prop :=
  ∀ i j : Fin w.length, i ≠ j → (w.get i).1 = (w.get j).1 → (w.get i).2 ≠ (w.get j).2

/-- Corner `i` is the initial endpoint of arc `i`; its terminal endpoint is
corner `finRotate _ i`.  Pairing two arcs identifies their corners: initial with
initial when the signs agree (parameter preserved, as in `WordRel`), initial
with terminal when they differ. -/
def orientablePairing_normalForm_aux_WordCornerRel {L : Type*}
    (w : List (PolygonMoves.Signed L)) (a b : Fin w.length) : Prop :=
  ∃ i j : Fin w.length, i ≠ j ∧ (w.get i).1 = (w.get j).1 ∧
    if (w.get i).2 = (w.get j).2 then
      (a = i ∧ b = j) ∨ (a = finRotate _ i ∧ b = finRotate _ j)
    else
      (a = i ∧ b = finRotate _ j) ∨ (a = finRotate _ i ∧ b = j)

/-- All corners of the word are one vertex. -/
def orientablePairing_normalForm_aux_WordOneVertex {L : Type*}
    (w : List (PolygonMoves.Signed L)) : Prop :=
  ∀ a b : Fin w.length,
    Relation.EqvGen (orientablePairing_normalForm_aux_WordCornerRel w) a b

/-- **Leaf.**  Each orbit of `P.pair` has exactly the two arcs `i` and
`P.pair i` (`PairingData.orbit_eq_iff`), and `P.edgeCount > 0`. -/
theorem orientablePairing_normalForm_aux_natWord_isPolygonWord_aux_count_ofFn
    {n : ℕ} {A : Type*} [DecidableEq A] (f : Fin n → A) (a : A) :
    (List.ofFn f).count a = (Finset.univ.filter fun i => f i = a).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [List.count_cons]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ]
      simp [ih]
      omega

theorem orientablePairing_normalForm_aux_natWord_isPolygonWord (P : PairingData) :
    PolygonMoves.IsPolygonWord (orientablePairing_normalForm_aux_natWord P) := by
  let e := orientablePairing_normalForm_aux_enc P
  let labels := (orientablePairing_normalForm_aux_natWord P).map Prod.fst
  have hcount : ∀ a ∈ labels, labels.count a = 2 := by
    intro a ha
    have ha' : a ∈ List.ofFn (fun i : Fin P.edgeCount => e (P.orbit i)) := by
      simpa [labels, orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf, e] using ha
    obtain ⟨i, hi⟩ := (List.mem_ofFn.mp ha')
    rw [← hi]
    have hlabels : labels =
        List.ofFn (fun j : Fin P.edgeCount => e (P.orbit j)) := by
      simp only [labels, orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf, List.map_map, List.map_ofFn]
      congr 1
    rw [hlabels]
    rw [orientablePairing_normalForm_aux_natWord_isPolygonWord_aux_count_ofFn]
    have hfilt : (Finset.univ.filter fun j : Fin P.edgeCount =>
        e (P.orbit j) = e (P.orbit i)) = {i, P.pair i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      rw [show e (P.orbit j) = e (P.orbit i) ↔ P.orbit j = P.orbit i from
        (orientablePairing_normalForm_aux_enc_injective P).eq_iff]
      rw [P.orbit_eq_iff]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · right
          rw [h, P.pair_pair]
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (P.pair_pair i).symm
    rw [hfilt]
    simp [Ne.symm (P.pair_ne i)]
  unfold PolygonMoves.IsPolygonWord
  refine ⟨?_, ?_, hcount⟩
  · apply List.ne_nil_of_length_pos
    simpa [orientablePairing_normalForm_aux_natWord] using P.edgeCount_pos
  · have hlen : labels.length =
        (orientablePairing_normalForm_aux_natWord P).length := by simp [labels]
    rw [← hlen, ← List.sum_toFinset_count_eq_length labels]
    apply Finset.even_sum
    intro a ha
    rw [hcount a (List.mem_toFinset.mp ha)]
    exact ⟨1, by omega⟩

/-- **Leaf.**  From `IsOrientablePairing`: the two arcs with one label are
`i` and `P.pair i`, whose signs differ. -/
theorem orientablePairing_normalForm_aux_natWord_orientable (P : PairingData)
    (hor : IsOrientablePairing P) :
    orientablePairing_normalForm_aux_WordOrientable
      (orientablePairing_normalForm_aux_natWord P) := by
  intro i j hij hlabel
  let i' : Fin P.edgeCount := ⟨i, by
    simpa [orientablePairing_normalForm_aux_natWord] using i.2⟩
  let j' : Fin P.edgeCount := ⟨j, by
    simpa [orientablePairing_normalForm_aux_natWord] using j.2⟩
  have horbit : P.orbit i' = P.orbit j' :=
    orientablePairing_normalForm_aux_enc_injective P (by
      simpa [orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf, i', j'] using hlabel)
  rcases (P.orbit_eq_iff i' j').mp horbit with h | h
  · exfalso
    apply hij
    apply Fin.ext
    simpa [i', j'] using (congrArg Fin.val h).symm
  · have hi :
        ((orientablePairing_normalForm_aux_natWord P).get i).2 = P.sign i' := by
      simp [orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf, i']
    have hj :
        ((orientablePairing_normalForm_aux_natWord P).get j).2 = P.sign j' := by
      simp [orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf, j']
    rw [hi, hj, h]
    exact (hor i').symm

/-! ### One vertex: from `boundaryRel` chains to corner chains

Split of `_aux_natWord_oneVertex` (claude-14, 2026-10-24, after the lemma-3
PARTIAL that proved `_aux_endpoint`).  Fix a corner `a`.  The set of disk
points that are polygon vertices of corners corner-related to `a`
(`_aux_Reach`) is closed under one `boundaryRel` step (`_aux_step`) and
`boundaryRel` is symmetric (`_aux_symm`), so `EqvGen` induction carries it
along the chain from `P.oneVertex`.  At the end, `polygonVertex` is injective
(`_aux_endpoint` with parameter `0`), which recovers the corner `b`. -/

/-- A disk point on edge `i` at a polygon vertex is at parameter `0` or `1`,
at the initial or terminal corner of `i`. -/
lemma orientablePairing_normalForm_aux_natWord_oneVertex_aux_endpoint
    (n : ℕ) (hn : 0 < n) (i a : Fin n) (t : Set.Icc (0 : ℝ) 1)
    (h : edgePoint n i t = polygonVertex n a) :
    (t = ⟨0, by norm_num⟩ ∧ a = i) ∨
      (t = ⟨1, by norm_num⟩ ∧ a = finRotate n i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h' := edgePoint_eq_imp_coordinate_cases (m + 1) hn i a t
    ⟨0, by norm_num⟩ (by simpa [polygonVertex] using h)
  rcases h' with hc | hw | hw
  · by_cases ht : t = ⟨0, by norm_num⟩
    · left
      refine ⟨ht, Fin.ext ?_⟩
      subst t
      norm_num at hc ⊢
      exact_mod_cast hc.symm
    · right
      norm_num at hc
      have ht1 : t = ⟨1, by norm_num⟩ := by
        apply Subtype.ext
        have hi : ((i : ℕ) : ℝ) + 1 ≤ m + 1 := by
          exact_mod_cast (show (i : ℕ) + 1 ≤ m + 1 by omega)
        have ha : (a : ℝ) ≤ i + 1 := by linarith [t.2.2]
        have hai : (a : ℕ) ≤ i + 1 := by exact_mod_cast ha
        have hia : (i : ℕ) < a := by
          by_contra hia
          have hai' : (a : ℕ) ≤ i := by omega
          have haiR : (a : ℝ) ≤ i := by exact_mod_cast hai'
          have : (t : ℝ) = 0 := by linarith [t.2.1]
          exact ht (Subtype.ext this)
        have : (a : ℕ) = i + 1 := by omega
        have : (t : ℝ) = 1 := by
          have haiR : (a : ℝ) = i + 1 := by exact_mod_cast this
          nlinarith
        exact this
      refine ⟨ht1, ?_⟩
      have hi : (i : ℕ) < (m + 1) - 1 := by
        subst t
        norm_num at hc
        have ha : (a : ℕ) = i + 1 := by exact_mod_cast hc.symm
        omega
      rw [finRotate_of_lt (show (i : ℕ) < m by simpa using hi)]
      apply Fin.ext
      subst t
      norm_num at hc
      exact_mod_cast hc.symm
  · exfalso
    norm_num at hw
    have ha : ((a : ℕ) : ℝ) < m + 1 := by exact_mod_cast a.2
    have ha' : (a : ℕ) = m + 1 := by exact_mod_cast hw.2
    omega
  · right
    have ht : t = ⟨1, by norm_num⟩ := by
      apply Subtype.ext
      have hi : ((i : ℕ) : ℝ) + 1 ≤ m + 1 := by
        exact_mod_cast (show (i : ℕ) + 1 ≤ m + 1 by omega)
      norm_num at hw
      linarith [t.2.2]
    refine ⟨ht, ?_⟩
    have hi : (i : ℕ) = (m + 1) - 1 := by
      subst t
      norm_num at hw
      have hi' : (i : ℕ) = m := by exact_mod_cast hw.1
      omega
    have ha : a = (0 : Fin (m + 1)) := by
      apply Fin.ext
      norm_num at hw ⊢
      exact_mod_cast hw.2
    subst a
    rw [show i = Fin.last m by apply Fin.ext; simpa using hi]
    exact finRotate_last.symm


/-- The disk points that are vertices of corners corner-related to `a`. -/
def orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach (P : PairingData)
    (a : Fin (orientablePairing_normalForm_aux_natWord P).length) (x : Disk) : Prop :=
  ∃ c : Fin (orientablePairing_normalForm_aux_natWord P).length,
    x = polygonVertex P.edgeCount
      ⟨c, by simpa [orientablePairing_normalForm_aux_natWord] using c.2⟩ ∧
    Relation.EqvGen
      (orientablePairing_normalForm_aux_WordCornerRel
        (orientablePairing_normalForm_aux_natWord P)) a c

/-- **Leaf.**  `boundaryRel` is symmetric: from `x = edgePoint i t` and
`y = edgePoint (pair i) (pairedParameter pair sign i t)`, take arc `pair i`
and parameter `pairedParameter pair sign i t`; use `P.pair_pair` and that
`pairedParameter` is an involution (`reverseIcc` is, and the sign test is
symmetric in `i` and `pair i`). -/
theorem orientablePairing_normalForm_aux_natWord_oneVertex_aux_symm (P : PairingData)
    {x y : Disk} (h : P.Rel x y) : P.Rel y x := by
  sorry

/-- **Leaf.**  One `boundaryRel` step from a reached vertex reaches a vertex.
Write `x = edgePoint i t = polygonVertex c`.  By `_aux_endpoint`, either
`t = 0` and `c = i`, or `t = 1` and `c = finRotate i`.  Then
`y = edgePoint (pair i) s` with `s = t` (signs equal) or `s = 1 - t`, so `s`
is `0` or `1`; take `d = pair i` if `s = 0`, `d = finRotate (pair i)` if
`s = 1` (`edgePoint _ j 1 = polygonVertex (finRotate j)`).  The step `c ~ d`
is one `WordCornerRel` step with arcs `i` and `pair i`: their labels agree
(`P.orbit_pair`), `i ≠ pair i` (`P.pair_ne`), and the four cases of the
definition match the four cases above.  Word letters are
`(enc (P.orbit i), P.sign i)` (`_aux_wordOf_get`). -/
theorem orientablePairing_normalForm_aux_natWord_oneVertex_aux_step (P : PairingData)
    (a : Fin (orientablePairing_normalForm_aux_natWord P).length) {x y : Disk}
    (h : P.Rel x y)
    (hx : orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach P a x) :
    orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach P a y := by
  sorry

theorem orientablePairing_normalForm_aux_natWord_oneVertex_aux_lift
    (P : PairingData)
    (a b : Fin (orientablePairing_normalForm_aux_natWord P).length)
    (h : Relation.EqvGen P.Rel
      (polygonVertex P.edgeCount
        ⟨a, by simpa [orientablePairing_normalForm_aux_natWord] using a.2⟩)
      (polygonVertex P.edgeCount
        ⟨b, by simpa [orientablePairing_normalForm_aux_natWord] using b.2⟩)) :
    Relation.EqvGen
      (orientablePairing_normalForm_aux_WordCornerRel
        (orientablePairing_normalForm_aux_natWord P)) a b := by
  have hiff : ∀ {x y : Disk}, Relation.EqvGen P.Rel x y →
      (orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach P a x ↔
        orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach P a y) := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      exact ⟨orientablePairing_normalForm_aux_natWord_oneVertex_aux_step P a hr,
        orientablePairing_normalForm_aux_natWord_oneVertex_aux_step P a
          (orientablePairing_normalForm_aux_natWord_oneVertex_aux_symm P hr)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨c, hc, hac⟩ := (hiff h).mp ⟨a, rfl, Relation.EqvGen.refl _⟩
  have hcb : c = b := by
    rcases orientablePairing_normalForm_aux_natWord_oneVertex_aux_endpoint
        P.edgeCount P.edgeCount_pos _ _ ⟨0, by norm_num⟩ hc.symm with h0 | h1
    · exact Fin.ext (by simpa using (congrArg Fin.val h0.2).symm)
    · exact absurd (congrArg Subtype.val h1.1) (by norm_num)
  exact hcb ▸ hac

theorem orientablePairing_normalForm_aux_natWord_oneVertex (P : PairingData) :
    orientablePairing_normalForm_aux_WordOneVertex
      (orientablePairing_normalForm_aux_natWord P) := by
  unfold orientablePairing_normalForm_aux_WordOneVertex
  intro a b
  apply orientablePairing_normalForm_aux_natWord_oneVertex_aux_lift P a b
  exact P.oneVertex _ _

/-! ### Orientable cut-and-paste: span construction

Both pictures use the same two convex pieces of the disk, cut by the chord from
vertex `0` to vertex `q = |α₁| + 1 + |α₂|` (`cutOldA`/`cutOldB` of
`PolygonMoves` with `p = 0`).  Only the labelling of the piece boundaries
changes: piece `A` reads `α₁ y α₂ c⁻¹` in the old word and `α₂ c⁻¹ α₁ y` in the
new one, piece `B` reads `β₁ y⁻¹ β₂ c` and `β₂ c β₁ y⁻¹`.  So the new boundary
parametrisations are the old ones precomposed with circle homeomorphisms
`ρA`, `ρB` that permute the boundary arcs (`_aux_reparamA`, `_aux_reparamB`).
The relation bookkeeping (`_aux_forward`, `_aux_reverse`, `_aux_fibreForward`,
`_aux_fibreReverse`) only uses the edge formulas collected in `_aux_Data`. -/

/-- Banked (lemma-1, 2026-10-24): the two words have the same length. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_length
    {L : Type*} (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed L))
    (y c : PolygonMoves.Signed L) :
    (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).length =
      (α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length := by
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
  omega

open PolygonMoves in
/-- Edge formulas for the orientable cut.  `L` is the word length; the old word
is `α₁ y α₂ β₁ y⁻¹ β₂` with `|α₁| = n₁`, `|α₂| = n₂`, `|β₁| = m₁`, `|β₂| = m₂`,
and `q = n₁ + 1 + n₂`.  The `old` fields are those of `CutBoundaryData L 0 q`;
the `ρ` fields say where each old boundary arc goes in the new word
`α₂ c⁻¹ α₁ β₂ c β₁` (same length, same chord). -/
structure orientablePairing_normalForm_aux_cutPaste_aux_Data (L n₁ n₂ m₁ m₂ : ℕ)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle) : Prop where
  length : L = n₁ + 1 + n₂ + m₁ + 1 + m₂
  coverA : ∀ z : Circle,
    (∃ e s, e < n₁ + 1 + n₂ ∧ z = cutEdgeCircle L e s) ∨
      (∃ s : Icc (0 : ℝ) 1, z = cutChordParamA L 0 (n₁ + 1 + n₂) s)
  coverB : ∀ z : Circle,
    (∃ e s, n₁ + 1 + n₂ ≤ e ∧ e < L ∧ z = cutEdgeCircle L e s) ∨
      (∃ s : Icc (0 : ℝ) 1, z = cutChordParamB L 0 (n₁ + 1 + n₂) s)
  oldA_arc : ∀ e s, e < n₁ + 1 + n₂ →
    oldA (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)
  oldA_chord : ∀ s : Icc (0 : ℝ) 1,
    oldA (cutChordParamA L 0 (n₁ + 1 + n₂) s) = cutChordA L 0 (n₁ + 1 + n₂) s
  oldB_arc : ∀ e s, n₁ + 1 + n₂ ≤ e → e < L →
    oldB (cutEdgeCircle L e s) = (edgePoint L e s : ℂ)
  oldB_chord : ∀ s : Icc (0 : ℝ) 1,
    oldB (cutChordParamB L 0 (n₁ + 1 + n₂) s) = cutChordB L 0 (n₁ + 1 + n₂) s
  ρA_α₁ : ∀ e s, e < n₁ → ρA (cutEdgeCircle L e s) = cutEdgeCircle L (e + n₂ + 1) s
  ρA_y : ∀ s, ρA (cutEdgeCircle L n₁ s) = cutChordParamA L 0 (n₁ + 1 + n₂) s
  ρA_α₂ : ∀ e s, n₁ + 1 ≤ e → e < n₁ + 1 + n₂ →
    ρA (cutEdgeCircle L e s) = cutEdgeCircle L (e - n₁ - 1) s
  ρA_chord : ∀ s, ρA (cutChordParamA L 0 (n₁ + 1 + n₂) s) = cutEdgeCircle L n₂ s
  ρB_β₁ : ∀ e s, n₁ + 1 + n₂ ≤ e → e < n₁ + 1 + n₂ + m₁ →
    ρB (cutEdgeCircle L e s) = cutEdgeCircle L (e + m₂ + 1) s
  ρB_y : ∀ s, ρB (cutEdgeCircle L (n₁ + 1 + n₂ + m₁) s) = cutChordParamB L 0 (n₁ + 1 + n₂) s
  ρB_β₂ : ∀ e s, n₁ + 1 + n₂ + m₁ + 1 ≤ e → e < L →
    ρB (cutEdgeCircle L e s) = cutEdgeCircle L (e - m₁ - 1) s
  ρB_chord : ∀ s, ρB (cutChordParamB L 0 (n₁ + 1 + n₂) s) =
    cutEdgeCircle L (n₁ + 1 + n₂ + m₂) s

open PolygonMoves in
/-- Generic `EqvGen` lift through a surjective parametrisation (copy of
`cutAndPaste_aux_triangle_charts_forward` with the words abstracted). -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_lift {Y L L' : Type*}
    [DecidableEq L] [DecidableEq L']
    (w₁ : List (Signed L)) (w₂ : List (Signed L')) (a b : Y → Disk)
    (has : Function.Surjective a)
    (hfib : ∀ y y', a y = a y' → Relation.EqvGen (WordRel w₂) (b y) (b y'))
    (hgen : ∀ y y', WordRel w₁ (a y) (a y') → Relation.EqvGen (WordRel w₂) (b y) (b y')) :
    ∀ y y', Relation.EqvGen (WordRel w₁) (a y) (a y') →
      Relation.EqvGen (WordRel w₂) (b y) (b y') := by
  intro y y' h
  have lift : ∀ p q : Disk, Relation.EqvGen (WordRel w₁) p q →
      ∀ yp yq, a yp = p → a yq = q → Relation.EqvGen (WordRel w₂) (b yp) (b yq) := by
    intro p q hpq
    induction hpq with
    | rel p q hpq =>
        intro yp yq hyp hyq
        apply hgen yp yq
        simpa [hyp, hyq] using hpq
    | refl p =>
        intro yp yq hyp hyq
        apply hfib yp yq
        rw [hyp, hyq]
    | symm p q _ ih =>
        intro yp yq hyp hyq
        exact Relation.EqvGen.symm _ _ (ih yq yp hyq hyp)
    | trans p q r _ _ ihpq ihqr =>
        intro yp yr hyp hyr
        obtain ⟨yq, hyq⟩ := has q
        exact Relation.EqvGen.trans _ _ _ (ihpq yp yq hyp hyq) (ihqr yq yr hyq hyr)
  exact lift (a y) (a y') h y y' rfl rfl

open PolygonMoves in
/-- Generic form of `PolygonMoves.cut_charts_package`: its proof never looks at
the two words, so it is copied with the words abstracted. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_package {Label : Type*}
    [DecidableEq Label] (w₁ w₂ : List (Signed Label))
    (KA KB KA' KB' : Set ℂ) (oldA oldB newA newB : Circle → ℂ) (φA φB ψA ψB : ℂ → ℂ)
    (hA : CutChartSpec KA oldA φA) (hB : CutChartSpec KB oldB φB)
    (hA' : CutChartSpec KA' newA ψA) (hB' : CutChartSpec KB' newB ψB)
    (hcov : KA ∪ KB = Metric.closedBall 0 1) (hcov' : KA' ∪ KB' = Metric.closedBall 0 1)
    (hdisj : interior KA ∩ KB = ∅) (hdisjB : interior KB ∩ KA = ∅)
    (hdisj' : interior KA' ∩ KB' = ∅) (hdisjB' : interior KB' ∩ KA' = ∅)
    (hfwd : ∀ (i i' : Bool) (y y' : Circle) (P P' N N' : Disk),
      (P : ℂ) = (if i then oldB y else oldA y) → (P' : ℂ) = (if i' then oldB y' else oldA y') →
      (N : ℂ) = (if i then newB y else newA y) → (N' : ℂ) = (if i' then newB y' else newA y') →
      WordRel w₁ P P' →
      Relation.EqvGen (WordRel w₂) N N')
    (hrev : ∀ (i i' : Bool) (y y' : Circle) (P P' N N' : Disk),
      (P : ℂ) = (if i then oldB y else oldA y) → (P' : ℂ) = (if i' then oldB y' else oldA y') →
      (N : ℂ) = (if i then newB y else newA y) → (N' : ℂ) = (if i' then newB y' else newA y') →
      WordRel w₂ N N' →
      Relation.EqvGen (WordRel w₁) P P')
    (hffib : ∀ (y y' : Circle) (N N' : Disk), oldA y = oldB y' →
      (N : ℂ) = newA y → (N' : ℂ) = newB y' →
      Relation.EqvGen (WordRel w₂) N N')
    (hrfib : ∀ (y y' : Circle) (P P' : Disk), newA y = newB y' →
      (P : ℂ) = oldA y → (P' : ℂ) = oldB y' →
      Relation.EqvGen (WordRel w₁) P P') :
    ∃ a b : Fin 2 × Disk → Disk, Continuous a ∧ Continuous b ∧
      Function.Surjective a ∧ Function.Surjective b ∧
      (∀ y y', WordRel w₁ (a y) (a y') →
        Relation.EqvGen (WordRel w₂)
          (b y) (b y')) ∧
      (∀ y y', WordRel w₂ (b y) (b y') →
        Relation.EqvGen (WordRel w₁)
          (a y) (a y')) ∧
      (∀ y y', a y = a y' → Relation.EqvGen (WordRel w₂) (b y) (b y')) ∧
      (∀ y y', b y = b y' → Relation.EqvGen (WordRel w₁) (a y) (a y')) := by
  have hKAsub : KA ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov]
    exact subset_union_left
  have hKBsub : KB ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov]
    exact subset_union_right
  have hKA'sub : KA' ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov']
    exact subset_union_left
  have hKB'sub : KB' ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [← hcov']
    exact subset_union_right
  let a : Fin 2 × Disk → Disk := fun iz =>
    ⟨if iz.1 = 0 then φA iz.2 else φB iz.2, by
      rcases iz with ⟨i, z⟩
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, Fin.val_zero, ↓reduceIte]
        exact hKAsub (by rw [← hA.2.2.1]; exact ⟨z, z.2, rfl⟩)
      · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
        exact hKBsub (by rw [← hB.2.2.1]; exact ⟨z, z.2, rfl⟩)⟩
  let b : Fin 2 × Disk → Disk := fun iz =>
    ⟨if iz.1 = 0 then ψA iz.2 else ψB iz.2, by
      rcases iz with ⟨i, z⟩
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, Fin.val_zero, ↓reduceIte]
        exact hKA'sub (by rw [← hA'.2.2.1]; exact ⟨z, z.2, rfl⟩)
      · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
        exact hKB'sub (by rw [← hB'.2.2.1]; exact ⟨z, z.2, rfl⟩)⟩
  have ha_cont : Continuous a := by
    rw [continuous_prod_of_discrete_left]
    intro i
    apply Continuous.subtype_mk
    fin_cases i
    · simpa [a] using hA.1.comp continuous_subtype_val
    · simpa [a] using hB.1.comp continuous_subtype_val
  have hb_cont : Continuous b := by
    rw [continuous_prod_of_discrete_left]
    intro i
    apply Continuous.subtype_mk
    fin_cases i
    · simpa [b] using hA'.1.comp continuous_subtype_val
    · simpa [b] using hB'.1.comp continuous_subtype_val
  have ha_surj : Function.Surjective a := by
    intro p
    have hp : (p : ℂ) ∈ KA ∪ KB := by rw [hcov]; exact p.2
    rcases hp with hp | hp
    · rw [← hA.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(0, ⟨z, hz⟩), by apply Subtype.ext; simpa [a] using he⟩
    · rw [← hB.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(1, ⟨z, hz⟩), by apply Subtype.ext; simpa [a] using he⟩
  have hb_surj : Function.Surjective b := by
    intro p
    have hp : (p : ℂ) ∈ KA' ∪ KB' := by rw [hcov']; exact p.2
    rcases hp with hp | hp
    · rw [← hA'.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(0, ⟨z, hz⟩), by apply Subtype.ext; simpa [b] using he⟩
    · rw [← hB'.2.2.1] at hp
      rcases hp with ⟨z, hz, he⟩
      exact ⟨(1, ⟨z, hz⟩), by apply Subtype.ext; simpa [b] using he⟩
  have parameter_boundary_old : ∀ y : Fin 2 × Disk, ‖(a y : ℂ)‖ = 1 →
      ∃ c : Circle,
        ((a y : ℂ) = if y.1.1 = 0 then oldA c else oldB c) ∧
        ((b y : ℂ) = if y.1.1 = 0 then newA c else newB c) := by
    rintro ⟨i, z⟩ hy
    fin_cases i
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hA.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKAsub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖φA (z : ℂ)‖ = 1 := by simpa [a] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hA.2.2.2.1 c
      · simpa [b, c] using hA'.2.2.2.1 c
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hB.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKBsub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖φB (z : ℂ)‖ = 1 := by simpa [a] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hB.2.2.2.1 c
      · simpa [b, c] using hB'.2.2.2.1 c
  have parameter_boundary_new : ∀ y : Fin 2 × Disk, ‖(b y : ℂ)‖ = 1 →
      ∃ c : Circle,
        ((a y : ℂ) = if y.1.1 = 0 then oldA c else oldB c) ∧
        ((b y : ℂ) = if y.1.1 = 0 then newA c else newB c) := by
    rintro ⟨i, z⟩ hy
    fin_cases i
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hA'.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKA'sub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖ψA (z : ℂ)‖ = 1 := by simpa [b] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hA.2.2.2.1 c
      · simpa [b, c] using hA'.2.2.2.1 c
    · have hz : ‖(z : ℂ)‖ = 1 := by
        have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
        apply le_antisymm hle
        by_contra hn
        have hlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hn
        have hi := hB'.2.2.2.2 (z : ℂ) hlt
        have hi' := interior_mono hKB'sub hi
        rw [interior_closedBall (0 : ℂ) one_ne_zero] at hi'
        have he : ‖ψB (z : ℂ)‖ = 1 := by simpa [b] using hy
        simpa [Metric.mem_ball, dist_zero_right, he] using hi'
      let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
      refine ⟨c, ?_, ?_⟩
      · simpa [a, c] using hB.2.2.2.1 c
      · simpa [b, c] using hB'.2.2.2.1 c
  have word_boundary : ∀ (w : List (Signed Label)) (P P' : Disk),
      WordRel w P P' → ‖(P : ℂ)‖ = 1 ∧ ‖(P' : ℂ)‖ = 1 := by
    intro w P P' h
    rcases h with ⟨i, j, hij, s, hl, hP, hP'⟩
    constructor
    · rw [hP]; simp [edgePoint, Complex.norm_exp]
    · rw [hP']; simp [edgePoint, Complex.norm_exp]
  have mixed_old : ∀ z z' : Disk, φA z = φB z' →
      ∃ c c' : Circle, oldA c = oldB c' ∧ ψA z = newA c ∧ ψB z' = newB c' := by
    intro z z' he
    have hzA : φA z ∈ KA := by rw [← hA.2.2.1]; exact ⟨z, z.2, rfl⟩
    have hzB : φB z' ∈ KB := by rw [← hB.2.2.1]; exact ⟨z', z'.2, rfl⟩
    have hz : ‖(z : ℂ)‖ = 1 := by
      have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
      apply le_antisymm hle
      by_contra hn
      have hi := hA.2.2.2.2 (z : ℂ) (lt_of_not_ge hn)
      have hm : φA z ∈ interior KA ∩ KB := ⟨hi, he ▸ hzB⟩
      rw [hdisj] at hm
      exact hm
    have hz' : ‖(z' : ℂ)‖ = 1 := by
      have hle : ‖(z' : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z'.2
      apply le_antisymm hle
      by_contra hn
      have hi := hB.2.2.2.2 (z' : ℂ) (lt_of_not_ge hn)
      have hm : φB z' ∈ interior KB ∩ KA := ⟨hi, he.symm ▸ hzA⟩
      rw [hdisjB] at hm
      exact hm
    let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
    let c' : Circle := ⟨z', by simpa [Circle, Submonoid.unitSphere] using hz'⟩
    refine ⟨c, c', ?_, ?_, ?_⟩
    · rw [← hA.2.2.2.1 c, ← hB.2.2.2.1 c']
      exact he
    · exact hA'.2.2.2.1 c
    · exact hB'.2.2.2.1 c'
  have mixed_new : ∀ z z' : Disk, ψA z = ψB z' →
      ∃ c c' : Circle, newA c = newB c' ∧ φA z = oldA c ∧ φB z' = oldB c' := by
    intro z z' he
    have hzA : ψA z ∈ KA' := by rw [← hA'.2.2.1]; exact ⟨z, z.2, rfl⟩
    have hzB : ψB z' ∈ KB' := by rw [← hB'.2.2.1]; exact ⟨z', z'.2, rfl⟩
    have hz : ‖(z : ℂ)‖ = 1 := by
      have hle : ‖(z : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2
      apply le_antisymm hle
      by_contra hn
      have hi := hA'.2.2.2.2 (z : ℂ) (lt_of_not_ge hn)
      have hm : ψA z ∈ interior KA' ∩ KB' := ⟨hi, he ▸ hzB⟩
      rw [hdisj'] at hm
      exact hm
    have hz' : ‖(z' : ℂ)‖ = 1 := by
      have hle : ‖(z' : ℂ)‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z'.2
      apply le_antisymm hle
      by_contra hn
      have hi := hB'.2.2.2.2 (z' : ℂ) (lt_of_not_ge hn)
      have hm : ψB z' ∈ interior KB' ∩ KA' := ⟨hi, he.symm ▸ hzA⟩
      rw [hdisjB'] at hm
      exact hm
    let c : Circle := ⟨z, by simpa [Circle, Submonoid.unitSphere] using hz⟩
    let c' : Circle := ⟨z', by simpa [Circle, Submonoid.unitSphere] using hz'⟩
    refine ⟨c, c', ?_, ?_, ?_⟩
    · rw [← hA'.2.2.2.1 c, ← hB'.2.2.2.1 c']
      exact he
    · exact hA.2.2.2.1 c
    · exact hB.2.2.2.1 c'
  refine ⟨a, b, ha_cont, hb_cont, ha_surj, hb_surj, ?_, ?_, ?_, ?_⟩
  · intro y y' h
    rcases word_boundary _ _ _ h with ⟨hy, hy'⟩
    rcases parameter_boundary_old y hy with ⟨c, hc, hd⟩
    rcases parameter_boundary_old y' hy' with ⟨c', hc', hd'⟩
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · exact hfwd false false c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
    · exact hfwd false true c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
    · exact hfwd true false c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
    · exact hfwd true true c c' _ _ _ _ (by simpa using hc) (by simpa using hc')
        (by simpa using hd) (by simpa using hd') h
  · intro y y' h
    rcases word_boundary _ _ _ h with ⟨hy, hy'⟩
    rcases parameter_boundary_new y hy with ⟨c, hd, hc⟩
    rcases parameter_boundary_new y' hy' with ⟨c', hd', hc'⟩
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · exact hrev false false c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
    · exact hrev false true c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
    · exact hrev true false c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
    · exact hrev true true c c' _ _ _ _ (by simpa using hd) (by simpa using hd')
        (by simpa using hc) (by simpa using hc') h
  · intro y y' h
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · have hz : z = z' := Subtype.ext (hA.2.1 (by exact z.2) (by exact z'.2) (congrArg Subtype.val h))
      subst z'; exact .refl _
    · have he : φA z = φB z' := by simpa [a] using congrArg Subtype.val h
      rcases mixed_old z z' he with ⟨c, c', hcc, hz, hz'⟩
      exact hffib c c' _ _ hcc (by simpa [b] using hz) (by simpa [b] using hz')
    · have he : φA z' = φB z := by simpa [a] using (congrArg Subtype.val h).symm
      rcases mixed_old z' z he with ⟨c, c', hcc, hz', hz⟩
      exact (hffib c c' _ _ hcc (by simpa [b] using hz') (by simpa [b] using hz)).symm
    · have hz : z = z' := Subtype.ext (hB.2.1 z.2 z'.2 (congrArg Subtype.val h))
      subst z'; exact .refl _
  · intro y y' h
    rcases y with ⟨i, z⟩; rcases y' with ⟨i', z'⟩
    fin_cases i <;> fin_cases i'
    · have hz : z = z' := Subtype.ext (hA'.2.1 z.2 z'.2 (congrArg Subtype.val h))
      subst z'; exact .refl _
    · have he : ψA z = ψB z' := by simpa [b] using congrArg Subtype.val h
      rcases mixed_new z z' he with ⟨c, c', hcc, hz, hz'⟩
      exact hrfib c c' _ _ hcc (by simpa [a] using hz) (by simpa [a] using hz')
    · have he : ψA z' = ψB z := by simpa [b] using (congrArg Subtype.val h).symm
      rcases mixed_new z' z he with ⟨c, c', hcc, hz', hz⟩
      exact (hrfib c c' _ _ hcc (by simpa [a] using hz') (by simpa [a] using hz)).symm
    · have hz : z = z' := Subtype.ext (hB'.2.1 z.2 z'.2 (congrArg Subtype.val h))
      subst z'; exact .refl _


open PolygonMoves in
/-- **Leaf (circle reparametrisation, piece `A`).**  An orientation-preserving
piecewise-linear homeomorphism of the parameter circle of piece `A` that moves
the old boundary arcs `α₁ y α₂ c⁻¹` to the new positions `α₂ c⁻¹ α₁ y`: the
`α₁` arcs shift by `n₂ + 1`, the `y` arc goes onto the chord arc, the `α₂`
arcs shift back by `n₁ + 1`, and the chord arc goes onto arc `n₂`.  The pieces
fit at the junction angles (e.g. arc `n₁` at `s = 0` and the chord at `s = 0`
are both at angle `α q`); `n₁ = 0` and `n₂ = 0` are allowed.  Built like
`equivariantLift_of_interval` from a monotone lift on `[0, 2π]`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reparamA (L n₁ n₂ : ℕ)
    (hL : n₁ + 1 + n₂ < L) :
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ e s, e < n₁ → ρ (cutEdgeCircle L e s) = cutEdgeCircle L (e + n₂ + 1) s) ∧
      (∀ s, ρ (cutEdgeCircle L n₁ s) = cutChordParamA L 0 (n₁ + 1 + n₂) s) ∧
      (∀ e s, n₁ + 1 ≤ e → e < n₁ + 1 + n₂ →
        ρ (cutEdgeCircle L e s) = cutEdgeCircle L (e - n₁ - 1) s) ∧
      (∀ s, ρ (cutChordParamA L 0 (n₁ + 1 + n₂) s) = cutEdgeCircle L n₂ s) := by
  sorry

open PolygonMoves in
/-- **Leaf (circle reparametrisation, piece `B`).**  As `_aux_reparamA` for
piece `B`: old arcs `β₁ y⁻¹ β₂ c` (arcs `q … L-1`, then the chord arc
`cutChordParamB`, angles `2π … α q + 2π`) go to `β₂ c β₁ y⁻¹`.  With `m₁ = 0`
the `y⁻¹` arc starts at angle `α q`, where the chord arc ends; both formulas
then give angle `0`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reparamB (L n₁ n₂ m₁ m₂ : ℕ)
    (hL : L = n₁ + 1 + n₂ + m₁ + 1 + m₂) :
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ e s, n₁ + 1 + n₂ ≤ e → e < n₁ + 1 + n₂ + m₁ →
        ρ (cutEdgeCircle L e s) = cutEdgeCircle L (e + m₂ + 1) s) ∧
      (∀ s, ρ (cutEdgeCircle L (n₁ + 1 + n₂ + m₁) s) = cutChordParamB L 0 (n₁ + 1 + n₂) s) ∧
      (∀ e s, n₁ + 1 + n₂ + m₁ + 1 ≤ e → e < L →
        ρ (cutEdgeCircle L e s) = cutEdgeCircle L (e - m₁ - 1) s) ∧
      (∀ s, ρ (cutChordParamB L 0 (n₁ + 1 + n₂) s) =
        cutEdgeCircle L (n₁ + 1 + n₂ + m₂) s) := by
  sorry

open PolygonMoves in
/-- **Leaf (forward generators).**  An old side identification between two
boundary points of the pieces becomes a chain of new identifications between
the corresponding new points.  Model: `PolygonMoves.cut_forward_generators`
(transfer each point to a side of the new word, then relate the sides).  The
`y` pair lands on the chord, so its two points become equal; the other labels
move rigidly with their arcs.  Vertex points have several preimages; their new
images are related through `EqvGen` chains, as in `cut_transfer_consistency`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (i i' : Bool) (z z' : Circle) (P P' N N' : Disk)
    (hP : (P : ℂ) = (if i then oldB z else oldA z))
    (hP' : (P' : ℂ) = (if i' then oldB z' else oldA z'))
    (hN : (N : ℂ) = (if i then oldB (ρB z) else oldA (ρA z)))
    (hN' : (N' : ℂ) = (if i' then oldB (ρB z') else oldA (ρA z')))
    (h : WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂) P P') :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N N' := by
  sorry

open PolygonMoves in
/-- **Leaf (reverse generators).**  Converse of `_aux_forward`: a new side
identification pulls back to an old chain.  The `c` pair lands on the old
chord, so its two points become equal.  Model: `cut_reverse_generators`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (i i' : Bool) (z z' : Circle) (P P' N N' : Disk)
    (hP : (P : ℂ) = (if i then oldB z else oldA z))
    (hP' : (P' : ℂ) = (if i' then oldB z' else oldA z'))
    (hN : (N : ℂ) = (if i then oldB (ρB z) else oldA (ρA z)))
    (hN' : (N' : ℂ) = (if i' then oldB (ρB z') else oldA (ρA z')))
    (h : WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁) N N') :
    Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P P' := by
  sorry

open PolygonMoves in
/-- **Leaf (forward fibre).**  A point on both old pieces lies on the chord
`c` (or is one of its end vertices).  Its two new images are on the new sides
`c⁻¹` (position `n₂`, parameter `s`) and `c` (position `q + m₂`, parameter
`1 - s`), which the new word identifies.  Model: `cut_forward_fibre`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_fibreForward {L : Type*}
    [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (z z' : Circle) (N N' : Disk) (h : oldA z = oldB z')
    (hN : (N : ℂ) = oldA (ρA z)) (hN' : (N' : ℂ) = oldB (ρB z')) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N N' := by
  sorry

open PolygonMoves in
/-- **Leaf (reverse fibre).**  A point on both new pieces lies on the new
chord `y`.  Its old preimages are on the old sides `y` (position `n₁`) and
`y⁻¹` (position `q + m₁`), which the old word identifies.  Model:
`cut_reverse_fibre`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_fibreReverse {L : Type*}
    [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (z z' : Circle) (P P' : Disk) (h : oldA (ρA z) = oldB (ρB z'))
    (hP : (P : ℂ) = oldA z) (hP' : (P' : ℂ) = oldB z') :
    Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P P' := by
  sorry

open PolygonMoves in
/-- **Leaf (orientable cut-and-paste).**  Cut the polygon
`α₁ y α₂ β₁ y⁻¹ β₂` along a new chord `c` from the start of `α₁` to the start
of `β₁`.  The pieces are `α₁ y α₂ c⁻¹` and `β₁ y⁻¹ β₂ c`; gluing them along `y`
gives `α₂ c⁻¹ α₁ β₂ c β₁`.  (Checks: `a b a⁻¹ b⁻¹` with `y = a` gives
`b c⁻¹ b⁻¹ c`; `a a⁻¹ b b⁻¹` gives `c⁻¹ b b⁻¹ c`.)  `PolygonMoves.cutAndPaste`
is the crosscap version (`x … x`) and does not apply to orientable words;
its chart machinery (`polygonSurface_homeomorph_of_span`, `cutPiece`,
`cutSeam`) is the model for this one. -/
theorem orientablePairing_normalForm_aux_cutPaste {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (hw : IsPolygonWord (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) :
    Nonempty (PolygonSurface (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂) ≃ₜ
      PolygonSurface (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) := by
  have hlen := orientablePairing_normalForm_aux_cutPaste_aux_length α₁ α₂ β₁ β₂ y c
  set W := α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂ with hW
  set W' := α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁ with hW'
  set n := W.length with hn
  set q := α₁.length + 1 + α₂.length with hq
  have hWlen : n = α₁.length + 1 + α₂.length + β₁.length + 1 + β₂.length := by
    simp only [hn, hW, List.length_append, List.length_cons, List.length_nil]
  have hpq : 0 < q := by omega
  have hqL : q < n := by omega
  obtain ⟨ρA, hρA1, hρA2, hρA3, hρA4⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reparamA n α₁.length α₂.length hqL
  obtain ⟨ρB, hρB1, hρB2, hρB3, hρB4⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reparamB n α₁.length α₂.length
      β₁.length β₂.length hWlen
  have hPQ : cutPoint n 0 ≠ cutPoint n q := cutPoint_ne hpq (by omega)
  have hnorm := cutPoint_norm n
  obtain ⟨cA, hcA⟩ := cutPiece_interior_nonempty (hnorm _) (hnorm _) hPQ
  obtain ⟨cB, hcB⟩ := cutPiece_interior_nonempty (hnorm _) (hnorm _) hPQ.symm
  have hrA := cutOldA_range hpq hqL (cutPiece_frontier (hnorm _) (hnorm _) hPQ) cutCross_exp
  have hrB := cutOldB_range hpq hqL
    (cutPiece_frontier (hnorm _) (hnorm _) hPQ.symm) cutCross_exp
  obtain ⟨φA, hφA⟩ := cutAndPaste_aux_boundary_chart _ cA (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcA _ (cutOldA_continuous hpq hqL)
    (cutOldA_injective hpq hqL) hrA
  obtain ⟨φB, hφB⟩ := cutAndPaste_aux_boundary_chart _ cB (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcB _ (cutOldB_continuous hpq hqL)
    (cutOldB_injective hpq hqL) hrB
  obtain ⟨ψA, hψA⟩ := cutAndPaste_aux_boundary_chart _ cA (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcA (fun z => cutOldA n 0 q (ρA z))
    ((cutOldA_continuous hpq hqL).comp ρA.continuous)
    ((cutOldA_injective hpq hqL).comp ρA.injective)
    (by rw [Set.range_comp', ρA.surjective.range_eq, Set.image_univ]; exact hrA)
  obtain ⟨ψB, hψB⟩ := cutAndPaste_aux_boundary_chart _ cB (cutPiece_convex_compact _ _).1
    (cutPiece_convex_compact _ _).2 hcB (fun z => cutOldB n 0 q (ρB z))
    ((cutOldB_continuous hpq hqL).comp ρB.continuous)
    ((cutOldB_injective hpq hqL).comp ρB.injective)
    (by rw [Set.range_comp', ρB.surjective.range_eq, Set.image_univ]; exact hrB)
  obtain ⟨hA1, hB1, hB2⟩ := cutBoundary_old_fields hpq hqL
  have D : orientablePairing_normalForm_aux_cutPaste_aux_Data n α₁.length α₂.length
      β₁.length β₂.length (cutOldA n 0 q) (cutOldB n 0 q) ρA ρB :=
    { length := hWlen
      coverA := fun z => by
        rcases cutBoundary_coverA hpq hqL z with ⟨e, s, -, he, hz⟩ | h
        · exact Or.inl ⟨e, s, he, hz⟩
        · exact Or.inr h
      coverB := fun z => by
        rcases cutBoundary_coverB hpq hqL z with ⟨e, s, he, hz⟩ | h
        · exact Or.inl ⟨e, s, by omega, by omega, hz⟩
        · exact Or.inr h
      oldA_arc := fun e s he =>
        cutBoundaryData_concrete_aux_oldA_arc s hpq hqL (Nat.zero_le e) he
      oldA_chord := hA1
      oldB_arc := fun e s he he' => hB1 e s (Or.inl ⟨he, he'⟩)
      oldB_chord := hB2
      ρA_α₁ := hρA1
      ρA_y := hρA2
      ρA_α₂ := hρA3
      ρA_chord := hρA4
      ρB_β₁ := hρB1
      ρB_y := hρB2
      ρB_β₂ := hρB3
      ρB_chord := hρB4 }
  obtain ⟨a, b, ha, hb, has, hbs, hf, hr, hfa, hfb⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_package W W' _ _ _ _
      (cutOldA n 0 q) (cutOldB n 0 q) (fun z => cutOldA n 0 q (ρA z))
      (fun z => cutOldB n 0 q (ρB z)) φA φB ψA ψB hφA hφB hψA hψB
      (cutPiece_union_disjoint _ _ hPQ).1 (cutPiece_union_disjoint _ _ hPQ).1
      (cutPiece_union_disjoint _ _ hPQ).2 (cutPiece_union_disjoint _ _ hPQ.symm).2
      (cutPiece_union_disjoint _ _ hPQ).2 (cutPiece_union_disjoint _ _ hPQ.symm).2
      (fun i i' z z' P P' N N' hP hP' hN hN' h =>
        orientablePairing_normalForm_aux_cutPaste_aux_forward α₁ α₂ β₁ β₂ y c hy hc
          _ _ ρA ρB D i i' z z' P P' N N' hP hP' hN hN' h)
      (fun i i' z z' P P' N N' hP hP' hN hN' h =>
        orientablePairing_normalForm_aux_cutPaste_aux_reverse α₁ α₂ β₁ β₂ y c hy hc
          _ _ ρA ρB D i i' z z' P P' N N' hP hP' hN hN' h)
      (fun z z' N N' h hN hN' =>
        orientablePairing_normalForm_aux_cutPaste_aux_fibreForward α₁ α₂ β₁ β₂ y c hy hc
          _ _ ρA ρB D z z' N N' h hN hN')
      (fun z z' P P' h hP hP' =>
        orientablePairing_normalForm_aux_cutPaste_aux_fibreReverse α₁ α₂ β₁ β₂ y c hy hc
          _ _ ρA ρB D z z' P P' h hP hP')
  exact polygonSurface_homeomorph_of_span W W' a b ha hb has hbs fun z z' =>
    ⟨orientablePairing_normalForm_aux_cutPaste_aux_lift W W' a b has hfa hf z z',
      orientablePairing_normalForm_aux_cutPaste_aux_lift W' W b a hbs hfb hr z z'⟩

open PolygonMoves in
/-- One elementary move on words over `ℕ`.  Each constructor carries the
hypotheses its homeomorphism needs, so `_aux_step_homeomorph` is a case split. -/
inductive orientablePairing_normalForm_aux_Step :
    List (Signed ℕ) → List (Signed ℕ) → Prop
  | rotation (u v : List (Signed ℕ)) (hw : IsPolygonWord (u ++ v)) :
      orientablePairing_normalForm_aux_Step (u ++ v) (v ++ u)
  | relabel (w : List (Signed ℕ)) (e : ℕ ≃ ℕ) (flip : ℕ → Bool)
      (hw : IsPolygonWord w) :
      orientablePairing_normalForm_aux_Step w
        (w.map fun x => (e x.1, xor x.2 (flip x.1)))
  | cutPaste (α₁ α₂ β₁ β₂ : List (Signed ℕ)) (y c : Signed ℕ)
      (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
      (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
      (hw : IsPolygonWord (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) :
      orientablePairing_normalForm_aux_Step
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)
        (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)

theorem orientablePairing_normalForm_aux_step_homeomorph
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w') :
    Nonempty (PolygonMoves.PolygonSurface w ≃ₜ PolygonMoves.PolygonSurface w') := by
  cases hs with
  | rotation u v hw => exact PolygonMoves.rotation u v hw
  | relabel w e flip hw => exact PolygonMoves.relabelInvert w e flip hw
  | cutPaste α₁ α₂ β₁ β₂ y c hy hc hw =>
      exact orientablePairing_normalForm_aux_cutPaste α₁ α₂ β₁ β₂ y c hy hc hw

theorem orientablePairing_normalForm_aux_reach_homeomorph
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hr : Relation.ReflTransGen orientablePairing_normalForm_aux_Step w w') :
    Nonempty (PolygonMoves.PolygonSurface w ≃ₜ PolygonMoves.PolygonSurface w') := by
  induction hr with
  | refl => exact ⟨Homeomorph.refl _⟩
  | tail _ hs ih =>
      exact ⟨ih.some.trans (orientablePairing_normalForm_aux_step_homeomorph hs).some⟩

/-- The standard word `a₀ b₀ a₀⁻¹ b₀⁻¹ ⋯` with `aⱼ = 2j`, `bⱼ = 2j + 1`. -/
def orientablePairing_normalForm_aux_standardWord (h : ℕ) :
    List (PolygonMoves.Signed ℕ) :=
  (List.range h).flatMap fun j =>
    [(2 * j, true), (2 * j + 1, true), (2 * j, false), (2 * j + 1, false)]

theorem orientablePairing_normalForm_aux_normalize_aux_uniqueMate
    (w : List (PolygonMoves.Signed ℕ)) (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (i : Fin w.length) :
    ∃! j : Fin w.length,
      j ≠ i ∧ (w.get j).1 = (w.get i).1 ∧ (w.get j).2 ≠ (w.get i).2 := by
  let S : Finset (Fin w.length) :=
    Finset.univ.filter fun j => (w.get j).1 = (w.get i).1
  have hmem : i ∈ S := by simp [S]
  have hcard : S.card = 2 := by
    have hc := hw.2.2 (w.get i).1 (by
      apply List.mem_map.mpr
      exact ⟨w.get i, List.get_mem w i, rfl⟩)
    have hof := orientablePairing_normalForm_aux_natWord_isPolygonWord_aux_count_ofFn
      (fun j : Fin w.length => (w.get j).1) (w.get i).1
    rw [← hof]
    simpa [List.map_eq_map] using hc
  have herase : (S.erase i).card = 1 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  obtain ⟨j, hjS⟩ := Finset.card_eq_one.mp herase
  have hjmem : j ∈ S.erase i := by simp [hjS]
  have hji : j ≠ i := by exact (Finset.mem_erase.mp hjmem).1
  have hjlabel : (w.get j).1 = (w.get i).1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hjmem)).2
  refine ⟨j, ⟨hji, hjlabel, hor j i hji hjlabel⟩, ?_⟩
  intro k hk
  have hkmem : k ∈ S.erase i := Finset.mem_erase.mpr ⟨hk.1, by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.2.1⟩⟩
  simpa [hjS] using hkmem

/-- **Leaf (interlocking).**  In an orientable one-vertex word, the two arcs
`i < j` of a label are separated by a third arc whose mate lies outside them.
Otherwise the arcs strictly between `i` and `j` pair among themselves, and,
since the signs of `i` and `j` differ, the corners `i+1, …, j` are closed under
`WordCornerRel` and miss corner `i`. -/
theorem orientablePairing_normalForm_aux_normalize_aux_interlock
    (w : List (PolygonMoves.Signed ℕ)) (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w)
    (i j : Fin w.length) (hij : i < j) (hlab : (w.get i).1 = (w.get j).1) :
    ∃ k l : Fin w.length, i < k ∧ k < j ∧ (j < l ∨ l < i) ∧
      (w.get k).1 = (w.get l).1 := by
  sorry

/-- **Leaf.**  Every `Step` keeps the word a polygon word: rotation and
relabelling (by an equivalence) permute the label counts, and `cutPaste`
trades the pair `y, y⁻¹` for the fresh pair `c⁻¹, c`. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w) : PolygonMoves.IsPolygonWord w' := by
  sorry

/-- **Leaf.**  Every `Step` keeps the word orientable: `flip` changes both arcs
of a label together, and `cutPaste` gives the new pair the signs `false, true`. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_orientable
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w) :
    orientablePairing_normalForm_aux_WordOrientable w' := by
  sorry

/-- **Leaf.**  Every `Step` keeps the word one-vertex.  Rotation shifts corners
and relabelling leaves `WordCornerRel` unchanged; for `cutPaste`, send each
corner of the new word to the corner of the old word at the same point of the
cut polygon (the corners at the ends of `c` go to the corners at the ends of `y`)
and check that each `WordCornerRel` step maps to a chain of old steps. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_oneVertex
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w) :
    orientablePairing_normalForm_aux_WordOneVertex w' := by
  sorry

theorem orientablePairing_normalForm_aux_normalize_aux_step_length
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w') : w'.length = w.length := by
  cases hs with
  | rotation u v hw => simp [Nat.add_comm]
  | relabel w e flip hw => simp
  | cutPaste α₁ α₂ β₁ β₂ y c hy hc hw => simp; omega

theorem orientablePairing_normalForm_aux_normalize_aux_standardWord_length (k : ℕ) :
    (orientablePairing_normalForm_aux_standardWord k).length = 4 * k := by
  induction k with
  | zero => simp [orientablePairing_normalForm_aux_standardWord]
  | succ k ih =>
      simp only [orientablePairing_normalForm_aux_standardWord, List.range_succ,
        List.flatMap_append, List.length_append] at ih ⊢
      simp [ih]; ring

/-- **Leaf (one commutator block).**  If the word is `k` standard blocks
followed by a tail `r` with labels `≥ 2k` and at least one more block's worth
of letters, then steps reach `k + 1` standard blocks followed by a tail with
labels `≥ 2k + 2`.  Route (Massey, ch. 1 §7): no label of the standard prefix
interlocks with a label of `r`, so `_aux_interlock` applied to the first arc of
`r` gives `x … y … x⁻¹ … y⁻¹` inside `r`; two `cutPaste` steps (with rotations
to place the pieces) give a block `c d c⁻¹ d⁻¹`; rotate it to sit after the
prefix and relabel `c ↦ 2k`, `d ↦ 2k + 1`, moving the tail's labels above
`2k + 1`.  Use `_aux_step_isPolygonWord` and the other `_aux_step_*` leaves to
carry the hypotheses through the intermediate words. -/
theorem orientablePairing_normalForm_aux_normalize_aux_block (k m : ℕ) (hm : 1 ≤ m)
    (r : List (PolygonMoves.Signed ℕ))
    (hw : PolygonMoves.IsPolygonWord (orientablePairing_normalForm_aux_standardWord k ++ r))
    (hor : orientablePairing_normalForm_aux_WordOrientable
      (orientablePairing_normalForm_aux_standardWord k ++ r))
    (hv : orientablePairing_normalForm_aux_WordOneVertex
      (orientablePairing_normalForm_aux_standardWord k ++ r))
    (hlen : (orientablePairing_normalForm_aux_standardWord k ++ r).length = 4 * (k + m))
    (hr : ∀ x ∈ r, 2 * k ≤ x.1) :
    ∃ r' : List (PolygonMoves.Signed ℕ),
      Relation.ReflTransGen orientablePairing_normalForm_aux_Step
        (orientablePairing_normalForm_aux_standardWord k ++ r)
        (orientablePairing_normalForm_aux_standardWord (k + 1) ++ r') ∧
      ∀ x ∈ r', 2 * (k + 1) ≤ x.1 := by
  sorry

/-- The hypotheses of `_aux_normalize` hold all along a chain of steps. -/
theorem orientablePairing_normalForm_aux_normalize_aux_reach_invariants
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hr : Relation.ReflTransGen orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w) :
    PolygonMoves.IsPolygonWord w' ∧ orientablePairing_normalForm_aux_WordOrientable w' ∧
      orientablePairing_normalForm_aux_WordOneVertex w' ∧ w'.length = w.length := by
  induction hr with
  | refl => exact ⟨hw, hor, hv, rfl⟩
  | tail _ hs ih =>
      obtain ⟨hw', hor', hv', hl⟩ := ih
      exact ⟨orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord hs hw',
        orientablePairing_normalForm_aux_normalize_aux_step_orientable hs hw' hor',
        orientablePairing_normalForm_aux_normalize_aux_step_oneVertex hs hw' hor' hv',
        (orientablePairing_normalForm_aux_normalize_aux_step_length hs).trans hl⟩

/-- **Combinatorial normalizer.**  Every orientable one-vertex polygon word of
length `4h` reaches the standard word: apply `_aux_block` `h` times, carrying
the hypotheses with `_aux_reach_invariants`; after `h` blocks the tail is
empty by length. -/
theorem orientablePairing_normalForm_aux_normalize (h : ℕ) (hh : 1 ≤ h)
    (w : List (PolygonMoves.Signed ℕ)) (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w)
    (hlen : w.length = 4 * h) :
    Relation.ReflTransGen orientablePairing_normalForm_aux_Step w
      (orientablePairing_normalForm_aux_standardWord h) := by
  have key : ∀ k ≤ h, ∃ r : List (PolygonMoves.Signed ℕ),
      Relation.ReflTransGen orientablePairing_normalForm_aux_Step w
        (orientablePairing_normalForm_aux_standardWord k ++ r) ∧
      ∀ x ∈ r, 2 * k ≤ x.1 := by
    intro k hk
    induction k with
    | zero => exact ⟨w, by
        simpa [orientablePairing_normalForm_aux_standardWord] using Relation.ReflTransGen.refl,
        fun x _ => by simp⟩
    | succ k ih =>
        obtain ⟨r, hreach, hr⟩ := ih (by omega)
        obtain ⟨hw', hor', hv', hl⟩ :=
          orientablePairing_normalForm_aux_normalize_aux_reach_invariants hreach hw hor hv
        obtain ⟨r', hreach', hr'⟩ :=
          orientablePairing_normalForm_aux_normalize_aux_block k (h - k) (by omega) r
            hw' hor' hv' (by rw [hl, hlen]; congr 1; omega) hr
        exact ⟨r', hreach.trans hreach', hr'⟩
  obtain ⟨r, hreach, -⟩ := key h le_rfl
  obtain ⟨-, -, -, hl⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_reach_invariants hreach hw hor hv
  have hr : r = [] := by
    rw [List.length_append, orientablePairing_normalForm_aux_normalize_aux_standardWord_length,
      hlen] at hl
    exact List.length_eq_zero_iff.mp (by omega)
  simpa [hr] using hreach

/-- **Leaf (standard word).**  The standard word presents `Surface true h`.
Either compare `WordRel` with `SurfaceRel true h` directly (the
`polygonNF_handle_eqvGen_iff` argument in `problems/t98A01/lean/Main.lean`,
about 150 lines), or go through `orientableStandardPairingData`, the bridge
`_aux_bridge`, `_aux_relabel` and `standardPairingData_space_homeomorph`. -/
@[simp] lemma orientablePairing_normalForm_aux_standard_aux_length (h : ℕ) :
    (orientablePairing_normalForm_aux_standardWord h).length = 4 * h := by
  simp [orientablePairing_normalForm_aux_standardWord, List.length_flatMap]
  omega

-- The `ℕ` label of a standard orbit: `aⱼ ↦ 2j`, `bⱼ ↦ 2j + 1`.
def orientablePairing_normalForm_aux_standard_aux_label (h : ℕ) (hh : 0 < h)
    (o : PairingOrbit (orientableStandardPairingData h hh).pair) : ℕ :=
  let p := orientableOrbitEquiv h o
  2 * p.1.1 + if p.2 then 1 else 0

theorem orientablePairing_normalForm_aux_standard_aux_label_injective (h : ℕ) (hh : 0 < h) :
    Function.Injective (orientablePairing_normalForm_aux_standard_aux_label h hh) := by
  intro a b hab
  apply (orientableOrbitEquiv h).injective
  simp only [orientablePairing_normalForm_aux_standard_aux_label] at hab
  generalize orientableOrbitEquiv h a = p at hab
  generalize orientableOrbitEquiv h b = q at hab
  rcases p with ⟨⟨p, hp⟩, s⟩
  rcases q with ⟨⟨q, hq⟩, r⟩
  cases s <;> cases r <;> simp at hab ⊢ <;> omega

theorem orientablePairing_normalForm_aux_standard_aux_get (h n : ℕ) (hn : n < (orientablePairing_normalForm_aux_standardWord h).length) :
    (orientablePairing_normalForm_aux_standardWord h)[n] =
      (2 * (n / 4) + ![0, 1, 0, 1] ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩,
        ![true, true, false, false] ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩) := by
  induction h with
  | zero => simp [orientablePairing_normalForm_aux_standardWord] at hn
  | succ h ih =>
    have hs : orientablePairing_normalForm_aux_standardWord (h + 1) =
        orientablePairing_normalForm_aux_standardWord h ++
          [(2 * h, true), (2 * h + 1, true), (2 * h, false), (2 * h + 1, false)] := by
      simp [orientablePairing_normalForm_aux_standardWord, List.range_succ,
        List.flatMap_append]
    have hl := orientablePairing_normalForm_aux_standard_aux_length h
    simp only [hs, List.getElem_append]
    split_ifs with hlt
    · exact ih hlt
    · have hn' : n < 4 * h + 4 := by
        have := orientablePairing_normalForm_aux_standard_aux_length (h + 1)
        omega
      have hq : n / 4 = h := by omega
      have : n - (orientablePairing_normalForm_aux_standardWord h).length = n % 4 := by omega
      simp only [this, hq]
      obtain h0 | h0 | h0 | h0 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      all_goals simp [h0]

theorem orientablePairing_normalForm_aux_standard_aux_wordEq (h : ℕ) (hh : 0 < h) :
    ((orientablePairing_normalForm_aux_wordOf (orientableStandardPairingData h hh)).map
        fun x => (orientablePairing_normalForm_aux_standard_aux_label h hh x.1, x.2)).map (fun x => (x.1, xor x.2 true)) =
      orientablePairing_normalForm_aux_standardWord h := by
  apply List.ext_getElem
  · simp only [List.length_map, orientablePairing_normalForm_aux_wordOf_length,
      orientablePairing_normalForm_aux_standard_aux_length]
    rfl
  · intro n h₁ h₂
    rw [orientablePairing_normalForm_aux_standard_aux_get h n h₂]
    simp only [List.getElem_map, orientablePairing_normalForm_aux_wordOf, List.getElem_ofFn]
    have hn : n < 4 * h := by
      rw [orientablePairing_normalForm_aux_standard_aux_length] at h₂
      exact h₂
    let i : Fin (4 * h) := ⟨n, hn⟩
    have hc1 : ((orientableCoord h i).1 : ℕ) = n / 4 := by
      simp [i, orientableCoord, Fin.coe_divNat]
    have hc2 : (orientableCoord h i).2 = ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ :=
      Fin.ext (by simp [i, orientableCoord, Fin.coe_modNat])
    change (2 * ((orientableCoord h i).1 : ℕ) +
        (if handleOrbitLabel (orientableCoord h i).2 then 1 else 0),
        xor (handleSign (orientableCoord h i).2) true) = _
    rw [hc1, hc2]
    obtain h0 | h0 | h0 | h0 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    all_goals simp [h0, handleOrbitLabel, handleSign]

open PolygonMoves in
theorem orientablePairing_normalForm_aux_standard (h : ℕ) (hh : 1 ≤ h) :
    Nonempty (PolygonMoves.PolygonSurface
      (orientablePairing_normalForm_aux_standardWord h) ≃ₜ Surface true h) := by
  have hh' : 0 < h := hh
  let P := orientableStandardPairingData h hh'
  obtain ⟨e₁⟩ := orientablePairing_normalForm_aux_bridge P
  obtain ⟨e₂⟩ := orientablePairing_normalForm_aux_relabel
    (orientablePairing_normalForm_aux_wordOf P) _ (orientablePairing_normalForm_aux_standard_aux_label_injective h hh')
  let w₁ := (orientablePairing_normalForm_aux_wordOf P).map
    fun x => (orientablePairing_normalForm_aux_standard_aux_label h hh' x.1, x.2)
  have hflip : WordRel (w₁.map fun x => (x.1, xor x.2 true)) = WordRel w₁ :=
    relabelInvert_aux_wordRel w₁ (Equiv.refl ℕ) (fun _ => true)
  have e₃ : PolygonSurface w₁ ≃ₜ PolygonSurface (w₁.map fun x => (x.1, xor x.2 true)) := by
    change Quotient (Relation.EqvGen.setoid (WordRel w₁)) ≃ₜ
      Quotient (Relation.EqvGen.setoid (WordRel (w₁.map fun x => (x.1, xor x.2 true))))
    rw [hflip]
    exact Homeomorph.refl _
  have e₀ : P.Space ≃ₜ Surface true h := standardPairingData_space_homeomorph true h hh'
  rw [← orientablePairing_normalForm_aux_standard_aux_wordEq h hh']
  exact ⟨(e₃.symm.trans (e₂.symm.trans e₁.symm)).trans e₀⟩

/-- **Orientable polygon-word normal form.**  Assembled from the leaves
above: bridge to the word of `P`, relabel into `ℕ`, normalize, compare with
the standard surface. -/
theorem orientablePairing_normalForm
    (h : ℕ) (hh : 1 ≤ h) (P : PairingData)
    (hor : IsOrientablePairing P) (hedges : P.edgeCount = 4 * h) :
    Nonempty (P.Space ≃ₜ Surface true h) := by
  obtain ⟨e₁⟩ := orientablePairing_normalForm_aux_bridge P
  obtain ⟨e₂⟩ := orientablePairing_normalForm_aux_relabel
    (orientablePairing_normalForm_aux_wordOf P) _
    (orientablePairing_normalForm_aux_enc_injective P)
  have hlen : (orientablePairing_normalForm_aux_natWord P).length = 4 * h := by
    simp [orientablePairing_normalForm_aux_natWord, hedges]
  obtain ⟨e₃⟩ := orientablePairing_normalForm_aux_reach_homeomorph
    (orientablePairing_normalForm_aux_normalize h hh _
      (orientablePairing_normalForm_aux_natWord_isPolygonWord P)
      (orientablePairing_normalForm_aux_natWord_orientable P hor)
      (orientablePairing_normalForm_aux_natWord_oneVertex P) hlen)
  obtain ⟨e₄⟩ := orientablePairing_normalForm_aux_standard h hh
  exact ⟨e₁.trans (e₂.trans (e₃.trans e₄))⟩


/-- A connected positive finite cover of a positive-genus standard orientable
surface is the standard orientable surface of genus `n * (g - 1) + 1`. -/
theorem connectedFiniteCover_homeomorph_standardSurface
    (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n) :
    Nonempty (E ≃ₜ Surface true (n * (g - 1) + 1)) := by
  obtain ⟨P, hor, hedges, hE⟩ :=
    standardCover_pairingData g n hg hn E p hp hsheets
  have hh : 1 ≤ n * (g - 1) + 1 := by omega
  obtain ⟨hP⟩ := orientablePairing_normalForm
    (n * (g - 1) + 1) hh P hor hedges
  exact ⟨hE.some.trans hP⟩

end ConstructionTargets.StandardSurfaceFiniteCover

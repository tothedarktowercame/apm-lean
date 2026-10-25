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

/-- **Leaf (one dual-tree glue).**  With at least two faces and a connected
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
  sorry

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

/-- **Leaf (one 1-skeleton contraction).**  A one-face complex with at least
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
  sorry

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

/-- **Leaf (read off the pairing).**  A one-face one-vertex complex is
`PairingData`: reindex `Σ f : Fin 1, Fin (sides f)` as `Fin (sides 0)` and
`Σ _ : Fin 1, Disk` as `Disk`.  `oneVertex` comes from `vertexCount = 1`:
corner classes generate the identifications of `polygonVertex`. -/
-- BEGIN SEAT AREA
theorem standardCover_pairingData_aux_toPairing
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : C.vertexCount = 1)
    (hor : C.IsOrientable) :
    ∃ P : PairingData, IsOrientablePairing P ∧ P.edgeCount = C.totalSides ∧
      Nonempty (C.Space ≃ₜ P.Space) := by
  sorry
-- END SEAT AREA

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
theorem orientablePairing_normalForm_aux_relabel {L L' : Type*}
    [DecidableEq L] [DecidableEq L'] (w : List (Signed L)) (f : L → L')
    (hf : Function.Injective f) :
    Nonempty (PolygonSurface w ≃ₜ PolygonSurface (w.map fun x => (f x.1, x.2))) := by
  sorry

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
theorem orientablePairing_normalForm_aux_natWord_isPolygonWord (P : PairingData) :
    PolygonMoves.IsPolygonWord (orientablePairing_normalForm_aux_natWord P) := by
  sorry

/-- **Leaf.**  From `IsOrientablePairing`: the two arcs with one label are
`i` and `P.pair i`, whose signs differ. -/
theorem orientablePairing_normalForm_aux_natWord_orientable (P : PairingData)
    (hor : IsOrientablePairing P) :
    orientablePairing_normalForm_aux_WordOrientable
      (orientablePairing_normalForm_aux_natWord P) := by
  sorry

/-- **Leaf (geometric to combinatorial vertex).**  From `P.oneVertex`.  A
`boundaryRel` step that starts at a polygon vertex ends at a polygon vertex
(an edge parameter `0` or `1` goes to `0` or `1`), and two arcs related at
their endpoints have corner-related corners.  So the set of disk points that
are corners corner-related to corner `a` is closed under `boundaryRel` in both
directions, which turns the `EqvGen` chain of `oneVertex` into a
`WordCornerRel` chain.  Needs: `edgePoint` is injective on the boundary away
from the identification `edgePoint n i 1 = edgePoint n (i+1) 0`. -/
theorem orientablePairing_normalForm_aux_natWord_oneVertex (P : PairingData) :
    orientablePairing_normalForm_aux_WordOneVertex
      (orientablePairing_normalForm_aux_natWord P) := by
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
  sorry

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

/-- **Leaf (combinatorial normalizer).**  Every orientable one-vertex polygon
word of length `4h` reaches the standard word.  Route (Massey, ch. 1 §7): in
an orientable one-vertex word every pair `x … x⁻¹` is interlocked with some
pair `y … y⁻¹` (otherwise the corners between the two `x` arcs form a
separate vertex); two `cutPaste` steps turn `x … y … x⁻¹ … y⁻¹` into a
commutator block `c d c⁻¹ d⁻¹` followed by the rest, and `cutPaste`
preserves length, orientability and one-vertexness.  Measure: the number of
standard commutator blocks at the front.  Split this into one lemma per step
(interlocked pair exists; two cut-pastes produce a block; invariants are
preserved) plus well-founded induction, if it does not close in one seat. -/
theorem orientablePairing_normalForm_aux_normalize (h : ℕ) (hh : 1 ≤ h)
    (w : List (PolygonMoves.Signed ℕ)) (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w)
    (hlen : w.length = 4 * h) :
    Relation.ReflTransGen orientablePairing_normalForm_aux_Step w
      (orientablePairing_normalForm_aux_standardWord h) := by
  sorry

/-- **Leaf (standard word).**  The standard word presents `Surface true h`.
Either compare `WordRel` with `SurfaceRel true h` directly (the
`polygonNF_handle_eqvGen_iff` argument in `problems/t98A01/lean/Main.lean`,
about 150 lines), or go through `orientableStandardPairingData`, the bridge
`_aux_bridge`, `_aux_relabel` and `standardPairingData_space_homeomorph`. -/
theorem orientablePairing_normalForm_aux_standard (h : ℕ) (hh : 1 ≤ h) :
    Nonempty (PolygonMoves.PolygonSurface
      (orientablePairing_normalForm_aux_standardWord h) ≃ₜ Surface true h) := by
  sorry

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

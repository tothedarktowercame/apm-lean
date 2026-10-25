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
  letI : ContractibleSpace Disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : LocPathConnectedSpace Disk :=
    (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace
  let q : C(Disk, Surface true g) :=
    ⟨surfaceQuotient true g, continuous_surfaceQuotient true g⟩
  obtain ⟨L, hL, huniq⟩ := hp.existsUnique_continuousMap_lifts q
    standardCover_pairingData_aux_lift_aux_center e he
  refine ⟨L, ⟨hL.2, hL.1⟩, ?_⟩
  intro L' hL'
  exact huniq L' ⟨hL'.2, hL'.1⟩

/-! Split of `_aux_sidePairing` (claude-14, 2026-10-25, after the lemma-1
PARTIAL that banked `_aux_continuousEdge`).  Side `k` and side `basePair k`
(reversed) are one `SurfaceRel` step apart (`_aux_edgeRel`), so the two
lifted edge paths lift the same path and agree once they agree at `0`.  The
face on the other side exists by `_aux_fibre`; the involution comes from
`_aux_homeomorph_aux_lift_injective`, moved here from the homeomorph split. -/

theorem standardCover_pairingData_aux_lift_aux_sidePairing_aux_continuousEdge
    (m e : ℕ) : Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦ edgePoint m e t) := by
  apply Continuous.subtype_mk
  change Continuous fun t : Set.Icc (0 : ℝ) 1 ↦
    Complex.exp (Complex.I * (2 * Real.pi * ((e : ℝ) + t.1) / m))
  fun_prop

/-- Side `k` at `t` and side `basePair k` at `1 - t` are the same point of the
surface (one `SurfaceRel` step, read backwards when `k % 4 ≥ 2`). -/
theorem standardCover_pairingData_aux_lift_aux_sidePairing_aux_edgeRel (g : ℕ)
    (k : Fin (4 * g)) (t : Set.Icc (0 : ℝ) 1) :
    surfaceQuotient true g (edgePoint (4 * g) k t) =
      surfaceQuotient true g (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)) := by
  have step : ∀ j : ℕ, j < g → ∀ r : ℕ, r < 2 → ∀ s : Set.Icc (0 : ℝ) 1,
      surfaceQuotient true g (edgePoint (4 * g) (4 * j + r) s) =
        surfaceQuotient true g (edgePoint (4 * g) (4 * j + r + 2) (reverseIcc s)) := by
    intro j hj r hr s
    apply Quotient.sound
    apply Relation.EqvGen.rel
    rw [SurfaceRel, if_pos rfl]
    refine ⟨j, hj, s, ?_⟩
    interval_cases r
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨k, hk⟩ := k
  simp only [standardCover_pairingData_aux_lift_aux_basePair]
  split_ifs with h
  · have := step (k / 4) (by omega) (k % 4) h t
    rwa [show 4 * (k / 4) + k % 4 = k by omega] at this
  · have := step (k / 4) (by omega) (k % 4 - 2) (by omega) (reverseIcc t)
    rw [reverseIcc_reverseIcc, show 4 * (k / 4) + (k % 4 - 2) = k - 2 by omega,
      show k - 2 + 2 = k by omega] at this
    exact this.symm

/-- Leaf: over every point `x` of the disk, the lifted disks fill the fibre.
The points `L i x` are pairwise distinct (`_aux_homeomorph_aux_lift_injective`)
and lie over `surfaceQuotient true g x`.  If `n > 0`, `hsheets` makes that
fibre finite with `n` points, so they fill it.  If `n = 0`, `hfib` makes the
fibre over the centre empty; lifting a path in the base from
`surfaceQuotient true g x` to the image of the centre, starting at `e`, gives
a point of that fibre, a contradiction. -/
theorem standardCover_pairingData_aux_lift_aux_sidePairing_aux_fibre
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e)
    (x : Disk) (e : E) (he : p e = surfaceQuotient true g x) : ∃ j, L j x = e := by
  letI : ContractibleSpace Disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : LocPathConnectedSpace Disk :=
    (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace
  let q : C(Disk, Surface true g) :=
    ⟨surfaceQuotient true g, continuous_surfaceQuotient true g⟩
  obtain ⟨K, hK, -⟩ := hp.existsUnique_continuousMap_lifts q x e he
  obtain ⟨j, hj, -⟩ := hfib
    (K standardCover_pairingData_aux_lift_aux_center)
    (by rw [← Function.comp_apply (f := p), hK.2]; rfl)
  refine ⟨j, ?_⟩
  have hLK : (L j : Disk → E) = K :=
    hp.eq_of_comp_eq (L j).continuous K.continuous
      (by rw [hL]; exact hK.2.symm) _ hj
  rw [hLK, hK.1]

/-- Two lifted disks that meet at the same point of the disk are the
same face.  `L i` and `L j` both lift `surfaceQuotient true g` through `p`
and agree at `x`; the disk is connected, so they agree everywhere
(`IsCoveringMap.eq_of_comp_eq`), in particular at the centre, and the
uniqueness in `hfib` gives `i = j`. -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_lift_injective
    (g n : ℕ)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e)
    (x : Disk) (i j : Fin n) (h : L i x = L j x) : i = j := by
  letI : ContractibleSpace Disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  have hij : (L i : Disk → E) = L j :=
    hp.eq_of_comp_eq (L i).continuous (L j).continuous (by rw [hL, hL]) x h
  obtain ⟨k, -, hk⟩ := hfib (L j standardCover_pairingData_aux_lift_aux_center)
    (by rw [← Function.comp_apply (f := p), hL])
  exact (hk i (congrFun hij _)).trans (hk j rfl).symm

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
  have hrev : Continuous reverseIcc :=
    Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  have hpath : ∀ i (k : Fin (4 * g)), ∃ j, ∀ t, L i (edgePoint (4 * g) k t) =
      L j (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)) := by
    intro i k
    obtain ⟨j, hj⟩ := standardCover_pairingData_aux_lift_aux_sidePairing_aux_fibre
      g n hg E p hp hsheets L hL hfib
      (edgePoint (4 * g) (standardCover_pairingData_aux_lift_aux_basePair g k)
        (reverseIcc t0))
      (L i (edgePoint (4 * g) k t0))
      (by rw [← Function.comp_apply (f := p), hL,
        standardCover_pairingData_aux_lift_aux_sidePairing_aux_edgeRel])
    refine ⟨j, fun t => ?_⟩
    have h := hp.eq_of_comp_eq
      (g₁ := fun t => L i (edgePoint (4 * g) k t))
      (g₂ := fun t => L j (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)))
      ((L i).continuous.comp
        (standardCover_pairingData_aux_lift_aux_sidePairing_aux_continuousEdge _ _))
      ((L j).continuous.comp
        ((standardCover_pairingData_aux_lift_aux_sidePairing_aux_continuousEdge _ _).comp
          hrev))
      (by
        funext s
        change (p ∘ L i) _ = (p ∘ L j) _
        rw [hL, hL]
        exact standardCover_pairingData_aux_lift_aux_sidePairing_aux_edgeRel g k s)
      t0 hj.symm
    exact congrFun h t
  choose σ hσ using hpath
  refine ⟨σ, fun i k => ?_, hσ⟩
  have h2 := hσ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k)
    (reverseIcc t0)
  rw [reverseIcc_reverseIcc, standardCover_pairingData_aux_lift_aux_basePair_basePair] at h2
  exact standardCover_pairingData_aux_lift_aux_homeomorph_aux_lift_injective g n E p hp L hL
    hfib (edgePoint (4 * g) k t0) _ _ (h2.symm.trans (hσ i k t0).symm)

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

/-- Banked by lemma-3 (2026-10-24): the lifts form one continuous map on the
disjoint union of the disks. -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_piecewise_continuous
    (n : ℕ) (E : Type*) [TopologicalSpace E]
    (L : Fin n → C(Disk, E)) :
    Continuous (fun z : Σ _ : Fin n, Disk => L z.1 z.2) := by
  apply continuous_sigma
  intro i
  exact (L i).continuous

/-- Leaf: a cover of `Surface true g` is Hausdorff.  The base is Hausdorff:
it is homeomorphic to `(standardPairingData true g _).Space`
(`standardPairingData_space_homeomorph`), which is Hausdorff by
`PairingData.spaceT2`.  Two points of one fibre lie in disjoint sheets of a
trivialization; points of different fibres lie in preimages of disjoint
open sets. -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_t2
    (g : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p) :
    T2Space E := by
  let P := standardPairingData true g hg
  letI : T2Space P.Space := P.spaceT2
  let h : P.Space ≃ₜ Surface true g :=
    standardPairingData_space_homeomorph true g hg
  letI : T2Space (Surface true g) := h.t2Space
  refine ⟨fun x y hxy ↦ ?_⟩
  by_cases hxy' : p x = p y
  · exact hp.isSeparatedMap x y hxy' hxy
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hxy'
    refine ⟨p ⁻¹' u, p ⁻¹' v, hu.preimage hp.continuous, hv.preimage hp.continuous,
      hxu, hyv, ?_⟩
    exact huv.preimage _

/-- Every point of `E` lies on a lifted disk: write `p e` as the image of a
point of the disk and apply `_aux_sidePairing_aux_fibre`. -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_surjective
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (hsheets : ∀ b, Nat.card {e : E // p e = b} = n)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e)
    (e : E) : ∃ i x, L i x = e := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep (p e)
  obtain ⟨j, hj⟩ := standardCover_pairingData_aux_lift_aux_sidePairing_aux_fibre
    g n hg E p hp hsheets L hL hfib x e hx.symm
  exact ⟨j, x, hj⟩

/-- Leaf: chains of the base relation lift to chains of the lifted complex,
from any face.  A `SurfaceRel true g` step joins side `k = 4j` (or `4j + 1`)
at `t` to side `basePair k` at `1 - t`; from face `i` it is the `Rel` step
along side `⟨i, k⟩` to face `σ i k`, and the reverse step from face `i` runs
along side `⟨i, basePair k⟩` to face `σ i (basePair k)`.  Since every step
lifts in both directions from every face, induction over the symmetric
reflexive-transitive closure gives the chain (the `symm` case of a direct
induction on `EqvGen` does not go through: the face reached is not
controlled). -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_baseChain
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    {x y : Disk} (h : Relation.EqvGen (SurfaceRel true g) x y) (i : Fin n) :
    ∃ j, Relation.EqvGen (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Rel
      ⟨i, x⟩ ⟨j, y⟩ := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  have lift : ∀ {a b : Disk}, Relation.EqvGen (SurfaceRel true g) a b →
      ((∀ i : Fin n, ∃ j, Relation.EqvGen C.Rel ⟨i, a⟩ ⟨j, b⟩) ∧
       (∀ j : Fin n, ∃ i, Relation.EqvGen C.Rel ⟨i, a⟩ ⟨j, b⟩)) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        simp only [SurfaceRel, if_true] at hab
        rcases hab with ⟨q, hq, t, hab | hab⟩
        · rcases hab with ⟨rfl, rfl⟩
          constructor
          · intro i
            refine ⟨σ i ⟨4 * q, by omega⟩, Relation.EqvGen.rel _ _ ?_⟩
            dsimp [C, PolygonComplex.Rel,
              standardCover_pairingData_aux_lift_aux_complex]
            refine ⟨⟨i, ⟨4 * q, by change 4 * q < 4 * g; omega⟩⟩, t, rfl, ?_⟩
            simp [C, PolygonComplex.pairedParameter,
              standardCover_pairingData_aux_lift_aux_complex,
              standardCover_pairingData_aux_lift_aux_basePair,
              standardCover_pairingData_aux_lift_aux_baseSign, reverseIcc]
          · intro j
            let k : Fin (4 * g) := ⟨4 * q + 2, by omega⟩
            refine ⟨σ j k, Relation.EqvGen.rel _ _ ?_⟩
            dsimp [C, PolygonComplex.Rel,
              standardCover_pairingData_aux_lift_aux_complex]
            refine ⟨⟨σ j k, ⟨4 * q, by change 4 * q < 4 * g; omega⟩⟩, t, rfl, ?_⟩
            simp [C, k, PolygonComplex.pairedParameter,
              standardCover_pairingData_aux_lift_aux_complex,
              standardCover_pairingData_aux_lift_aux_basePair,
              standardCover_pairingData_aux_lift_aux_baseSign, reverseIcc] 
            symm
            convert hσ j k using 1
            apply Fin.ext
            simp [k, standardCover_pairingData_aux_lift_aux_basePair]
        · rcases hab with ⟨rfl, rfl⟩
          constructor
          · intro i
            refine ⟨σ i ⟨4 * q + 1, by omega⟩, Relation.EqvGen.rel _ _ ?_⟩
            dsimp [C, PolygonComplex.Rel,
              standardCover_pairingData_aux_lift_aux_complex]
            refine ⟨⟨i, ⟨4 * q + 1, by change 4 * q + 1 < 4 * g; omega⟩⟩, t, rfl, ?_⟩
            have hm : (4 * q + 3) % 4 = 3 := by omega
            simp [C, PolygonComplex.pairedParameter,
              standardCover_pairingData_aux_lift_aux_complex,
              standardCover_pairingData_aux_lift_aux_basePair,
              standardCover_pairingData_aux_lift_aux_baseSign, reverseIcc, hm]
          · intro j
            let k : Fin (4 * g) := ⟨4 * q + 3, by omega⟩
            refine ⟨σ j k, Relation.EqvGen.rel _ _ ?_⟩
            dsimp [C, PolygonComplex.Rel,
              standardCover_pairingData_aux_lift_aux_complex]
            refine ⟨⟨σ j k, ⟨4 * q + 1, by change 4 * q + 1 < 4 * g; omega⟩⟩, t, rfl, ?_⟩
            have hm : (4 * q + 3) % 4 = 3 := by omega
            simp [C, k, PolygonComplex.pairedParameter,
              standardCover_pairingData_aux_lift_aux_complex,
              standardCover_pairingData_aux_lift_aux_basePair,
              standardCover_pairingData_aux_lift_aux_baseSign, reverseIcc, hm]
            symm
            convert hσ j k using 1
            apply Fin.ext
            simp [k, standardCover_pairingData_aux_lift_aux_basePair]
    | refl a =>
        exact ⟨fun i => ⟨i, .refl _⟩, fun i => ⟨i, .refl _⟩⟩
    | symm a b _ ih =>
        exact ⟨fun i => by
          obtain ⟨j, hj⟩ := ih.2 i
          exact ⟨j, hj.symm⟩,
          fun j => by
            obtain ⟨i, hi⟩ := ih.1 j
            exact ⟨i, hi.symm⟩⟩
    | trans a b c _ _ ih₁ ih₂ =>
        constructor
        · intro i
          obtain ⟨j, hij⟩ := ih₁.1 i
          obtain ⟨k, hjk⟩ := ih₂.1 j
          exact ⟨k, Relation.EqvGen.trans _ _ _ hij hjk⟩
        · intro k
          obtain ⟨j, hjk⟩ := ih₂.2 k
          obtain ⟨i, hij⟩ := ih₁.2 j
          exact ⟨i, Relation.EqvGen.trans _ _ _ hij hjk⟩
  exact (lift h).1 i

/-- One gluing step of the lifted complex joins equal points of `E`
(`hside`, with the parameter reversed because paired sides carry opposite
signs). -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_descends
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (L : Fin n → C(Disk, E))
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (hside : ∀ i (k : Fin (4 * g)) t, L i (edgePoint (4 * g) k t) =
      L (σ i k) (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)))
    {a b : Σ _ : Fin n, Disk}
    (h : Relation.EqvGen (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Rel a b) :
    L a.1 a.2 = L b.1 b.2 := by
  induction h with
  | rel a b hab =>
    obtain ⟨s, t, rfl, rfl⟩ := hab
    have hsign : standardCover_pairingData_aux_lift_aux_baseSign g s.2 ≠
        standardCover_pairingData_aux_lift_aux_baseSign g
          (standardCover_pairingData_aux_lift_aux_basePair g s.2) :=
      (standardCover_pairingData_aux_lift_aux_baseSign_basePair g s.2).symm
    dsimp only [PolygonComplex.pairedParameter, standardCover_pairingData_aux_lift_aux_complex,
      Function.Involutive.toPerm, Equiv.coe_fn_mk]
    rw [if_neg hsign]
    exact hside s.1 s.2 t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The lifts make exactly the identifications of the lifted complex. -/
theorem standardCover_pairingData_aux_lift_aux_homeomorph_aux_identifies
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (p : E → Surface true g) (hp : IsCoveringMap p)
    (L : Fin n → C(Disk, E)) (hL : ∀ i, p ∘ L i = surfaceQuotient true g)
    (hfib : ∀ e, p e = surfaceQuotient true g standardCover_pairingData_aux_lift_aux_center →
      ∃! i, L i standardCover_pairingData_aux_lift_aux_center = e)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (hside : ∀ i (k : Fin (4 * g)) t, L i (edgePoint (4 * g) k t) =
      L (σ i k) (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)))
    (a b : Σ _ : Fin n, Disk) (h : L a.1 a.2 = L b.1 b.2) :
    Relation.EqvGen (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Rel a b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  have hq : surfaceQuotient true g x = surfaceQuotient true g y := by
    have hx := congrFun (hL i) x
    have hy := congrFun (hL j) y
    simp only [Function.comp] at hx hy
    rw [← hx, ← hy, h]
  obtain ⟨j', hj'⟩ :=
    standardCover_pairingData_aux_lift_aux_homeomorph_aux_baseChain g n hg σ hσ
      (Quotient.exact hq) i
  have hd := standardCover_pairingData_aux_lift_aux_homeomorph_aux_descends
    g n hg E L σ hσ hside hj'
  have : j' = j :=
    standardCover_pairingData_aux_lift_aux_homeomorph_aux_lift_injective g n E p hp L hL hfib
      y j' j (hd.symm.trans h)
  subst this
  exact hj'

/-- The lifts assemble to a homeomorphism.  The map `⟨i, x⟩ ↦ L i x`
descends to `C.Space` (`_aux_descends`), is injective there
(`_aux_identifies`) and onto (`_aux_surjective`); `C.Space` is compact and
`E` is Hausdorff (`_aux_t2`), so the continuous bijection is a
homeomorphism. -/
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
  set C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  letI : T2Space E := standardCover_pairingData_aux_lift_aux_homeomorph_aux_t2 g hg E p hp
  let Φ : C.Space → E := Quotient.lift (fun z : Σ _ : Fin n, Disk => L z.1 z.2)
    (fun a b h => standardCover_pairingData_aux_lift_aux_homeomorph_aux_descends
      g n hg E L σ hσ hside h)
  have hΦ : Continuous Φ := by
    rw [continuous_coinduced_dom]
    exact standardCover_pairingData_aux_lift_aux_homeomorph_aux_piecewise_continuous n E L
  have hinj : Function.Injective Φ := by
    intro a b hab
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound
      (standardCover_pairingData_aux_lift_aux_homeomorph_aux_identifies g n hg E p hp L hL hfib
        σ hσ hside _ _ hab)
  have hsurj : Function.Surjective Φ := by
    intro e
    obtain ⟨i, x, hx⟩ := standardCover_pairingData_aux_lift_aux_homeomorph_aux_surjective
      g n hg E p hp hsheets L hL hfib e
    exact ⟨Quotient.mk _ ⟨i, x⟩, hx⟩
  haveI : CompactSpace (Σ _ : Fin n, Disk) := by
    haveI : CompactSpace Disk :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
    infer_instance
  haveI : CompactSpace C.Space :=
    Quotient.compactSpace (s := Relation.EqvGen.setoid C.Rel)
  exact ⟨(hΦ.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm⟩

/-- Leaf: a connected glued space has connected face-dual graph.  The faces
in one dual class form a union of glued disks that is closed and open in
`C.Space`, since every side of such a face is glued to a face of the same
class. -/
theorem standardCover_pairingData_aux_lift_aux_dualConnected_aux_rel
    (C : PolygonComplex) {x y : Σ _ : Fin C.faceCount, Disk} (h : C.Rel x y) :
    ∃ s : C.Side, s.1 = x.1 ∧ (C.pair s).1 = y.1 := by
  obtain ⟨s, t, rfl, rfl⟩ := h
  exact ⟨s, rfl, rfl⟩

theorem standardCover_pairingData_aux_lift_aux_dualConnected_aux_eqv
    (C : PolygonComplex) {x y : Σ _ : Fin C.faceCount, Disk}
    (h : Relation.EqvGen C.Rel x y) :
    Relation.EqvGen
      (fun a b => ∃ s : C.Side, s.1 = a ∧ (C.pair s).1 = b) x.1 y.1 := by
  induction h with
  | rel x y h =>
      exact Relation.EqvGen.rel _ _
        (standardCover_pairingData_aux_lift_aux_dualConnected_aux_rel C h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem standardCover_pairingData_aux_lift_aux_dualConnected (C : PolygonComplex)
    [ConnectedSpace C.Space] : C.DualConnected := by
  intro f f'
  let R : Fin C.faceCount → Fin C.faceCount → Prop :=
    fun a b => ∃ s : C.Side, s.1 = a ∧ (C.pair s).1 = b
  let A : Set (Fin C.faceCount) := {a | Relation.EqvGen R f a}
  let U : Set (Σ _ : Fin C.faceCount, Disk) := Sigma.fst ⁻¹' A
  let q : (Σ _ : Fin C.faceCount, Disk) → C.Space :=
    fun x => Quotient.mk (Relation.EqvGen.setoid C.Rel) x
  let S : Set C.Space := q '' U
  have hsat : q ⁻¹' S = U := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      change Relation.EqvGen R f x.1
      have hy' : Relation.EqvGen R f y.1 := hy
      have he : Relation.EqvGen C.Rel y x := Quotient.exact hxy
      exact Relation.EqvGen.trans _ _ _ hy'
        (standardCover_pairingData_aux_lift_aux_dualConnected_aux_eqv C he)
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hUopen : IsOpen U := by
    exact isOpen_sigma_fst_preimage A
  have hUclosed : IsClosed U := by
    rw [← isOpen_compl_iff]
    have h : IsOpen (Sigma.fst ⁻¹' (Aᶜ) :
        Set (Σ _ : Fin C.faceCount, Disk)) :=
      isOpen_sigma_fst_preimage (Aᶜ)
    convert h using 1 <;> ext x <;> simp [U]
  have hSopen : IsOpen S := by
    change IsOpen (q ⁻¹' S)
    rw [hsat]
    exact hUopen
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    change IsOpen (q ⁻¹' Sᶜ)
    rw [preimage_compl, hsat]
    exact hUclosed.isOpen_compl
  have hSne : S.Nonempty := by
    let x : Σ _ : Fin C.faceCount, Disk :=
      ⟨f, standardCover_pairingData_aux_lift_aux_center⟩
    exact ⟨q x, x, Relation.EqvGen.refl _, rfl⟩
  have hSuniv : S = Set.univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSne
  let x : Σ _ : Fin C.faceCount, Disk :=
    ⟨f', standardCover_pairingData_aux_lift_aux_center⟩
  have hxS : q x ∈ S := by rw [hSuniv]; trivial
  have hxpre : x ∈ q ⁻¹' S := hxS
  rw [hsat] at hxpre
  exact hxpre

/-! Split of `_aux_vertexCount` (claude-14, 2026-10-25, after the lemma-3
PARTIAL).  No fibre count is needed: `i ↦ [⟨i, 0⟩]` is a bijection
`Fin n → Vertex`.  It is onto because every corner is joined to a corner at
position `0` (`_aux_step`, `_aux_chain`), and one-to-one because
`L i (edgePoint (4g) k 0)` is constant on corner classes (`_aux_respect`)
and lifted disks meeting at one point are the same face
(`_aux_homeomorph_aux_lift_injective`). -/

/-- Leaf (banked by lemma-3, 2026-10-25): one corner step from any side,
`s ~ nextCorner (pair s)`, since every pairing reverses the parameter. -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (s : (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Side) :
    Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel s
      ((standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).nextCorner
        ((standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).pair s)) := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  change Relation.EqvGen C.CornerRel s (C.nextCorner (C.pair s))
  apply Relation.EqvGen.rel
  refine ⟨s, ?_⟩
  have hs : C.sign s ≠ C.sign (C.pair s) := by
    rcases s with ⟨j, e⟩
    exact (standardCover_pairingData_aux_lift_aux_baseSign_basePair g e).symm
  rw [if_neg hs]
  exact Or.inl ⟨rfl, rfl⟩

/-- Leaf: `_aux_step` when `k % 4 = 0`: three `_aux_corner` steps from `s = ⟨i, k⟩`. -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod0
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (i : Fin n) (k : Fin (4 * g))
    (hk : k.1 % 4 = 0) :
    ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  let a := C.nextCorner (C.pair (⟨i, k⟩ : C.Side))
  let b := C.nextCorner (C.pair a)
  let c := C.nextCorner (C.pair b)
  refine ⟨c.1, Relation.EqvGen.trans _ _ _
    (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
      g n hg σ hσ ⟨i, k⟩)
    (Relation.EqvGen.trans _ _ _
      (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
        g n hg σ hσ a)
      (Relation.EqvGen.trans _ _ _
        (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
          g n hg σ hσ b) ?_))⟩
  have ha : a.2.1 = k.1 + 3 := by
    show ((standardCover_pairingData_aux_lift_aux_basePair g k).1 + 1) % (4 * g) = k.1 + 3
    have := k.2
    simp only [standardCover_pairingData_aux_lift_aux_basePair]
    split <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  have hb : b.2.1 = k.1 + 2 := by
    show ((standardCover_pairingData_aux_lift_aux_basePair g a.2).1 + 1) % (4 * g) = k.1 + 2
    have := k.2
    simp only [standardCover_pairingData_aux_lift_aux_basePair, ha]
    split <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  have hc : c.2.1 = (k.1 + 1) % (4 * g) := by
    show ((standardCover_pairingData_aux_lift_aux_basePair g b.2).1 + 1) % (4 * g) = _
    simp only [standardCover_pairingData_aux_lift_aux_basePair, hb]
    split
    · omega
    · rw [show k.1 + 2 - 2 + 1 = k.1 + 1 by omega]
  have heq : c =
      ⟨c.1, ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ :=
    Sigma.ext rfl (heq_of_eq (Fin.ext hc))
  change Relation.EqvGen C.CornerRel c _
  rw [heq]
  exact Relation.EqvGen.refl _

/-- Leaf: `_aux_step` when `k % 4 = 1`: one `_aux_corner` step backwards from `s = ⟨i, k - 1⟩`. -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod1
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (i : Fin n) (k : Fin (4 * g))
    (hk : k.1 % 4 = 1) :
    ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  let e : Fin (4 * g) := ⟨k.1 - 1, by omega⟩
  let s : C.Side := ⟨i, e⟩
  refine ⟨(C.pair s).1, ?_⟩
  have heq : C.nextCorner (C.pair (C.pair s)) = ⟨i, k⟩ := by
    rw [C.pair_pair]
    apply Sigma.ext
    · rfl
    · simp only [C, standardCover_pairingData_aux_lift_aux_complex]
      apply heq_of_eq
      apply Fin.ext
      change ((e.1 + 1) % (4 * g)) = k.1
      have hev : e.1 + 1 = k.1 := by
        simp [e]
        omega
      rw [hev, Nat.mod_eq_of_lt k.2]
  have heq' : C.pair s =
      ⟨(C.pair s).1, ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ := by
    apply Sigma.ext
    · rfl
    · simp only [C, standardCover_pairingData_aux_lift_aux_complex]
      apply heq_of_eq
      apply Fin.ext
      change (standardCover_pairingData_aux_lift_aux_basePair g e).1 =
        (k.1 + 1) % (4 * g)
      have hklt : k.1 + 1 < 4 * g := by omega
      rw [Nat.mod_eq_of_lt hklt]
      have hemod : e.1 % 4 = 0 := by
        simp [e]
        omega
      simp [standardCover_pairingData_aux_lift_aux_basePair, hemod, e]
      omega
  rw [← heq]
  refine Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _
      (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
        g n hg σ hσ (C.pair s))) ?_
  rw [heq']
  exact Relation.EqvGen.refl _

/-- Leaf: `_aux_step` when `k % 4 = 2`: one `_aux_corner` step backwards from `s = ⟨σ i (basePair (k + 1)), k + 1⟩` (note `k + 1 < 4g`). -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod2
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (i : Fin n) (k : Fin (4 * g))
    (hk : k.1 % 4 = 2) :
    ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  have hk1 : k.1 + 1 < 4 * g := by omega
  let e : Fin (4 * g) := ⟨k.1 + 1, hk1⟩
  let j : Fin n := σ i (standardCover_pairingData_aux_lift_aux_basePair g e)
  let s : C.Side := ⟨j, e⟩
  refine ⟨j, ?_⟩
  have heq : C.nextCorner (C.pair s) = ⟨i, k⟩ := by
    apply Sigma.ext
    · change σ j e = i
      simpa [j, standardCover_pairingData_aux_lift_aux_basePair_basePair] using
        hσ i (standardCover_pairingData_aux_lift_aux_basePair g e)
    · apply heq_of_eq
      apply Fin.ext
      change
        ((standardCover_pairingData_aux_lift_aux_basePair g e).1 + 1) % (4 * g) = k.1
      have hemod : (k.1 + 1) % 4 = 3 := by omega
      simp [e, standardCover_pairingData_aux_lift_aux_basePair, hemod]
      rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt k.2]
  rw [← heq]
  simpa [s, e, Nat.mod_eq_of_lt hk1] using
    (Relation.EqvGen.symm _ _
      (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
        g n hg σ hσ s))

/-- Leaf: `_aux_step` when `k % 4 = 3`: three `_aux_corner` steps from `s = ⟨i, k⟩`. -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod3
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (i : Fin n) (k : Fin (4 * g))
    (hk : k.1 % 4 = 3) :
    ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  let a := C.nextCorner (C.pair (⟨i, k⟩ : C.Side))
  let b := C.nextCorner (C.pair a)
  let c := C.nextCorner (C.pair b)
  refine ⟨c.1, Relation.EqvGen.trans _ _ _
    (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
      g n hg σ hσ ⟨i, k⟩)
    (Relation.EqvGen.trans _ _ _
      (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
        g n hg σ hσ a)
      (Relation.EqvGen.trans _ _ _
        (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_corner
          g n hg σ hσ b) ?_))⟩
  have ha : a.2.1 = k.1 - 1 := by
    show ((standardCover_pairingData_aux_lift_aux_basePair g k).1 + 1) % (4 * g) = k.1 - 1
    have := k.2
    simp only [standardCover_pairingData_aux_lift_aux_basePair]
    split <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  have hb : b.2.1 = k.1 - 2 := by
    show ((standardCover_pairingData_aux_lift_aux_basePair g a.2).1 + 1) % (4 * g) = k.1 - 2
    have := k.2
    simp only [standardCover_pairingData_aux_lift_aux_basePair, ha]
    split <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  have hc : c.2.1 = (k.1 + 1) % (4 * g) := by
    show ((standardCover_pairingData_aux_lift_aux_basePair g b.2).1 + 1) % (4 * g) = _
    have := k.2
    simp only [standardCover_pairingData_aux_lift_aux_basePair, hb]
    split
    · rw [show k.1 - 2 + 2 + 1 = k.1 + 1 by omega]
    · omega
  have heq : c =
      ⟨c.1, ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ :=
    Sigma.ext rfl (heq_of_eq (Fin.ext hc))
  change Relation.EqvGen C.CornerRel c _
  rw [heq]
  exact Relation.EqvGen.refl _

/-- Leaf: in the lifted complex every corner `⟨i, k⟩` is joined to a corner
`⟨i', k + 1⟩` of some face.  In the base `4g`-gon the corner relation gives
`4j ~ 4j+3 ~ 4j+2 ~ 4j+1 ~ 4j+4` (indices mod `4g`); each step lifts to a
`CornerRel` step from any face, taking `s = ⟨i, k⟩` or `s = ⟨i, k - 1⟩`
(every pairing reverses the parameter, by `_aux_baseSign_basePair`). -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_step
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (i : Fin n) (k : Fin (4 * g)) :
    ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩ := by
  have hk : k.1 % 4 = 0 ∨ k.1 % 4 = 1 ∨ k.1 % 4 = 2 ∨ k.1 % 4 = 3 := by omega
  rcases hk with hk | hk | hk | hk
  · exact standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod0 g n hg σ hσ i k hk
  · exact standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod1 g n hg σ hσ i k hk
  · exact standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod2 g n hg σ hσ i k hk
  · exact standardCover_pairingData_aux_lift_aux_vertexCount_aux_step_aux_mod3 g n hg σ hσ i k hk

/-- Leaf: every corner is joined to a corner at position `0`.  Induction on
`m` from the step hypothesis gives a face `i'` with `⟨i, k⟩` joined to
`⟨i', (k + m) % 4g⟩`; take `m = 4g - k`. -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_chain
    (g n : ℕ) (hg : 1 ≤ g)
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (hstep : ∀ (i : Fin n) (k : Fin (4 * g)), ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨(k.1 + 1) % (4 * g), Nat.mod_lt _ (by omega)⟩⟩)
    (i : Fin n) (k : Fin (4 * g)) :
    ∃ i' : Fin n, Relation.EqvGen
      (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel
      ⟨i, k⟩ ⟨i', ⟨0, k.pos⟩⟩ := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  have h4 : 0 < 4 * g := by omega
  have hiter : ∀ (m : ℕ) (j : Fin n) (l : Fin (4 * g)),
      ∃ j' : Fin n, Relation.EqvGen C.CornerRel
        ⟨j, l⟩ ⟨j', ⟨(l.1 + m) % (4 * g), Nat.mod_lt _ h4⟩⟩ := by
    intro m
    induction m with
    | zero =>
        intro j l
        refine ⟨j, ?_⟩
        simpa only [Nat.add_zero, Nat.mod_eq_of_lt l.isLt] using
          (Relation.EqvGen.refl (r := C.CornerRel) ⟨j, l⟩)
    | succ m ih =>
        intro j l
        obtain ⟨j₁, hj₁⟩ := ih j l
        let l₁ : Fin (4 * g) :=
          ⟨(l.1 + m) % (4 * g), Nat.mod_lt _ h4⟩
        obtain ⟨j₂, hj₂⟩ := hstep j₁ l₁
        refine ⟨j₂, hj₁.trans _ _ _ ?_⟩
        convert hj₂ using 1
        congr 1
        apply Fin.ext
        dsimp [l₁]
        calc
          (l.1 + (m + 1)) % (4 * g) = (l.1 + m + 1) % (4 * g) := by
            congr 1 <;> omega
          _ = ((l.1 + m) % (4 * g) + 1) % (4 * g) :=
            (Nat.mod_add_mod _ _ _).symm
  obtain ⟨i', hi'⟩ := hiter (4 * g - k.1) i k
  refine ⟨i', ?_⟩
  convert hi' using 1
  congr 1
  apply Fin.ext
  simp

/-- Leaf: the corner `⟨i, k⟩` goes to `L i (edgePoint (4g) k 0)`, and one
`CornerRel` step preserves it.  The signs always differ, so the step is
`s ~ nextCorner (pair s)` or `nextCorner s ~ pair s`; both are `hside` at
`t = 0` or `t = 1`, with `edgePoint m k 1 = edgePoint m ((k + 1) % m) 0`
(`PolygonBoundaryVertexClasses.edgePoint_one_eq_succ_zero` and periodicity
of `Complex.exp`). -/
theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_respect_aux_next
    (m : ℕ) (hm : 0 < m) (k : Fin m) :
    edgePoint m ((k.1 + 1) % m)
        PolygonBoundaryVertexClasses.zeroIcc =
      edgePoint m k PolygonBoundaryVertexClasses.oneIcc := by
  rw [PolygonBoundaryVertexClasses.edgePoint_one_eq_succ_zero]
  by_cases hk : k.1 + 1 < m
  · rw [Nat.mod_eq_of_lt hk]
  · have heq : k.1 + 1 = m := by omega
    rw [heq, Nat.mod_self]
    simpa using (PolygonMoves.rotation_aux_edgePoint_period m 0 (by omega)
      PolygonBoundaryVertexClasses.zeroIcc).symm

theorem standardCover_pairingData_aux_lift_aux_vertexCount_aux_respect
    (g n : ℕ) (hg : 1 ≤ g)
    (E : Type*) [TopologicalSpace E]
    (L : Fin n → C(Disk, E))
    (σ : Fin n → Fin (4 * g) → Fin n)
    (hσ : ∀ i k, σ (σ i k) (standardCover_pairingData_aux_lift_aux_basePair g k) = i)
    (hside : ∀ i (k : Fin (4 * g)) t, L i (edgePoint (4 * g) k t) =
      L (σ i k) (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g k) (reverseIcc t)))
    (a b : (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).Side)
    (h : (standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ).CornerRel a b) :
    L a.1 (edgePoint (4 * g) a.2 ⟨0, by norm_num⟩) =
      L b.1 (edgePoint (4 * g) b.2 ⟨0, by norm_num⟩) := by
  let C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  obtain ⟨s, hs⟩ := h
  have hpair : C.pair s =
      ⟨σ s.1 s.2, standardCover_pairingData_aux_lift_aux_basePair g s.2⟩ := by
    rfl
  have hsign : C.sign s ≠ C.sign (C.pair s) := by
    exact (standardCover_pairingData_aux_lift_aux_baseSign_basePair g s.2).symm
  rw [if_neg hsign] at hs
  rcases hs with hs | hs
  · rcases hs with ⟨ha, hb⟩
    subst a
    subst b
    have hside0 := hside s.1 s.2 PolygonBoundaryVertexClasses.zeroIcc
    simp only [reverseIcc, PolygonBoundaryVertexClasses.zeroIcc,
      PolygonBoundaryVertexClasses.oneIcc, sub_zero] at hside0
    change L s.1 (edgePoint (4 * g) s.2 ⟨0, by norm_num⟩) =
      L (C.nextCorner (C.pair s)).1
        (edgePoint (4 * g) (C.nextCorner (C.pair s)).2 ⟨0, by norm_num⟩)
    rw [hpair]
    change L s.1 (edgePoint (4 * g) s.2 ⟨0, by norm_num⟩) =
      L (σ s.1 s.2) (edgePoint (4 * g)
        (((standardCover_pairingData_aux_lift_aux_basePair g s.2).1 + 1) % (4 * g))
        PolygonBoundaryVertexClasses.zeroIcc)
    rw [standardCover_pairingData_aux_lift_aux_vertexCount_aux_respect_aux_next
      (m := 4 * g) (hm := by omega)
      (k := standardCover_pairingData_aux_lift_aux_basePair g s.2)]
    exact hside0
  · rcases hs with ⟨ha, hb⟩
    subst a
    subst b
    have hside1 := hside s.1 s.2 PolygonBoundaryVertexClasses.oneIcc
    simp only [reverseIcc, PolygonBoundaryVertexClasses.zeroIcc,
      PolygonBoundaryVertexClasses.oneIcc, sub_self] at hside1
    change L (C.nextCorner s).1
        (edgePoint (4 * g) (C.nextCorner s).2 ⟨0, by norm_num⟩) =
      L (C.pair s).1 (edgePoint (4 * g) (C.pair s).2 ⟨0, by norm_num⟩)
    rw [hpair]
    change L s.1 (edgePoint (4 * g) ((s.2.1 + 1) % (4 * g))
        PolygonBoundaryVertexClasses.zeroIcc) =
      L (σ s.1 s.2) (edgePoint (4 * g)
        (standardCover_pairingData_aux_lift_aux_basePair g s.2)
        PolygonBoundaryVertexClasses.zeroIcc)
    rw [standardCover_pairingData_aux_lift_aux_vertexCount_aux_respect_aux_next
      (m := 4 * g) (hm := by omega) (k := s.2)]
    exact hside1

/-- The corner classes of the lifted complex correspond to the `n`
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
  set C := standardCover_pairingData_aux_lift_aux_complex g n hg σ hσ
  have h4 : 0 < 4 * g := by omega
  let φ : C.Side → E := fun a => L a.1 (edgePoint (4 * g) a.2 ⟨0, by norm_num⟩)
  have hφ : ∀ a b, Relation.EqvGen C.CornerRel a b → φ a = φ b := by
    intro a b h
    induction h with
    | rel a b hab =>
      exact standardCover_pairingData_aux_lift_aux_vertexCount_aux_respect
        g n hg E L σ hσ hside a b hab
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let f : Fin n → C.Vertex := fun i =>
    Quotient.mk (Relation.EqvGen.setoid C.CornerRel) ⟨i, ⟨0, h4⟩⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h := hφ _ _ (Quotient.exact hij)
    exact standardCover_pairingData_aux_lift_aux_homeomorph_aux_lift_injective
      g n E p hp L hL hfib _ i j h
  have hsurj : Function.Surjective f := by
    intro v
    induction v using Quotient.ind with
    | _ a =>
      obtain ⟨i, k⟩ := a
      obtain ⟨i', h⟩ := standardCover_pairingData_aux_lift_aux_vertexCount_aux_chain
        g n hg σ hσ
        (standardCover_pairingData_aux_lift_aux_vertexCount_aux_step g n hg σ hσ) i k
      exact ⟨i', (Quotient.sound h).symm⟩
  rw [PolygonComplex.vertexCount, ← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩,
    Nat.card_eq_fintype_card, Fintype.card_fin]

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

/-- **Leaf (cyclic enumeration).**  Starting just after side `i` of an
`a`-gon and walking once round, the `a - 1` steps hit every other side once. -/
theorem standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_cyclic
    (a : ℕ) (i : Fin a) :
    ∃ e : Fin (a - 1) ≃ {j : Fin a // j ≠ i},
      ∀ m, (e m).1.val = (i.val + 1 + m.val) % a := by
  let f : Fin (a - 1) → {j : Fin a // j ≠ i} := fun m =>
    ⟨⟨(i.val + 1 + m.val) % a, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩, by
      intro h
      have hval : (i.val + 1 + m.val) % a = i.val := congrArg Fin.val h
      by_cases hx : i.val + 1 + m.val < a
      · rw [Nat.mod_eq_of_lt hx] at hval
        omega
      · rw [Nat.mod_eq_sub_mod (le_of_not_gt hx),
          Nat.mod_eq_of_lt (by omega)] at hval
        omega⟩
  have hf : Function.Injective f := by
    intro m n h
    apply Fin.ext
    have hval : (i.val + 1 + m.val) % a = (i.val + 1 + n.val) % a :=
      congrArg (fun x => x.1.val) h
    by_cases hm : i.val + 1 + m.val < a
    · rw [Nat.mod_eq_of_lt hm] at hval
      by_cases hn : i.val + 1 + n.val < a
      · rw [Nat.mod_eq_of_lt hn] at hval
        omega
      · rw [Nat.mod_eq_sub_mod (le_of_not_gt hn),
          Nat.mod_eq_of_lt (by omega)] at hval
        omega
    · rw [Nat.mod_eq_sub_mod (le_of_not_gt hm),
        Nat.mod_eq_of_lt (by omega)] at hval
      by_cases hn : i.val + 1 + n.val < a
      · rw [Nat.mod_eq_of_lt hn] at hval
        omega
      · rw [Nat.mod_eq_sub_mod (le_of_not_gt hn),
          Nat.mod_eq_of_lt (by omega)] at hval
        omega
  have hcard : Fintype.card (Fin (a - 1)) =
      Fintype.card {j : Fin a // j ≠ i} := by
    rw [Fintype.card_fin]
    simpa using (Set.card_ne_eq i)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro m
  rfl

/-- **Leaf (sides of the merged complex).**  Given the faces of `C'` (all faces
of `C` but `(C.pair s).1`, with `merged` in place of `s.1`) and their side
counts, the sides of `C'` correspond to the sides of `C` other than `s` and
`C.pair s`: unmerged faces keep their sides, and the merged face walks round
`s.1` from just after `s`, then round `(C.pair s).1` from just after
`C.pair s`. -/
theorem standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_sideEquiv_aux_length
    (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (h : n + 2 = a + b) :
    n = (a - 1) + (b - 1) := by
  omega

theorem standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_sideEquiv
    (C : PolygonComplex) (s : C.Side) (hs : s.1 ≠ (C.pair s).1)
    {m : ℕ} (old : Fin m → Fin C.faceCount) (merged : Fin m)
    (sides' : Fin m → ℕ)
    (old_merged : old merged = s.1) (old_injective : Function.Injective old)
    (old_ne : ∀ k, old k ≠ (C.pair s).1)
    (old_surj : ∀ f, f ≠ (C.pair s).1 → ∃ k, old k = f)
    (sides_old : ∀ k, k ≠ merged → sides' k = C.sides (old k))
    (sides_merged : sides' merged + 2 = C.sides s.1 + C.sides (C.pair s).1) :
    ∃ e : (Σ k : Fin m, Fin (sides' k)) ≃ {u : C.Side // u ≠ s ∧ u ≠ C.pair s},
      (∀ t : Σ k : Fin m, Fin (sides' k), t.1 ≠ merged →
        (e t).1.1 = old t.1 ∧ (e t).1.2.val = t.2.val) ∧
      (∀ j : Fin (sides' merged),
        (e ⟨merged, j⟩).1.1 =
            (if j.val + 1 < C.sides s.1 then s.1 else (C.pair s).1) ∧
          (e ⟨merged, j⟩).1.2.val =
            if j.val + 1 < C.sides s.1 then (s.2.val + 1 + j.val) % C.sides s.1
            else ((C.pair s).2.val + 1 + (j.val + 1 - C.sides s.1)) %
              C.sides (C.pair s).1) := by
  classical
  obtain ⟨i, si⟩ := s
  obtain ⟨j, sj, hq⟩ : ∃ j sj, C.pair ⟨i, si⟩ = ⟨j, sj⟩ := ⟨_, _, rfl⟩
  simp only [hq] at hs old_ne old_surj sides_merged ⊢
  dsimp only at hs old_merged sides_merged ⊢
  obtain ⟨ea, hea⟩ :=
    standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_cyclic (C.sides i) si
  obtain ⟨eb, heb⟩ :=
    standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_cyclic (C.sides j) sj
  have ha : 0 < C.sides i := C.sides_pos i
  have hb : 0 < C.sides j := C.sides_pos j
  have hlen : sides' merged = (C.sides i - 1) + (C.sides j - 1) :=
    standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_sideEquiv_aux_length
      _ _ _ ha hb sides_merged
  have lt1 : ∀ t : Σ k : Fin m, Fin (sides' k), t.1 = merged →
      t.2.val < (C.sides i - 1) + (C.sides j - 1) := by
    rintro ⟨k, x⟩ hk
    dsimp only at hk ⊢
    subst hk
    exact hlen ▸ x.isLt
  have lt3 : ∀ t : Σ k : Fin m, Fin (sides' k), t.1 ≠ merged →
      t.2.val < C.sides (old t.1) := by
    rintro ⟨k, x⟩ hk
    exact sides_old k hk ▸ x.isLt
  let F : (Σ k : Fin m, Fin (sides' k)) → C.Side := fun t =>
    if hk : t.1 = merged then
      if hj : t.2.val + 1 < C.sides i then
        ⟨i, (ea ⟨t.2.val, by omega⟩).1⟩
      else
        ⟨j, (eb ⟨t.2.val + 1 - C.sides i, by have := lt1 t hk; omega⟩).1⟩
    else ⟨old t.1, ⟨t.2.val, lt3 t hk⟩⟩
  have F_old : ∀ t, (ht : t.1 ≠ merged) → F t = ⟨old t.1, ⟨t.2.val, lt3 t ht⟩⟩ :=
    fun t ht => dif_neg ht
  have F_lo : ∀ x : Fin (sides' merged), (hx : x.val + 1 < C.sides i) →
      F ⟨merged, x⟩ = ⟨i, (ea ⟨x.val, by omega⟩).1⟩ :=
    fun x hx => by simp only [F, dif_pos rfl, dif_pos hx]
  have F_hi : ∀ x : Fin (sides' merged), (hx : ¬ x.val + 1 < C.sides i) →
      F ⟨merged, x⟩ = ⟨j, (eb ⟨x.val + 1 - C.sides i, by
        have := lt1 ⟨merged, x⟩ rfl; dsimp only at this; omega⟩).1⟩ :=
    fun x hx => by simp only [F, dif_pos rfl, dif_neg hx]
  have F_ne : ∀ t, F t ≠ ⟨i, si⟩ ∧ F t ≠ ⟨j, sj⟩ := by
    rintro ⟨k, x⟩
    by_cases hk : k = merged
    · subst hk
      by_cases hx : x.val + 1 < C.sides i
      · rw [F_lo x hx]
        exact ⟨fun h => (ea _).2 (eq_of_heq (Sigma.mk.inj_iff.1 h).2),
          fun h => hs (Sigma.mk.inj_iff.1 h).1⟩
      · rw [F_hi x hx]
        exact ⟨fun h => hs (Sigma.mk.inj_iff.1 h).1.symm,
          fun h => (eb _).2 (eq_of_heq (Sigma.mk.inj_iff.1 h).2)⟩
    · rw [F_old _ hk]
      exact ⟨fun h => hk (old_injective ((Sigma.mk.inj_iff.1 h).1.trans old_merged.symm)),
        fun h => old_ne k (Sigma.mk.inj_iff.1 h).1⟩
  have F_inj : Function.Injective F := by
    rintro ⟨k, x⟩ ⟨k', y⟩ hxy
    by_cases hk : k = merged <;> by_cases hk' : k' = merged
    · subst hk; subst hk'
      have hval : x.val = y.val := by
        by_cases hx : x.val + 1 < C.sides i <;> by_cases hy : y.val + 1 < C.sides i
        · rw [F_lo x hx, F_lo y hy] at hxy
          have := ea.injective (Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.1 hxy).2))
          exact congrArg (fun z : Fin (C.sides i - 1) => z.val) this
        · rw [F_lo x hx, F_hi y hy] at hxy
          exact absurd (Sigma.mk.inj_iff.1 hxy).1 hs
        · rw [F_hi x hx, F_lo y hy] at hxy
          exact absurd (Sigma.mk.inj_iff.1 hxy).1.symm hs
        · rw [F_hi x hx, F_hi y hy] at hxy
          have := eb.injective (Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.1 hxy).2))
          have := congrArg Fin.val this
          dsimp only at this
          omega
      exact congrArg (Sigma.mk _) (Fin.ext hval)
    · subst hk
      exfalso
      rw [F_old ⟨k', y⟩ hk'] at hxy
      by_cases hx : x.val + 1 < C.sides i
      · rw [F_lo x hx] at hxy
        exact hk' (old_injective ((Sigma.mk.inj_iff.1 hxy).1.symm.trans old_merged.symm))
      · rw [F_hi x hx] at hxy
        exact old_ne k' (Sigma.mk.inj_iff.1 hxy).1.symm
    · subst hk'
      exfalso
      rw [F_old ⟨k, x⟩ hk] at hxy
      by_cases hy : y.val + 1 < C.sides i
      · rw [F_lo y hy] at hxy
        exact hk (old_injective ((Sigma.mk.inj_iff.1 hxy).1.trans old_merged.symm))
      · rw [F_hi y hy] at hxy
        exact old_ne k (Sigma.mk.inj_iff.1 hxy).1
    · rw [F_old ⟨k, x⟩ hk, F_old ⟨k', y⟩ hk'] at hxy
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hxy
      have hkk := old_injective h1
      dsimp only at hkk
      subst hkk
      have := congrArg Fin.val (eq_of_heq h2)
      exact congrArg (Sigma.mk _) (Fin.ext this)
  have F_surj : ∀ u : C.Side, u ≠ ⟨i, si⟩ → u ≠ ⟨j, sj⟩ → ∃ t, F t = u := by
    rintro ⟨k, x⟩ hu1 hu2
    by_cases hki : k = i
    · subst hki
      obtain ⟨y, hy⟩ := ea.surjective ⟨x, fun h => hu1 (h ▸ rfl)⟩
      have hy1 : y.val + 1 < C.sides k := by have := y.isLt; omega
      refine ⟨⟨merged, ⟨y.val, by rw [hlen]; have := y.isLt; omega⟩⟩, ?_⟩
      rw [F_lo _ hy1]
      simp only [Fin.eta, hy]
    · by_cases hkj : k = j
      · subst hkj
        obtain ⟨y, hy⟩ := eb.surjective ⟨x, fun h => hu2 (h ▸ rfl)⟩
        have hy0 := y.isLt
        refine ⟨⟨merged, ⟨(C.sides i - 1) + y.val, by rw [hlen]; omega⟩⟩, ?_⟩
        have hn : ¬ (C.sides i - 1 + y.val) + 1 < C.sides i := by omega
        rw [F_hi _ hn]
        dsimp only
        have : (⟨C.sides i - 1 + y.val + 1 - C.sides i, by omega⟩ : Fin (C.sides k - 1)) = y :=
          Fin.ext (by dsimp only; omega)
        rw [this, hy]
      · obtain ⟨k', hk'⟩ := old_surj k hkj
        have hkm : k' ≠ merged := by
          intro h; subst h; exact hki (hk'.symm.trans old_merged)
        subst hk'
        refine ⟨⟨k', ⟨x.val, by rw [sides_old k' hkm]; exact x.isLt⟩⟩, ?_⟩
        rw [F_old _ hkm]
  let f : (Σ k : Fin m, Fin (sides' k)) → {u : C.Side // u ≠ ⟨i, si⟩ ∧ u ≠ ⟨j, sj⟩} :=
    fun t => ⟨F t, F_ne t⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => F_inj (congrArg Subtype.val h), fun u => ?_⟩
    obtain ⟨t, ht⟩ := F_surj u.1 u.2.1 u.2.2
    exact ⟨t, Subtype.ext ht⟩
  refine ⟨(Equiv.ofBijective f hf).trans
    (Equiv.subtypeEquivRight (fun u => by rw [hq])), ?_, ?_⟩
  · intro t ht
    change (F t).1 = old t.1 ∧ (F t).2.val = t.2.val
    rw [F_old t ht]
    exact ⟨rfl, rfl⟩
  · intro x
    change (F ⟨merged, x⟩).1 = _ ∧ (F ⟨merged, x⟩).2.val = _
    by_cases hx : x.val + 1 < C.sides i
    · rw [F_lo x hx, if_pos hx, if_pos hx]
      exact ⟨rfl, hea _⟩
    · rw [F_hi x hx, if_neg hx, if_neg hx]
      refine ⟨rfl, ?_⟩
      rw [hq]
      exact heb _

/-- Split by claude-14 (2026-10-25) after lemma-1's PARTIAL: the faces of `C'`
are `Fin.succAbove (C.pair s).1`, the side correspondence is
`_aux_sideEquiv`, and `pair`/`sign` are transported along it. -/
theorem standardCover_pairingData_aux_glueStep_aux_mergeExists
    (C : PolygonComplex) (hsides : ∀ f, 2 ≤ C.sides f) (s : C.Side)
    (hs : s.1 ≠ (C.pair s).1) :
    ∃ C' : PolygonComplex,
      Nonempty (standardCover_pairingData_aux_glueStep_aux_GlueData C C' s) := by
  obtain ⟨m, hm⟩ : ∃ m, C.faceCount = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fin.pos s.1).ne'
  set p : Fin C.faceCount := (C.pair s).1 with hp
  let old : Fin m → Fin C.faceCount := fun k =>
    Fin.cast hm.symm ((Fin.cast hm p).succAbove k)
  have old_injective : Function.Injective old := fun k k' h =>
    Fin.succAbove_right_injective (Fin.cast_injective _ h)
  have old_ne : ∀ k, old k ≠ p := by
    intro k h
    have h' := congrArg (Fin.cast hm) h
    simp only [old, Fin.cast_cast, Fin.cast_eq_self] at h'
    exact Fin.succAbove_ne (Fin.cast hm p) k h'
  have old_surj : ∀ f, f ≠ p → ∃ k, old k = f := by
    intro f hf
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := Fin.cast hm f)
      (y := Fin.cast hm p) (fun h => hf (Fin.cast_injective _ h))
    exact ⟨k, by ext; simp [old, hk]⟩
  obtain ⟨merged, old_merged⟩ := old_surj s.1 hs
  let a := C.sides s.1
  let b := C.sides p
  let sides' : Fin m → ℕ := fun k => if k = merged then a + b - 2 else C.sides (old k)
  have sides_old : ∀ k, k ≠ merged → sides' k = C.sides (old k) := fun k hk =>
    if_neg hk
  have sides_merged : sides' merged + 2 = C.sides s.1 + C.sides p := by
    have := hsides s.1; have := hsides p
    simp only [sides', if_pos rfl, a, b]; omega
  obtain ⟨e, he_old, he_merged⟩ :=
    standardCover_pairingData_aux_glueStep_aux_mergeExists_aux_sideEquiv C s hs
      old merged sides' old_merged old_injective old_ne old_surj sides_old sides_merged
  let Q : {u : C.Side // u ≠ s ∧ u ≠ C.pair s} → {u : C.Side // u ≠ s ∧ u ≠ C.pair s} :=
    fun u => ⟨C.pair u.1, fun h => u.2.2 (by
        have := congrArg C.pair h; rwa [C.pair_pair] at this),
      fun h => u.2.1 (C.pair.injective h)⟩
  have hQ : Function.Involutive Q := fun u => Subtype.ext (C.pair_pair u.1)
  let pair' : Equiv.Perm (Σ k : Fin m, Fin (sides' k)) :=
    (e.trans hQ.toPerm).trans e.symm
  have pair'_apply : ∀ t, e (pair' t) = Q (e t) := fun t => by simp [pair']
  let C' : PolygonComplex :=
    { faceCount := m
      sides := sides'
      sides_pos := fun k => by
        by_cases hk : k = merged
        · have := hsides s.1; have := hsides p
          simp only [sides', if_pos hk, a, b]; omega
        · rw [sides_old k hk]; exact C.sides_pos _
      pair := pair'
      pair_pair := fun t => e.injective (by rw [pair'_apply, pair'_apply]; exact hQ _)
      pair_ne := fun t h => C.pair_ne (e t).1 (by
        have := congrArg (fun u => u.1) (pair'_apply t); simp only [h] at this
        exact this.symm)
      sign := fun t => C.sign (e t).1 }
  refine ⟨C', ⟨
    { faceCount_succ := hm.symm
      merged := merged
      old := old
      old_merged := old_merged
      old_injective := old_injective
      old_ne := old_ne
      sides_old := sides_old
      sides_merged := sides_merged
      toOld := fun t => (e t).1
      toOld_injective := fun t t' h => e.injective (Subtype.ext h)
      toOld_ne := fun t => (e t).2
      toOld_surj := fun u hu hu' => ⟨e.symm ⟨u, hu, hu'⟩, by simp⟩
      toOld_fst := fun t ht => (he_old t ht).1
      toOld_val := fun t ht => (he_old t ht).2
      toOld_merged_fst := fun j => (he_merged j).1
      toOld_merged_val := fun j => (he_merged j).2
      pair_toOld := fun t => congrArg Subtype.val (pair'_apply t)
      sign_toOld := fun t => rfl }⟩⟩

/-- **Leaf (arc count).**  Every side of `C` except `s` and `C.pair s` is a
side of `C'`, once. -/
theorem standardCover_pairingData_aux_glueStep_aux_totalSides
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s) :
    C'.totalSides + 2 = C.totalSides := by
  let e : C'.Side ≃ {u : C.Side // u ≠ s ∧ u ≠ C.pair s} :=
    Equiv.ofBijective
      (fun t ↦ ⟨D.toOld t, D.toOld_ne t⟩)
      ⟨fun _ _ h ↦ D.toOld_injective (congrArg Subtype.val h), fun u ↦ by
        obtain ⟨t, ht⟩ := D.toOld_surj u.1 u.2.1 u.2.2
        exact ⟨t, Subtype.ext ht⟩⟩
  have hcard : Fintype.card C'.Side =
      Fintype.card {u : C.Side // u ≠ s ∧ u ≠ C.pair s} :=
    Fintype.card_congr e
  have hp : Fintype.card {u : C.Side // u = s ∨ u = C.pair s} = 2 := by
    rw [Fintype.card_subtype]
    have hfilter : Finset.filter (fun u : C.Side ↦ u = s ∨ u = C.pair s) Finset.univ =
        {s, C.pair s} := by
      ext u
      simp [eq_comm]
    rw [hfilter, Finset.card_pair]
    exact (C.pair_ne s).symm
  have hle : 2 ≤ Fintype.card C.Side := by
    rw [← hp]
    exact Fintype.card_subtype_le _
  have hcompl : Fintype.card {u : C.Side // u ≠ s ∧ u ≠ C.pair s} =
      Fintype.card C.Side - 2 := by
    simpa only [not_or] using
      (Fintype.card_subtype_compl (fun u : C.Side ↦ u = s ∨ u = C.pair s)).trans
        (congrArg (Fintype.card C.Side - ·) hp)
  have hC : C.totalSides = Fintype.card C.Side := by
    simp [PolygonComplex.totalSides, Fintype.card_sigma]
  have hC' : C'.totalSides = Fintype.card C'.Side := by
    simp [PolygonComplex.totalSides, Fintype.card_sigma]
  rw [hC', hC, hcard, hcompl]
  omega

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
  have hold_surj : ∀ x : Fin C.faceCount, x ≠ (C.pair s).1 →
      ∃ k : Fin C'.faceCount, D.old k = x := by
    intro x hx
    by_contra hnot
    let F : Fin C'.faceCount ⊕ Fin 2 → Fin C.faceCount
      | Sum.inl k => D.old k
      | Sum.inr j => if j = 0 then (C.pair s).1 else x
    have hF : Function.Injective F := by
      intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b => exact congrArg Sum.inl (D.old_injective hab)
          | inr b =>
              exfalso
              simp only [F] at hab
              split at hab
              · exact D.old_ne a hab
              · exact hnot ⟨a, hab⟩
      | inr a =>
          cases b with
          | inl b =>
              exfalso
              simp only [F] at hab
              split at hab
              · exact D.old_ne b hab.symm
              · exact hnot ⟨b, hab.symm⟩
          | inr b =>
              apply congrArg Sum.inr
              fin_cases a
              · fin_cases b
                · rfl
                · exfalso
                  exact hx (by simpa [F] using hab.symm)
              · fin_cases b
                · exfalso
                  exact hx (by simpa [F] using hab)
                · rfl
    have hc := Fintype.card_le_of_injective F hF
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    have hcount := D.faceCount_succ
    omega
  let liftFace (x : Fin C.faceCount) : Fin C'.faceCount :=
    if hx : x = (C.pair s).1 then D.merged
    else Classical.choose (hold_surj x hx)
  have liftFace_pair : liftFace (C.pair s).1 = D.merged := by
    simp [liftFace]
  have liftFace_old (k : Fin C'.faceCount) : liftFace (D.old k) = k := by
    simp only [liftFace, D.old_ne k, ↓reduceDIte]
    exact D.old_injective (Classical.choose_spec (hold_surj (D.old k) (D.old_ne k)))
  have liftFace_s : liftFace s.1 = D.merged := by
    rw [← D.old_merged, liftFace_old]
  have liftFace_toOld (t : C'.Side) : liftFace (D.toOld t).1 = t.1 := by
    by_cases ht : t.1 = D.merged
    · obtain ⟨tf, m⟩ := t
      dsimp only at ht ⊢
      subst tf
      rw [D.toOld_merged_fst]
      split_ifs <;> simp only [liftFace_s, liftFace_pair]
    · rw [D.toOld_fst t ht, liftFace_old]
  have map_edge : ∀ {a b : Fin C.faceCount},
      (∃ u : C.Side, u.1 = a ∧ (C.pair u).1 = b) →
      Relation.EqvGen (fun a b => ∃ t : C'.Side,
        t.1 = a ∧ (C'.pair t).1 = b) (liftFace a) (liftFace b) := by
    rintro a b ⟨u, rfl, rfl⟩
    by_cases hu : u = s
    · subst hu
      rw [liftFace_s, liftFace_pair]
      exact Relation.EqvGen.refl _
    by_cases hup : u = C.pair s
    · subst hup
      rw [C.pair_pair, liftFace_pair, liftFace_s]
      exact Relation.EqvGen.refl _
    obtain ⟨t, ht⟩ := D.toOld_surj u hu hup
    apply Relation.EqvGen.rel
    refine ⟨t, ?_, ?_⟩
    · rw [← ht, liftFace_toOld]
    · calc
        (C'.pair t).1 = liftFace (D.toOld (C'.pair t)).1 :=
          (liftFace_toOld (C'.pair t)).symm
        _ = liftFace (C.pair u).1 := by rw [D.pair_toOld, ht]
  intro f g
  have map_path : ∀ {a b : Fin C.faceCount},
      Relation.EqvGen (fun a b => ∃ u : C.Side,
        u.1 = a ∧ (C.pair u).1 = b) a b →
      Relation.EqvGen (fun a b => ∃ t : C'.Side,
        t.1 = a ∧ (C'.pair t).1 = b) (liftFace a) (liftFace b) := by
    intro a b path
    induction path with
    | rel a b h => exact map_edge h
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  have mapped := map_path (hconn (D.old f) (D.old g))
  simpa only [liftFace_old] using mapped

/-- **Leaf (corners).**  `toOld` induces a bijection of corner classes.  The
four corners at the ends of `s` and `C.pair s` lie in two `C`-classes (by
orientability); in `C'` they are the two junctions of the merged face. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_cutRel
    {C : PolygonComplex} (s : C.Side) (hor : C.IsOrientable) :
    Relation.EqvGen C.CornerRel s (C.nextCorner (C.pair s)) ∧
      Relation.EqvGen C.CornerRel (C.nextCorner s) (C.pair s) := by
  constructor
  · apply Relation.EqvGen.rel
    refine ⟨s, ?_⟩
    rw [if_neg (Ne.symm (hor s))]
    exact Or.inl ⟨rfl, rfl⟩
  · apply Relation.EqvGen.rel
    refine ⟨s, ?_⟩
    rw [if_neg (Ne.symm (hor s))]
    exact Or.inr ⟨rfl, rfl⟩

/-- The only failure of `toOld` to literally commute with `nextCorner` is at
the two joins of the merged polygon; there it crosses one of the two deleted
sides, hence gives one old corner-equivalence step. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_unmerged
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (t : C'.Side) (ht : t.1 ≠ D.merged) :
    D.toOld (C'.nextCorner t) = C.nextCorner (D.toOld t) := by
  have hf : (D.toOld (C'.nextCorner t)).1 = (C.nextCorner (D.toOld t)).1 := by
    simp only [PolygonComplex.nextCorner]
    exact (D.toOld_fst (C'.nextCorner t) (by simpa [PolygonComplex.nextCorner] using ht)).trans
      (D.toOld_fst t ht).symm
  apply Sigma.ext hf
  apply (Fin.heq_ext_iff (congrArg C.sides hf)).2
  simp only [PolygonComplex.nextCorner]
  have hs : C.sides (D.toOld t).1 = C'.sides t.1 :=
    (congrArg C.sides (D.toOld_fst t ht)).trans (D.sides_old t.1 ht).symm
  rw [D.toOld_val t ht, hs]
  exact D.toOld_val (C'.nextCorner t) (by simpa [PolygonComplex.nextCorner] using ht)


/-- **Leaf (first half).**  Merged side `m` and its successor both come from
`s.1` (`m + 2 < C.sides s.1`); `toOld` sends them to sides `s.2 + 1 + m` and
`s.2 + 2 + m` (mod `C.sides s.1`), so it commutes with `nextCorner` literally.
(`m + 1` does not wrap: the merged face has `C.sides s.1 + C.sides (C.pair s).1 - 2`
sides and `C.sides (C.pair s).1 ≥ 1`.) -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_first
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (m : Fin (C'.sides D.merged)) (hm : m.val + 2 < C.sides s.1) :
    D.toOld (C'.nextCorner ⟨D.merged, m⟩) = C.nextCorner (D.toOld ⟨D.merged, m⟩) := by
  sorry

/-- **Leaf (second half).**  Merged side `m` and its successor both come from
`(C.pair s).1` (`C.sides s.1 ≤ m + 1` and `m + 1` does not wrap); `toOld` sends
them to consecutive sides `(C.pair s).2 + 1 + (m + 1 - C.sides s.1)` and the next
(mod `C.sides (C.pair s).1`), so it commutes with `nextCorner` literally. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_second
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (m : Fin (C'.sides D.merged)) (hm₁ : C.sides s.1 ≤ m.val + 1)
    (hm₂ : m.val + 1 < C'.sides D.merged) :
    D.toOld (C'.nextCorner ⟨D.merged, m⟩) = C.nextCorner (D.toOld ⟨D.merged, m⟩) := by
  sorry

/-- **Leaf (first junction).**  `m + 2 = C.sides s.1`: `m` is the last side
taken from `s.1`, so `toOld m` is side `s.2 - 1` and `C.nextCorner (toOld m) = s`.
If `C.sides (C.pair s).1 ≥ 2`, the next merged side is the first one from
`(C.pair s).1`, `toOld` of it is `C.nextCorner (C.pair s)`, and
`(_aux_cutRel s hor).1` gives the step.  Degenerate case
`C.sides (C.pair s).1 = 1`: then `m + 1` wraps to `0`, `toOld 0 = C.nextCorner s`,
and `C.nextCorner (C.pair s) = C.pair s` (a 1-gon), so both halves of
`_aux_cutRel` compose: `C.nextCorner s ~ C.pair s ~ s`. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_join
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) (m : Fin (C'.sides D.merged))
    (hm : m.val + 2 = C.sides s.1) :
    Relation.EqvGen C.CornerRel (D.toOld (C'.nextCorner ⟨D.merged, m⟩))
      (C.nextCorner (D.toOld ⟨D.merged, m⟩)) := by
  sorry

/-- **Leaf (wrap-around junction).**  `m` is the last merged side and comes from
`(C.pair s).1`, so `toOld m` is side `(C.pair s).2 - 1` and
`C.nextCorner (toOld m) = C.pair s`; `m + 1` wraps to `0`.  If `C.sides s.1 ≥ 2`,
`toOld 0 = C.nextCorner s` and `(_aux_cutRel s hor).2` gives the step.
Degenerate case `C.sides s.1 = 1`: then `toOld 0` is the first side from
`(C.pair s).1`, i.e. `C.nextCorner (C.pair s)`, and `C.nextCorner s = s`, so
`_aux_cutRel` composes: `C.nextCorner (C.pair s) ~ s = C.nextCorner s ~ C.pair s`. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_wrap
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) (m : Fin (C'.sides D.merged))
    (hm₁ : C.sides s.1 ≤ m.val + 1) (hm₂ : m.val + 1 = C'.sides D.merged) :
    Relation.EqvGen C.CornerRel (D.toOld (C'.nextCorner ⟨D.merged, m⟩))
      (C.nextCorner (D.toOld ⟨D.merged, m⟩)) := by
  sorry

/-- At a corner of the merged polygon, `toOld` commutes with `nextCorner` up to
one old corner-equivalence step: within one half it commutes literally
(`_aux_first`, `_aux_second`); at the two junctions it crosses a deleted side,
and `_aux_cutRel` gives the step (`_aux_join`, `_aux_wrap`). -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) (t : C'.Side) (ht : t.1 = D.merged) :
    Relation.EqvGen C.CornerRel (D.toOld (C'.nextCorner t))
      (C.nextCorner (D.toOld t)) := by
  obtain ⟨tf, m⟩ := t
  dsimp only at ht
  subst ht
  have hlt := m.isLt
  by_cases h₁ : m.val + 2 < C.sides s.1
  · rw [standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_first D m h₁]
    exact Relation.EqvGen.refl _
  by_cases h₂ : m.val + 2 = C.sides s.1
  · exact standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_join D hor m h₂
  by_cases h₃ : m.val + 1 < C'.sides D.merged
  · rw [standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_second D m (by omega) h₃]
    exact Relation.EqvGen.refl _
  · exact standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged_aux_wrap D hor m (by omega) (by omega)

theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) (t : C'.Side) :
    Relation.EqvGen C.CornerRel (D.toOld (C'.nextCorner t))
      (C.nextCorner (D.toOld t)) := by
  by_cases ht : t.1 = D.merged
  · exact standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_merged D hor t ht
  · rw [standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next_aux_unmerged D t ht]
    exact Relation.EqvGen.refl _

/-- Once the cyclic-boundary calculation is isolated in `_aux_next`, every
generating corner identification of the glued complex maps to an old corner
equivalence. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_mapRel
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) {a b : C'.Side} (h : C'.CornerRel a b) :
    Relation.EqvGen C.CornerRel (D.toOld a) (D.toOld b) := by
  obtain ⟨t, ht⟩ := h
  have hnext := standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next D hor
  have hrel : ∀ x y, C.CornerRel x y → Relation.EqvGen C.CornerRel x y :=
    fun x y h => Relation.EqvGen.rel x y h
  have hsign : C'.sign t = C'.sign (C'.pair t) ↔
      C.sign (D.toOld t) = C.sign (C.pair (D.toOld t)) := by
    rw [D.sign_toOld, D.sign_toOld, D.pair_toOld]
  by_cases hs : C'.sign t = C'.sign (C'.pair t)
  · rw [if_pos hs] at ht
    have hs' := hsign.mp hs
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb]
    · rw [D.pair_toOld]
      exact hrel _ _ ⟨D.toOld t, by rw [if_pos hs']; exact Or.inl ⟨rfl, rfl⟩⟩
    · refine (hnext t).trans _ _ _ ((hrel _ _ ⟨D.toOld t, ?_⟩).trans _ _ _
        (hnext (C'.pair t)).symm)
      rw [if_pos hs', D.pair_toOld]; exact Or.inr ⟨rfl, rfl⟩
  · rw [if_neg hs] at ht
    have hs' : ¬ C.sign (D.toOld t) = C.sign (C.pair (D.toOld t)) :=
      fun h => hs (hsign.mpr h)
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb]
    · refine (hrel _ _ ⟨D.toOld t, ?_⟩).trans _ _ _ (hnext (C'.pair t)).symm
      rw [if_neg hs', D.pair_toOld]; exact Or.inl ⟨rfl, rfl⟩
    · refine (hnext t).trans _ _ _ (hrel _ _ ⟨D.toOld t, ?_⟩)
      rw [if_neg hs', D.pair_toOld]; exact Or.inr ⟨rfl, rfl⟩

/-- **Leaf (inverse on corners).**  A map back from the corners of `C` to the
corners of `C'`: a left inverse of `toOld`, sending each corner to one in its
own `C`-class, and carrying every generating identification of `C` to a
`C'`-equivalence.  The deleted corners `s` and `C.pair s` go to preimages of
corners in their classes (`_aux_cutRel`: `s ~ nextCorner (C.pair s)` and
`C.pair s ~ nextCorner s`). -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back_aux_leftInverse
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s) :
    ∃ g : C.Side → C'.Side, ∀ t, g (D.toOld t) = t := by
  haveI : Nonempty C'.Side := ⟨⟨D.merged, ⟨0, C'.sides_pos D.merged⟩⟩⟩
  let g : C.Side → C'.Side := Function.invFun D.toOld
  refine ⟨g, ?_⟩
  intro t
  exact Function.leftInverse_invFun D.toOld_injective t

/-- **Leaf (choice of the inverse).**  A left inverse of `toOld` whose values
at the deleted sides `s` and `C.pair s` are preimages of corners in their own
`C`-classes.  By `_aux_cutRel`, `s ~ nextCorner (C.pair s)` and
`C.pair s ~ nextCorner s`; the faces `s.1` and `(C.pair s).1` differ
(`old_ne`, `old_merged`), so these corners are deleted only when a face is a
1-gon, and then follow the class one more step (`sides_merged` with
`C'.sides_pos` rules out both faces being 1-gons). -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back_aux_choose
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) :
    ∃ g : C.Side → C'.Side, (∀ t, g (D.toOld t) = t) ∧
      (∀ u, Relation.EqvGen C.CornerRel (D.toOld (g u)) u) := by
  have hfaces : s.1 ≠ (C.pair s).1 := by
    intro h
    exact D.old_ne D.merged (D.old_merged.trans h)
  have hfixed : ∀ t : C.Side, C.nextCorner t = t → C.sides t.1 = 1 := by
    intro t ht
    have hv := congrArg (fun u : C.Side => u.2.val) ht
    simp only [PolygonComplex.nextCorner] at hv
    have hp := C.sides_pos t.1
    by_cases hlt : t.2.val + 1 < C.sides t.1
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq : t.2.val + 1 = C.sides t.1 := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  have hpre : ∀ u : C.Side, ∃ t : C'.Side,
      Relation.EqvGen C.CornerRel (D.toOld t) u := by
    intro u
    by_cases hu : u = s
    · subst u
      by_cases hp : C.nextCorner (C.pair s) = C.pair s
      · have hsidesp := hfixed (C.pair s) hp
        have hsides : C.nextCorner s ≠ s := by
          intro hs
          have hsidess := hfixed s hs
          have hm := C'.sides_pos D.merged
          have heq := D.sides_merged
          omega
        have hn1 : C.nextCorner s ≠ s := hsides
        have hn2 : C.nextCorner s ≠ C.pair s := by
          intro h
          have hf := congrArg (fun x : C.Side => x.1) h
          simp only [PolygonComplex.nextCorner] at hf
          exact hfaces hf
        obtain ⟨t, ht⟩ := D.toOld_surj (C.nextCorner s) hn1 hn2
        refine ⟨t, ?_⟩
        rw [ht]
        have hc := standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_cutRel s hor
        rw [hp] at hc
        exact hc.2.trans _ _ _ hc.1.symm
      · have hn1 : C.nextCorner (C.pair s) ≠ s := by
          intro h
          exact hfaces ((congrArg (fun x : C.Side => x.1) h).symm)
        obtain ⟨t, ht⟩ := D.toOld_surj (C.nextCorner (C.pair s)) hn1 hp
        refine ⟨t, ?_⟩
        rw [ht]
        exact (standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_cutRel s hor).1.symm
    · by_cases hup : u = C.pair s
      · subst u
        by_cases hs : C.nextCorner s = s
        · have hsidess := hfixed s hs
          have hsidesp : C.nextCorner (C.pair s) ≠ C.pair s := by
            intro hp
            have hsidesp := hfixed (C.pair s) hp
            have hm := C'.sides_pos D.merged
            have heq := D.sides_merged
            omega
          have hn1 : C.nextCorner (C.pair s) ≠ s := by
            intro h
            exact hfaces ((congrArg (fun x : C.Side => x.1) h).symm)
          obtain ⟨t, ht⟩ := D.toOld_surj (C.nextCorner (C.pair s)) hn1 hsidesp
          refine ⟨t, ?_⟩
          rw [ht]
          have hc := standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_cutRel s hor
          rw [hs] at hc
          exact hc.1.symm.trans _ _ _ hc.2
        · have hn2 : C.nextCorner s ≠ C.pair s := by
            intro h
            have hf := congrArg (fun x : C.Side => x.1) h
            simp only [PolygonComplex.nextCorner] at hf
            exact hfaces hf
          obtain ⟨t, ht⟩ := D.toOld_surj (C.nextCorner s) hs hn2
          refine ⟨t, ?_⟩
          rw [ht]
          exact (standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_cutRel s hor).2
      · obtain ⟨t, ht⟩ := D.toOld_surj u hu hup
        refine ⟨t, ?_⟩
        rw [ht]
        exact Relation.EqvGen.refl u
  let g : C.Side → C'.Side := fun u =>
    if h : ∃ t, D.toOld t = u then Classical.choose h else Classical.choose (hpre u)
  refine ⟨g, ?_, ?_⟩
  · intro t
    have h : ∃ v, D.toOld v = D.toOld t := ⟨t, rfl⟩
    rw [show g (D.toOld t) = Classical.choose h by simp only [g, dif_pos h]]
    exact D.toOld_injective (Classical.choose_spec h)
  · intro u
    by_cases h : ∃ t, D.toOld t = u
    · rw [show g u = Classical.choose h by simp only [g, dif_pos h]]
      rw [Classical.choose_spec h]
      exact Relation.EqvGen.refl u
    · rw [show g u = Classical.choose (hpre u) by simp only [g, dif_neg h]]
      exact Classical.choose_spec (hpre u)

/-- **Leaf (corner classes reflect).**  Two corners of `C'` whose images are
`C`-equivalent are already `C'`-equivalent: the map of corner classes induced
by `toOld` is injective.  A `C`-path between images may pass through the
deleted corners `s` and `C.pair s`; each such visit enters and leaves through
the two junction corners of the merged face of `C'`. -/
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back_aux_reflect
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) (x y : C'.Side)
    (h : Relation.EqvGen C.CornerRel (D.toOld x) (D.toOld y)) :
    Relation.EqvGen C'.CornerRel x y := by
  sorry

theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) :
    ∃ g : C.Side → C'.Side, (∀ t, g (D.toOld t) = t) ∧
      (∀ u, Relation.EqvGen C.CornerRel (D.toOld (g u)) u) ∧
      (∀ a b, C.CornerRel a b → Relation.EqvGen C'.CornerRel (g a) (g b)) := by
  obtain ⟨g, hg1, hg2⟩ :=
    standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back_aux_choose D hor
  refine ⟨g, hg1, hg2, fun a b hab => ?_⟩
  apply standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back_aux_reflect D hor
  exact (hg2 a).trans _ _ _ ((Relation.EqvGen.rel _ _ hab).trans _ _ _ (hg2 b).symm)

theorem standardCover_pairingData_aux_glueStep_aux_vertexCount
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) : C'.vertexCount = C.vertexCount := by
  obtain ⟨g, hg1, hg2, hg3⟩ :=
    standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back D hor
  have lift : ∀ {α β : Type} {r : α → α → Prop} {r' : β → β → Prop} (h : α → β),
      (∀ a b, r a b → Relation.EqvGen r' (h a) (h b)) →
      ∀ a b, Relation.EqvGen r a b → Relation.EqvGen r' (h a) (h b) := by
    intro α β r r' h hh a b hab
    induction hab with
    | rel x y hxy => exact hh x y hxy
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  have hF := lift (r := C'.CornerRel) (r' := C.CornerRel) D.toOld
    (fun a b h => standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_mapRel D hor h)
  have hG := lift (r := C.CornerRel) (r' := C'.CornerRel) g hg3
  let F : C'.Vertex → C.Vertex := Quotient.map D.toOld hF
  let G : C.Vertex → C'.Vertex := Quotient.map g hG
  have e : C'.Vertex ≃ C.Vertex :=
    { toFun := F
      invFun := G
      left_inv := by
        intro x
        induction x using Quotient.ind with
        | _ t => exact congrArg (Quotient.mk _) (hg1 t)
      right_inv := by
        intro x
        induction x using Quotient.ind with
        | _ u => exact Quotient.sound (hg2 u) }
  exact Nat.card_congr e

/- A common compact parametrizing space gives the required homeomorphism of
polygon-complex quotients once it has the same fibres on both sides.  This is
the quotient-topology part of the glue step; the remaining geometric task is
to parametrize two disks joined along the chosen side by the merged disk. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_span
    {C C' : PolygonComplex} {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (a : Y → Σ _ : Fin C.faceCount, Disk)
    (b : Y → Σ _ : Fin C'.faceCount, Disk)
    (ha : Continuous a) (hb : Continuous b)
    (hasurj : Function.Surjective a) (hbsurj : Function.Surjective b)
    (hrel : ∀ y y', Relation.EqvGen C.Rel (a y) (a y') ↔
      Relation.EqvGen C'.Rel (b y) (b y')) :
    Nonempty (C.Space ≃ₜ C'.Space) := by
  let A : Y → C.Space := fun y => Quotient.mk (Relation.EqvGen.setoid C.Rel) (a y)
  let B : Y → C'.Space := fun y => Quotient.mk (Relation.EqvGen.setoid C'.Rel) (b y)
  have hqa : Topology.IsQuotientMap A := by
    exact isQuotientMap_quot_mk.comp
      (IsQuotientMap.of_surjective_continuous hasurj ha)
  have hqb : Topology.IsQuotientMap B := by
    exact isQuotientMap_quot_mk.comp
      (IsQuotientMap.of_surjective_continuous hbsurj hb)
  have hfib : ∀ y y', A y = A y' ↔ B y = B y' := by
    intro y y'
    change Quotient.mk _ (a y) = Quotient.mk _ (a y') ↔
      Quotient.mk _ (b y) = Quotient.mk _ (b y')
    rw [Quotient.eq, Quotient.eq]
    exact hrel y y'
  obtain ⟨sA, hsA⟩ := hqa.surjective.hasRightInverse
  obtain ⟨sB, hsB⟩ := hqb.surjective.hasRightInverse
  let f : C.Space → C'.Space := B ∘ sA
  let g : C'.Space → C.Space := A ∘ sB
  have hfA : f ∘ A = B := by
    funext y
    exact (hfib (sA (A y)) y).mp (hsA (A y))
  have hgB : g ∘ B = A := by
    funext y
    exact (hfib (sB (B y)) y).mpr (hsB (B y))
  refine ⟨{
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_ }
    continuous_toFun := hqa.continuous_iff.mpr ?_
    continuous_invFun := hqb.continuous_iff.mpr ?_ }⟩
  · intro x
    obtain ⟨y, rfl⟩ := hqa.surjective x
    rw [show f (A y) = B y from congrFun hfA y]
    exact congrFun hgB y
  · intro x
    obtain ⟨y, rfl⟩ := hqb.surjective x
    rw [show g (B y) = A y from congrFun hgB y]
    exact congrFun hfA y
  · rw [hfA]
    exact continuous_coinduced_rng.comp hb
  · rw [hgB]
    exact continuous_coinduced_rng.comp ha

/-- Charts of the two halves of the merged `(p + q - 2)`-gon cut along the chord
from corner `p - 1` to corner `0`.  `hL` carries the `p`-gon onto the half that
holds arcs `0, …, p - 2` (arc `(i + 1 + m) % p` onto arc `m`) and side `i` onto
the chord, run from corner `p - 1` to corner `0`; `hR` carries the `q`-gon onto
the other half (arc `(j + 1 + k) % q` onto arc `p - 1 + k`) and side `j` onto
the same chord run backwards. -/
structure standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
    (p q i j : ℕ) (hL hR : Disk → Disk) : Prop where
  continuous_left : Continuous hL
  continuous_right : Continuous hR
  injective_left : Function.Injective hL
  injective_right : Function.Injective hR
  cover : ∀ z, (∃ x, hL x = z) ∨ ∃ y, hR y = z
  seam : ∀ x y, hL x = hR y ↔
    ∃ t, x = edgePoint p i t ∧ y = edgePoint q j (reverseIcc t)
  edge_left : ∀ m, m + 1 < p → ∀ t,
    hL (edgePoint p ((i + 1 + m) % p) t) = edgePoint (p + q - 2) m t
  edge_right : ∀ m, p ≤ m + 1 → m < p + q - 2 → ∀ t,
    hR (edgePoint q ((j + 1 + (m + 1 - p)) % q) t) = edgePoint (p + q - 2) m t
  interior_left : ∀ x : Disk, ‖(x : ℂ)‖ < 1 → ‖(hL x : ℂ)‖ < 1
  interior_right : ∀ y : Disk, ‖(y : ℂ)‖ < 1 → ‖(hR y : ℂ)‖ < 1

/-- The chord corners `0` and `p - 1` of the merged polygon are distinct corners
(banked by lemma-1). -/
lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_cut
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    let L := p + q - 2
    0 < p - 1 ∧ p - 1 < L ∧
      PolygonMoves.cutPoint L 0 ≠ PolygonMoves.cutPoint L (p - 1) := by
  dsimp
  have hp' : 0 < p - 1 := by omega
  have hL : p - 1 < p + q - 2 := by omega
  refine ⟨hp', hL, PolygonMoves.cutPoint_ne hp' ?_⟩
  omega

/-- **Leaf (geometry).**  The circle reparametrization for the left half: the `p`-gon
boundary onto the boundary parameter of `cutOldA (p + q - 2) 0 (p - 1)`,
piecewise linear in the angle. -/
def standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    (p L : ℕ) (x : ℝ) : ℝ :=
  if x ≤ p - 1 then x else
    (p - 1) + (x - (p - 1)) * (L - (p - 1))

def standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    (p L : ℕ) (y : ℝ) : ℝ :=
  if y ≤ p - 1 then y else
    (p - 1) + (y - (p - 1)) / (L - (p - 1))

lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_props
    (p L : ℕ) (hp : 2 ≤ p) (hL : p - 1 < L) :
    let f := standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f p L
    let g := standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g p L
    Continuous f ∧ Continuous g ∧ f 0 = 0 ∧ f p = L ∧ g 0 = 0 ∧ g L = p ∧
      Set.MapsTo f (Set.Icc 0 p) (Set.Icc 0 L) ∧
      Set.MapsTo g (Set.Icc 0 L) (Set.Icc 0 p) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) p, g (f x) = x) ∧
      (∀ y ∈ Set.Icc (0 : ℝ) L, f (g y) = y) := by
  dsimp
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ p)]
  have hd : (0 : ℝ) < L - (p - 1) := by
    have hh : ((p - 1 : ℕ) : ℝ) < L := by exact_mod_cast hL
    rw [hcast] at hh
    linarith
  have hf : Continuous
      (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f p L) := by
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro x hx
    rw [hx]
    ring
  have hg : Continuous
      (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g p L) := by
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro x hx
    rw [hx]
    field_simp
    ring
  refine ⟨hf, hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    rw [if_pos (by linarith)]
  · unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    rw [if_neg (by linarith)]
    push_cast
    ring
  · unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    rw [if_pos (by linarith)]
  · unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    have hh : ((p - 1 : ℕ) : ℝ) < L := by exact_mod_cast hL
    rw [hcast] at hh
    rw [if_neg (by linarith)]
    field_simp [hd.ne']
    ring
  · intro x hx
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    split_ifs with h
    · exact ⟨hx.1, le_trans h (by
        have hh : ((p - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hL.le
        rw [hcast] at hh
        exact hh)⟩
    · constructor
      · nlinarith
      · have hxp : x ≤ p := hx.2
        nlinarith
  · intro y hy
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    split_ifs with h
    · exact ⟨hy.1, le_trans h (by linarith)⟩
    · constructor
      · have : 0 ≤ y - (p - 1) := le_of_lt (sub_pos.mpr (lt_of_not_ge h))
        have : 0 ≤ (y - (p - 1)) / (L - (p - 1)) := div_nonneg this hd.le
        linarith
      · have hyL : y ≤ L := hy.2
        have hz : y - (p - 1) ≤ L - (p - 1) := by linarith
        have := (div_le_one hd).2 hz
        linarith
  · intro x hx
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    by_cases h : x ≤ (p : ℝ) - 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg (by nlinarith)]
      field_simp
      ring
  · intro y hy
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_g
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    by_cases h : y ≤ (p : ℝ) - 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg (by have := div_pos (sub_pos.mpr (lt_of_not_ge h)) hd; linarith)]
      field_simp
      ring

/-- The banked interval map is the identity on arcs `0, …, p - 2` and stretches
the last arc `[p - 1, p]` linearly onto `[p - 1, L]`. -/
lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_formulas
    (p L : ℕ) (hp : 2 ≤ p) (hL : p - 1 < L) :
    (∀ m, m + 1 < p → ∀ t : Set.Icc (0 : ℝ) 1,
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f p L
        ((m : ℝ) + t) = m + t) ∧
    (∀ t : Set.Icc (0 : ℝ) 1,
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f p L
        ((p : ℝ) - 1 + t) = (p : ℝ) - 1 + t * ((L : ℝ) - ((p : ℝ) - 1))) := by
  constructor
  · intro m hm t
    have hm2 : ((m + 1 + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast (show m + 1 + 1 ≤ p from hm)
    push_cast at hm2
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    rw [if_pos (by linarith [t.2.2])]
  · intro t
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
    by_cases h0 : (p : ℝ) - 1 + t ≤ p - 1
    · have ht : (t : ℝ) = 0 := le_antisymm (by linarith) t.2.1
      rw [if_pos h0, ht]; ring
    · rw [if_neg h0]; ring

/-- The banked interval homeomorphism descends to a circle homeomorphism
(`PolygonMoves.equivariantLift_of_interval`, `equivariantCircleLift_homeomorph`). -/
lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_lift
    (p L : ℕ) (hp : 2 ≤ p) (hL : p - 1 < L) :
    ∃ g : Circle ≃ₜ Circle, ∀ x ∈ Set.Icc (0 : ℝ) p,
      g (AddCircle.toCircle (x : AddCircle (p : ℝ))) =
        AddCircle.toCircle
          ((standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
            p L x : ℝ) : AddCircle (L : ℝ)) := by
  obtain ⟨hfc, hgc, hf0, hfp, hg0, hgL, hfm, hgm, hl, hr⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_props
      p L hp hL
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hQ : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨F, hF⟩ := PolygonMoves.equivariantLift_of_interval (p : ℝ) L hP hQ _ _
    hfc hgc hf0 hfp hg0 hgL hfm hgm hl hr
  obtain ⟨g, hg⟩ := PolygonMoves.equivariantCircleLift_homeomorph (p : ℝ) L hP hQ F
  exact ⟨g, fun x hx => by rw [hg, hF x hx]⟩

/-- **Leaf (geometry).**  The circle reparametrization for the left half: the `p`-gon
boundary onto the boundary parameter of `cutOldA (p + q - 2) 0 (p - 1)`,
piecewise linear in the angle.  Rotate by `-(i + 1)` arcs, then apply `_aux_lift`. -/
lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL
    (p q i : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hi : i < p) :
    let L := p + q - 2
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ m, m + 1 < p → ∀ t,
        ρ ⟨edgePoint p ((i + 1 + m) % p) t,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint p ((i + 1 + m) % p) t⟩ =
          PolygonMoves.cutEdgeCircle L m t) ∧
      (∀ t, ρ ⟨edgePoint p i t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint p i t⟩ =
        PolygonMoves.cutChordParamA L 0 (p - 1) t) := by
  dsimp only
  have hLp : p - 1 < p + q - 2 := by omega
  obtain ⟨g, hg⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_lift
      p (p + q - 2) hp hLp
  obtain ⟨hfa, hfi⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_formulas
      p (p + q - 2) hp hLp
  have hP : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hπ := Real.pi_pos
  let r : Circle := Circle.exp (2 * Real.pi / p * ((i : ℝ) + 1))
  let ρ : Circle ≃ₜ Circle := (Homeomorph.mulLeft r⁻¹).trans g
  have hexp : ∀ a b : ℝ, ∀ k : ℤ, a = b + k * (2 * Real.pi) →
      Circle.exp a = Circle.exp b := by
    intro a b k h
    rw [h, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  -- ρ at the point with edge coordinate `a ≡ x + i + 1 (mod p)` is `f x`.
  have hρ : ∀ x ∈ Set.Icc (0 : ℝ) p, ∀ (a : ℝ) (k : ℤ), a = x + ((i : ℝ) + 1) + k * p →
      ρ (AddCircle.toCircle (a : AddCircle (p : ℝ))) =
        AddCircle.toCircle
          ((standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL_aux_f
            p (p + q - 2) x : ℝ) : AddCircle ((p + q - 2 : ℕ) : ℝ)) := by
    intro x hx a k ha
    rw [← hg x hx]
    change g (r⁻¹ * _) = _
    congr 1
    rw [AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk, ← Circle.exp_neg,
      ← Circle.exp_add]
    exact hexp _ _ k (by rw [ha]; field_simp; ring)
  refine ⟨ρ, ?_, ?_⟩
  · intro m hm t
    change ρ (edgePointCircle p ((i + 1 + m) % p) t) = edgePointCircle (p + q - 2) m t
    have hm2 : ((m + 1 + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast (show m + 1 + 1 ≤ p from hm)
    push_cast at hm2
    have hmd : (((i + 1 + m) % p : ℕ) : ℝ) + p * ((i + 1 + m) / p : ℕ) = i + 1 + m := by
      exact_mod_cast Nat.mod_add_div (i + 1 + m) p
    rw [edgePointCircle_eq_toCircle, edgePointCircle_eq_toCircle]
    simp only [← AddCircle.coe_add]
    rw [hρ ((m : ℝ) + t) ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
        ((((i + 1 + m) % p : ℕ) : ℝ) + t)
        (-(((i + 1 + m) / p : ℕ) : ℤ))
        (by rw [Int.cast_neg, Int.cast_natCast]; linarith),
      hfa m hm t]
  · intro t
    change ρ (edgePointCircle p i t) = _
    rw [edgePointCircle_eq_toCircle]
    simp only [← AddCircle.coe_add]
    rw [hρ ((p : ℝ) - 1 + t) ⟨by linarith [t.2.1], by linarith [t.2.2]⟩ ((i : ℝ) + t) (-1)
        (by push_cast; ring),
      hfi t]
    unfold PolygonMoves.cutChordParamA PolygonMoves.cutAlpha
    rw [AddCircle.homeomorphCircle'_apply_mk, AddCircle.toCircle_apply_mk]
    have hc1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((p + q - 2 : ℕ) : ℝ) = (p : ℝ) + q - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hLpos : (0 : ℝ) < (p : ℝ) + q - 2 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    rw [hc1, hc2]
    congr 1
    field_simp
    ring


/-- **Leaf (geometry).**  The circle reparametrization for the right half: the `q`-gon
boundary onto the boundary parameter of `cutOldB (p + q - 2) 0 (p - 1)`. -/
def standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
    (p q : ℕ) (x : ℝ) : ℝ :=
  if x ≤ q - 1 then x else (q - 1) + (x - (q - 1)) * (p - 1)

def standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g
    (p q : ℕ) (y : ℝ) : ℝ :=
  if y ≤ q - 1 then y else (q - 1) + (y - (q - 1)) / (p - 1)

lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_props
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    let L : ℝ := p + q - 2
    let f := standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f p q
    let g := standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g p q
    Continuous f ∧ Continuous g ∧ f 0 = 0 ∧ f q = L ∧ g 0 = 0 ∧ g L = q ∧
      Set.MapsTo f (Set.Icc 0 q) (Set.Icc 0 L) ∧
      Set.MapsTo g (Set.Icc 0 L) (Set.Icc 0 q) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) q, g (f x) = x) ∧
      (∀ y ∈ Set.Icc (0 : ℝ) L, f (g y) = y) := by
  dsimp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hp' : (0 : ℝ) < p - 1 := by linarith
  have hq' : (1 : ℝ) ≤ q := by linarith
  have hL : (p + q - 2 : ℝ) = (q : ℝ) - 1 + ((p : ℝ) - 1) := by
    norm_num at *; linarith
  have hf : Continuous (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f p q) := by
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro x hx; rw [hx]; ring
  have hg : Continuous (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g p q) := by
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro x hx; rw [hx]; field_simp; ring
  refine ⟨hf, hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f]; omega
  · rw [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f, if_neg (by linarith)]
    rw [hL]; field_simp; ring
  · simp [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g]; omega
  · rw [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g, if_neg (by rw [hL]; linarith)]
    rw [hL]; field_simp; ring
  · intro x hx
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
    split_ifs with h <;> constructor <;> rw [hL] at * <;> nlinarith [hx.1, hx.2]
  · intro y hy
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g
    split_ifs with h <;> constructor <;> rw [hL] at * <;>
      field_simp <;> nlinarith [hy.1, hy.2]
  · intro x hx
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g
    by_cases h : x ≤ (q : ℝ) - 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg (by nlinarith [hp'])]
      field_simp; ring
  · intro y hy
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
    unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g
    by_cases h : y ≤ (q : ℝ) - 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg (by field_simp; nlinarith [hp'])]
      field_simp; ring

lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR
    (p q j : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hj : j < q) :
    let L := p + q - 2
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ k, k + 1 < q → ∀ t,
        ρ ⟨edgePoint q ((j + 1 + k) % q) t,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint q ((j + 1 + k) % q) t⟩ =
          PolygonMoves.cutEdgeCircle L (p - 1 + k) t) ∧
      (∀ t, ρ ⟨edgePoint q j t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint q j t⟩ =
        PolygonMoves.cutChordParamB L 0 (p - 1) t) := by
  dsimp
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL' : (0 : ℝ) < p + q - 2 := by linarith
  obtain ⟨hfc, hgc, hf0, hfq, hg0, hgL, hfm, hgm, hleft, hright⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_props p q hp hq
  obtain ⟨F, hF⟩ := PolygonMoves.equivariantLift_of_interval (q : ℝ) (p + q - 2 : ℝ)
    hq' hL'
    (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f p q)
    (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_g p q)
    hfc hgc hf0 hfq hg0 hgL hfm hgm hleft hright
  obtain ⟨G, hG⟩ := PolygonMoves.equivariantCircleLift_homeomorph
    (q : ℝ) (p + q - 2 : ℝ) hq' hL' F
  let r : Circle := Circle.exp (-2 * Real.pi * (j + 1) / q)
  let s : Circle := Circle.exp (2 * Real.pi * (p - 1) / (p + q - 2))
  let ρ := ((Homeomorph.mulLeft r).trans G).trans (Homeomorph.mulLeft s)
  have hsource : ∀ k, k < q → ∀ t : Set.Icc (0 : ℝ) 1,
      @HMul.hMul Circle Circle Circle _ r ⟨(edgePoint q ((j + 1 + k) % q) t : ℂ),
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint q ((j + 1 + k) % q) t⟩ =
        AddCircle.toCircle ((k + t.1 : ℝ) : AddCircle (q : ℝ)) := by
    intro k hk t
    have hpt : (⟨(edgePoint q ((j + 1 + k) % q) t : ℂ),
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint q ((j + 1 + k) % q) t⟩ : Circle) =
        Circle.exp (2 * Real.pi * ((((j + 1 + k) % q : ℕ) : ℝ) + t.1) / q) := by
      apply Subtype.ext
      change Complex.exp (Complex.I * (2 * Real.pi * ((((j + 1 + k) % q : ℕ) : ℝ) + t.1) / q)) =
        ((Circle.exp (2 * Real.pi * ((((j + 1 + k) % q : ℕ) : ℝ) + t.1) / q) : Circle) : ℂ)
      rw [Circle.coe_exp]
      push_cast
      ring_nf
    rw [hpt, AddCircle.toCircle_apply_mk, ← Circle.exp_add]
    have hmod : (j + 1 + k) % q + q * ((j + 1 + k) / q) = j + 1 + k :=
      Nat.mod_add_div _ _
    have hmod' : ((((j + 1 + k) % q : ℕ) : ℝ) +
        q * (((j + 1 + k) / q : ℕ) : ℝ)) = j + 1 + k := by exact_mod_cast hmod
    have hr : ((((j + 1 + k) % q : ℕ) : ℝ)) =
        j + 1 + k - q * (((j + 1 + k) / q : ℕ) : ℝ) := by linarith
    have heq : -2 * Real.pi * (j + 1) / (q : ℝ) +
          2 * Real.pi * ((((j + 1 + k) % q : ℕ) : ℝ) + t.1) / q =
        2 * Real.pi / q * (k + t.1) +
          ((-(((j + 1 + k) / q : ℕ) : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hr, Int.cast_neg, Int.cast_natCast]
      field_simp
      ring
    rw [heq, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have hρ : ∀ k, k < q → ∀ t : Set.Icc (0 : ℝ) 1,
      ρ ⟨edgePoint q ((j + 1 + k) % q) t,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint q ((j + 1 + k) % q) t⟩ =
        AddCircle.toCircle
          ((standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
            p q (k + t.1) + (p - 1) : ℝ) : AddCircle (p + q - 2 : ℝ)) := by
    intro k hk t
    change s * G (r * _) = _
    rw [hsource k hk t, hG, hF]
    · rw [AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk]
      change Circle.exp _ * Circle.exp _ = Circle.exp _
      rw [← Circle.exp_add]
      congr 1
      field_simp
      ring
    · have hkq : (k : ℝ) + 1 ≤ q := by exact_mod_cast (show k + 1 ≤ q by omega)
      exact ⟨by linarith [t.2.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)], by linarith [t.2.2]⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro k hk t
    rw [hρ k (by omega) t]
    rw [PolygonMoves.cutBoundaryData_concrete_aux_edge_circle]
    rw [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f,
      if_pos (by
        have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        have hkR : (k : ℝ) + 1 ≤ q - 1 := by rw [← hqsub]; exact_mod_cast (show k + 1 ≤ q - 1 by omega)
        linarith [t.2.2])]
    rw [AddCircle.toCircle_apply_mk, AddCircle.homeomorphCircle'_apply_mk]
    congr 1
    unfold PolygonMoves.cutAlpha
    norm_num [Nat.cast_sub (by omega : 2 ≤ p + q), Nat.cast_sub (by omega : 1 ≤ p)]
    field_simp
    ring
  · intro t
    have hjk : (q - 1) < q := by omega
    have he : (j + 1 + (q - 1)) % q = j := by
      have hq1 : 1 ≤ q := by omega
      rw [show j + 1 + (q - 1) = j + q by omega, Nat.add_mod, Nat.mod_self,
        add_zero, Nat.mod_mod]
      exact Nat.mod_eq_of_lt hj
    rw [show (⟨edgePoint q j t, _⟩ : Circle) =
      ⟨edgePoint q ((j + 1 + (q - 1)) % q) t,
        by simpa [Circle, Submonoid.unitSphere] using
          norm_edgePoint q ((j + 1 + (q - 1)) % q) t⟩ by simp [he]]
    rw [hρ (q - 1) hjk t]
    have hf_last :
        standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
          p q ((q - 1 : ℕ) + t.1) =
          (q - 1 : ℕ) + t.1 * ((p : ℝ) - 1) := by
      unfold standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR_aux_f
      have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      split_ifs with h
      · have ht : t.1 = 0 := by rw [hqcast] at h; linarith [t.2.1]
        rw [ht]; ring
      · rw [hqcast]; ring
    rw [hf_last]
    rw [AddCircle.toCircle_apply_mk]
    unfold PolygonMoves.cutChordParamB
    rw [AddCircle.homeomorphCircle'_apply_mk]
    congr 1
    unfold PolygonMoves.cutAlpha
    norm_num [Nat.cast_sub (by omega : 2 ≤ p + q), Nat.cast_sub (by omega : 1 ≤ p),
      Nat.cast_sub (by omega : 1 ≤ q)]
    field_simp
    ring

/-- **Leaf (geometry, assembly).**  Given the two circle reparametrizations
(`_aux_reparamL`, `_aux_reparamR`), the half charts exist: `β = cutOldA ∘ ρL`
and `cutOldB ∘ ρR` with the cone chart `cutAndPaste_aux_boundary_chart`,
restricted to `Disk`; seam and cover from `cutPiece_union_disjoint`, interiors
from `interior K ⊆ ball`. -/
lemma standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_assemble
    (p q i j : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hi : i < p) (hj : j < q)
    (ρL ρR : Circle ≃ₜ Circle)
    (hLedge : ∀ m, m + 1 < p → ∀ t,
      ρL ⟨edgePoint p ((i + 1 + m) % p) t,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint p ((i + 1 + m) % p) t⟩ =
        PolygonMoves.cutEdgeCircle (p + q - 2) m t)
    (hLchord : ∀ t, ρL ⟨edgePoint p i t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint p i t⟩ =
        PolygonMoves.cutChordParamA (p + q - 2) 0 (p - 1) t)
    (hRedge : ∀ k, k + 1 < q → ∀ t,
      ρR ⟨edgePoint q ((j + 1 + k) % q) t,
          by simpa [Circle, Submonoid.unitSphere] using
            norm_edgePoint q ((j + 1 + k) % q) t⟩ =
        PolygonMoves.cutEdgeCircle (p + q - 2) (p - 1 + k) t)
    (hRchord : ∀ t, ρR ⟨edgePoint q j t,
          by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint q j t⟩ =
        PolygonMoves.cutChordParamB (p + q - 2) 0 (p - 1) t) :
    ∃ hL hR : Disk → Disk,
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
        p q i j hL hR := by
  let L := p + q - 2
  let P := PolygonMoves.cutPoint L 0
  let Q := PolygonMoves.cutPoint L (p - 1)
  have hpq : 0 < p - 1 := by omega
  have hqL : p - 1 < L := by dsimp [L]; omega
  have hPQ : P ≠ Q := by
    exact PolygonMoves.cutPoint_ne hpq (by dsimp [L]; omega)
  have hnP : ‖P‖ = 1 := PolygonMoves.cutPoint_norm _ _
  have hnQ : ‖Q‖ = 1 := PolygonMoves.cutPoint_norm _ _
  let βL : Circle → ℂ := fun z => PolygonMoves.cutOldA L 0 (p - 1) (ρL z)
  let βR : Circle → ℂ := fun z => PolygonMoves.cutOldB L 0 (p - 1) (ρR z)
  obtain ⟨cL, hcL⟩ := PolygonMoves.cutPiece_interior_nonempty hnP hnQ hPQ
  obtain ⟨cR, hcR⟩ := PolygonMoves.cutPiece_interior_nonempty hnQ hnP hPQ.symm
  have hrL := PolygonMoves.cutOldA_range hpq hqL
    (PolygonMoves.cutPiece_frontier hnP hnQ hPQ) PolygonMoves.cutCross_exp
  have hrR := PolygonMoves.cutOldB_range hpq hqL
    (PolygonMoves.cutPiece_frontier hnQ hnP hPQ.symm) PolygonMoves.cutCross_exp
  obtain ⟨φL, hφL⟩ := PolygonMoves.cutAndPaste_aux_boundary_chart
    (PolygonMoves.cutPiece P Q) cL (PolygonMoves.cutPiece_convex_compact P Q).1
    (PolygonMoves.cutPiece_convex_compact P Q).2 hcL βL
    ((PolygonMoves.cutOldA_continuous hpq hqL).comp ρL.continuous)
    ((PolygonMoves.cutOldA_injective hpq hqL).comp ρL.injective)
    (by simp only [βL, Set.range_comp']; rw [ρL.surjective.range_eq, Set.image_univ]; exact hrL)
  obtain ⟨φR, hφR⟩ := PolygonMoves.cutAndPaste_aux_boundary_chart
    (PolygonMoves.cutPiece Q P) cR (PolygonMoves.cutPiece_convex_compact Q P).1
    (PolygonMoves.cutPiece_convex_compact Q P).2 hcR βR
    ((PolygonMoves.cutOldB_continuous hpq hqL).comp ρR.continuous)
    ((PolygonMoves.cutOldB_injective hpq hqL).comp ρR.injective)
    (by simp only [βR, Set.range_comp']; rw [ρR.surjective.range_eq, Set.image_univ]; exact hrR)
  let fL : Disk → Disk := fun z => ⟨φL z, by
    have hz : φL z ∈ PolygonMoves.cutPiece P Q := by
      rw [← hφL.2.2.1]
      exact ⟨z, z.2, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.1⟩
  let fR : Disk → Disk := fun z => ⟨φR z, by
    have hz : φR z ∈ PolygonMoves.cutPiece Q P := by
      rw [← hφR.2.2.1]
      exact ⟨z, z.2, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.1⟩
  refine ⟨fL, fR, ?_⟩
  constructor
  · exact Continuous.subtype_mk (hφL.1.comp continuous_subtype_val) _
  · exact Continuous.subtype_mk (hφR.1.comp continuous_subtype_val) _
  · intro x y h
    apply Subtype.ext
    apply hφL.2.1 x.2 y.2
    exact congrArg Subtype.val h
  · intro x y h
    apply Subtype.ext
    apply hφR.2.1 x.2 y.2
    exact congrArg Subtype.val h
  · intro z
    have hz : (z : ℂ) ∈ PolygonMoves.cutPiece P Q ∪ PolygonMoves.cutPiece Q P := by
      rw [(PolygonMoves.cutPiece_union_disjoint P Q hPQ).1]
      exact z.2
    rcases hz with hz | hz
    · rw [← hφL.2.2.1] at hz
      rcases hz with ⟨x, hx, he⟩
      exact Or.inl ⟨⟨x, hx⟩, Subtype.ext he⟩
    · rw [← hφR.2.2.1] at hz
      rcases hz with ⟨x, hx, he⟩
      exact Or.inr ⟨⟨x, hx⟩, Subtype.ext he⟩
  · intro x y
    constructor
    · intro heq
      have hxpiece : φL x ∈ PolygonMoves.cutPiece P Q := by
        rw [← hφL.2.2.1]; exact ⟨x, x.2, rfl⟩
      have hypiece : φR y ∈ PolygonMoves.cutPiece Q P := by
        rw [← hφR.2.2.1]; exact ⟨y, y.2, rfl⟩
      have hxy : φL x = φR y := congrArg Subtype.val heq
      have hnx : ‖(x : ℂ)‖ = 1 := by
        have hxle : ‖(x : ℂ)‖ ≤ 1 := by
          have hx := x.2
          rw [Metric.mem_closedBall, dist_zero_right] at hx
          exact hx
        apply le_antisymm hxle
        by_contra h
        have hlt : ‖(x : ℂ)‖ < 1 := lt_of_not_ge h
        have hi := hφL.2.2.2.2 x hlt
        have : φL x ∈ interior (PolygonMoves.cutPiece P Q) ∩
            PolygonMoves.cutPiece Q P := ⟨hi, hxy ▸ hypiece⟩
        rw [(PolygonMoves.cutPiece_union_disjoint P Q hPQ).2] at this
        exact this
      have hny : ‖(y : ℂ)‖ = 1 := by
        have hyle : ‖(y : ℂ)‖ ≤ 1 := by
          have hy := y.2
          rw [Metric.mem_closedBall, dist_zero_right] at hy
          exact hy
        apply le_antisymm hyle
        by_contra h
        have hlt : ‖(y : ℂ)‖ < 1 := lt_of_not_ge h
        have hi := hφR.2.2.2.2 y hlt
        have : φR y ∈ interior (PolygonMoves.cutPiece Q P) ∩
            PolygonMoves.cutPiece P Q := ⟨hi, hxy ▸ hxpiece⟩
        rw [(PolygonMoves.cutPiece_union_disjoint Q P hPQ.symm).2] at this
        exact this
      let zx : Circle := ⟨x, by simpa [Circle, Submonoid.unitSphere] using hnx⟩
      let zy : Circle := ⟨y, by simpa [Circle, Submonoid.unitSphere] using hny⟩
      have hbx : φL x = βL zx := by simpa [zx] using hφL.2.2.2.1 zx
      have hby : φR y = βR zy := by simpa [zy] using hφR.2.2.2.1 zy
      have hfront : φL x ∈ frontier (PolygonMoves.cutPiece P Q) := by
        rw [← hrL]; exact ⟨ρL zx, by simpa [βL] using hbx.symm⟩
      rw [PolygonMoves.cutPiece_frontier hnP hnQ hPQ] at hfront
      have hseg : φL x ∈ segment ℝ P Q := by
        rcases hfront with hc | hs
        · have hb := hypiece
          change ‖φR y‖ ≤ 1 ∧
            PolygonMoves.cutCross (P - Q) (φR y - Q) ≤ 0 at hb
          have hcross := PolygonMoves.cutPiece_union_disjoint_aux_cross P Q (φL x)
          rw [← hxy] at hb
          have hz : PolygonMoves.cutCross (Q - P) (φL x - P) = 0 := by
            linarith [hc.2, hb.2, hcross]
          exact (PolygonMoves.cutPiece_frontier_aux_chord hnP hnQ hPQ
            (PolygonMoves.cutPiece_frontier_aux_line hPQ)).mp ⟨hc.1.le, hz⟩
        · exact hs
      rcases hseg with ⟨a, b, ha, hb, hab, hval⟩
      let t : Set.Icc (0 : ℝ) 1 := ⟨a, by constructor <;> linarith⟩
      have hchA : φL x = PolygonMoves.cutChordA L 0 (p - 1) t := by
        rw [← hval]
        simp [PolygonMoves.cutChordA, t, P, Q, smul_eq_mul]
        have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
        linear_combination habC * Q
      obtain ⟨hA, -, hB⟩ := PolygonMoves.cutBoundary_old_fields hpq hqL
      have hxrho : ρL zx = PolygonMoves.cutChordParamA L 0 (p - 1) t := by
        apply PolygonMoves.cutOldA_injective hpq hqL
        rw [hA]
        simpa [βL] using hbx.symm.trans hchA
      have hyt : ρR zy = PolygonMoves.cutChordParamB L 0 (p - 1) (reverseIcc t) := by
        apply PolygonMoves.cutOldB_injective hpq hqL
        rw [hB]
        calc
          PolygonMoves.cutOldB L 0 (p - 1) (ρR zy) = φR y := hby.symm
          _ = φL x := hxy.symm
          _ = PolygonMoves.cutChordA L 0 (p - 1) t := hchA
          _ = PolygonMoves.cutChordB L 0 (p - 1) (reverseIcc t) :=
            PolygonMoves.cut_retransfer_consistency_aux_chords t
      refine ⟨t, ?_, ?_⟩
      ·
        have := ρL.injective (hxrho.trans (hLchord t).symm)
        have hv := congrArg (fun z : Circle => (z : ℂ)) this
        apply Subtype.ext
        exact hv
      ·
        have := ρR.injective (hyt.trans (hRchord (reverseIcc t)).symm)
        have hv := congrArg (fun z : Circle => (z : ℂ)) this
        apply Subtype.ext
        exact hv
    · rintro ⟨t, rfl, rfl⟩
      apply Subtype.ext
      change φL _ = φR _
      let zL : Circle := ⟨edgePoint p i t,
        by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint p i t⟩
      let zR : Circle := ⟨edgePoint q j (reverseIcc t),
        by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint q j (reverseIcc t)⟩
      have hbL := hφL.2.2.2.1 zL
      have hbR := hφR.2.2.2.1 zR
      change φL (edgePoint p i t) = βL zL at hbL
      change φR (edgePoint q j (reverseIcc t)) = βR zR at hbR
      rw [hbL, hbR]
      dsimp [βL, βR]
      rw [hLchord, hRchord]
      obtain ⟨hA, -, hB⟩ := PolygonMoves.cutBoundary_old_fields hpq hqL
      rw [hA, hB, PolygonMoves.cut_retransfer_consistency_aux_chords]
      congr 2
  · intro m hm t
    apply Subtype.ext
    change φL _ = _
    let z : Circle := ⟨edgePoint p ((i + 1 + m) % p) t,
      by simpa [Circle, Submonoid.unitSphere] using norm_edgePoint p ((i + 1 + m) % p) t⟩
    have hb := hφL.2.2.2.1 z
    change φL (edgePoint p ((i + 1 + m) % p) t) = βL z at hb
    rw [hb]
    dsimp [βL]
    rw [hLedge m hm]
    exact PolygonMoves.cutBoundaryData_concrete_aux_oldA_arc t hpq hqL (by omega) (by omega)
  · intro m hm1 hm2 t
    apply Subtype.ext
    change φR _ = _
    let z : Circle := ⟨edgePoint q ((j + 1 + (m + 1 - p)) % q) t,
      by simpa [Circle, Submonoid.unitSphere] using
        norm_edgePoint q ((j + 1 + (m + 1 - p)) % q) t⟩
    have hb := hφR.2.2.2.1 z
    change φR (edgePoint q ((j + 1 + (m + 1 - p)) % q) t) = βR z at hb
    rw [hb]
    dsimp [βR]
    let k := m + 1 - p
    have hk : k + 1 < q := by dsimp [k]; omega
    rw [hRedge k hk]
    obtain ⟨-, hB, -⟩ := PolygonMoves.cutBoundary_old_fields hpq hqL
    rw [show p - 1 + k = m by dsimp [k]; omega]
    exact hB m t (Or.inl ⟨by omega, by simpa [L] using hm2⟩)
  · intro x hx
    have hi := hφL.2.2.2.2 x hx
    rw [PolygonMoves.cutPiece_frontier_aux_interior hPQ] at hi
    exact hi.1
  · intro y hy
    have hi := hφR.2.2.2.2 y hy
    rw [PolygonMoves.cutPiece_frontier_aux_interior hPQ.symm] at hi
    exact hi.1

/-- The half charts exist (assembly of `_aux_reparamL`, `_aux_reparamR` and
`_aux_assemble`). -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves
    (p q i j : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hi : i < p) (hj : j < q) :
    ∃ hL hR : Disk → Disk,
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
        p q i j hL hR := by
  obtain ⟨ρL, hLedge, hLchord⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamL
      p q i hp hq hi
  obtain ⟨ρR, hRedge, hRchord⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_reparamR
      p q j hp hq hj
  exact standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves_aux_assemble
    p q i j hp hq hi hj ρL ρR hLedge hLchord hRedge hRchord

open Classical in
/-- The face of `C'` that an unmerged face of `C` became. -/
def standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (f : Fin C.faceCount) : Fin C'.faceCount :=
  if h : ∃ k, D.old k = f then h.choose else D.merged

/-- The disks of `C` sent to the disks of `C'`: the two glued disks go onto
the two halves of the merged disk, every other disk is kept. -/
def standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hL hR : Disk → Disk) :
    (Σ _ : Fin C.faceCount, Disk) → Σ _ : Fin C'.faceCount, Disk :=
  fun x =>
    if x.1 = s.1 then ⟨D.merged, hL x.2⟩
    else if x.1 = (C.pair s).1 then ⟨D.merged, hR x.2⟩
    else ⟨standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D x.1, x.2⟩

/-- The step along `s` becomes equality: equal images of the two glued disks
come from a `C.Rel` step along `s` (banked by lemma-2). -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_seam
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) {hL hR : Disk → Disk}
    (hH : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
      (C.sides s.1) (C.sides (C.pair s).1) s.2 (C.pair s).2 hL hR)
    (x z : Disk)
    (heq : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
        ⟨s.1, x⟩ =
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
        ⟨(C.pair s).1, z⟩) :
    Relation.EqvGen C.Rel (⟨s.1, x⟩ : Σ _ : Fin C.faceCount, Disk)
      ⟨(C.pair s).1, z⟩ := by
  have hfaces : s.1 ≠ (C.pair s).1 := by
    intro h
    have := D.old_ne D.merged
    exact this (D.old_merged.trans h)
  have him : hL x = hR z := by
    simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
      hfaces, hfaces.symm] using congrArg Sigma.snd heq
  obtain ⟨t, rfl, rfl⟩ := (hH.seam x z).mp him
  apply Relation.EqvGen.rel
  refine ⟨s, t, rfl, ?_⟩
  simp only [PolygonComplex.pairedParameter]
  rw [if_neg (Ne.symm (hor s))]

/-- **Leaf (fibres, faces).**  An unmerged face of `C` is `old` of a face of `C'`
other than `merged`, and `oldInv` finds it: `old` is injective, misses
`(C.pair s).1`, and `C'` has one face fewer (`faceCount_succ`), so its range is
every other face. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_oldInv
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (f : Fin C.faceCount) (h1 : f ≠ s.1) (h2 : f ≠ (C.pair s).1) :
    D.old (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f) = f ∧
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f ≠ D.merged := by
  have hold_surj : ∀ x : Fin C.faceCount, x ≠ (C.pair s).1 →
      ∃ k : Fin C'.faceCount, D.old k = x := by
    intro x hx
    by_contra hnot
    let F : Fin C'.faceCount ⊕ Fin 2 → Fin C.faceCount
      | Sum.inl k => D.old k
      | Sum.inr j => if j = 0 then (C.pair s).1 else x
    have hF : Function.Injective F := by
      intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b => exact congrArg Sum.inl (D.old_injective hab)
          | inr b =>
              exfalso
              simp only [F] at hab
              split at hab
              · exact D.old_ne a hab
              · exact hnot ⟨a, hab⟩
      | inr a =>
          cases b with
          | inl b =>
              exfalso
              simp only [F] at hab
              split at hab
              · exact D.old_ne b hab.symm
              · exact hnot ⟨b, hab.symm⟩
          | inr b =>
              apply congrArg Sum.inr
              fin_cases a
              · fin_cases b
                · rfl
                · exfalso
                  exact hx (by simpa [F] using hab.symm)
              · fin_cases b
                · exfalso
                  exact hx (by simpa [F] using hab)
                · rfl
    have hc := Fintype.card_le_of_injective F hF
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    have hcount := D.faceCount_succ
    omega
  have hex := hold_surj f h2
  simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv,
    dif_pos hex]
  refine ⟨Classical.choose_spec hex, ?_⟩
  intro heq
  apply h1
  exact (Classical.choose_spec hex).symm.trans
    ((congrArg D.old heq).trans D.old_merged)

/-- **Leaf (fibres, sides).**  Each side `v` of `C'` is the image of side
`toOld v` of `C`, with the arc parameter kept.  Unmerged faces: `toOld_fst`,
`toOld_val`, `sides_old` and `oldInv (old k) = k` (from `old_injective`).
Merged face: `toOld_merged_fst`, `toOld_merged_val`, then `hH.edge_left` or
`hH.edge_right`, with `sides_merged` for `C'.sides merged = p + q - 2`. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_edgeImage
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    {hL hR : Disk → Disk}
    (hH : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
      (C.sides s.1) (C.sides (C.pair s).1) s.2 (C.pair s).2 hL hR)
    (v : C'.Side) (t : Set.Icc (0 : ℝ) 1) :
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
        ⟨(D.toOld v).1, edgePoint (C.sides (D.toOld v).1) (D.toOld v).2 t⟩ =
      ⟨v.1, edgePoint (C'.sides v.1) v.2 t⟩ := by
  by_cases hv : v.1 = D.merged
  · obtain ⟨vf, m⟩ := v
    dsimp only at hv ⊢
    subst vf
    have hsizes : C'.sides D.merged =
        C.sides s.1 + C.sides (C.pair s).1 - 2 := by
      have := D.sides_merged
      omega
    by_cases hm : m.val + 1 < C.sides s.1
    · have hfst : (D.toOld ⟨D.merged, m⟩).1 = s.1 := by
        simpa [hm] using D.toOld_merged_fst m
      have hval : (D.toOld ⟨D.merged, m⟩).2.val =
          (s.2.val + 1 + m.val) % C.sides s.1 := by
        simpa [hm] using D.toOld_merged_val m
      have hedge := hH.edge_left m.val hm t
      have hinput : (⟨(D.toOld ⟨D.merged, m⟩).1,
          edgePoint (C.sides (D.toOld ⟨D.merged, m⟩).1)
            (D.toOld ⟨D.merged, m⟩).2 t⟩ : Σ _ : Fin C.faceCount, Disk) =
          ⟨s.1, edgePoint (C.sides s.1)
            ((s.2.val + 1 + m.val) % C.sides s.1) t⟩ := by
        refine @Sigma.ext (Fin C.faceCount) (fun _ => Disk) _ _ hfst ?_
        apply heq_of_eq
        apply Subtype.ext
        simp only [edgePoint, Subtype.coe_eta, Subtype.coe_mk]
        rw [hval, hfst]
      rw [hinput]
      simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
        if_pos]
      rw [hedge, ← hsizes]
    · have hfst : (D.toOld ⟨D.merged, m⟩).1 = (C.pair s).1 := by
        simpa [hm] using D.toOld_merged_fst m
      have hval : (D.toOld ⟨D.merged, m⟩).2.val =
          ((C.pair s).2.val + 1 + (m.val + 1 - C.sides s.1)) %
            C.sides (C.pair s).1 := by
        simpa [hm] using D.toOld_merged_val m
      have hlo : C.sides s.1 ≤ m.val + 1 := by omega
      have hhi : m.val < C.sides s.1 + C.sides (C.pair s).1 - 2 := by
        simpa [hsizes] using m.isLt
      have hedge := hH.edge_right m.val hlo hhi t
      have hinput : (⟨(D.toOld ⟨D.merged, m⟩).1,
          edgePoint (C.sides (D.toOld ⟨D.merged, m⟩).1)
            (D.toOld ⟨D.merged, m⟩).2 t⟩ : Σ _ : Fin C.faceCount, Disk) =
          ⟨(C.pair s).1, edgePoint (C.sides (C.pair s).1)
            (((C.pair s).2.val + 1 + (m.val + 1 - C.sides s.1)) %
              C.sides (C.pair s).1) t⟩ := by
        refine @Sigma.ext (Fin C.faceCount) (fun _ => Disk) _ _ hfst ?_
        apply heq_of_eq
        apply Subtype.ext
        simp only [edgePoint, Subtype.coe_eta, Subtype.coe_mk]
        rw [hval, hfst]
      rw [hinput]
      have hne : (C.pair s).1 ≠ s.1 := by
        intro h
        exact D.old_ne D.merged (D.old_merged.trans h.symm)
      simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
        if_neg hne, if_pos]
      rw [hedge, ← hsizes]
  · have hfst := D.toOld_fst v hv
    have hval := D.toOld_val v hv
    have hsides := D.sides_old v.1 hv
    have hn1 : (D.toOld v).1 ≠ s.1 := by
      rw [hfst]
      intro h
      exact hv (D.old_injective (h.trans D.old_merged.symm))
    have hn2 : (D.toOld v).1 ≠ (C.pair s).1 := by
      rw [hfst]
      exact D.old_ne v.1
    have hinv : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D
        (D.old v.1) = v.1 := by
      simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv]
      split
      · rename_i hex
        exact D.old_injective (Classical.choose_spec hex)
      · rename_i h
        exact False.elim (h ⟨v.1, rfl⟩)
    simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
      if_neg hn1, if_neg hn2]
    have hinv' : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D
        (D.toOld v).1 = v.1 := by rw [hfst]; exact hinv
    apply Sigma.ext hinv'
    apply heq_of_eq
    apply Subtype.ext
    simp only [edgePoint, Subtype.coe_eta, Subtype.coe_mk]
    rw [hval, hfst]
    congr 4
    exact_mod_cast hsides.symm

/-- **Leaf (fibres, kernel).**  Points of the disks of `C` with the same image are
identified in `C`: within one glued disk by `hH.injective_left`/`_right`, across
the two glued disks by `_aux_seam`, on unmerged disks by `hfaces` (their faces
are distinct and never `merged`). -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_kernel
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) {hL hR : Disk → Disk}
    (hH : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
      (C.sides s.1) (C.sides (C.pair s).1) s.2 (C.pair s).2 hL hR)
    (hfaces : ∀ f, f ≠ s.1 → f ≠ (C.pair s).1 →
      D.old (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f) = f ∧
        standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f ≠ D.merged)
    (y y' : Σ _ : Fin C.faceCount, Disk)
    (heq : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y =
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y') :
    Relation.EqvGen C.Rel y y' := by
  rcases y with ⟨f, x⟩
  rcases y' with ⟨g, z⟩
  have hne : s.1 ≠ (C.pair s).1 := by
    have h := D.old_ne D.merged
    rwa [D.old_merged] at h
  by_cases hf : f = s.1
  · subst f
    by_cases hg : g = s.1
    · subst g
      have hx : x = z := hH.injective_left (by
        simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
          hne] using congrArg Sigma.snd heq)
      subst z
      exact Relation.EqvGen.refl _
    · by_cases hg' : g = (C.pair s).1
      · subst g
        exact standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_seam
          D hor hH x z heq
      · have hgdata := hfaces g hg hg'
        have : D.merged =
            standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D g := by
          simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
            hg, hg'] using congrArg Sigma.fst heq
        exact False.elim (hgdata.2 this.symm)
  · by_cases hf' : f = (C.pair s).1
    · subst f
      by_cases hg : g = s.1
      · subst g
        exact (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_seam
          D hor hH z x heq.symm).symm
      · by_cases hg' : g = (C.pair s).1
        · subst g
          have hx : x = z := hH.injective_right (by
            simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
              hne.symm] using congrArg Sigma.snd heq)
          subst z
          exact Relation.EqvGen.refl _
        · have hgdata := hfaces g hg hg'
          have : D.merged =
              standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D g := by
            simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
              hne.symm, hg, hg'] using congrArg Sigma.fst heq
          exact False.elim (hgdata.2 this.symm)
    · by_cases hg : g = s.1
      · subst g
        have hfdata := hfaces f hf hf'
        have : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f =
            D.merged := by
          simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
            hf, hf'] using congrArg Sigma.fst heq
        exact False.elim (hfdata.2 this)
      · by_cases hg' : g = (C.pair s).1
        · subst g
          have hfdata := hfaces f hf hf'
          have : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f =
              D.merged := by
            simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
              hf, hf', hne.symm] using congrArg Sigma.fst heq
          exact False.elim (hfdata.2 this)
        · have hfdata := hfaces f hf hf'
          have hgdata := hfaces g hg hg'
          have hfg : f = g := by
            have hinv :
                standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f =
                  standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D g := by
              simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
                hf, hf', hg, hg'] using congrArg Sigma.fst heq
            exact hfdata.1.symm.trans ((congrArg D.old hinv).trans hgdata.1)
          subst g
          have hx : x = z := by
            simpa [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
              hf, hf'] using congrArg Sigma.snd heq
          subst z
          exact Relation.EqvGen.refl _

/-- **Leaf (fibres, forward step).**  A generating step of `C` maps to equality or
to one generating step of `C'`.  Along `s` or `C.pair s` the images are equal
(`hH.seam`; `hor` makes the paired parameter `reverseIcc`).  Along any other
side `u = toOld v` (`toOld_surj`), `himage` sends both ends onto the `C'` step
along `v`, matched by `pair_toOld` and `sign_toOld`. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_step
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) {hL hR : Disk → Disk}
    (hH : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
      (C.sides s.1) (C.sides (C.pair s).1) s.2 (C.pair s).2 hL hR)
    (himage : ∀ (v : C'.Side) (t : Set.Icc (0 : ℝ) 1),
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
          ⟨(D.toOld v).1, edgePoint (C.sides (D.toOld v).1) (D.toOld v).2 t⟩ =
        ⟨v.1, edgePoint (C'.sides v.1) v.2 t⟩)
    (x y : Σ _ : Fin C.faceCount, Disk) (hxy : C.Rel x y) :
    Relation.EqvGen C'.Rel
      (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR x)
      (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y) := by
  obtain ⟨u, t, rfl, rfl⟩ := hxy
  have hfaces : s.1 ≠ (C.pair s).1 := by
    intro h
    exact D.old_ne D.merged (D.old_merged.trans h)
  by_cases hu : u = s
  · subst u
    have heq :
        standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
            ⟨s.1, edgePoint (C.sides s.1) s.2 t⟩ =
          standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
            ⟨(C.pair s).1, edgePoint (C.sides (C.pair s).1) (C.pair s).2
              (C.pairedParameter s t)⟩ := by
      simp only [PolygonComplex.pairedParameter]
      rw [if_neg (Ne.symm (hor s))]
      simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge]
      simp only [if_true, if_false, hfaces, hfaces.symm]
      exact congrArg
        (fun z : Disk ↦ (⟨D.merged, z⟩ : Σ _ : Fin C'.faceCount, Disk))
        ((hH.seam _ _).2 ⟨t, rfl, rfl⟩)
    rw [heq]
    exact Relation.EqvGen.refl _
  by_cases hup : u = C.pair s
  · subst u
    have hpar : C.pairedParameter (C.pair s) t = reverseIcc t := by
      simp only [PolygonComplex.pairedParameter]
      rw [if_neg (Ne.symm (hor (C.pair s)))]
    have heq :
        standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
            ⟨(C.pair s).1, edgePoint (C.sides (C.pair s).1) (C.pair s).2 t⟩ =
          standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
            ⟨(C.pair (C.pair s)).1,
              edgePoint (C.sides (C.pair (C.pair s)).1) (C.pair (C.pair s)).2
                (C.pairedParameter (C.pair s) t)⟩ := by
      rw [C.pair_pair]
      simp only [hpar, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge]
      simp only [if_true, if_false, hfaces, hfaces.symm]
      exact congrArg
        (fun z : Disk ↦ (⟨D.merged, z⟩ : Σ _ : Fin C'.faceCount, Disk))
        ((hH.seam _ _).2 ⟨reverseIcc t, rfl,
          congrArg (edgePoint (C.sides (C.pair s).1) (C.pair s).2)
            (reverseIcc_reverseIcc t).symm⟩).symm
    rw [heq]
    exact Relation.EqvGen.refl _
  obtain ⟨v, hv⟩ := D.toOld_surj u hu hup
  apply Relation.EqvGen.rel
  refine ⟨v, t, ?_, ?_⟩
  · rw [← hv]
    exact himage v t
  · have hparam : C.pairedParameter u t = C'.pairedParameter v t := by
      simp only [PolygonComplex.pairedParameter]
      rw [D.sign_toOld, D.sign_toOld, D.pair_toOld, hv]
    rw [hparam, ← hv, ← D.pair_toOld]
    exact himage (C'.pair v) (C'.pairedParameter v t)

/-- **Leaf (fibres, reverse step).**  A generating step of `C'` along side `v`
lifts to the `C` step along `toOld v` (`himage` at both ends, `pair_toOld`,
`sign_toOld`); any preimages of its two ends are joined to those by `hker`. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_lift
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    {hL hR : Disk → Disk}
    (himage : ∀ (v : C'.Side) (t : Set.Icc (0 : ℝ) 1),
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
          ⟨(D.toOld v).1, edgePoint (C.sides (D.toOld v).1) (D.toOld v).2 t⟩ =
        ⟨v.1, edgePoint (C'.sides v.1) v.2 t⟩)
    (hker : ∀ y y' : Σ _ : Fin C.faceCount, Disk,
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y =
          standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y' →
        Relation.EqvGen C.Rel y y')
    (z z' : Σ _ : Fin C'.faceCount, Disk) (hzz : C'.Rel z z')
    (y y' : Σ _ : Fin C.faceCount, Disk)
    (hy : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y = z)
    (hy' : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y' = z') :
    Relation.EqvGen C.Rel y y' := by
  rcases hzz with ⟨v, t, rfl, rfl⟩
  let x : Σ _ : Fin C.faceCount, Disk :=
    ⟨(D.toOld v).1, edgePoint (C.sides (D.toOld v).1) (D.toOld v).2 t⟩
  let x' : Σ _ : Fin C.faceCount, Disk :=
    ⟨(C.pair (D.toOld v)).1,
      edgePoint (C.sides (C.pair (D.toOld v)).1) (C.pair (D.toOld v)).2
        (C.pairedParameter (D.toOld v) t)⟩
  have hpar : C'.pairedParameter v t = C.pairedParameter (D.toOld v) t := by
    simp only [PolygonComplex.pairedParameter]
    rw [D.sign_toOld, D.sign_toOld, D.pair_toOld]
  have hx : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR x =
      ⟨v.1, edgePoint (C'.sides v.1) v.2 t⟩ := himage v t
  have hx' : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR x' =
      ⟨(C'.pair v).1,
        edgePoint (C'.sides (C'.pair v).1) (C'.pair v).2
          (C'.pairedParameter v t)⟩ := by
    dsimp [x']
    rw [← hpar]
    have hi := himage (C'.pair v) (C'.pairedParameter v t)
    rw [D.pair_toOld] at hi
    exact hi
  have hrel : C.Rel x x' := by
    exact ⟨D.toOld v, t, rfl, rfl⟩
  have hstep : Relation.EqvGen C.Rel x x' := by
    apply Relation.EqvGen.rel
    exact hrel
  exact Relation.EqvGen.trans y x y'
    (hker y x (hy.trans hx.symm))
    (Relation.EqvGen.trans x x' y' hstep
      (hker x' y' (hx'.trans hy'.symm)))

/-- Two points of the disks of `C` are identified in `C` exactly when their
images are identified in `C'` (assembly of `_aux_oldInv`, `_aux_edgeImage`,
`_aux_kernel`, `_aux_step`, `_aux_lift`; induction on `EqvGen` both ways, the
reverse one over preimages, which exist by `hH.cover`). -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hsides : ∀ f, 2 ≤ C.sides f) (hor : C.IsOrientable) {hL hR : Disk → Disk}
    (hH : standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
      (C.sides s.1) (C.sides (C.pair s).1) s.2 (C.pair s).2 hL hR)
    (y y' : Σ _ : Fin C.faceCount, Disk) :
    Relation.EqvGen C.Rel y y' ↔
      Relation.EqvGen C'.Rel
        (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y)
        (standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR y') := by
  let b := standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
  have hfaces := fun f (h1 : f ≠ s.1) (h2 : f ≠ (C.pair s).1) =>
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_oldInv D f h1 h2
  have himage := fun v t =>
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_edgeImage D hH v t
  have hker := fun y y' h =>
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_kernel
      D hor hH hfaces y y' h
  have hne : s.1 ≠ (C.pair s).1 := by
    have h := D.old_ne D.merged
    rwa [D.old_merged] at h
  have hsurj : ∀ w, ∃ x, b x = w := by
    rintro ⟨k, z⟩
    by_cases hk : k = D.merged
    · subst hk
      rcases hH.cover z with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨⟨s.1, x⟩, by
          simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, hx]⟩
      · exact ⟨⟨(C.pair s).1, x⟩, by
          simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
            hne.symm, hx]⟩
    · have h1 : D.old k ≠ s.1 := by
        intro h
        exact hk (D.old_injective (h.trans D.old_merged.symm))
      have h2 : D.old k ≠ (C.pair s).1 := D.old_ne k
      have hinv :
          standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D (D.old k) = k :=
        D.old_injective (hfaces _ h1 h2).1
      refine ⟨⟨D.old k, z⟩, ?_⟩
      simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, h1, h2, hinv]
  constructor
  · intro h
    induction h with
    | rel x x' hxx =>
      exact standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_step
        D hor hH himage x x' hxx
    | refl x => exact Relation.EqvGen.refl _
    | symm x x' _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x w x' _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    have key : ∀ z z', Relation.EqvGen C'.Rel z z' →
        ∀ x x', b x = z → b x' = z' → Relation.EqvGen C.Rel x x' := by
      intro z z' hz
      induction hz with
      | rel z z' hzz =>
        intro x x' hx hx'
        exact standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres_aux_lift
          D himage hker z z' hzz x x' hx hx'
      | refl z =>
        intro x x' hx hx'
        exact hker x x' (hx.trans hx'.symm)
      | symm z z' _ ih =>
        intro x x' hx hx'
        exact Relation.EqvGen.symm _ _ (ih x' x hx' hx)
      | trans z w z' _ _ ih₁ ih₂ =>
        intro x x' hx hx'
        obtain ⟨m, hm⟩ := hsurj w
        exact Relation.EqvGen.trans _ _ _ (ih₁ x m hx hm) (ih₂ m x' hm hx')
    exact key _ _ h y y' rfl rfl

/-- The disks of `s.1` and `(C.pair s).1`, glued along `s` with the parameter
reversed, form one disk whose boundary is the merged face's boundary; all other
identifications are carried by `toOld`.  Proved from `_aux_span` with the map
`_aux_merge` built on the half charts `_aux_halves`; the fibre comparison is
`_aux_fibres`. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hsides : ∀ f, 2 ≤ C.sides f) (hor : C.IsOrientable) :
    Nonempty (C.Space ≃ₜ C'.Space) := by
  obtain ⟨hL, hR, hH⟩ :=
    standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves
      (C.sides s.1) (C.sides (C.pair s).1) s.2 (C.pair s).2
      (hsides _) (hsides _) s.2.isLt (C.pair s).2.isLt
  let b := standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge D hL hR
  have hne : s.1 ≠ (C.pair s).1 := by
    have h := D.old_ne D.merged
    rwa [D.old_merged] at h
  have hb : Continuous b := by
    refine continuous_sigma fun f => ?_
    by_cases h1 : f = s.1
    · have : (fun x : Disk => b ⟨f, x⟩) = fun x => ⟨D.merged, hL x⟩ := by
        funext x
        simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, h1]
      rw [this]
      exact continuous_sigmaMk.comp hH.continuous_left
    by_cases h2 : f = (C.pair s).1
    · have : (fun x : Disk => b ⟨f, x⟩) = fun x => ⟨D.merged, hR x⟩ := by
        funext x
        simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, h1, h2,
          hne.symm]
      rw [this]
      exact continuous_sigmaMk.comp hH.continuous_right
    · have : (fun x : Disk => b ⟨f, x⟩) = fun x =>
          ⟨standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D f, x⟩ := by
        funext x
        simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, h1, h2]
      rw [this]
      exact continuous_sigmaMk.comp continuous_id
  have hbsurj : Function.Surjective b := by
    rintro ⟨k, z⟩
    by_cases hk : k = D.merged
    · subst hk
      rcases hH.cover z with ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨⟨s.1, x⟩, by
          simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, hx]⟩
      · exact ⟨⟨(C.pair s).1, y⟩, by
          simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge,
            hne.symm, hy]⟩
    · have h1 : D.old k ≠ s.1 := by
        intro h
        exact hk (D.old_injective (h.trans D.old_merged.symm))
      have h2 : D.old k ≠ (C.pair s).1 := D.old_ne k
      have hinv :
          standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv D (D.old k) = k := by
        have hex : ∃ k', D.old k' = D.old k := ⟨k, rfl⟩
        simp only [standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_oldInv,
          dif_pos hex]
        exact D.old_injective hex.choose_spec
      refine ⟨⟨D.old k, z⟩, ?_⟩
      simp [b, standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_merge, h1, h2, hinv]
  exact standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_span
    (Y := Σ _ : Fin C.faceCount, Disk) id b continuous_id hb
    Function.surjective_id hbsurj
    (fun y y' =>
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_fibres D hsides hor hH y y')

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
  by_contra h
  push_neg at h
  have hface : ∀ f g : Fin C.faceCount, f = g := by
    intro f g
    apply Fin.ext
    have hf : f.val = 0 := by omega
    have hg : g.val = 0 := by omega
    omega
  have hbase (f : Fin C.faceCount) (k : ℕ) (hk : k < C.sides f) :
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel)
          (⟨f, ⟨k, hk⟩⟩ : C.Side) =
        Quotient.mk (Relation.EqvGen.setoid C.CornerRel)
          (⟨f, ⟨0, C.sides_pos f⟩⟩ : C.Side) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < C.sides f := by omega
      have hs := h (⟨f, ⟨k, hk'⟩⟩ : C.Side)
      have hmod : (k + 1) % C.sides f = k + 1 := Nat.mod_eq_of_lt hk
      have hnxt : C.nextCorner (⟨f, ⟨k, hk'⟩⟩ : C.Side) =
          (⟨f, ⟨k + 1, hk⟩⟩ : C.Side) := by
        simp [PolygonComplex.nextCorner, hmod]
      rw [hnxt] at hs
      exact hs.symm.trans (ih hk')
  have hsub : Subsingleton C.Vertex := by
    constructor
    intro x y
    induction x using Quotient.inductionOn with
    | _ s =>
      induction y using Quotient.inductionOn with
      | _ t =>
        obtain ⟨f, i⟩ := s
        obtain ⟨g, j⟩ := t
        obtain rfl := hface f g
        exact (hbase f i.val i.isLt).trans (hbase f j.val j.isLt).symm
  have hc : C.vertexCount ≤ 1 := by
    exact (Finite.card_le_one_iff_subsingleton).2 hsub
  omega

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
  let f0 : Fin C.faceCount := ⟨0, by omega⟩
  have face_eq (f : Fin C.faceCount) : f = f0 := Fin.eq_of_val_eq (by omega)
  let se : C.Side ≃ Fin (C.sides f0) :=
    { toFun := fun t => Fin.cast (congrArg C.sides (face_eq t.1)) t.2
      invFun := fun i => ⟨f0, i⟩
      left_inv := by
        rintro ⟨f, i⟩
        have hf := face_eq f
        cases hf
        rfl
      right_inv := by intro i; simp }
  let good : Finset (Fin (C.sides f0)) :=
    (Finset.univ.erase (se s)).erase (se (C.pair s))
  have hps : C.pair s ≠ s := C.pair_ne s
  have hsep : se (C.pair s) ≠ se s := fun h => hps (se.injective h)
  letI : Unique (Fin C.faceCount) := ⟨⟨f0⟩, face_eq⟩
  have hN : C.sides f0 = C.totalSides := by
    rw [PolygonComplex.totalSides, Fintype.sum_unique]
    exact congrArg C.sides (face_eq default).symm
  have hgood : good.card + 2 = C.totalSides := by
    rw [← hN]
    simp [good, hps]
    omega
  have hgoodpos : 0 < good.card := by omega
  let oe : Fin good.card ≃o good := good.orderIsoOfFin rfl
  let pg : good → good := fun u =>
    ⟨se (C.pair (se.symm u.1)), by
      have hm := u.2
      simp only [good, Finset.mem_erase, Finset.mem_univ, and_true] at hm ⊢
      rcases hm with ⟨hup, hus⟩
      constructor
      · intro hp
        apply hus
        have he := C.pair.injective (se.injective hp)
        simpa using congrArg se he
      · intro hp
        apply hup
        have hp' := congrArg (fun x => se (C.pair (se.symm x))) hp
        simpa [C.pair_pair] using hp'⟩
  have pg_inv (u : good) : pg (pg u) = u := by
    apply Subtype.ext
    simp [pg, C.pair_pair]
  let pe : Equiv.Perm good :=
    { toFun := pg
      invFun := pg
      left_inv := pg_inv
      right_inv := pg_inv }
  let ne : (Σ _ : Fin 1, Fin good.card) ≃ good :=
    { toFun := fun t => oe t.2
      invFun := fun u => ⟨⟨0, Nat.zero_lt_one⟩, oe.symm u⟩
      left_inv := by
        intro t
        apply Sigma.ext (Fin.eq_of_val_eq (by simp))
        simp
      right_inv := by intro u; simp }
  let np : Equiv.Perm (Σ _ : Fin 1, Fin good.card) := ne.trans (pe.trans ne.symm)
  let C' : PolygonComplex :=
    { faceCount := 1
      sides := fun _ => good.card
      sides_pos := fun _ => hgoodpos
      pair := np
      pair_pair := by
        intro t
        simp [np, pe, pg, C.pair_pair]
      pair_ne := by
        intro t ht
        have hp : C.pair (se.symm (ne t).1) = se.symm (ne t).1 := by
          have := congrArg ne ht
          have hv := congrArg Subtype.val this
          apply se.injective
          simpa [np, pe, pg] using hv
        exact C.pair_ne _ hp
      sign := fun t => C.sign (se.symm (ne t)) }
  refine ⟨C', ⟨{
    faceCount_eq := rfl
    totalSides_add_two := ?_
    toOld := fun t => se.symm (ne t)
    toOld_injective := by
      intro t t' h
      apply ne.injective
      apply Subtype.ext
      exact se.symm.injective h
    toOld_ne := ?_
    toOld_surj := ?_
    toOld_lt := ?_
    pair_toOld := ?_
    sign_toOld := fun _ => rfl }⟩⟩
  · simpa [C', PolygonComplex.totalSides] using hgood
  · intro t
    have hm := (ne t).2
    simp only [good, Finset.mem_erase, Finset.mem_univ, and_true] at hm
    exact ⟨fun h => hm.2 (congrArg se h), fun h => hm.1 (congrArg se h)⟩
  · intro u hus hup
    have hu : se u ∈ good := by simp [good, hus, hup]
    exact ⟨ne.symm ⟨se u, hu⟩, by simp⟩
  · intro t t' htt
    change (se.symm (ne t)).2.val < (se.symm (ne t')).2.val
    change (ne t).1.val < (ne t').1.val
    exact oe.strictMono htt
  · intro t
    apply se.injective
    change (ne (np t)).1 = se (C.pair (se.symm (ne t)))
    simp [np, pe, pg]

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
lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_cutRel
    {C : PolygonComplex} (s : C.Side) (hor : C.IsOrientable) :
    Relation.EqvGen C.CornerRel s (C.nextCorner (C.pair s)) ∧
      Relation.EqvGen C.CornerRel (C.nextCorner s) (C.pair s) := by
  constructor
  · apply Relation.EqvGen.rel
    refine ⟨s, ?_⟩
    rw [if_neg (Ne.symm (hor s))]
    exact Or.inl ⟨rfl, rfl⟩
  · apply Relation.EqvGen.rel
    refine ⟨s, ?_⟩
    rw [if_neg (Ne.symm (hor s))]
    exact Or.inr ⟨rfl, rfl⟩

lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_twoClasses
    {C : PolygonComplex} {s : C.Side}
    (hs : Quotient.mk (Relation.EqvGen.setoid C.CornerRel) s ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner s))
    (hor : C.IsOrientable) :
    Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner (C.pair s)) ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.pair s) := by
  intro h
  apply hs
  have hrel :=
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_cutRel s hor
  exact (Quotient.sound hrel.1).trans (h.trans (Quotient.sound hrel.2).symm)

/-- **Leaf (counting a merge).**  Adding one generator `a ~ b` between two
inequivalent elements merges exactly two classes into one. -/
lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mergeCount_aux_iff
    {α : Type} (r : α → α → Prop) (a b x y : α) :
    Relation.EqvGen (fun u v => r u v ∨ (u = a ∧ v = b)) x y ↔
      Relation.EqvGen r x y ∨
        (Relation.EqvGen r x a ∧ Relation.EqvGen r b y) ∨
        (Relation.EqvGen r x b ∧ Relation.EqvGen r a y) := by
  let R := Relation.EqvGen r
  let T := fun x y => R x y ∨ (R x a ∧ R b y) ∨ (R x b ∧ R a y)
  have hrefl : ∀ x, T x x := fun x => Or.inl (Relation.EqvGen.refl x)
  have hsymm : ∀ {x y}, T x y → T y x := by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2.symm, h.1.symm⟩)
    · exact Or.inr (Or.inl ⟨h.2.symm, h.1.symm⟩)
  have htrans : ∀ {x y z}, T x y → T y z → T x z := by
    intro x y z hxy hyz
    rcases hxy with hxy | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · rcases hyz with hyz | ⟨hya, hbz⟩ | ⟨hyb, haz⟩
      · exact Or.inl (hxy.trans _ _ _ hyz)
      · exact Or.inr (Or.inl ⟨hxy.trans _ _ _ hya, hbz⟩)
      · exact Or.inr (Or.inr ⟨hxy.trans _ _ _ hyb, haz⟩)
    · rcases hyz with hyz | ⟨hya, hbz⟩ | ⟨hyb, haz⟩
      · exact Or.inr (Or.inl ⟨hxa, hby.trans _ _ _ hyz⟩)
      · exact Or.inl (hxa.trans _ _ _ (hby.trans _ _ _ hya).symm |>.trans _ _ _ hbz)
      · exact Or.inl (hxa.trans _ _ _ haz)
    · rcases hyz with hyz | ⟨hya, hbz⟩ | ⟨hyb, haz⟩
      · exact Or.inr (Or.inr ⟨hxb, hay.trans _ _ _ hyz⟩)
      · exact Or.inl (hxb.trans _ _ _ hbz)
      · exact Or.inl (hxb.trans _ _ _ (hay.trans _ _ _ hyb).symm |>.trans _ _ _ haz)
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
        rcases hxy with hxy | ⟨rfl, rfl⟩
        · exact Or.inl (Relation.EqvGen.rel x y hxy)
        · exact Or.inr (Or.inl ⟨Relation.EqvGen.refl _, Relation.EqvGen.refl _⟩)
    | refl x => exact hrefl x
    | symm x y _ ih => exact hsymm ih
    | trans x y z _ _ ih₁ ih₂ => exact htrans ih₁ ih₂
  · intro h
    have hold : ∀ {x y}, Relation.EqvGen r x y →
        Relation.EqvGen (fun u v => r u v ∨ (u = a ∧ v = b)) x y := by
      intro x y hxy
      induction hxy with
      | rel x y h => exact Relation.EqvGen.rel x y (Or.inl h)
      | refl x => exact Relation.EqvGen.refl x
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
    rcases h with h | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact hold h
    · exact (hold hxa).trans _ _ _ ((Relation.EqvGen.rel a b (Or.inr ⟨rfl, rfl⟩)).trans _ _ _ (hold hby))
    · exact (hold hxb).trans _ _ _ ((Relation.EqvGen.rel a b (Or.inr ⟨rfl, rfl⟩)).symm.trans _ _ _ (hold hay))

theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mergeCount
    {α : Type} [Finite α] (r : α → α → Prop) (a b : α)
    (hab : ¬ Relation.EqvGen r a b) :
    Nat.card (Quotient (Relation.EqvGen.setoid
        (fun x y => r x y ∨ (x = a ∧ y = b)))) + 1 =
      Nat.card (Quotient (Relation.EqvGen.setoid r)) := by
  classical
  let R := Relation.EqvGen.setoid r
  let S := Relation.EqvGen.setoid (fun x y => r x y ∨ (x = a ∧ y = b))
  let qa : Quotient R := Quotient.mk R a
  let qb : Quotient R := Quotient.mk R b
  have habq : qa ≠ qb := by
    intro h
    exact hab (Quotient.exact h)
  let f : Quotient R → Quotient S := Quotient.map id (by
    intro x y h
    exact (standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mergeCount_aux_iff
      r a b x y).mpr (Or.inl h))
  have hf_surj : Function.Surjective f := by
    intro q
    induction q using Quotient.ind with
    | _ x => exact ⟨Quotient.mk R x, rfl⟩
  have hf_eq : ∀ q q' : Quotient R, f q = f q' ↔
      q = q' ∨ (q = qa ∧ q' = qb) ∨ (q = qb ∧ q' = qa) := by
    intro q q'
    induction q using Quotient.ind with
    | _ x =>
      induction q' using Quotient.ind with
      | _ y =>
        change Quotient.mk S x = Quotient.mk S y ↔ _
        rw [Quotient.eq]
        change Relation.EqvGen (fun u v => r u v ∨ (u = a ∧ v = b)) x y ↔ _
        rw [standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mergeCount_aux_iff]
        simp only [qa, qb, R, Quotient.eq]
        constructor <;> intro h
        · rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h₁, h₂.symm⟩)
          · exact Or.inr (Or.inr ⟨h₁, h₂.symm⟩)
        · rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h₁, h₂.symm⟩)
          · exact Or.inr (Or.inr ⟨h₁, h₂.symm⟩)
  let A := {q : Quotient R // q ≠ qb}
  let e : A ≃ Quotient S := Equiv.ofBijective (fun q => f q.1) ⟨by
    intro x y hxy
    have h := (hf_eq x.1 y.1).mp hxy
    rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
    · exact Subtype.ext h
    · exact False.elim (y.2 h)
    · exact False.elim (x.2 h)
    , by
      intro z
      obtain ⟨q, hq⟩ := hf_surj z
      by_cases hqb : q = qb
      · refine ⟨⟨qa, habq⟩, ?_⟩
        exact ((hf_eq qa q).mpr (Or.inr (Or.inl ⟨rfl, hqb⟩))).trans hq
      · exact ⟨⟨q, hqb⟩, hq⟩⟩
  letI : Fintype (Quotient R) := Fintype.ofFinite _
  letI : Fintype (Quotient S) := Fintype.ofFinite _
  have hcardA : Fintype.card A + 1 = Fintype.card (Quotient R) := by
    rw [Fintype.card_subtype_compl (fun q : Quotient R => q = qb)]
    simp
    have hpos : 0 < Fintype.card (Quotient R) :=
      Fintype.card_pos_iff.mpr ⟨Quotient.mk R a⟩
    omega
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_congr e]
  exact hcardA

lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_face
    {C : PolygonComplex} (h1 : C.faceCount = 1) (u v : C.Side) : u.1 = v.1 := by
  apply Fin.eq_of_val_eq
  omega

/-- With one face, a side is determined by its index. -/
lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_ext
    {C : PolygonComplex} (h1 : C.faceCount = 1) {u v : C.Side}
    (hval : u.2.val = v.2.val) : u = v := by
  have hf := standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_face h1 u v
  apply Sigma.ext hf
  apply (Fin.heq_ext_iff (congrArg C.sides hf)).2
  exact hval

/-- **Leaf (cyclic enumeration).**  `toOld` is the increasing enumeration of
the indices other than `s` and `C.pair s` (`toOld_lt`, `toOld_surj`), so
`toOld (C'.nextCorner t)` is the first surviving side cyclically after
`toOld t`: the next side, or the one after it when the next side is removed,
or the one after that when the next two sides are both removed (`s` and
`C.pair s` adjacent).  Includes the wrap-around at the last index. -/
lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_skip_aux
    (m n a b : ℕ) (hsize : m + 2 = n) (ha : a < n) (hb : b < n)
    (hab : a ≠ b) (f : Fin m → Fin n)
    (hf : ∀ i j, i.val < j.val → (f i).val < (f j).val)
    (hne : ∀ i, (f i).val ≠ a ∧ (f i).val ≠ b)
    (hsurj : ∀ z, z < n → z ≠ a → z ≠ b → ∃ i, (f i).val = z)
    (hm : 0 < m) (i : Fin m) : let j : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩;
    (f j).val = ((f i).val + 1) % n ∨
      (((f i).val + 1) % n = a ∨ ((f i).val + 1) % n = b) ∧
        ((f j).val = ((f i).val + 2) % n ∨
          (((f i).val + 2) % n = a ∨ ((f i).val + 2) % n = b) ∧
            (f j).val = ((f i).val + 3) % n) := by
  intro j
  have hmono {p q : Fin m} (hpq : p.val ≤ q.val) : (f p).val ≤ (f q).val := by
    rcases lt_or_eq_of_le hpq with h | h
    · exact Nat.le_of_lt (hf p q h)
    · rw [Fin.ext h]
  have hyn := (f j).isLt
  have hxn := (f i).isLt
  obtain ⟨hya, hyb⟩ := hne j
  have hmod (d : ℕ) (hd : d ≤ 3) : ((f i).val + d) % n =
      if (f i).val + d < n then (f i).val + d else (f i).val + d - n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have h1 := hmod 1 (by omega)
  have h2 := hmod 2 (by omega)
  have h3 := hmod 3 (by omega)
  by_cases hi : i.val + 1 < m
  · have hj : j.val = i.val + 1 := Nat.mod_eq_of_lt hi
    have hxy : (f i).val < (f j).val := hf i j (by omega)
    have hgapz {z : ℕ} (hz1 : (f i).val < z) (hz2 : z < (f j).val) : z = a ∨ z = b := by
      by_contra hzab
      push_neg at hzab
      obtain ⟨k, hk⟩ := hsurj z (by omega) hzab.1 hzab.2
      by_cases hki : k.val ≤ i.val
      · have := hmono hki; omega
      · have := hmono (show j.val ≤ k.val by omega); omega
    by_cases g1 : (f j).val = (f i).val + 1
    · left; split_ifs at h1 <;> omega
    · have r1 := hgapz (z := (f i).val + 1) (by omega) (by omega)
      by_cases g2 : (f j).val = (f i).val + 2
      · right; split_ifs at h1 h2 <;> omega
      · have r2 := hgapz (z := (f i).val + 2) (by omega) (by omega)
        have g3 : (f j).val = (f i).val + 3 := by
          by_contra g3
          have r3 := hgapz (z := (f i).val + 3) (by omega) (by omega)
          omega
        right; split_ifs at h1 h2 h3 <;> omega
  · have hj : j.val = 0 := by
      show (i.val + 1) % m = 0
      rw [show i.val + 1 = m by omega, Nat.mod_self]
    have himax : i.val + 1 = m := by omega
    have hhigh {z : ℕ} (hz1 : (f i).val < z) (hzn : z < n) : z = a ∨ z = b := by
      by_contra hzab
      push_neg at hzab
      obtain ⟨k, hk⟩ := hsurj z hzn hzab.1 hzab.2
      have := hmono (show k.val ≤ i.val by omega)
      omega
    have hlow {z : ℕ} (hz0 : z < (f j).val) : z = a ∨ z = b := by
      by_contra hzab
      push_neg at hzab
      obtain ⟨k, hk⟩ := hsurj z (by omega) hzab.1 hzab.2
      have := hmono (show j.val ≤ k.val by omega)
      omega
    -- the removed values are exactly those cyclically strictly between f i and f j
    have hr (d : ℕ) (hd : 1 ≤ d) (hdn : (f i).val + d < n + (f j).val) :
        ((f i).val + d) % n = a ∨ ((f i).val + d) % n = b := by
      have hdl : d ≤ 3 ∨ 3 < d := by omega
      by_cases hw : (f i).val + d < n
      · rw [Nat.mod_eq_of_lt hw]; exact hhigh (by omega) hw
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        exact hlow (by omega)
    by_cases g1 : (f i).val + 1 = n + (f j).val
    · left; split_ifs at h1 <;> omega
    · have r1 := hr 1 le_rfl (by omega)
      by_cases g2 : (f i).val + 2 = n + (f j).val
      · right; split_ifs at h1 h2 <;> omega
      · have r2 := hr 2 (by omega) (by omega)
        have g3 : (f i).val + 3 = n + (f j).val := by
          by_contra g3
          have r3 := hr 3 (by omega) (by omega)
          split_ifs at h1 h2 h3 <;> omega
        right; split_ifs at h1 h2 h3 <;> omega
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_skip
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (t : C'.Side) :
    D.toOld (C'.nextCorner t) = C.nextCorner (D.toOld t) ∨
      ((C.nextCorner (D.toOld t) = s ∨ C.nextCorner (D.toOld t) = C.pair s) ∧
        (D.toOld (C'.nextCorner t) = C.nextCorner (C.nextCorner (D.toOld t)) ∨
          ((C.nextCorner (C.nextCorner (D.toOld t)) = s ∨
              C.nextCorner (C.nextCorner (D.toOld t)) = C.pair s) ∧
            D.toOld (C'.nextCorner t) =
              C.nextCorner (C.nextCorner (C.nextCorner (D.toOld t)))))) := by
  let m := C'.sides t.1
  let n := C.sides (D.toOld t).1
  have hfold (u : C.Side) : u.1 = (D.toOld t).1 :=
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_face h1 _ _
  have hfnew (u : C'.Side) : u.1 = t.1 := by
    apply Fin.eq_of_val_eq
    have := D.faceCount_eq
    omega
  let f : Fin m → Fin n := fun i =>
    ⟨(D.toOld ⟨t.1, i⟩).2.val, by
      calc
        _ < C.sides (D.toOld ⟨t.1, i⟩).1 := (D.toOld ⟨t.1, i⟩).2.isLt
        _ = n := congrArg C.sides (hfold (D.toOld ⟨t.1, i⟩))⟩
  have hCold : C.totalSides = n := by
    rw [PolygonComplex.totalSides]
    haveI : Unique (Fin C.faceCount) :=
      ⟨⟨(D.toOld t).1⟩, fun x => hfold ⟨x, ⟨0, C.sides_pos x⟩⟩⟩
    rw [Fintype.sum_unique]
    exact congrArg C.sides (hfold ⟨default, ⟨0, C.sides_pos default⟩⟩)
  have hCnew : C'.totalSides = m := by
    rw [PolygonComplex.totalSides]
    haveI : Unique (Fin C'.faceCount) :=
      ⟨⟨t.1⟩, fun x => hfnew ⟨x, ⟨0, C'.sides_pos x⟩⟩⟩
    rw [Fintype.sum_unique]
    exact congrArg C'.sides (hfnew ⟨default, ⟨0, C'.sides_pos default⟩⟩)
  have hsize : m + 2 = n := by
    rw [← hCnew, ← hCold]
    exact D.totalSides_add_two
  have hfa : s.2.val < n := by
    calc _ < C.sides s.1 := s.2.isLt
      _ = n := congrArg C.sides (hfold s)
  have hfb : (C.pair s).2.val < n := by
    calc _ < C.sides (C.pair s).1 := (C.pair s).2.isLt
      _ = n := congrArg C.sides (hfold (C.pair s))
  have hab : s.2.val ≠ (C.pair s).2.val := by
    intro he
    apply C.pair_ne s
    apply standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_ext h1 he.symm
  have hstrict : ∀ i j, i.val < j.val → (f i).val < (f j).val := by
    intro i j hij
    exact D.toOld_lt ⟨t.1, i⟩ ⟨t.1, j⟩ hij
  have hfne : ∀ i, (f i).val ≠ s.2.val ∧ (f i).val ≠ (C.pair s).2.val := by
    intro i
    rcases D.toOld_ne ⟨t.1, i⟩ with ⟨ha, hb⟩
    constructor
    · intro hh
      apply ha
      exact standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_ext h1 hh
    · intro hh
      apply hb
      exact standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_ext h1 hh
  have hfsurj : ∀ z, z < n → z ≠ s.2.val → z ≠ (C.pair s).2.val →
      ∃ i, (f i).val = z := by
    intro z hz hzs hzp
    let u : C.Side := ⟨(D.toOld t).1, ⟨z, hz⟩⟩
    have hus : u ≠ s := by
      intro hh
      exact hzs (congrArg (fun q : C.Side => q.2.val) hh)
    have hup : u ≠ C.pair s := by
      intro hh
      exact hzp (congrArg (fun q : C.Side => q.2.val) hh)
    obtain ⟨v, hv⟩ := D.toOld_surj u hus hup
    let i : Fin m := Fin.cast (congrArg C'.sides (hfnew v)) v.2
    refine ⟨i, ?_⟩
    change (D.toOld ⟨t.1, i⟩).2.val = z
    have hvt : (⟨t.1, i⟩ : C'.Side) = v := by
      apply standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_ext
        D.faceCount_eq
      simp [i]
    rw [hvt, hv]
  have harith :=
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_skip_aux
      m n s.2.val (C.pair s).2.val hsize hfa hfb hab f hstrict hfne hfsurj
      (C'.sides_pos t.1) t.2
  have heq {u v : C.Side} (h : u.2.val = v.2.val) : u = v :=
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_ext h1 h
  rcases harith with h | ⟨hr, h | ⟨hr2, h⟩⟩
  · exact Or.inl (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using h))
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · rcases hr with hr | hr
      · exact Or.inl (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using hr))
      · exact Or.inr (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using hr))
    · exact heq (by simpa [f, m, n, PolygonComplex.nextCorner] using h)
  · refine Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩
    · rcases hr with hr | hr
      · exact Or.inl (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using hr))
      · exact Or.inr (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using hr))
    · rcases hr2 with hr2 | hr2
      · exact Or.inl (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using hr2))
      · exact Or.inr (heq (by simpa [f, m, n, PolygonComplex.nextCorner] using hr2))
    · exact heq (by simpa [f, m, n, PolygonComplex.nextCorner] using h)

/-- A removed side's two corners are equivalent modulo the merge: for `s` it
is the merge itself, for `C.pair s` it is `_aux_cutRel` around the merge. -/
lemma standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_removed
    {C : PolygonComplex} {s w : C.Side} (hor : C.IsOrientable)
    (hw : w = s ∨ w = C.pair s) :
    Relation.EqvGen (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
      (C.nextCorner w) w := by
  have hcut := standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_cutRel s hor
  have hlift : ∀ {x y}, Relation.EqvGen C.CornerRel x y →
      Relation.EqvGen (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s)) x y := by
    intro x y h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (Or.inl hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
  have hmerge : Relation.EqvGen (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
      s (C.nextCorner s) := Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
  rcases hw with rfl | rfl
  · exact hmerge.symm
  · exact (hlift hcut.1).symm.trans _ _ _ (hmerge.trans _ _ _ (hlift hcut.2))

/-- **Leaf (boundary order).**  Modulo the merge `s ~ nextCorner s`, `toOld`
commutes with `nextCorner`.  The only places where it does not commute
literally are the sides of `C'` just before a removed side (`s` or
`C.pair s`); there `_aux_cutRel` (`s ~ nextCorner (C.pair s)`,
`nextCorner s ~ C.pair s`) and the merge close the gap.  Includes the case
where `s` and `C.pair s` are adjacent, and the wrap-around at the last side. -/
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (hor : C.IsOrientable) (t : C'.Side) :
    Relation.EqvGen (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
      (D.toOld (C'.nextCorner t)) (C.nextCorner (D.toOld t)) := by
  rcases standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_skip D h1 t with h | ⟨hw, h | ⟨hw', h⟩⟩
  · rw [h]
    exact Relation.EqvGen.refl _
  · rw [h]
    exact standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_removed hor hw
  · rw [h]
    exact (standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_removed hor hw').trans _ _ _ (standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_removed hor hw)

/-- Every generating corner identification of `C'` maps under `toOld` to an
equivalence of `C` modulo the merge. -/
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mapRel
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (hor : C.IsOrientable) {a b : C'.Side}
    (h : C'.CornerRel a b) :
    Relation.EqvGen (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
      (D.toOld a) (D.toOld b) := by
  obtain ⟨t, ht⟩ := h
  have hnext := standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next D h1 hor
  have hrel : ∀ x y, C.CornerRel x y →
      Relation.EqvGen (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s)) x y :=
    fun x y h => Relation.EqvGen.rel x y (Or.inl h)
  have hsign : C'.sign t = C'.sign (C'.pair t) ↔
      C.sign (D.toOld t) = C.sign (C.pair (D.toOld t)) := by
    rw [D.sign_toOld, D.sign_toOld, D.pair_toOld]
  by_cases hs : C'.sign t = C'.sign (C'.pair t)
  · rw [if_pos hs] at ht
    have hs' := hsign.mp hs
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb]
    · rw [D.pair_toOld]
      exact hrel _ _ ⟨D.toOld t, by rw [if_pos hs']; exact Or.inl ⟨rfl, rfl⟩⟩
    · refine (hnext t).trans _ _ _ ((hrel _ _ ⟨D.toOld t, ?_⟩).trans _ _ _
        (hnext (C'.pair t)).symm)
      rw [if_pos hs', D.pair_toOld]; exact Or.inr ⟨rfl, rfl⟩
  · rw [if_neg hs] at ht
    have hs' : ¬ C.sign (D.toOld t) = C.sign (C.pair (D.toOld t)) :=
      fun h => hs (hsign.mpr h)
    rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb]
    · refine (hrel _ _ ⟨D.toOld t, ?_⟩).trans _ _ _ (hnext (C'.pair t)).symm
      rw [if_neg hs', D.pair_toOld]; exact Or.inl ⟨rfl, rfl⟩
    · refine (hnext t).trans _ _ _ (hrel _ _ ⟨D.toOld t, ?_⟩)
      rw [if_neg hs', D.pair_toOld]; exact Or.inr ⟨rfl, rfl⟩

/-- **Leaf (inverse on corners).**  A map back from the corners of `C` to the
corners of `C'`: a left inverse of `toOld`, sending each corner `u` to a
corner whose image is equivalent to `u` modulo the merge, and carrying every
generating identification of `C`, and the merge `s ~ nextCorner s` itself, to
a `C'`-equivalence.  The removed corners `s` and `C.pair s` go to the
`C'`-corner at the junction where the removed side was (the initial corner of
the next surviving side). -/
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back_aux_leftInverse
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s) :
    ∃ g : C.Side → C'.Side, ∀ t, g (D.toOld t) = t := by
  haveI : Nonempty C'.Side := by
    have hface : 0 < C'.faceCount := by rw [D.faceCount_eq]; exact Nat.zero_lt_one
    let f : Fin C'.faceCount := ⟨0, hface⟩
    exact ⟨⟨f, ⟨0, C'.sides_pos f⟩⟩⟩
  let g : C.Side → C'.Side := Function.invFun D.toOld
  refine ⟨g, ?_⟩
  intro t
  exact Function.leftInverse_invFun D.toOld_injective t

theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back_aux_choose
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides) (hor : C.IsOrientable) :
    ∃ g : C.Side → C'.Side, (∀ t, g (D.toOld t) = t) ∧
      (∀ u, Relation.EqvGen
        (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
        (D.toOld (g u)) u) := by
  let R := fun x y : C.Side => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s)
  have hside : ∀ t : C.Side, C.sides t.1 = C.totalSides := by
    intro t
    classical
    letI : Unique (Fin C.faceCount) :=
      ⟨⟨t.1⟩, fun u => Fin.eq_of_val_eq (by omega)⟩
    rw [PolygonComplex.totalSides, Fintype.sum_unique]
    exact congrArg C.sides (Unique.uniq _ _)
  have hnext : ∀ t : C.Side, C.nextCorner t ≠ t := by
    intro t ht
    have hv := congrArg (fun u : C.Side => u.2.val) ht
    simp only [PolygonComplex.nextCorner] at hv
    have hp := C.sides_pos t.1
    by_cases hlt : t.2.val + 1 < C.sides t.1
    · rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · have heq : t.2.val + 1 = C.sides t.1 := by omega
      rw [heq, Nat.mod_self] at hv
      have hn := hside t
      omega
  have hnext2 : ∀ t : C.Side, C.nextCorner (C.nextCorner t) ≠ t := by
    intro t ht
    have hv := congrArg (fun u : C.Side => u.2.val) ht
    simp only [PolygonComplex.nextCorner] at hv
    have hn := hside t
    have hp := C.sides_pos t.1
    by_cases hlt : t.2.val + 2 < C.sides t.1
    · have hlt1 : t.2.val + 1 < C.sides t.1 := by omega
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · by_cases heq : t.2.val + 1 = C.sides t.1
      · rw [heq, Nat.mod_self] at hv
        have hone : 1 < C.sides t.1 := by omega
        rw [Nat.mod_eq_of_lt hone] at hv
        omega
      · have hlt1 : t.2.val + 1 < C.sides t.1 := by omega
        have heq2 : t.2.val + 2 = C.sides t.1 := by omega
        rw [Nat.mod_eq_of_lt hlt1, heq2, Nat.mod_self] at hv
        omega
  have hlift : ∀ {x y}, Relation.EqvGen C.CornerRel x y → Relation.EqvGen R x y := by
    intro x y h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (Or.inl hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
  have hm : Relation.EqvGen R s (C.nextCorner s) :=
    Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
  have hc := standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_cutRel s hor
  have hpre : ∀ u : C.Side, ∃ t : C'.Side, Relation.EqvGen R (D.toOld t) u := by
    intro u
    by_cases hu : u = s
    · subst u
      by_cases hp : C.nextCorner s = C.pair s
      · have hn1 : C.nextCorner (C.nextCorner s) ≠ s := hnext2 s
        have hn2 : C.nextCorner (C.nextCorner s) ≠ C.pair s := by
          rw [← hp]
          exact hnext (C.nextCorner s)
        obtain ⟨t, ht⟩ := D.toOld_surj _ hn1 hn2
        refine ⟨t, ?_⟩
        rw [ht, hp]
        exact (hlift hc.1).symm
      · obtain ⟨t, ht⟩ := D.toOld_surj (C.nextCorner s) (hnext s) hp
        exact ⟨t, by rw [ht]; exact hm.symm⟩
    · by_cases hup : u = C.pair s
      · subst u
        by_cases hs : C.nextCorner (C.pair s) = s
        · have hn1 : C.nextCorner s ≠ s := hnext s
          have hn2 : C.nextCorner s ≠ C.pair s := by
            intro h
            apply hnext2 (C.pair s)
            rw [hs, h]
          obtain ⟨t, ht⟩ := D.toOld_surj _ hn1 hn2
          refine ⟨t, ?_⟩
          rw [ht]
          exact hlift hc.2
        · have hn2 : C.nextCorner (C.pair s) ≠ C.pair s := hnext _
          obtain ⟨t, ht⟩ := D.toOld_surj _ hs hn2
          refine ⟨t, ?_⟩
          rw [ht]
          exact standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_next_aux_removed hor (Or.inr rfl)
      · obtain ⟨t, ht⟩ := D.toOld_surj u hu hup
        exact ⟨t, by rw [ht]; exact Relation.EqvGen.refl _⟩
  let g : C.Side → C'.Side := fun u =>
    if h : ∃ t, D.toOld t = u then Classical.choose h else Classical.choose (hpre u)
  refine ⟨g, ?_, ?_⟩
  · intro t
    have h : ∃ v, D.toOld v = D.toOld t := ⟨t, rfl⟩
    rw [show g (D.toOld t) = Classical.choose h by simp only [g, dif_pos h]]
    exact D.toOld_injective (Classical.choose_spec h)
  · intro u
    by_cases h : ∃ t, D.toOld t = u
    · rw [show g u = Classical.choose h by simp only [g, dif_pos h]]
      rw [Classical.choose_spec h]
      exact Relation.EqvGen.refl _
    · rw [show g u = Classical.choose (hpre u) by simp only [g, dif_neg h]]
      exact Classical.choose_spec (hpre u)

theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back_aux_mapRel
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides) (hor : C.IsOrientable)
    (g : C.Side → C'.Side)
    (hg1 : ∀ t, g (D.toOld t) = t)
    (hg2 : ∀ u, Relation.EqvGen
      (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
      (D.toOld (g u)) u) :
    ∀ a b, (C.CornerRel a b ∨ (a = s ∧ b = C.nextCorner s)) →
      Relation.EqvGen C'.CornerRel (g a) (g b) := by
  sorry

theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides) (hor : C.IsOrientable) :
    ∃ g : C.Side → C'.Side, (∀ t, g (D.toOld t) = t) ∧
      (∀ u, Relation.EqvGen
        (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s)) (D.toOld (g u)) u) ∧
      (∀ a b, (C.CornerRel a b ∨ (a = s ∧ b = C.nextCorner s)) →
        Relation.EqvGen C'.CornerRel (g a) (g b)) := by
  obtain ⟨g, hg1, hg2⟩ :=
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back_aux_choose
      D h1 h5 hor
  exact ⟨g, hg1, hg2,
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back_aux_mapRel
      D h1 h5 hor g hg1 hg2⟩

theorem standardCover_pairingData_aux_contractStep_aux_vertexCount
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides)
    (hs : Quotient.mk (Relation.EqvGen.setoid C.CornerRel) s ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner s))
    (hor : C.IsOrientable) : C'.vertexCount + 1 = C.vertexCount := by
  obtain ⟨g, hg1, hg2, hg3⟩ :=
    standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back D h1 h5 hor
  have lift : ∀ {α β : Type} {r : α → α → Prop} {r' : β → β → Prop} (h : α → β),
      (∀ a b, r a b → Relation.EqvGen r' (h a) (h b)) →
      ∀ a b, Relation.EqvGen r a b → Relation.EqvGen r' (h a) (h b) := by
    intro α β r r' h hh a b hab
    induction hab with
    | rel x y hxy => exact hh x y hxy
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  have hF := lift (r := C'.CornerRel)
    (r' := fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s)) D.toOld
    (fun a b h => standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mapRel
      D h1 hor h)
  have hG := lift (r := fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))
    (r' := C'.CornerRel) g hg3
  let F : C'.Vertex → Quotient (Relation.EqvGen.setoid
      (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))) :=
    Quotient.map D.toOld hF
  let G : Quotient (Relation.EqvGen.setoid
      (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))) → C'.Vertex :=
    Quotient.map g hG
  have e : C'.Vertex ≃ Quotient (Relation.EqvGen.setoid
      (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s))) :=
    { toFun := F
      invFun := G
      left_inv := by
        intro x
        induction x using Quotient.ind with
        | _ t => exact congrArg (Quotient.mk _) (hg1 t)
      right_inv := by
        intro x
        induction x using Quotient.ind with
        | _ u => exact Quotient.sound (hg2 u) }
  have hab : ¬ Relation.EqvGen C.CornerRel s (C.nextCorner s) :=
    fun h => hs (Quotient.sound h)
  have hc := standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mergeCount
    C.CornerRel s (C.nextCorner s) hab
  show Nat.card C'.Vertex + 1 = Nat.card C.Vertex
  rw [Nat.card_congr e]
  exact hc

/-! Re-split of `_aux_contractStep` (claude-14, 2026-10-25, after the lemma-2
PARTIAL on `_aux_homeomorph`).  The earlier leaf asked for `C.Space ≃ₜ C'.Space`
for any side `s` with distinct ends.  That is "a surface with an embedded arc
collapsed is the same surface", and no disk map gives it: a map that collapses
side `s` to a point descends to `C.Space → C'.Space` collapsing the arc, which is
not injective.  Route now (Massey, Ch. 1 §8): cut-and-paste moves, each a cut
(`GlueData` read backwards) followed by a glue (`_aux_glueStep_aux_homeomorph`),
shrink one vertex class to a single corner (`_aux_isolate`); the two sides at
that corner are `a a⁻¹`, and cancelling them (`_aux_homeomorph`, now for
adjacent sides only) is `PolygonMoves.inversePairCancellation`. -/

lemma standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_face_eq
    (C : PolygonComplex) (h1 : C.faceCount = 1) (f g : Fin C.faceCount) : f = g := by
  apply Fin.ext
  omega

lemma standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_sides_eq_total
    (C : PolygonComplex) (h1 : C.faceCount = 1) (f : Fin C.faceCount) :
    C.sides f = C.totalSides := by
  letI : Unique (Fin C.faceCount) :=
    ⟨⟨0, by omega⟩, fun a => Fin.ext (by omega)⟩
  rw [show f = default from Unique.eq_default f]
  simp [PolygonComplex.totalSides]

lemma standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_totalSides_pos
    (C : PolygonComplex) (h1 : C.faceCount = 1) : 0 < C.totalSides := by
  let f : Fin C.faceCount := ⟨0, by omega⟩
  rw [← standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_sides_eq_total C h1 f]
  exact C.sides_pos f

lemma standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_target_sizes
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) :
    C'.faceCount = 1 ∧ C'.totalSides + 2 = C.totalSides ∧
      (∀ f : Fin C.faceCount, C.sides f = C.totalSides) ∧
      (∀ f : Fin C'.faceCount, C'.sides f = C'.totalSides) := by
  refine ⟨D.faceCount_eq, D.totalSides_add_two, ?_, ?_⟩
  · exact fun f =>
      standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_sides_eq_total C h1 f
  · exact fun f =>
      standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_sides_eq_total
        C' D.faceCount_eq f

lemma standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_removed_signs
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (hor : C.IsOrientable) :
    C.sign (C.pair s) = !C.sign s ∧ C'.IsOrientable := by
  constructor
  · cases hs : C.sign s <;> cases hp : C.sign (C.pair s) <;>
      simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
        Bool.true_eq_false, not_false_eq_true]
    · exact False.elim (hor s (hp.trans hs.symm))
    · exact False.elim (hor s (hp.trans hs.symm))
  · exact standardCover_pairingData_aux_contractStep_aux_orientable D hor

/-! Split of `_aux_homeomorph` (claude-14, 2026-10-25, after the lemma-1
PARTIAL).  Read the one face of `C` as a word (`_aux_word`, labels `lab`,
signs `C.sign`); `_aux_bridge` identifies `C.Space` with its `PolygonSurface`.
`_aux_inner`/`_aux_wrap` locate `s`, `C.pair s` as an `x x⁻¹` in the word
(rotated in the wrap case), with the word of `C'` (labels pulled back along
`D.toOld`) the remaining letters; then `PolygonMoves.rotation` and
`PolygonMoves.inversePairCancellation`. -/

/-- The side of a one-face complex at boundary position `i`. -/
def standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_side (C : PolygonComplex) (h1 : C.faceCount = 1)
    (i : Fin C.totalSides) : C.Side :=
  ⟨⟨0, by omega⟩, ⟨i.val, by
    rw [standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_sides_eq_total C h1]; exact i.isLt⟩⟩

/-- The boundary word of a one-face complex, labelled by `lab`. -/
def standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word {L : Type*} (C : PolygonComplex) (h1 : C.faceCount = 1)
    (lab : C.Side → L) : List (PolygonMoves.Signed L) :=
  List.ofFn fun i : Fin C.totalSides =>
    (lab (standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_side C h1 i), C.sign (standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_side C h1 i))

/-- A labelling that names exactly the pairs `{a, C.pair a}`. -/
def standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_GoodLabel {L : Type*} (C : PolygonComplex) (lab : C.Side → L) : Prop :=
  ∀ a b, lab a = lab b ↔ (b = a ∨ b = C.pair a)

/-- **Leaf.**  The smaller position of each pair is a good label; pulled back
along `D.toOld` it is a good label for `C'` (`D.pair_toOld`,
`D.toOld_injective`). -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_goodLabel
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s) :
    standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_GoodLabel C (fun u : C.Side => min u.2.val (C.pair u).2.val) ∧
      standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_GoodLabel C'
        (fun u : C'.Side => min (D.toOld u).2.val (C.pair (D.toOld u)).2.val) := by
  sorry

/-- **Leaf.**  The word of a one-face complex under a good label is a polygon
word: nonempty (`C.sides_pos`), and every label occurs exactly twice
(`C.pair_ne`, `C.pair_pair`), hence even length. -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_isPolygonWord {L : Type*} [DecidableEq L]
    (C : PolygonComplex) (h1 : C.faceCount = 1) (lab : C.Side → L)
    (hlab : standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_GoodLabel C lab) :
    PolygonMoves.IsPolygonWord (standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word C h1 lab) := by
  sorry

/-- **Leaf (bridge).**  `C.Rel` on the single face is `WordRel` of the word:
side `s` at position `s.2` with parameter `pairedParameter`, exactly the
`if`-on-signs of `WordRel`.  Same argument as
`_aux_toPairing_aux_homeomorph_aux_eqv_forward`/`_reverse` together with
`orientablePairing_normalForm_aux_bridge` (no vertex condition is needed). -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_bridge {L : Type*} [DecidableEq L]
    (C : PolygonComplex) (h1 : C.faceCount = 1) (lab : C.Side → L)
    (hlab : standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_GoodLabel C lab) :
    Nonempty (C.Space ≃ₜ PolygonMoves.PolygonSurface (standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word C h1 lab)) := by
  sorry

/-- **Leaf (no wrap).**  If `s` is not the last side, `C.pair s` is the next
one (`hadj`), with the opposite sign (`hor`): the word of `C` is
`u ++ [x, x⁻¹] ++ v` with `u` the first `s.2` letters, and (`D.toOld_lt`,
`D.toOld_surj`, `D.sign_toOld`) the word of `C'` is `u ++ v`. -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_inner
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (hadj : C.nextCorner s = C.pair s)
    (hor : C.IsOrientable) (hk : s.2.val + 1 < C.totalSides) :
    ∃ (u v : List (PolygonMoves.Signed ℕ)) (x : PolygonMoves.Signed ℕ),
      standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word C h1 (fun u : C.Side => min u.2.val (C.pair u).2.val) =
          u ++ [x, PolygonMoves.inv x] ++ v ∧
        standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word C' D.faceCount_eq
          (fun u : C'.Side => min (D.toOld u).2.val (C.pair (D.toOld u)).2.val) = u ++ v ∧
        x.1 ∉ (u ++ v).map Prod.fst := by
  sorry

/-- **Leaf (wrap).**  If `s` is the last side, `C.pair s` is side `0`: the
word of `C` is `x⁻¹ :: v ++ [x]` and the word of `C'` is `v`. -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_wrap
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (hadj : C.nextCorner s = C.pair s)
    (hor : C.IsOrientable) (hk : ¬ s.2.val + 1 < C.totalSides) :
    ∃ (v : List (PolygonMoves.Signed ℕ)) (x : PolygonMoves.Signed ℕ),
      standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word C h1 (fun u : C.Side => min u.2.val (C.pair u).2.val) =
          (PolygonMoves.inv x :: v) ++ [x] ∧
        standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_word C' D.faceCount_eq
          (fun u : C'.Side => min (D.toOld u).2.val (C.pair (D.toOld u)).2.val) = v ∧
        x.1 ∉ v.map Prod.fst := by
  sorry

/-- **Leaf (cancel an adjacent pair).**  Side `C.pair s` follows side `s`
on the boundary (`a a⁻¹`).  Zip the two sides together: the disk map of
`PolygonMoves.inversePairCancellation_aux_collapse` (rotated so the pair sits
at the chosen position; `PolygonMoves.rotation_aux_disk_homeomorph`) descends
to `C.Space ≃ₜ C'.Space` by the argument of
`PolygonMoves.polygonSurface_homeomorph_of_collapse`.  Unlike a collapse of a
general side, the zip is injective on the interior and identifies only points
`C.Rel` already identifies. -/
theorem standardCover_pairingData_aux_contractStep_aux_homeomorph
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides)
    (hadj : C.nextCorner s = C.pair s)
    (hor : C.IsOrientable) : Nonempty (C.Space ≃ₜ C'.Space) := by
  obtain ⟨hlab, hlab'⟩ := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_goodLabel D
  obtain ⟨e₁⟩ := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_bridge C h1 _ hlab
  obtain ⟨e₄⟩ := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_bridge C' D.faceCount_eq _ hlab'
  have hw' := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_isPolygonWord C' D.faceCount_eq _ hlab'
  by_cases hk : s.2.val + 1 < C.totalSides
  · obtain ⟨u, v, x, hw, hv, hx⟩ := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_inner D h1 hadj hor hk
    rw [hv] at hw' e₄
    rw [hw] at e₁
    obtain ⟨e₂⟩ := PolygonMoves.inversePairCancellation u v x hx hw'
    exact ⟨e₁.trans (e₂.trans e₄.symm)⟩
  · obtain ⟨v, x, hw, hv, hx⟩ := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_wrap D h1 hadj hor hk
    have hwC := standardCover_pairingData_aux_contractStep_aux_homeomorph_aux_isPolygonWord C h1 _ hlab
    rw [hv] at hw' e₄
    rw [hw] at e₁ hwC
    obtain ⟨e₃⟩ := PolygonMoves.rotation (PolygonMoves.inv x :: v) [x] hwC
    have hrot : [x] ++ (PolygonMoves.inv x :: v) = [] ++ [x, PolygonMoves.inv x] ++ v := by simp
    rw [hrot] at e₃
    obtain ⟨e₂⟩ := PolygonMoves.inversePairCancellation [] v x (by simpa using hx)
      (by simpa using hw')
    simp only [List.nil_append] at e₂ e₃
    exact ⟨e₁.trans (e₃.trans (e₂.trans e₄.symm))⟩

/-- **Leaf (the middle corner of `a a⁻¹` is its own vertex).**  If
`C.pair s = C.nextCorner s` and `C` is orientable, every `CornerRel` step
from the corner `m = C.nextCorner s` returns to `m` (the only sides at `m` are
`s` and `C.pair s`), so the class of `m` is `{m}`, and `s ≠ m` because the face
has at least two sides. -/
lemma standardCover_pairingData_aux_contractStep_aux_adjacentDistinct_aux_next_injective
    (C : PolygonComplex) (h1 : C.faceCount = 1) :
    Function.Injective C.nextCorner := by
  intro u v huv
  have hf : u.1 = v.1 := by
    apply Fin.eq_of_val_eq
    omega
  apply Sigma.ext hf
  apply (Fin.heq_ext_iff (congrArg C.sides hf)).2
  have hv := congrArg (fun w : C.Side => w.2.val) huv
  simp only [PolygonComplex.nextCorner] at hv
  have hsizes : C.sides u.1 = C.sides v.1 := congrArg C.sides hf
  by_cases hu : u.2.val + 1 < C.sides u.1
  · rw [Nat.mod_eq_of_lt hu] at hv
    by_cases hv' : v.2.val + 1 < C.sides v.1
    · rw [Nat.mod_eq_of_lt hv'] at hv
      omega
    · have heq : v.2.val + 1 = C.sides v.1 := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  · have heq : u.2.val + 1 = C.sides u.1 := by omega
    rw [heq, Nat.mod_self] at hv
    by_cases hv' : v.2.val + 1 < C.sides v.1
    · rw [Nat.mod_eq_of_lt hv'] at hv
      omega
    · have heq' : v.2.val + 1 = C.sides v.1 := by omega
      omega

lemma standardCover_pairingData_aux_contractStep_aux_adjacentDistinct_aux_next_ne
    (C : PolygonComplex) (h1 : C.faceCount = 1) (h3 : 3 ≤ C.totalSides)
    (u : C.Side) : C.nextCorner u ≠ u := by
  letI : Unique (Fin C.faceCount) :=
    { default := ⟨0, by omega⟩
      uniq := fun f => Fin.ext (by have := f.2; omega) }
  have hsides : C.totalSides = C.sides u.1 := by
    calc
      C.totalSides = C.sides (default : Fin C.faceCount) := by
        simp [PolygonComplex.totalSides]
      _ = C.sides u.1 := congrArg C.sides (Subsingleton.elim _ _)
  intro hu
  have hv := congrArg (fun w : C.Side => w.2.val) hu
  simp only [PolygonComplex.nextCorner] at hv
  by_cases hlt : u.2.val + 1 < C.sides u.1
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : u.2.val + 1 = C.sides u.1 := by omega
    rw [heq, Nat.mod_self] at hv
    omega

lemma standardCover_pairingData_aux_contractStep_aux_adjacentDistinct_aux_step
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hor : C.IsOrientable)
    (s a b : C.Side) (hadj : C.nextCorner s = C.pair s)
    (hab : C.CornerRel a b) :
    (a = C.nextCorner s ↔ b = C.nextCorner s) := by
  obtain ⟨u, hu⟩ := hab
  rw [if_neg (Ne.symm (hor u))] at hu
  have hn :=
    standardCover_pairingData_aux_contractStep_aux_adjacentDistinct_aux_next_injective C h1
  rcases hu with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · constructor
    · intro h
      subst a
      subst b
      have hp : C.pair u = s := by
        have := congrArg C.pair h
        simpa [hadj, C.pair_pair] using this
      simpa [hp]
    · intro h
      subst a
      subst b
      have hp : C.pair u = s := hn h
      have := congrArg C.pair hp
      simpa [C.pair_pair, hadj] using this
  · constructor
    · intro h
      subst a
      subst b
      have hu : u = s := hn h
      simpa [hu, hadj]
    · intro h
      subst a
      subst b
      have hu : u = s := C.pair.injective (by simpa [hadj] using h)
      simpa [hu]

theorem standardCover_pairingData_aux_contractStep_aux_adjacentDistinct
    (C : PolygonComplex) (h1 : C.faceCount = 1) (h3 : 3 ≤ C.totalSides)
    (hor : C.IsOrientable) (s : C.Side) (hadj : C.nextCorner s = C.pair s) :
    Quotient.mk (Relation.EqvGen.setoid C.CornerRel) s ≠
      Quotient.mk (Relation.EqvGen.setoid C.CornerRel) (C.nextCorner s) := by
  intro hq
  have hrel : Relation.EqvGen C.CornerRel s (C.nextCorner s) := Quotient.exact hq
  have key : ∀ a b, Relation.EqvGen C.CornerRel a b →
      (a = C.nextCorner s ↔ b = C.nextCorner s) := by
    intro a b h
    induction h with
    | rel a b hab =>
        exact standardCover_pairingData_aux_contractStep_aux_adjacentDistinct_aux_step
          C h1 hor s a b hadj hab
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hs : s = C.nextCorner s := (key s (C.nextCorner s) hrel).mpr rfl
  exact (standardCover_pairingData_aux_contractStep_aux_adjacentDistinct_aux_next_ne
    C h1 h3 s) hs.symm

/-- **Leaf, NOT YET SPLIT (bring a pair together).**  A one-face orientable
complex with at least two vertices is homeomorphic to one with the same
number of sides and vertices in which some side is followed by its partner.
Massey's induction on the corner count of a vertex class `Q`: if `Q` has one
corner, the sides at it are `a a⁻¹` (orientability); otherwise take sides
`a` (from `P ≠ Q` to `Q`) and `b` (from `Q`) at a corner of `Q`, with
`b ≠ C.pair a` (else done), cut off the triangle `a b c⁻¹` and glue it back
along `b`: `X a b Y b⁻¹ Z` becomes `X c Y c⁻¹ a Z`, with one fewer corner in
`Q` and the same vertex count.  The cut is a `GlueData` read backwards and
both homeomorphisms are `_aux_glueStep_aux_homeomorph`; vertex counts are kept
by `_aux_glueStep_aux_vertexCount`. -/
theorem standardCover_pairingData_aux_contractStep_aux_isolate
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : 2 ≤ C.vertexCount)
    (hlarge : 2 * C.vertexCount < C.totalSides) (hor : C.IsOrientable) :
    ∃ C₁ : PolygonComplex, C₁.faceCount = 1 ∧ C₁.totalSides = C.totalSides ∧
      C₁.vertexCount = C.vertexCount ∧ C₁.IsOrientable ∧
      Nonempty (C.Space ≃ₜ C₁.Space) ∧
      ∃ s : C₁.Side, C₁.nextCorner s = C₁.pair s := by
  sorry

/-- **One vertex removed.**  Move corners by cut-and-paste until some side
is followed by its partner (`_aux_isolate`), then cancel that pair
(`_aux_homeomorph`): two boundary arcs go, and the middle corner, a vertex on
its own (`_aux_adjacentDistinct`), merges away.  `2 * vertexCount < totalSides`
excludes the sphere words, where the contraction would reach zero sides; it
is preserved by the step. -/
theorem standardCover_pairingData_aux_contractStep
    (C : PolygonComplex) (h1 : C.faceCount = 1) (hV : 2 ≤ C.vertexCount)
    (hlarge : 2 * C.vertexCount < C.totalSides) (hor : C.IsOrientable) :
    ∃ C' : PolygonComplex, C'.faceCount = 1 ∧ C'.totalSides + 2 = C.totalSides ∧
      C'.vertexCount + 1 = C.vertexCount ∧ C'.IsOrientable ∧
      Nonempty (C.Space ≃ₜ C'.Space) := by
  obtain ⟨C₁, h1₁, hT₁, hV₁, hor₁, ⟨e₁⟩, s, hadj⟩ :=
    standardCover_pairingData_aux_contractStep_aux_isolate C h1 hV hlarge hor
  have h5 : 5 ≤ C₁.totalSides := by
    have := standardCover_pairingData_aux_contractStep_aux_totalSides_five_le C hV hlarge
    omega
  have hs := standardCover_pairingData_aux_contractStep_aux_adjacentDistinct
    C₁ h1₁ (by omega) hor₁ s hadj
  obtain ⟨C', ⟨D⟩⟩ :=
    standardCover_pairingData_aux_contractStep_aux_contractExists C₁ h1₁ (by omega) s
  obtain ⟨e₂⟩ := standardCover_pairingData_aux_contractStep_aux_homeomorph D h1₁ h5 hadj hor₁
  exact ⟨C', D.faceCount_eq, by have := D.totalSides_add_two; omega,
    by have := standardCover_pairingData_aux_contractStep_aux_vertexCount D h1₁ h5 hs hor₁
       omega,
    standardCover_pairingData_aux_contractStep_aux_orientable D hor₁,
    ⟨e₁.trans e₂⟩⟩

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
theorem standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_val
    (C : PolygonComplex) (h1 : C.faceCount = 1) (s : C.Side) :
    (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 s).1 = s.2.1 := by
  letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
  have hf : s.1 = default := Unique.uniq
    (standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1) s.1
  obtain ⟨f, i⟩ := s
  dsimp at hf ⊢
  subst f
  simp [standardCover_pairingData_aux_toPairing_aux_sideEquiv,
    Equiv.uniqueSigma, finCongr]

theorem standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_next
    (C : PolygonComplex) (h1 : C.faceCount = 1) (s : C.Side) :
    polygonVertex C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 (C.nextCorner s)) =
      edgePoint C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 s)
        PolygonBoundaryVertexClasses.oneIcc := by
  rw [PolygonBoundaryVertexClasses.edgePoint_one_eq_succ_zero]
  unfold polygonVertex
  by_cases h : s.2.1 + 1 < C.sides s.1
  · apply congrArg (fun k : ℕ => edgePoint C.totalSides k
      PolygonBoundaryVertexClasses.zeroIcc)
    rw [standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_val,
      standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_val]
    simp [PolygonComplex.nextCorner, Nat.mod_eq_of_lt h]
  · have hw : s.2.1 + 1 = C.sides s.1 := by omega
    rw [standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_val,
      standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_val]
    apply Subtype.ext
    simp only [PolygonComplex.nextCorner, hw, Nat.mod_self, edgePoint,
      PolygonBoundaryVertexClasses.zeroIcc, Set.mem_Icc, le_refl, zero_le_one,
      add_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one, Complex.ofReal_zero,
      Complex.exp_zero]
    rw [show C.totalSides = C.sides s.1 by
      letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
      simpa [PolygonComplex.totalSides] using
        congrArg C.sides (Subsingleton.elim default s.1)]
    simp only [mul_zero, zero_div, Complex.exp_zero]
    have hn : (C.sides s.1 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (C.sides_pos s.1))
    have hfrac : 2 * (Real.pi : ℂ) * (C.sides s.1 : ℂ) /
        (C.sides s.1 : ℂ) = 2 * Real.pi := by field_simp
    rw [show (↑(↑(C.sides s.1) : ℝ) : ℂ) = (C.sides s.1 : ℂ) by norm_num,
      hfrac]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Complex.exp_two_pi_mul_I.symm

theorem standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_rel
    (C : PolygonComplex) (h1 : C.faceCount = 1) (s : C.Side)
    (t : Set.Icc (0 : ℝ) 1) :
    boundaryRel C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_pair C h1)
        (standardCover_pairingData_aux_toPairing_aux_sign C h1)
      (edgePoint C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 s) t)
      (edgePoint C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 (C.pair s))
        (C.pairedParameter s t)) := by
  refine ⟨standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 s, t, rfl, ?_⟩
  simp [standardCover_pairingData_aux_toPairing_aux_pair,
    standardCover_pairingData_aux_toPairing_aux_sign,
    PolygonSurfacePiOne.pairedParameter, PolygonComplex.pairedParameter,
    Equiv.permCongr_apply]

theorem standardCover_pairingData_aux_toPairing_aux_cornerStep
    (C : PolygonComplex) (h1 : C.faceCount = 1) (a b : C.Side)
    (hab : C.CornerRel a b) :
    Relation.EqvGen (boundaryRel C.totalSides
        (standardCover_pairingData_aux_toPairing_aux_pair C h1)
        (standardCover_pairingData_aux_toPairing_aux_sign C h1))
      (polygonVertex C.totalSides (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 a))
      (polygonVertex C.totalSides (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 b)) := by
  obtain ⟨s, hs⟩ := hab
  by_cases hsign : C.sign s = C.sign (C.pair s)
  · simp only [hsign, if_pos] at hs
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a; subst b
      apply Relation.EqvGen.rel
      simpa [polygonVertex, PolygonComplex.pairedParameter, hsign,
        PolygonBoundaryVertexClasses.zeroIcc] using
        (standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_rel C h1 s
          PolygonBoundaryVertexClasses.zeroIcc)
    · subst a; subst b
      apply Relation.EqvGen.rel
      rw [standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_next,
        standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_next]
      simpa [PolygonComplex.pairedParameter, hsign] using
        (standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_rel C h1 s
          PolygonBoundaryVertexClasses.oneIcc)
  · simp only [hsign, if_neg] at hs
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a; subst b
      apply Relation.EqvGen.rel
      rw [standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_next]
      simpa [polygonVertex, PolygonComplex.pairedParameter, hsign, reverseIcc,
        PolygonBoundaryVertexClasses.zeroIcc,
        PolygonBoundaryVertexClasses.oneIcc] using
        (standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_rel C h1 s
          PolygonBoundaryVertexClasses.zeroIcc)
    · subst a; subst b
      apply Relation.EqvGen.rel
      rw [standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_next]
      simpa [polygonVertex, PolygonComplex.pairedParameter, hsign, reverseIcc,
        PolygonBoundaryVertexClasses.zeroIcc,
        PolygonBoundaryVertexClasses.oneIcc] using
        (standardCover_pairingData_aux_toPairing_aux_cornerStep_aux_rel C h1 s
          PolygonBoundaryVertexClasses.oneIcc)

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
theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_sides
    (C : PolygonComplex) (h1 : C.faceCount = 1) (f : Fin C.faceCount) :
    C.sides f = C.totalSides := by
  letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
  rw [show f = default from Unique.eq_default f]
  simp [PolygonComplex.totalSides]

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_sideVal
    (C : PolygonComplex) (h1 : C.faceCount = 1) (s : C.Side) :
    (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 s).val = s.2.val := by
  letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
  obtain ⟨f, i⟩ := s
  have hf : f = default := Unique.eq_default f
  subst f
  simp [standardCover_pairingData_aux_toPairing_aux_sideEquiv,
    Equiv.uniqueSigma_apply]

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_edgePoint
    (C : PolygonComplex) (h1 : C.faceCount = 1) (s : C.Side)
    (t : Set.Icc (0 : ℝ) 1) :
    edgePoint (C.sides s.1) s.2 t = edgePoint C.totalSides
      (standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1 s) t := by
  exact congrArg₂ (fun m e : ℕ => edgePoint m e t)
    (standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_sides C h1 s.1)
    (standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_sideVal C h1 s).symm

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_rel_forward
    (C : PolygonComplex) (h1 : C.faceCount = 1)
    {x y : Σ _ : Fin C.faceCount, Disk} (hxy : C.Rel x y) :
    boundaryRel C.totalSides
      (standardCover_pairingData_aux_toPairing_aux_pair C h1)
      (standardCover_pairingData_aux_toPairing_aux_sign C h1) x.2 y.2 := by
  rcases hxy with ⟨s, t, rfl, rfl⟩
  let e := standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1
  refine ⟨e s, t, ?_, ?_⟩
  · exact standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_edgePoint C h1 s t
  · rw [standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_edgePoint C h1 (C.pair s)]
    simp [standardCover_pairingData_aux_toPairing_aux_pair, Equiv.permCongr_apply,
      PolygonComplex.pairedParameter, PolygonSurfacePiOne.pairedParameter,
      standardCover_pairingData_aux_toPairing_aux_sign, e]

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_rel_reverse
    (C : PolygonComplex) (h1 : C.faceCount = 1) {x y : Disk}
    (hxy : boundaryRel C.totalSides
      (standardCover_pairingData_aux_toPairing_aux_pair C h1)
      (standardCover_pairingData_aux_toPairing_aux_sign C h1) x y) :
    C.Rel
      ⟨(standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1).default, x⟩
      ⟨(standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1).default, y⟩ := by
  letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
  rcases hxy with ⟨i, t, rfl, rfl⟩
  let e := standardCover_pairingData_aux_toPairing_aux_sideEquiv C h1
  let s : C.Side := e.symm i
  refine ⟨s, t, ?_, ?_⟩
  · apply Sigma.ext (Unique.eq_default s.1).symm
    rw [standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_edgePoint C h1 s]
    simp [s, e]
  · apply Sigma.ext (Unique.eq_default (C.pair s).1).symm
    rw [standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_edgePoint C h1 (C.pair s)]
    simp [standardCover_pairingData_aux_toPairing_aux_pair, Equiv.permCongr_apply,
      PolygonComplex.pairedParameter, PolygonSurfacePiOne.pairedParameter,
      standardCover_pairingData_aux_toPairing_aux_sign, s, e]

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_eqv_forward
    (C : PolygonComplex) (h1 : C.faceCount = 1)
    {x y : Σ _ : Fin C.faceCount, Disk}
    (hxy : Relation.EqvGen C.Rel x y) :
    Relation.EqvGen (boundaryRel C.totalSides
      (standardCover_pairingData_aux_toPairing_aux_pair C h1)
      (standardCover_pairingData_aux_toPairing_aux_sign C h1)) x.2 y.2 := by
  induction hxy with
  | rel x y h =>
      apply Relation.EqvGen.rel
      exact standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_rel_forward C h1 h
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_eqv_reverse
    (C : PolygonComplex) (h1 : C.faceCount = 1) {x y : Disk}
    (hxy : Relation.EqvGen (boundaryRel C.totalSides
      (standardCover_pairingData_aux_toPairing_aux_pair C h1)
      (standardCover_pairingData_aux_toPairing_aux_sign C h1)) x y) :
    Relation.EqvGen C.Rel
      ⟨(standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1).default, x⟩
      ⟨(standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1).default, y⟩ := by
  induction hxy with
  | rel x y h =>
      apply Relation.EqvGen.rel
      exact standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_rel_reverse C h1 h
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem standardCover_pairingData_aux_toPairing_aux_homeomorph
    (C : PolygonComplex) (h1 : C.faceCount = 1)
    (hvert : ∀ i j : Fin C.totalSides,
      Relation.EqvGen (boundaryRel C.totalSides
          (standardCover_pairingData_aux_toPairing_aux_pair C h1)
          (standardCover_pairingData_aux_toPairing_aux_sign C h1))
        (polygonVertex C.totalSides i) (polygonVertex C.totalSides j)) :
    Nonempty (C.Space ≃ₜ
      (standardCover_pairingData_aux_toPairing_aux_pairing C h1 hvert).Space) := by
  let P := standardCover_pairingData_aux_toPairing_aux_pairing C h1 hvert
  letI := standardCover_pairingData_aux_toPairing_aux_uniqueFace C h1
  refine ⟨{
    toFun := Quotient.lift (fun z : Σ _ : Fin C.faceCount, Disk =>
      Quotient.mk (Relation.EqvGen.setoid P.Rel) z.2) (fun _ _ h => Quotient.sound ?_)
    invFun := Quotient.lift (fun x : Disk =>
      Quotient.mk (Relation.EqvGen.setoid C.Rel) ⟨default, x⟩)
      (fun _ _ h => Quotient.sound ?_)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }⟩
  · exact standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_eqv_forward C h1 h
  · exact standardCover_pairingData_aux_toPairing_aux_homeomorph_aux_eqv_reverse C h1 h
  · rintro ⟨⟨f, x⟩⟩
    have hf : f = default := Unique.eq_default f
    subst f
    rfl
  · rintro ⟨x⟩
    rfl
  · apply Continuous.quotient_lift
    apply continuous_sigma
    intro f
    exact continuous_coinduced_rng
  · apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp continuous_sigmaMk

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
  rcases h with ⟨i, t, hx, hy⟩
  refine ⟨P.pair i, pairedParameter P.pair P.sign i t, hy, ?_⟩
  rw [P.pair_pair i]
  have ht :
      pairedParameter P.pair P.sign (P.pair i)
          (pairedParameter P.pair P.sign i t) = t := by
    by_cases hs : P.sign i = P.sign (P.pair i)
    · unfold PolygonSurfacePiOne.pairedParameter
      rw [P.pair_pair, if_pos hs.symm, if_pos hs]
    · have hs' : P.sign (P.pair i) ≠ P.sign i := by
        exact fun hsi => hs hsi.symm
      unfold PolygonSurfacePiOne.pairedParameter
      rw [P.pair_pair, if_neg hs', if_neg hs, reverseIcc_reverseIcc]
  exact hx.trans (congrArg (edgePoint P.edgeCount i) ht.symm)

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
theorem orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_finRotate
    {n m : ℕ} (h : n = m) (i : Fin n) (j : Fin m)
    (hv : (i : ℕ) = j) :
    (finRotate n i : ℕ) = finRotate m j := by
  subst m
  have : i = j := Fin.ext hv
  subst j
  rfl

theorem orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_one
    (n : ℕ) (hn : 0 < n) (i : Fin n) :
    edgePoint n i PolygonBoundaryVertexClasses.oneIcc =
      polygonVertex n (finRotate n i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [PolygonBoundaryVertexClasses.edgePoint_one_eq_succ_zero]
  by_cases hi : (i : ℕ) < m
  · rw [finRotate_of_lt hi]
    rfl
  · have hilast : i = Fin.last m := by
      apply Fin.ext
      simp
      omega
    rw [hilast, finRotate_last]
    apply Subtype.ext
    simp only [polygonVertex, edgePoint, PolygonBoundaryVertexClasses.zeroIcc,
      Nat.cast_add, Nat.cast_one, Fin.val_zero]
    simp only [Fin.val_last, Nat.cast_succ, Nat.cast_zero, add_zero]
    push_cast
    simp only [add_zero, zero_add]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    have hfrac : (2 : ℂ) * Real.pi * ((m : ℂ) + 1) / ((m : ℂ) + 1) =
        2 * Real.pi := by
      have hmC : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast hm
      field_simp
    rw [hfrac]
    rw [mul_comm]
    convert Complex.exp_two_pi_mul_I using 1 <;> simp

theorem orientablePairing_normalForm_aux_natWord_oneVertex_aux_step (P : PairingData)
    (a : Fin (orientablePairing_normalForm_aux_natWord P).length) {x y : Disk}
    (h : P.Rel x y)
    (hx : orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach P a x) :
    orientablePairing_normalForm_aux_natWord_oneVertex_aux_Reach P a y := by
  rcases h with ⟨i, t, hxi, hyi⟩
  rcases hx with ⟨c, hxc, hac⟩
  have hit : edgePoint P.edgeCount i t =
      polygonVertex P.edgeCount
        ⟨c, by simpa [orientablePairing_normalForm_aux_natWord] using c.2⟩ := by
    rw [← hxi, hxc]
  rcases orientablePairing_normalForm_aux_natWord_oneVertex_aux_endpoint
      P.edgeCount P.edgeCount_pos i
      ⟨c, by simpa [orientablePairing_normalForm_aux_natWord] using c.2⟩ t hit with
    hzero | hone
  let i' : Fin (orientablePairing_normalForm_aux_natWord P).length :=
    ⟨i, by simpa [orientablePairing_normalForm_aux_natWord] using i.2⟩
  let j' : Fin (orientablePairing_normalForm_aux_natWord P).length :=
    ⟨P.pair i, by simpa [orientablePairing_normalForm_aux_natWord] using (P.pair i).2⟩
  have hlen : (orientablePairing_normalForm_aux_natWord P).length = P.edgeCount := by
    simp [orientablePairing_normalForm_aux_natWord]
  have hij : i' ≠ j' := by
    intro e
    apply P.pair_ne i
    exact Fin.ext (congrArg Fin.val e).symm
  have hlab :
      ((orientablePairing_normalForm_aux_natWord P).get i').1 =
        ((orientablePairing_normalForm_aux_natWord P).get j').1 := by
    simp [orientablePairing_normalForm_aux_natWord,
      orientablePairing_normalForm_aux_wordOf, i', j']
  by_cases hs : P.sign i = P.sign (P.pair i)
  · refine ⟨j', ?_, Relation.EqvGen.trans a c j' hac
        (Relation.EqvGen.rel c j' ?_)⟩
    · rw [hyi]
      simp [PolygonSurfacePiOne.pairedParameter, hs, hzero.1, polygonVertex, j']
    · refine ⟨i', j', hij, hlab, ?_⟩
      have hsign :
          ((orientablePairing_normalForm_aux_natWord P).get i').2 =
            ((orientablePairing_normalForm_aux_natWord P).get j').2 := by
        simpa [orientablePairing_normalForm_aux_natWord,
          orientablePairing_normalForm_aux_wordOf, i', j'] using hs
      rw [if_pos hsign]
      exact Or.inl ⟨Fin.ext (by simpa [i'] using
        (congrArg Fin.val hzero.2)), rfl⟩
  · let d : Fin (orientablePairing_normalForm_aux_natWord P).length :=
      finRotate _ j'
    refine ⟨d, ?_, Relation.EqvGen.trans a c d hac
      (Relation.EqvGen.rel c d ?_)⟩
    · rw [hyi]
      simp [PolygonSurfacePiOne.pairedParameter, hs, hzero.1,
        PolygonSurfacePiOne.reverseIcc, polygonVertex]
      change edgePoint P.edgeCount (P.pair i)
        PolygonBoundaryVertexClasses.oneIcc = _
      have hedge := orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_one
        P.edgeCount P.edgeCount_pos (P.pair i)
      rw [hedge]
      unfold polygonVertex
      exact congrArg (fun k : ℕ => edgePoint P.edgeCount k ⟨0, by simp⟩)
        (orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_finRotate
          hlen.symm (P.pair i) j' rfl)
    · refine ⟨i', j', hij, hlab, ?_⟩
      have hsign :
          ((orientablePairing_normalForm_aux_natWord P).get i').2 ≠
            ((orientablePairing_normalForm_aux_natWord P).get j').2 := by
        simpa [orientablePairing_normalForm_aux_natWord,
          orientablePairing_normalForm_aux_wordOf, i', j'] using hs
      rw [if_neg hsign]
      exact Or.inl ⟨Fin.ext (by simpa [i'] using
        (congrArg Fin.val hzero.2)), rfl⟩
  let i' : Fin (orientablePairing_normalForm_aux_natWord P).length :=
    ⟨i, by simpa [orientablePairing_normalForm_aux_natWord] using i.2⟩
  let j' : Fin (orientablePairing_normalForm_aux_natWord P).length :=
    ⟨P.pair i, by simpa [orientablePairing_normalForm_aux_natWord] using (P.pair i).2⟩
  have hlen : (orientablePairing_normalForm_aux_natWord P).length = P.edgeCount := by
    simp [orientablePairing_normalForm_aux_natWord]
  have hij : i' ≠ j' := by
    intro e
    apply P.pair_ne i
    exact Fin.ext (congrArg Fin.val e).symm
  have hlab :
      ((orientablePairing_normalForm_aux_natWord P).get i').1 =
        ((orientablePairing_normalForm_aux_natWord P).get j').1 := by
    simp [orientablePairing_normalForm_aux_natWord,
      orientablePairing_normalForm_aux_wordOf, i', j']
  by_cases hs : P.sign i = P.sign (P.pair i)
  · let d : Fin (orientablePairing_normalForm_aux_natWord P).length :=
      finRotate _ j'
    refine ⟨d, ?_, Relation.EqvGen.trans a c d hac
      (Relation.EqvGen.rel c d ?_)⟩
    · rw [hyi]
      simp [PolygonSurfacePiOne.pairedParameter, hs, hone.1, polygonVertex]
      change edgePoint P.edgeCount (P.pair i)
        PolygonBoundaryVertexClasses.oneIcc = _
      have hedge := orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_one
        P.edgeCount P.edgeCount_pos (P.pair i)
      rw [hedge]
      unfold polygonVertex
      exact congrArg (fun k : ℕ => edgePoint P.edgeCount k ⟨0, by simp⟩)
        (orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_finRotate
          hlen.symm (P.pair i) j' rfl)
    · refine ⟨i', j', hij, hlab, ?_⟩
      have hsign :
          ((orientablePairing_normalForm_aux_natWord P).get i').2 =
            ((orientablePairing_normalForm_aux_natWord P).get j').2 := by
        simpa [orientablePairing_normalForm_aux_natWord,
          orientablePairing_normalForm_aux_wordOf, i', j'] using hs
      rw [if_pos hsign]
      exact Or.inr ⟨Fin.ext (by simpa [i', orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf] using (show (c : Nat) =
          (finRotate _ i' : Nat) by
            rw [congrArg Fin.val hone.2]
            exact orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_finRotate
              hlen.symm i i' rfl)), rfl⟩
  · refine ⟨j', ?_, Relation.EqvGen.trans a c j' hac
        (Relation.EqvGen.rel c j' ?_)⟩
    · rw [hyi]
      simp [PolygonSurfacePiOne.pairedParameter, hs, hone.1,
        PolygonSurfacePiOne.reverseIcc, polygonVertex, j']
    · refine ⟨i', j', hij, hlab, ?_⟩
      have hsign :
          ((orientablePairing_normalForm_aux_natWord P).get i').2 ≠
            ((orientablePairing_normalForm_aux_natWord P).get j').2 := by
        simpa [orientablePairing_normalForm_aux_natWord,
          orientablePairing_normalForm_aux_wordOf, i', j'] using hs
      rw [if_neg hsign]
      exact Or.inr ⟨Fin.ext (by simpa [i', orientablePairing_normalForm_aux_natWord,
        orientablePairing_normalForm_aux_wordOf] using (show (c : Nat) =
          (finRotate _ i' : Nat) by
            rw [congrArg Fin.val hone.2]
            exact orientablePairing_normalForm_aux_natWord_oneVertex_aux_step_aux_finRotate
              hlen.symm i i' rfl)), rfl⟩

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


/-- The lift behind `_aux_angular`, before rotating by `n₂ + 1` arcs: on
`[0, L]` (in arc units) it fixes the `α₁` arcs, stretches the `y` arc onto
`[n₁, L - n₂ - 1]`, shifts the `α₂` arcs onto `[L - n₂ - 1, L - 1]` and
compresses the chord arc onto `[L - 1, L]`.  (lemma-3, banked.) -/
def orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    (L n₁ n₂ : ℕ) (x : ℝ) : ℝ :=
  if x ≤ n₁ then x
  else if x ≤ n₁ + 1 then
    n₁ + (x - n₁) * (L - n₁ - n₂ - 1)
  else if x ≤ n₁ + 1 + n₂ then
    L - n₂ - 1 + (x - (n₁ + 1))
  else L - 1 + (x - (n₁ + 1 + n₂)) / (L - (n₁ + 1 + n₂))

def orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    (L n₁ n₂ : ℕ) (y : ℝ) : ℝ :=
  if y ≤ n₁ then y
  else if y ≤ L - n₂ - 1 then
    n₁ + (y - n₁) / (L - n₁ - n₂ - 1)
  else if y ≤ L - 1 then
    n₁ + 1 + (y - (L - n₂ - 1))
  else n₁ + 1 + n₂ + (y - (L - 1)) * (L - (n₁ + 1 + n₂))

lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p_continuous
    (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    Continuous (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂) := by
  have hL' : (n₁ : ℝ) + 1 + n₂ < L := by exact_mod_cast hL
  unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
  have h3 : Continuous (fun x : ℝ => if x ≤ (n₁ : ℝ) + 1 + n₂ then
      (L : ℝ) - n₂ - 1 + (x - (n₁ + 1))
    else L - 1 + (x - (n₁ + 1 + n₂)) / (L - (n₁ + 1 + n₂))) := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro x hx; rw [hx]; field_simp; ring
  have h2 : Continuous (fun x : ℝ => if x ≤ (n₁ : ℝ) + 1 then
      n₁ + (x - n₁) * (L - n₁ - n₂ - 1)
    else if x ≤ n₁ + 1 + n₂ then L - n₂ - 1 + (x - (n₁ + 1))
    else L - 1 + (x - (n₁ + 1 + n₂)) / (L - (n₁ + 1 + n₂))) := by
    apply Continuous.if_le (by fun_prop) h3 (by fun_prop) (by fun_prop)
    intro x hx; rw [hx]
    simp only [if_pos (by linarith : (n₁ : ℝ) + 1 ≤ n₁ + 1 + n₂)]
    ring
  apply Continuous.if_le (by fun_prop) h2 (by fun_prop) (by fun_prop)
  intro x hx; rw [hx]
  simp only [if_pos (by norm_num : (n₁ : ℝ) ≤ n₁ + 1)]
  ring

lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q_continuous
    (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    Continuous (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q L n₁ n₂) := by
  have hL' : (n₁ : ℝ) + 1 + n₂ < L := by exact_mod_cast hL
  unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
  have h3 : Continuous (fun x : ℝ => if x ≤ (L : ℝ) - 1 then
      n₁ + 1 + (x - (L - n₂ - 1))
    else n₁ + 1 + n₂ + (x - (L - 1)) * (L - (n₁ + 1 + n₂))) := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro x hx; rw [hx]; ring
  have h2 : Continuous (fun x : ℝ => if x ≤ (L : ℝ) - n₂ - 1 then
      n₁ + (x - n₁) / (L - n₁ - n₂ - 1)
    else if x ≤ L - 1 then n₁ + 1 + (x - (L - n₂ - 1))
    else n₁ + 1 + n₂ + (x - (L - 1)) * (L - (n₁ + 1 + n₂))) := by
    apply Continuous.if_le (by fun_prop) h3 (by fun_prop) (by fun_prop)
    intro x hx; rw [hx]
    have hn : (0 : ℝ) ≤ n₂ := by positivity
    have hi : (L : ℝ) - n₂ - 1 ≤ L - 1 := by linarith
    rw [if_pos hi]
    field_simp [ne_of_gt (show (0 : ℝ) < L - n₁ - n₂ - 1 by linarith)]
    ring
  apply Continuous.if_le (by fun_prop) h2 (by fun_prop) (by fun_prop)
  intro x hx; rw [hx]
  simp only [if_pos (by linarith : (n₁ : ℝ) ≤ L - n₂ - 1)]
  field_simp
  ring

/-- **Leaf.**  `_p` and `_q` (the four-piece monotone map of `[0, L]` behind
`_aux_angular` and its piecewise inverse) are mutually inverse homeomorphisms of
`ℝ` that fix `0` and `L` and map `[0, L]` to itself.  The breakpoints of `_q`
are the images under `_p` of those of `_p`; both outer pieces are affine on
all of `ℝ`, so the inverse laws hold globally.  Continuity is already proved
(`_p_continuous`, `_q_continuous`). -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_props_aux_cast
    (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    (n₁ : ℝ) + 1 + n₂ < L := by
  exact_mod_cast hL

set_option maxHeartbeats 1000000 in
lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_props
    (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    let p := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂
    let q := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q L n₁ n₂
    Continuous p ∧ Continuous q ∧ Function.LeftInverse q p ∧ Function.RightInverse q p ∧
      p 0 = 0 ∧ p L = L ∧ q 0 = 0 ∧ q L = L ∧
      Set.MapsTo p (Set.Icc 0 L) (Set.Icc 0 L) ∧
      Set.MapsTo q (Set.Icc 0 L) (Set.Icc 0 L) := by
  have hL' := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_props_aux_cast L n₁ n₂ hL
  have hd : (0 : ℝ) < L - n₁ - n₂ - 1 := by linarith
  have hd' : (0 : ℝ) < L - (n₁ + 1 + n₂) := by linarith
  dsimp
  refine ⟨orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p_continuous L n₁ n₂ hL,
    orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q_continuous L n₁ n₂ hL,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    set_option maxHeartbeats 1000000 in
      split_ifs with h₁ h₂ h₃ k₁ k₂ k₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith
  · intro x
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    set_option maxHeartbeats 1000000 in
      split_ifs with h₁ h₂ h₃ k₁ k₂ k₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    simp
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    simp only [if_neg (by linarith : ¬ ((L : ℝ) ≤ n₁)),
      if_neg (by linarith : ¬ ((L : ℝ) ≤ n₁ + 1)),
      if_neg (by linarith : ¬ ((L : ℝ) ≤ n₁ + 1 + n₂))]
    field_simp [ne_of_gt hd']; ring
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    simp
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    simp only [if_neg (by linarith : ¬ ((L : ℝ) ≤ n₁)),
      if_neg (by linarith : ¬ ((L : ℝ) ≤ L - n₂ - 1)),
      if_neg (by norm_num : ¬ ((L : ℝ) ≤ L - 1))]
    ring
  · intro x hx
    constructor
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1]
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1, hx.2]
  · intro x hx
    constructor
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1, hx.2]
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1, hx.2]

/-- Values of `_p` on the four old arcs: identity on the `α₁` arcs, the `y`
arc stretched onto `[n₁, L - n₂ - 1]`, the `α₂` arcs shifted to start at
`L - n₂ - 1`, the chord arc compressed onto `[L - 1, L]`. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_formulas (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    (∀ e (s : Set.Icc (0 : ℝ) 1), e < n₁ → orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂ (e + s.1) = e + s.1) ∧
    (∀ s : Set.Icc (0 : ℝ) 1, orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂ (n₁ + s.1) = n₁ + s.1 * (L - n₁ - n₂ - 1)) ∧
    (∀ e (s : Set.Icc (0 : ℝ) 1), n₁ + 1 ≤ e → e < n₁ + 1 + n₂ →
      orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂ (e + s.1) = L - n₂ - 1 + (e - (n₁ + 1)) + s.1) ∧
    (∀ s : Set.Icc (0 : ℝ) 1,
      orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂ (n₁ + 1 + n₂ + s.1 * (L - (n₁ + 1 + n₂))) = L - 1 + s.1) := by
  have hL' : (n₁ : ℝ) + 1 + n₂ < L := by exact_mod_cast hL
  have hn₂ : (0 : ℝ) ≤ n₂ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e s he
    have he' : (e : ℝ) + 1 ≤ n₁ := by exact_mod_cast he
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    rw [if_pos (by linarith [s.2.2])]
  · intro s
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    by_cases h0 : (n₁ : ℝ) + s.1 ≤ n₁
    · have hs : s.1 = 0 := le_antisymm (by linarith) s.2.1
      rw [if_pos h0, hs]; ring
    · rw [if_neg h0, if_pos (by linarith [s.2.2])]; ring
  · intro e s he₀ he₁
    have he₀' : (n₁ : ℝ) + 1 ≤ e := by exact_mod_cast he₀
    have he₁' : (e : ℝ) + 1 ≤ n₁ + 1 + n₂ := by exact_mod_cast he₁
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    rw [if_neg (by linarith [s.2.1])]
    by_cases h1 : (e : ℝ) + s.1 ≤ n₁ + 1
    · have he : (e : ℝ) = n₁ + 1 := le_antisymm (by linarith [s.2.1]) he₀'
      have hs : s.1 = 0 := le_antisymm (by linarith) s.2.1
      rw [if_pos h1, he, hs]; ring
    · rw [if_neg h1, if_pos (by linarith [s.2.2])]; ring
  · intro s
    have hd : (0 : ℝ) < L - (n₁ + 1 + n₂) := by linarith
    have hx : 0 ≤ s.1 * (L - (n₁ + 1 + n₂)) := mul_nonneg s.2.1 hd.le
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    rw [if_neg (show ¬ ((n₁ : ℝ) + 1 + n₂ + s.1 * (L - (n₁ + 1 + n₂)) ≤ n₁) by linarith)]
    by_cases h2 : (n₁ : ℝ) + 1 + n₂ + s.1 * (L - (n₁ + 1 + n₂)) ≤ n₁ + 1 + n₂
    · have hs : s.1 = 0 := by
        rcases eq_or_lt_of_le s.2.1 with h | h
        · exact h.symm
        · nlinarith
      by_cases h1 : (n₁ : ℝ) + 1 + n₂ + s.1 * (L - (n₁ + 1 + n₂)) ≤ n₁ + 1
      · have hn : (n₂ : ℝ) = 0 := by rw [hs] at h1; linarith
        rw [if_pos h1, hs, hn]; ring
      · rw [if_neg h1, if_pos h2, hs]; ring
    · rw [if_neg (show ¬ ((n₁ : ℝ) + 1 + n₂ + s.1 * (L - (n₁ + 1 + n₂)) ≤ n₁ + 1) by
          intro h; exact h2 (by linarith)), if_neg h2]
      field_simp; ring

open PolygonMoves in
/-- **Leaf (circle reparametrisation, piece `A`).**  An orientation-preserving
piecewise-linear homeomorphism of the parameter circle of piece `A` that moves
the old boundary arcs `α₁ y α₂ c⁻¹` to the new positions `α₂ c⁻¹ α₁ y`: the
`α₁` arcs shift by `n₂ + 1`, the `y` arc goes onto the chord arc, the `α₂`
arcs shift back by `n₁ + 1`, and the chord arc goes onto arc `n₂`.  The pieces
fit at the junction angles (e.g. arc `n₁` at `s = 0` and the chord at `s = 0`
are both at angle `α q`); `n₁ = 0` and `n₂ = 0` are allowed.  Built like
`equivariantLift_of_interval` from a monotone lift on `[0, 2π]`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular
    (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ e (s : Set.Icc (0 : ℝ) 1), e < n₁ →
        ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L e + s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) =
          AddCircle.homeomorphCircle'
            (((cutAlpha L (e + n₂ + 1) + s.1 * (2 * Real.pi / L) : ℝ) :
              AddCircle (2 * Real.pi)))) ∧
      (∀ s : Set.Icc (0 : ℝ) 1, ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L n₁ + s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) =
        AddCircle.homeomorphCircle'
          (((cutAlpha L (n₁ + 1 + n₂) +
              s.1 * (cutAlpha L 0 + 2 * Real.pi - cutAlpha L (n₁ + 1 + n₂)) : ℝ) :
            AddCircle (2 * Real.pi)))) ∧
      (∀ e (s : Set.Icc (0 : ℝ) 1), n₁ + 1 ≤ e → e < n₁ + 1 + n₂ →
        ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L e + s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) =
          AddCircle.homeomorphCircle'
            (((cutAlpha L (e - n₁ - 1) + s.1 * (2 * Real.pi / L) : ℝ) :
              AddCircle (2 * Real.pi)))) ∧
      (∀ s : Set.Icc (0 : ℝ) 1, ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L (n₁ + 1 + n₂) +
              s.1 * (cutAlpha L 0 + 2 * Real.pi - cutAlpha L (n₁ + 1 + n₂)) : ℝ) :
              AddCircle (2 * Real.pi)))) =
        AddCircle.homeomorphCircle'
          (((cutAlpha L n₂ + s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) := by
  obtain ⟨hpc, hqc, hl, hr, hp0, hpL, hq0, hqL, hpm, hqm⟩ := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_props L n₁ n₂ hL
  obtain ⟨hf₁, hfy, hf₂, hfc⟩ := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_formulas L n₁ n₂ hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
  obtain ⟨F, hF⟩ := equivariantLift_of_interval (L : ℝ) L hLpos hLpos (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂) (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q L n₁ n₂)
    hpc hqc hp0 hpL hq0 hqL hpm hqm (fun x _ => hl x) (fun y _ => hr y)
  obtain ⟨g, hg⟩ := equivariantCircleLift_homeomorph (L : ℝ) L hLpos hLpos F
  let r : Circle := Circle.exp ((n₂ + 1) * (2 * Real.pi / L))
  refine ⟨g.trans (Homeomorph.mulLeft r), ?_⟩
  -- ρ at angle `2πx/L`, for `x ∈ [0, L]`, is the angle `2π(p x + n₂ + 1)/L`.
  have hρ : ∀ x ∈ Set.Icc (0 : ℝ) L, ∀ θ : ℝ, θ = 2 * Real.pi * x / L →
      (g.trans (Homeomorph.mulLeft r)) (AddCircle.homeomorphCircle' (θ : AddCircle (2 * Real.pi))) =
        Circle.exp (2 * Real.pi * (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂ x + n₂ + 1) / L) := by
    intro x hx θ hθ
    have h1 : AddCircle.homeomorphCircle' (θ : AddCircle (2 * Real.pi)) =
        AddCircle.toCircle (x : AddCircle (L : ℝ)) := by
      rw [AddCircle.homeomorphCircle'_apply_mk, AddCircle.toCircle_apply_mk, hθ]
      congr 1; field_simp
    rw [Homeomorph.trans_apply, h1, hg, hF x hx, AddCircle.toCircle_apply_mk]
    change r * _ = _
    rw [← Circle.exp_add]; congr 1; field_simp; ring
  -- Circle.exp agrees with homeomorphCircle' up to a multiple of `2π`.
  have hexp : ∀ a b : ℝ, ∀ k : ℤ, a = b + k * (2 * Real.pi) →
      Circle.exp a = AddCircle.homeomorphCircle' (b : AddCircle (2 * Real.pi)) := by
    intro a b k h
    rw [AddCircle.homeomorphCircle'_apply_mk, h, Circle.exp_add,
      Circle.exp_int_mul_two_pi, mul_one]
  have hπ := Real.pi_pos
  have hL' : (n₁ : ℝ) + 1 + n₂ < L := by exact_mod_cast hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e s he
    have he' : (e : ℝ) + 1 ≤ n₁ := by exact_mod_cast he
    rw [hρ (e + s.1) ⟨by linarith [s.2.1], by linarith [s.2.2]⟩ _
      (by unfold cutAlpha; field_simp; try ring), hf₁ e s he]
    exact hexp _ _ 0 (by unfold cutAlpha; push_cast; field_simp; try ring)
  · intro s
    rw [hρ (n₁ + s.1) ⟨by linarith [s.2.1], by linarith [s.2.2]⟩ _
      (by unfold cutAlpha; field_simp; try ring), hfy s]
    exact hexp _ _ 0 (by unfold cutAlpha; push_cast; field_simp; try ring)
  · intro e s he₀ he₁
    have he₀' : (n₁ : ℝ) + 1 ≤ e := by exact_mod_cast he₀
    have he₁' : (e : ℝ) + 1 ≤ n₁ + 1 + n₂ := by exact_mod_cast he₁
    rw [hρ (e + s.1) ⟨by linarith [s.2.1], by linarith [s.2.2]⟩ _
      (by unfold cutAlpha; field_simp; try ring), hf₂ e s he₀ he₁]
    have hsub : ((e - n₁ - 1 : ℕ) : ℝ) = e - n₁ - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    exact hexp _ _ 1 (by unfold cutAlpha; rw [hsub]; push_cast; field_simp; try ring)
  · intro s
    have hL' : (n₁ : ℝ) + 1 + n₂ < L := by exact_mod_cast hL
    rw [hρ (n₁ + 1 + n₂ + s.1 * (L - (n₁ + 1 + n₂)))
      ⟨by nlinarith [s.2.1, s.2.2], by nlinarith [s.2.1, s.2.2]⟩ _
      (by unfold cutAlpha; push_cast; field_simp; try ring), hfc s]
    exact hexp _ _ 1 (by unfold cutAlpha; push_cast; field_simp; try ring)

open PolygonMoves in
/-- Piece `A` reparametrisation in `cutEdgeCircle`/`cutChordParamA` form, read
off from the angular statement `_aux_angular`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reparamA (L n₁ n₂ : ℕ)
    (hL : n₁ + 1 + n₂ < L) :
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ e s, e < n₁ → ρ (cutEdgeCircle L e s) = cutEdgeCircle L (e + n₂ + 1) s) ∧
      (∀ s, ρ (cutEdgeCircle L n₁ s) = cutChordParamA L 0 (n₁ + 1 + n₂) s) ∧
      (∀ e s, n₁ + 1 ≤ e → e < n₁ + 1 + n₂ →
        ρ (cutEdgeCircle L e s) = cutEdgeCircle L (e - n₁ - 1) s) ∧
      (∀ s, ρ (cutChordParamA L 0 (n₁ + 1 + n₂) s) = cutEdgeCircle L n₂ s) := by
  obtain ⟨ρ, h₁, hy, h₂, hc⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular L n₁ n₂ hL
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · intro e s he
    rw [cutBoundaryData_concrete_aux_edge_circle,
      cutBoundaryData_concrete_aux_edge_circle]
    exact h₁ e s he
  · intro s
    rw [cutBoundaryData_concrete_aux_edge_circle]
    exact hy s
  · intro e s he₀ he₁
    rw [cutBoundaryData_concrete_aux_edge_circle,
      cutBoundaryData_concrete_aux_edge_circle]
    exact h₂ e s he₀ he₁
  · intro s
    rw [cutBoundaryData_concrete_aux_edge_circle]
    exact hc s

open PolygonMoves in
/-- **Leaf (circle reparametrisation, piece `B`).**  As `_aux_reparamA` for
piece `B`: old arcs `β₁ y⁻¹ β₂ c` (arcs `q … L-1`, then the chord arc
`cutChordParamB`, angles `2π … α q + 2π`) go to `β₂ c β₁ y⁻¹`.  With `m₁ = 0`
the `y⁻¹` arc starts at angle `α q`, where the chord arc ends; both formulas
then give angle `0`. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamB_aux_angular_aux_cutAlpha_zero
    (L : ℕ) : cutAlpha L 0 = 0 := by simp [cutAlpha]

set_option maxHeartbeats 1000000

lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamB_aux_angular_aux_props
    (L a b : ℕ) (hL : a + 1 + b < L) :
    let p := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L a b
    let q := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q L a b
    Continuous p ∧ Continuous q ∧ Function.LeftInverse q p ∧ Function.RightInverse q p ∧
      p 0 = 0 ∧ p L = L ∧ q 0 = 0 ∧ q L = L ∧
      Set.MapsTo p (Set.Icc 0 L) (Set.Icc 0 L) ∧
      Set.MapsTo q (Set.Icc 0 L) (Set.Icc 0 L) := by
  have hL' : (a : ℝ) + 1 + b < L := by exact_mod_cast hL
  have hd : (0 : ℝ) < L - a - b - 1 := by linarith
  have hd' : (0 : ℝ) < L - (a + 1 + b) := by linarith
  dsimp
  refine ⟨orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p_continuous L a b hL,
    orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q_continuous L a b hL,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    split_ifs with h₁ h₂ h₃ k₁ k₂ k₃ <;>
      field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith
  · intro x
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    set_option maxHeartbeats 1000000 in
      split_ifs with h₁ h₂ h₃ k₁ k₂ k₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    simp
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
    simp only [if_neg (by linarith : ¬ ((L : ℝ) ≤ a)),
      if_neg (by linarith : ¬ ((L : ℝ) ≤ a + 1)),
      if_neg (by linarith : ¬ ((L : ℝ) ≤ a + 1 + b))]
    field_simp [ne_of_gt hd']; ring
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    simp
  · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
    simp only [if_neg (by linarith : ¬ ((L : ℝ) ≤ a)),
      if_neg (by linarith : ¬ ((L : ℝ) ≤ L - b - 1)),
      if_neg (by norm_num : ¬ ((L : ℝ) ≤ L - 1))]
    ring
  · intro x hx
    constructor
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1]
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1, hx.2]
  · intro x hx
    constructor
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1, hx.2]
    · unfold orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q
      split_ifs with h₁ h₂ h₃ <;>
        field_simp [ne_of_gt hd, ne_of_gt hd'] at * <;> nlinarith [hx.1, hx.2]

open PolygonMoves

theorem orientablePairing_normalForm_aux_cutPaste_aux_reparamB_aux_angular
    (L n₁ n₂ m₁ m₂ : ℕ)
    (hL : L = n₁ + 1 + n₂ + m₁ + 1 + m₂) :
    ∃ ρ : Circle ≃ₜ Circle,
      (∀ e (s : Set.Icc (0 : ℝ) 1), n₁ + 1 + n₂ ≤ e → e < n₁ + 1 + n₂ + m₁ →
        ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L e + s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) =
          AddCircle.homeomorphCircle'
            (((cutAlpha L (e + m₂ + 1) + s.1 * (2 * Real.pi / L) : ℝ) :
              AddCircle (2 * Real.pi)))) ∧
      (∀ s : Set.Icc (0 : ℝ) 1,
        ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L (n₁ + 1 + n₂ + m₁) +
              s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) =
          AddCircle.homeomorphCircle'
            (((2 * Real.pi + s.1 * cutAlpha L (n₁ + 1 + n₂) : ℝ) :
              AddCircle (2 * Real.pi)))) ∧
      (∀ e (s : Set.Icc (0 : ℝ) 1), n₁ + 1 + n₂ + m₁ + 1 ≤ e → e < L →
        ρ (AddCircle.homeomorphCircle'
            (((cutAlpha L e + s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) =
          AddCircle.homeomorphCircle'
            (((cutAlpha L (e - m₁ - 1) + s.1 * (2 * Real.pi / L) : ℝ) :
              AddCircle (2 * Real.pi)))) ∧
      (∀ s : Set.Icc (0 : ℝ) 1,
        ρ (AddCircle.homeomorphCircle'
            (((2 * Real.pi + s.1 * cutAlpha L (n₁ + 1 + n₂) : ℝ) :
              AddCircle (2 * Real.pi)))) =
          AddCircle.homeomorphCircle'
            (((cutAlpha L (n₁ + 1 + n₂ + m₂) +
              s.1 * (2 * Real.pi / L) : ℝ) : AddCircle (2 * Real.pi)))) := by
  let q := n₁ + 1 + n₂
  have hm : m₁ + 1 + m₂ < L := by omega
  obtain ⟨hpc, hqc, hl, hr, hp0, hpL, hq0, hqL, hpm, hqm⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reparamB_aux_angular_aux_props
      L m₁ m₂ hm
  obtain ⟨hf₁, hfy, hf₂, hfc⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_formulas
      L m₁ m₂ hm
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
  obtain ⟨F, hF⟩ := equivariantLift_of_interval (L : ℝ) L hLpos hLpos
    (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L m₁ m₂)
    (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q L m₁ m₂)
    hpc hqc hp0 hpL hq0 hqL hpm hqm (fun x _ => hl x) (fun y _ => hr y)
  obtain ⟨g, hg⟩ := equivariantCircleLift_homeomorph (L : ℝ) L hLpos hLpos F
  let r₁ : Circle := Circle.exp (-(q : ℝ) * (2 * Real.pi / L))
  let r₂ : Circle := Circle.exp ((q + m₂ + 1 : ℝ) * (2 * Real.pi / L))
  let ρ := (Homeomorph.mulLeft r₁).trans (g.trans (Homeomorph.mulLeft r₂))
  refine ⟨ρ, ?_⟩
  have hρ : ∀ x ∈ Set.Icc (0 : ℝ) L, ∀ θ : ℝ,
      θ = 2 * Real.pi * (x + q) / L →
      ρ (AddCircle.homeomorphCircle' (θ : AddCircle (2 * Real.pi))) =
        Circle.exp (2 * Real.pi *
          (orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p
            L m₁ m₂ x + q + m₂ + 1) / L) := by
    intro x hx θ hθ
    have h1 : r₁ * AddCircle.homeomorphCircle' (θ : AddCircle (2 * Real.pi)) =
        AddCircle.toCircle (x : AddCircle (L : ℝ)) := by
      rw [AddCircle.homeomorphCircle'_apply_mk, AddCircle.toCircle_apply_mk]
      change Circle.exp _ * Circle.exp _ = Circle.exp _
      rw [← Circle.exp_add, hθ]
      congr 1; field_simp; ring
    change r₂ * g (r₁ * AddCircle.homeomorphCircle' (θ : AddCircle (2 * Real.pi))) = _
    rw [h1, hg, hF x hx, AddCircle.toCircle_apply_mk]
    change r₂ * Circle.exp _ = _
    rw [← Circle.exp_add]
    congr 1; field_simp; ring
  have hexp : ∀ a b : ℝ, ∀ k : ℤ, a = b + k * (2 * Real.pi) →
      Circle.exp a = AddCircle.homeomorphCircle' (b : AddCircle (2 * Real.pi)) := by
    intro a b k h
    rw [AddCircle.homeomorphCircle'_apply_mk, h, Circle.exp_add,
      Circle.exp_int_mul_two_pi, mul_one]
  have hπ := Real.pi_pos
  have hq : q = n₁ + 1 + n₂ := rfl
  have hreal : (L : ℝ) = q + m₁ + 1 + m₂ := by exact_mod_cast hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e s he₀ he₁
    have heq : q ≤ e := by simpa [q] using he₀
    have he : e - q < m₁ := by simp [q] at he₁ ⊢; omega
    have hecast : ((e - q : ℕ) : ℝ) = e - q := by rw [Nat.cast_sub heq]
    have hx0 : (0 : ℝ) ≤ (e - q : ℕ) + s.1 :=
      add_nonneg (Nat.cast_nonneg _) s.2.1
    have hxL : (e - q : ℕ) + s.1 ≤ (L : ℝ) := by
      have he' : ((e - q : ℕ) : ℝ) < m₁ := by exact_mod_cast he
      have hm' : (m₁ : ℝ) + 1 ≤ L := by exact_mod_cast (show m₁ + 1 ≤ L by omega)
      linarith [s.2.2]
    rw [hρ ((e - q : ℕ) + s.1)
      ⟨hx0, hxL⟩ _
      (by unfold cutAlpha; rw [hecast]; push_cast; simp [q]; field_simp; ring), hf₁ (e - q) s he]
    exact hexp _ _ 0 (by unfold cutAlpha; rw [hecast]; push_cast; simp [q]; field_simp; ring)
  · intro s
    have hx0 : (0 : ℝ) ≤ m₁ + s.1 := add_nonneg (Nat.cast_nonneg _) s.2.1
    have hxL : (m₁ : ℝ) + s.1 ≤ L := by
      have hm' : (m₁ : ℝ) + 1 ≤ L := by exact_mod_cast (show m₁ + 1 ≤ L by omega)
      linarith [s.2.2]
    rw [hρ (m₁ + s.1) ⟨hx0, hxL⟩ _
      (by unfold cutAlpha; push_cast; simp [q]; field_simp; ring), hfy s]
    exact hexp _ _ 0 (by unfold cutAlpha; push_cast; rw [hreal]; simp [q]; field_simp; ring)
  · intro e s he₀ he₁
    have heq : q ≤ e := by simp [q] at he₀ ⊢; omega
    have he0 : m₁ + 1 ≤ e - q := by simp [q] at he₀ ⊢; omega
    have he1 : e - q < m₁ + 1 + m₂ := by omega
    have hecast : ((e - q : ℕ) : ℝ) = e - q := by rw [Nat.cast_sub heq]
    have hx0 : (0 : ℝ) ≤ (e - q : ℕ) + s.1 :=
      add_nonneg (Nat.cast_nonneg _) s.2.1
    have hxL : (e - q : ℕ) + s.1 ≤ (L : ℝ) := by
      have he' : ((e - q : ℕ) : ℝ) < m₁ + 1 + m₂ := by exact_mod_cast he1
      have hm' : (m₁ : ℝ) + 1 + m₂ + 1 ≤ L := by exact_mod_cast (show m₁ + 1 + m₂ + 1 ≤ L by omega)
      linarith [s.2.2]
    rw [hρ ((e - q : ℕ) + s.1)
      ⟨hx0, hxL⟩ _
      (by unfold cutAlpha; rw [hecast]; push_cast; simp [q]; field_simp; ring),
      hf₂ (e - q) s he0 he1]
    have hsub : ((e - m₁ - 1 : ℕ) : ℝ) = e - m₁ - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    exact hexp _ _ 1 (by unfold cutAlpha; rw [hecast, hsub]; push_cast; simp [q]; field_simp; ring)
  · intro s
    have harg : (m₁ : ℝ) + 1 + m₂ + s.1 * (L - (m₁ + 1 + m₂)) + q =
        L + s.1 * q := by rw [hreal]; ring
    rw [hρ (m₁ + 1 + m₂ + s.1 * (L - (m₁ + 1 + m₂)))
      ⟨by nlinarith [s.2.1, s.2.2], by nlinarith [s.2.1, s.2.2]⟩ _
      (by unfold cutAlpha; push_cast; rw [harg]; simp [q]; field_simp), hfc s]
    exact hexp _ _ 1 (by unfold cutAlpha; push_cast; rw [hreal]; simp [q]; field_simp; ring)

open PolygonMoves in
/-- Piece `B` of the cut-and-paste reparametrisation, read off from the angular
statement `_aux_angular`. -/
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
  obtain ⟨ρ, h₁, hy, h₂, hc⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reparamB_aux_angular
      L n₁ n₂ m₁ m₂ hL
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · intro e s he₀ he₁
    rw [cutBoundaryData_concrete_aux_edge_circle,
      cutBoundaryData_concrete_aux_edge_circle]
    exact h₁ e s he₀ he₁
  · intro s
    rw [cutBoundaryData_concrete_aux_edge_circle]
    simpa [cutChordParamB, cutAlpha] using hy s
  · intro e s he₀ he₁
    rw [cutBoundaryData_concrete_aux_edge_circle,
      cutBoundaryData_concrete_aux_edge_circle]
    exact h₂ e s he₀ he₁
  · intro s
    rw [cutBoundaryData_concrete_aux_edge_circle]
    simpa [cutChordParamB, cutAlpha] using hc s

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_y_fresh
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed L)) (y : PolygonMoves.Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst) :
    y.1 ∉ α₁.map Prod.fst ∧ y.1 ∉ α₂.map Prod.fst ∧
      y.1 ∉ β₁.map Prod.fst ∧ y.1 ∉ β₂.map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or] at hy
  aesop

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_c_fresh
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed L))
    (y c : PolygonMoves.Signed L)
    (hc : c.1 ∉
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).map Prod.fst) :
    c.1 ∉ α₁.map Prod.fst ∧ c.1 ≠ y.1 ∧ c.1 ∉ α₂.map Prod.fst ∧
      c.1 ∉ β₁.map Prod.fst ∧ c.1 ∉ β₂.map Prod.fst := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or, PolygonMoves.inv,
    Prod.fst] at hc
  aesop

open PolygonMoves in
/-- Where an old boundary point (side `e`, parameter `s`) goes under the cut:
the `y` sides land on the chord (piece `A` reads it as `cutChordA`, piece `B` as
`cutChordB`), every other side moves rigidly to its position in the new word
`α₂ c⁻¹ α₁ β₂ c β₁` (`n₁ = |α₁|`, `n₂ = |α₂|`, `m₁ = |β₁|`, `m₂ = |β₂|`). -/
noncomputable def orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
    (L n₁ n₂ m₁ m₂ e : ℕ) (s : Icc (0 : ℝ) 1) : ℂ :=
  if e = n₁ then cutChordA L 0 (n₁ + 1 + n₂) s
  else if e = n₁ + 1 + n₂ + m₁ then cutChordB L 0 (n₁ + 1 + n₂) s
  else if e < n₁ then (edgePoint L (e + n₂ + 1) s : ℂ)
  else if e < n₁ + 1 + n₂ then (edgePoint L (e - n₁ - 1) s : ℂ)
  else if e < n₁ + 1 + n₂ + m₁ then (edgePoint L (e + m₂ + 1) s : ℂ)
  else (edgePoint L (e - m₁ - 1) s : ℂ)

open PolygonMoves in
lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_c
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (c : Signed L)
    (s : Icc (0 : ℝ) 1) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁))
      (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length α₂.length s)
      (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length
        (α₂.length + 1 + α₁.length + β₂.length) (reverseParameter s)) := by
  apply Relation.EqvGen.rel
  let i : Fin (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length :=
    ⟨α₂.length, by simp⟩
  let j : Fin (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length :=
    ⟨α₂.length + 1 + α₁.length + β₂.length, by simp; omega⟩
  have hi : (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i = inv c := by
    simp [i, List.get_eq_getElem, List.getElem_append]
  have hj : (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j = c := by
    rw [List.get_eq_getElem]
    simp [j, List.getElem_append, Nat.add_assoc]
    simp [Nat.add_comm, List.getElem_append]
  refine ⟨i, j, ?_, s, ?_, rfl, ?_⟩
  · intro h
    have := congrArg Fin.val h
    change α₂.length = α₂.length + 1 + α₁.length + β₂.length at this
    omega
  · rw [hi, hj]
    simp [inv]
  · rw [hi, hj]
    simp [inv, reverseParameter]
    rfl

open PolygonMoves in
lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA_end
    {L p q : ℕ} (hpq : p < q) (hqL : q < L) (s : Icc (0 : ℝ) 1)
    (h : ‖cutChordA L p q s‖ = 1) : s.1 = 0 ∨ s.1 = 1 := by
  exact cut_transfer_consistency_aux_chordA_end hpq hqL s h

open PolygonMoves in
lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordB_end
    {L p q : ℕ} (hpq : p < q) (hqL : q < L) (s : Icc (0 : ℝ) 1)
    (h : ‖cutChordB L p q s‖ = 1) : s.1 = 0 ∨ s.1 = 1 := by
  exact cut_transfer_consistency_aux_chordB_end hpq hqL s h

open PolygonMoves in
/-- **Leaf (piece `A`, arc, next-name case).**  The point is the end of side `e`
(`τ = 1`) and the start of side `e₀ = (e+1) % L` (`s₀ = 0`).  Seams: `e₀ = p`
(start of `y`, mapped to the chord) and the wrap at `q`, which need `_aux_c`.
Model: `PolygonMoves.cut_transfer_consistency_A_arc_aux_next`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_next
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : e₀ < α₁.length + 1 + α₂.length)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))
    (hN : (N : ℂ) =
      oldA (ρA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)))
    (hτ : τ.1 = 1) (hs₀ : s₀.1 = 0)
    (hadj : e₀ = (e + 1) % (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  let LL := (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
  let p := α₁.length
  let q := α₁.length + 1 + α₂.length
  let z : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let o : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have hlen : LL = p + 1 + α₂.length + β₁.length + 1 + β₂.length := by
    simp [LL, p]
    omega
  have hLL : 2 ≤ LL := by omega
  have he₀L : e₀ < LL := by omega
  have hs : s₀ = z := Subtype.ext hs₀
  have ht : τ = o := Subtype.ext hτ
  subst s₀
  subst τ
  have hedges : edgePoint LL e o = edgePoint LL e₀ z := by
    apply Subtype.ext
    exact hP.trans (D.oldA_arc e₀ z he₀)
  have hNform :
      (N : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        LL p α₂.length β₁.length β₂.length e₀ z := by
    rw [hN]
    by_cases h₁ : e₀ < p
    · rw [D.ρA_α₁ e₀ z h₁, D.oldA_arc]
      · change (edgePoint LL (e₀ + α₂.length + 1) z : ℂ) = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : e₀ ≠ p),
          if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
          if_pos h₁]
      · omega
    · by_cases hy₀ : e₀ = p
      · rw [hy₀] at hN ⊢
        rw [D.ρA_y, D.oldA_chord]
        change cutChordA LL 0 (p + 1 + α₂.length) z = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer, if_pos rfl]
      · have hp₀ : p + 1 ≤ e₀ := by omega
        rw [D.ρA_α₂ e₀ z hp₀ he₀, D.oldA_arc]
        · change (edgePoint LL (e₀ - p - 1) z : ℂ) = _
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg hy₀,
            if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
            if_neg (by omega : ¬ e₀ < p), if_pos he₀]
        · omega
  by_cases he₀z : e₀ = 0
  · rw [he₀z] at hNform hadj he₀
    have he_last : e + 1 = LL := by
      have hele : e + 1 ≤ LL := by omega
      by_contra hn
      have hlt : e + 1 < LL := by omega
      rw [Nat.mod_eq_of_lt hlt] at hadj
      omega
    let r := α₂.length + 1 + p + β₂.length
    refine ⟨edgePoint LL r z, ?_, ?_⟩
    · change (edgePoint LL r z : ℂ) =
        orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
          LL p α₂.length β₁.length β₂.length e o
      by_cases hb2 : β₂.length = 0
      · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : e ≠ p),
          if_pos (by omega : e = p + 1 + α₂.length + β₁.length)]
        simp [cutChordB, z, o]
        have hrq : r = p + 1 + α₂.length := by simp [r, hb2]; omega
        rw [hrq]
        simpa [z] using edgePoint_zero_eq_cutPoint LL (p + 1 + α₂.length)
      · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : e ≠ p),
          if_neg (by omega : e ≠ p + 1 + α₂.length + β₁.length),
          if_neg (by omega : ¬ e < p),
          if_neg (by omega : ¬ e < p + 1 + α₂.length),
          if_neg (by omega : ¬ e < p + 1 + α₂.length + β₁.length)]
        change (edgePoint LL r z : ℂ) = (edgePoint LL (e - β₁.length - 1) o : ℂ)
        rw [show e - β₁.length - 1 = r - 1 by omega]
        have hv := congrArg Subtype.val
          (cut_transfer_consistency_A_arc_aux_next_aux_edge LL (r - 1))
        have hr : r - 1 + 1 = r := by dsimp [r]; omega
        simpa [hr] using hv.symm
    · have hNz : N = edgePoint LL α₂.length o := by
        apply Subtype.ext
        rw [hNform]
        by_cases hp0 : p = 0
        · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_pos hp0.symm]
          simp [cutChordA, z, o, q, hp0]
          simpa [Nat.add_comm] using (edgePoint_one_eq_cutPoint LL α₂.length).symm
        · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg (Ne.symm hp0),
            if_neg (by omega : 0 ≠ p + 1 + α₂.length + β₁.length),
            if_pos (by omega : 0 < p)]
          rw [Nat.zero_add]
          exact congrArg Subtype.val
            (cut_transfer_consistency_A_arc_aux_next_aux_edge LL α₂.length).symm
      rw [hNz]
      simpa [LL, p, r, z, o, reverseParameter, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_c
          α₁ α₂ β₁ β₂ c o)
  · have he_next : e + 1 = e₀ := by
      have hlt : e + 1 < LL := by
        by_contra hn
        have heqL : e + 1 = LL := by omega
        rw [heqL, Nat.mod_self] at hadj
        omega
      rw [Nat.mod_eq_of_lt hlt] at hadj
      exact hadj.symm
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hNform]
    by_cases hltp : e₀ < p
    · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        if_neg (by omega : e₀ ≠ p),
        if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length), if_pos hltp]
      rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        if_neg (by omega : e ≠ p),
        if_neg (by omega : e ≠ p + 1 + α₂.length + β₁.length),
        if_pos (by omega : e < p)]
      have hv := congrArg Subtype.val
        (cut_transfer_consistency_A_arc_aux_next_aux_edge LL (e + α₂.length + 1))
      have hi : e₀ + α₂.length + 1 = e + α₂.length + 1 + 1 := by omega
      rw [hi]
      exact hv.symm
    · by_cases hep : e₀ = p
      · rw [hep] at hNform he_next ⊢
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer, if_pos rfl]
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : e ≠ p),
          if_neg (by omega : e ≠ p + 1 + α₂.length + β₁.length),
          if_pos (by omega : e < p)]
        change cutChordA LL 0 (p + 1 + α₂.length) z =
          (edgePoint LL (e + α₂.length + 1) o : ℂ)
        simp [cutChordA, z, o]
        have hi : e + α₂.length + 1 + 1 = p + 1 + α₂.length := by omega
        rw [← hi]
        exact (edgePoint_one_eq_cutPoint LL (e + α₂.length + 1)).symm
      · have hpe : p + 1 ≤ e₀ := by omega
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg hep,
          if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
          if_neg (by omega : ¬ e₀ < p), if_pos he₀]
        by_cases heyp : e = p
        · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer, if_pos heyp]
          rw [show e₀ - p - 1 = 0 by omega]
          change (edgePoint LL 0 z : ℂ) = cutChordA LL 0 (p + 1 + α₂.length) o
          rw [show (edgePoint LL 0 z : ℂ) = cutPoint LL 0 by
            simpa [z] using edgePoint_zero_eq_cutPoint LL 0]
          simp [cutChordA, o]
        · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg heyp,
            if_neg (by omega : e ≠ p + 1 + α₂.length + β₁.length),
            if_neg (by omega : ¬ e < p), if_pos (by omega : e < p + 1 + α₂.length)]
          have hv := congrArg Subtype.val
            (cut_transfer_consistency_A_arc_aux_next_aux_edge LL (e - p - 1))
          have hi : e₀ - p - 1 = e - p - 1 + 1 := by omega
          rw [hi]
          exact hv.symm

open PolygonMoves in
/-- **Leaf (piece `A`, arc, prev-name case).**  The point is the end of side `e₀`
(`s₀ = 1`) and the start of side `e = (e₀+1) % L` (`τ = 0`).  Seams at `p` and
at `q` (wrap into piece `B`), which need `_aux_c`.
Model: `PolygonMoves.cut_transfer_consistency_A_arc_aux_prev`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge (L k k' : ℕ) (s s' : Icc (0 : ℝ) 1)
    (hk : k = k') (hs : s = s') : (edgePoint L k s : ℂ) = edgePoint L k' s' := by
  subst hk; subst hs; rfl

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_one (L k : ℕ) :
    (edgePoint L k ⟨1, by constructor <;> norm_num⟩ : ℂ) =
      edgePoint L (k + 1) ⟨0, by constructor <;> norm_num⟩ := by
  simp only [edgePoint]
  congr 1
  push_cast
  ring

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_wrap (L : ℕ) (hL : L ≠ 0) :
    (edgePoint L L ⟨0, by constructor <;> norm_num⟩ : ℂ) =
      edgePoint L 0 ⟨0, by constructor <;> norm_num⟩ := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  simp only [edgePoint]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  field_simp
  ring

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_cut (L m : ℕ) :
    cutPoint L m = (edgePoint L m ⟨0, by constructor <;> norm_num⟩ : ℂ) := by
  simp only [cutPoint, cutAlpha, edgePoint]
  congr 1
  push_cast
  ring

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : e₀ < α₁.length + 1 + α₂.length)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))
    (hN : (N : ℂ) =
      oldA (ρA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)))
    (hs₀ : s₀.1 = 1) (hτ : τ.1 = 0)
    (hadj : e = (e₀ + 1) % (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  let LL := (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
  let p := α₁.length
  let q := α₁.length + 1 + α₂.length
  have hlen : LL = p + 1 + α₂.length + β₁.length + 1 + β₂.length := by
    simp [LL, p]; omega
  have he₀L : e₀ + 1 < LL := by omega
  have he_eq : e = e₀ + 1 := by
    change e = (e₀ + 1) % LL at hadj
    rw [Nat.mod_eq_of_lt he₀L] at hadj
    exact hadj
  clear hadj
  subst e
  have hs₀' : s₀ = ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext; exact hs₀
  have hτ' : τ = ⟨0, by constructor <;> norm_num⟩ := by
    apply Subtype.ext; exact hτ
  subst s₀
  subst τ
  have hNform : (N : ℂ) =
      orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        LL p α₂.length β₁.length β₂.length e₀ ⟨1, by constructor <;> norm_num⟩ := by
    rw [hN]
    by_cases h₁ : e₀ < p
    · rw [D.ρA_α₁ e₀ _ h₁, D.oldA_arc]
      · change (edgePoint LL (e₀ + α₂.length + 1) _ : ℂ) = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : e₀ ≠ p),
          if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length), if_pos h₁]
      · omega
    · by_cases hy₀ : e₀ = p
      · subst e₀
        rw [D.ρA_y, D.oldA_chord]
        change cutChordA LL 0 (p + 1 + α₂.length) _ = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer, if_pos rfl]
      · have hp₀ : p + 1 ≤ e₀ := by omega
        rw [D.ρA_α₂ e₀ _ hp₀ he₀, D.oldA_arc]
        · change (edgePoint LL (e₀ - p - 1) _ : ℂ) = _
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg hy₀, if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
            if_neg (by omega : ¬ e₀ < p), if_pos he₀]
        · omega
  by_cases hlast : e₀ + 1 = q
  · have he₀q : e₀ < q := by omega
    let T : Disk := edgePoint LL (α₂.length + 1 + p + β₂.length)
      ⟨1, by constructor <;> norm_num⟩
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      rw [hlast]
      change (edgePoint LL (α₂.length + 1 + p + β₂.length) _ : ℂ) =
        orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
          LL p α₂.length β₁.length β₂.length q _
      rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer]
      by_cases hb : β₁.length = 0
      · rw [if_neg (by omega : q ≠ p),
          if_pos (by omega : q = p + 1 + α₂.length + β₁.length)]
        simp only [cutChordB, Set.Icc.coe_zero, Complex.ofReal_zero, zero_mul, add_zero]
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_cut]
        refine (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_one _ _).trans ((orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge _ _ _ _ _ (by omega : _ = LL) rfl).trans ?_)
        exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_wrap LL (by omega)
      · rw [if_neg (by omega : q ≠ p),
          if_neg (by omega : q ≠ p + 1 + α₂.length + β₁.length),
          if_neg (by omega : ¬ q < p), if_neg (by omega : ¬ q < p + 1 + α₂.length),
          if_pos (by omega : q < p + 1 + α₂.length + β₁.length)]
        exact (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_one _ _).trans (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge _ _ _ _ _ (by omega) rfl)
    · have hc' := orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_c
          α₁ α₂ β₁ β₂ c (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
      have hN' : N = edgePoint LL α₂.length ⟨0, by constructor <;> norm_num⟩ := by
        apply Subtype.ext
        rw [hNform]
        by_cases he₀p : e₀ = p
        · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_pos he₀p]
          simp only [cutChordA]
          simp only [Complex.ofReal_one, one_mul, add_sub_cancel]
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_cut]
          exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge _ _ _ _ _ (by omega) rfl
        · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg he₀p, if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
            if_neg (by omega : ¬ e₀ < p), if_pos he₀q]
          rw [show e₀ - p - 1 = α₂.length - 1 by omega]
          have ha : 0 < α₂.length := by omega
          simp only [edgePoint]
          congr 1
          norm_num
          rw [Nat.cast_sub (by omega : 1 ≤ α₂.length)]
          push_cast
          ring
      rw [hN']
      have hwordlen : (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length = LL := by
        simp [LL]
        omega
      rw [hwordlen] at hc'
      simpa [T, p, reverseParameter] using hc'
  · by_cases he₀p : e₀ = p
    · subst e₀
      have hp1q : p + 1 < q := by omega
      let T : Disk := edgePoint LL 0 ⟨0, by constructor <;> norm_num⟩
      refine ⟨T, ?_, ?_⟩
      · dsimp [T]
        change (edgePoint LL 0 _ : ℂ) =
          orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
            LL p α₂.length β₁.length β₂.length (p + 1) _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : p + 1 ≠ p),
          if_neg (by omega : p + 1 ≠ p + 1 + α₂.length + β₁.length),
          if_neg (by omega : ¬ p + 1 < p), if_pos hp1q]
        congr 2 <;> omega
      · have hNT : N = T := by
          apply Subtype.ext
          rw [hNform, orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_pos rfl]
          change cutChordA LL 0 q _ = _
          simp [T, cutChordA, cutPoint, cutAlpha, edgePoint]
        rw [hNT]
        exact Relation.EqvGen.refl T
    · by_cases he₀_before : e₀ < p
      · let T : Disk := edgePoint LL (e₀ + α₂.length + 2)
          ⟨0, by constructor <;> norm_num⟩
        refine ⟨T, ?_, ?_⟩
        · dsimp [T]
          change (edgePoint LL (e₀ + α₂.length + 2) _ : ℂ) =
            orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
              LL p α₂.length β₁.length β₂.length (e₀ + 1) _
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer]
          by_cases hseam : e₀ + 1 = p
          · rw [if_pos hseam]
            simp only [cutChordA, Set.Icc.coe_zero, Complex.ofReal_zero, zero_mul, add_zero]
            rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_cut]
            exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge _ _ _ _ _ (by omega) rfl
          · rw [if_neg hseam,
              if_neg (by omega : e₀ + 1 ≠ p + 1 + α₂.length + β₁.length),
              if_pos (by omega : e₀ + 1 < p)]
            exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge _ _ _ _ _ (by omega) rfl
        · have hNT : N = T := by
            apply Subtype.ext
            rw [hNform, orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
              if_neg he₀p,
              if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length), if_pos he₀_before]
            simp only [T, edgePoint]
            congr 1
            norm_num
            push_cast
            ring
          rw [hNT]
          exact Relation.EqvGen.refl T
      · have hp₀ : p + 1 ≤ e₀ := by omega
        have he₀next : e₀ + 1 < q := by omega
        have he₀q' : e₀ < p + 1 + α₂.length := by omega
        let T : Disk := edgePoint LL (e₀ - p)
          ⟨0, by constructor <;> norm_num⟩
        refine ⟨T, ?_, ?_⟩
        · dsimp [T]
          change (edgePoint LL (e₀ - p) _ : ℂ) =
            orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
              LL p α₂.length β₁.length β₂.length (e₀ + 1) _
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg (by omega : e₀ + 1 ≠ p),
            if_neg (by omega : e₀ + 1 ≠ p + 1 + α₂.length + β₁.length),
            if_neg (by omega : ¬ e₀ + 1 < p), if_pos he₀next]
          congr 2 <;> omega
        · have hNT : N = T := by
            apply Subtype.ext
            rw [hNform, orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
              if_neg he₀p,
              if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
              if_neg he₀_before, if_pos he₀q']
            exact (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_one _ _).trans (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev_aux_edge _ _ _ _ _ (by omega) rfl)
          rw [hNT]
          exact Relation.EqvGen.refl T

open PolygonMoves in
/-- **Leaf (piece `A`, arc).**  The old point is `edgePoint L e₀ s₀` on an `A`
side `e₀ < q`.  By `cutEdgePoint_eq`, either `(e, τ) = (e₀, s₀)` (then `N` is the
transfer itself) or `(e, τ)` and `(e₀, s₀)` are the two endpoint names of one
vertex, and the two transfers are joined in the new word.  Model:
`PolygonMoves.cut_transfer_consistency_A_arc`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : e₀ < α₁.length + 1 + α₂.length)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))
    (hN : (N : ℂ) =
      oldA (ρA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  let LL := (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
  let p := α₁.length
  let q := α₁.length + 1 + α₂.length
  have hlen : LL = p + 1 + α₂.length + β₁.length + 1 + β₂.length := by
    simp [LL, p]
    omega
  have hLL : 2 ≤ LL := by omega
  have he₀L : e₀ < LL := by omega
  have hedges : edgePoint LL e τ = edgePoint LL e₀ s₀ := by
    apply Subtype.ext
    exact hP.trans (D.oldA_arc e₀ s₀ he₀)
  have hNform :
      (N : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        LL p α₂.length β₁.length β₂.length e₀ s₀ := by
    rw [hN]
    by_cases h₁ : e₀ < p
    · rw [D.ρA_α₁ e₀ s₀ h₁, D.oldA_arc]
      · change (edgePoint LL (e₀ + α₂.length + 1) s₀ : ℂ) = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega : e₀ ≠ p), if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
          if_pos h₁]
      · omega
    · by_cases hy₀ : e₀ = p
      · subst e₀
        rw [D.ρA_y, D.oldA_chord]
        change cutChordA LL 0 (p + 1 + α₂.length) s₀ = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer, if_pos rfl]
      · have hp₀ : p + 1 ≤ e₀ := by omega
        rw [D.ρA_α₂ e₀ s₀ hp₀ he₀, D.oldA_arc]
        · change (edgePoint LL (e₀ - p - 1) s₀ : ℂ) = _
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg hy₀, if_neg (by omega : e₀ ≠ p + 1 + α₂.length + β₁.length),
            if_neg (by omega : ¬ e₀ < p), if_pos he₀]
        · omega
  rcases cutEdgePoint_eq hLL (by exact he) he₀L hedges with hs | hf | hb
  · rcases hs with ⟨rfl, rfl⟩
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    exact hNform
  · rcases hf with ⟨hτ, hs₀, hadj⟩
    exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_next
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N e₀ s₀ he₀ hP hN hτ hs₀ hadj
  · rcases hb with ⟨hs₀, hτ, hadj⟩
    exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA_aux_prev
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N e₀ s₀ he₀ hP hN hs₀ hτ hadj

open PolygonMoves in
/-- **Leaf (piece `A`, chord).**  The old point is `cutChordA L 0 q s₀`; it lies on
the boundary only at `s₀ = 0` (`cutPoint L q`) or `s₀ = 1` (`cutPoint L 0`), see
`_aux_chordA_end`.  `N` is the new `edgePoint L n₂ s₀` (start/end of `c⁻¹`),
joined to the transfer of each name `(e, τ)` of that vertex, using `_aux_c`.
Model: `PolygonMoves.cut_transfer_consistency_A_chord`. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA_aux_zero
    {K : Type*} [DecidableEq K]
    (α₁ α₂ β₁ β₂ : List (Signed K)) (y c : Signed K)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk) (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))
    (hN : (N : ℂ) =
      oldA (ρA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))) (hs : s₀.1 = 0) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  let W := α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂
  let V := α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁
  let q := α₁.length + 1 + α₂.length
  have hlen : W.length = V.length := by simp [W, V]; omega
  have hL : 2 ≤ W.length := by simp [W]; omega
  have hqL : q < W.length := by simp [W, q]; omega
  have hs' : s₀ = (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext; exact hs
  subst s₀
  have hedges : edgePoint W.length e τ =
      edgePoint W.length q (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    calc
      (edgePoint W.length e τ : ℂ) = oldA (cutChordParamA W.length 0 q ⟨0, by constructor <;> norm_num⟩) := hP
      _ = cutChordA W.length 0 q 0 := D.oldA_chord _
      _ = (edgePoint W.length q ⟨0, by constructor <;> norm_num⟩ : ℂ) := by
        simpa [cutChordA] using (edgePoint_zero_eq_cutPoint W.length q).symm
  have hN' : N = edgePoint W.length α₂.length
      (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    calc
      (N : ℂ) = oldA (ρA (cutChordParamA W.length 0 q ⟨0, by constructor <;> norm_num⟩)) := hN
      _ = oldA (cutEdgeCircle W.length α₂.length ⟨0, by constructor <;> norm_num⟩) := by rw [D.ρA_chord]
      _ = (edgePoint W.length α₂.length ⟨0, by constructor <;> norm_num⟩ : ℂ) :=
        D.oldA_arc _ _ (by omega)
  rcases cutEdgePoint_eq hL he hqL hedges with hsame | hnext | hprev
  · rcases hsame with ⟨rfl, hτ⟩; subst τ
    refine ⟨edgePoint V.length (α₂.length + 1 + α₁.length + β₂.length)
      ⟨1, by constructor <;> norm_num⟩, ?_, ?_⟩
    · rw [← hlen]
      rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        if_neg (by dsimp [q]; omega)]
      by_cases hm : β₁.length = 0
      · have hm' : β₁ = [] := List.length_eq_zero_iff.mp hm
        rw [if_pos (by dsimp [q]; omega)]
        rw [edgePoint_one_eq_cutPoint]
        simp [cutChordB]
        have hi : α₂.length + 1 + α₁.length + β₂.length + 1 = W.length := by
          simp [W, hm']; omega
        rw [hi]
        have hraw : α₁.length + (α₂.length + (β₁.length + (β₂.length + 1)) + 1) =
            W.length := by simp [W]
        rw [hraw]
        change cutPoint W.length W.length = cutPoint W.length 0
        simpa using (cutPoint_add_length (L := W.length) (by omega) 0)
      · rw [if_neg (by dsimp [q]; omega), if_neg (by dsimp [q]; omega),
          if_neg (by omega), if_pos (by dsimp [q]; omega)]
        rw [edgePoint_one_eq_cutPoint, edgePoint_zero_eq_cutPoint]
        congr 2 <;> omega
    · rw [hN']
      rw [hlen]
      simpa [V, reverseParameter] using
        (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_c
          α₁ α₂ β₁ β₂ c (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))
  · rcases hnext with ⟨hτ, -, hadj⟩
    have heW : e < W.length := by exact he
    have he1L : e + 1 < W.length := by
      by_contra hn
      have : e + 1 = W.length := by omega
      rw [this, Nat.mod_self] at hadj
      omega
    rw [Nat.mod_eq_of_lt he1L] at hadj
    have heq : e + 1 = q := hadj.symm
    have hτ' : τ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
      apply Subtype.ext; exact hτ
    subst τ
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hN']
    by_cases hn₂ : α₂.length = 0
    · have heα : e = α₁.length := by dsimp [q] at heq; omega
      subst e
      simp [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        W, q, hn₂, cutChordA, edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint]
      exact edgePoint_zero_eq_cutPoint _ _
    · have heα : α₁.length < e := by dsimp [q] at heq; omega
      have heq' : e < q := by omega
      rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos heq']
      rw [edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint]
      congr 2 <;> omega
  · rcases hprev with ⟨hqone, -⟩
    norm_num at hqone

lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA_aux_one
    {K : Type*} [DecidableEq K]
    (α₁ α₂ β₁ β₂ : List (Signed K)) (y c : Signed K)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk) (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))
    (hN : (N : ℂ) =
      oldA (ρA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))) (hs : s₀.1 = 1) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  let W := α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂
  let V := α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁
  let q := α₁.length + 1 + α₂.length
  have hlen : W.length = V.length := by simp [W, V]; omega
  have hL : 2 ≤ W.length := by simp [W]; omega
  have h0L : 0 < W.length := by omega
  have hs' : s₀ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext; exact hs
  subst s₀
  have hedges : edgePoint W.length e τ =
      edgePoint W.length 0 (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    calc
      (edgePoint W.length e τ : ℂ) = oldA (cutChordParamA W.length 0 q ⟨1, by constructor <;> norm_num⟩) := hP
      _ = cutChordA W.length 0 q 1 := D.oldA_chord _
      _ = (edgePoint W.length 0 ⟨0, by constructor <;> norm_num⟩ : ℂ) := by
        simpa [cutChordA] using (edgePoint_zero_eq_cutPoint W.length 0).symm
  have hN' : N = edgePoint W.length α₂.length
      (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    calc
      (N : ℂ) = oldA (ρA (cutChordParamA W.length 0 q ⟨1, by constructor <;> norm_num⟩)) := hN
      _ = oldA (cutEdgeCircle W.length α₂.length ⟨1, by constructor <;> norm_num⟩) := by rw [D.ρA_chord]
      _ = (edgePoint W.length α₂.length ⟨1, by constructor <;> norm_num⟩ : ℂ) :=
        D.oldA_arc _ _ (by omega)
  rcases cutEdgePoint_eq hL he h0L hedges with hsame | hnext | hprev
  · rcases hsame with ⟨rfl, hτ⟩; subst τ
    refine ⟨N, ?_, Relation.EqvGen.refl N⟩
    rw [hN']
    by_cases hn₁ : α₁.length = 0
    · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        if_pos hn₁.symm]
      rw [edgePoint_one_eq_cutPoint]
      simp [cutChordA, q, hn₁]
      have hraw : α₂.length + (β₁.length + (β₂.length + 1)) + 1 = W.length := by
        simp [W, hn₁]
      rw [hraw]
      change cutPoint W.length (α₂.length + 1) = cutPoint W.length (1 + α₂.length)
      congr 1 <;> omega
    · rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
        if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [edgePoint_one_eq_cutPoint, edgePoint_zero_eq_cutPoint]
      congr 2 <;> omega
  · rcases hnext with ⟨hτ, -, hadj⟩
    have hτ' : τ = (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1) := by
      apply Subtype.ext; exact hτ
    subst τ
    have heW : e < W.length := by exact he
    have heLast : e + 1 = W.length := by
      have hel : e + 1 ≤ W.length := by omega
      rcases hel.eq_or_lt with h | h
      · exact h
      · rw [Nat.mod_eq_of_lt h] at hadj
        omega
    refine ⟨edgePoint V.length (α₂.length + 1 + α₁.length + β₂.length)
      ⟨0, by constructor <;> norm_num⟩, ?_, ?_⟩
    · rw [← hlen]
      by_cases hm₂ : β₂.length = 0
      · have heY : e = q + β₁.length := by simp [W, q, hm₂] at heLast ⊢; omega
        subst e
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega), if_pos (by omega), edgePoint_zero_eq_cutPoint]
        simp [cutChordB, q]
        have hraw : α₁.length + (α₂.length + (β₁.length + (β₂.length + 1)) + 1) =
            W.length := by simp [W]
        rw [hraw]
        change cutPoint W.length (α₂.length + 1 + α₁.length + β₂.length) =
          cutPoint W.length (α₁.length + 1 + α₂.length)
        congr 1 <;> omega
      · have heval : e = α₁.length + 1 + α₂.length + β₁.length + β₂.length := by
          simp [W] at heLast
          omega
        subst e
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega), if_neg (by simp [W, q] at heLast; omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [edgePoint_zero_eq_cutPoint, edgePoint_one_eq_cutPoint]
        have hre : α₁.length + 1 + α₂.length + β₁.length + β₂.length =
            (α₁.length + α₂.length + β₂.length) + (β₁.length + 1) := by omega
        have hsub : α₁.length + 1 + α₂.length + β₁.length + β₂.length - β₁.length - 1 =
            α₁.length + α₂.length + β₂.length := by
          rw [Nat.sub_sub, hre]
          simp
        rw [hsub]
        change cutPoint W.length (α₂.length + 1 + α₁.length + β₂.length) =
          cutPoint W.length (α₁.length + α₂.length + β₂.length + 1)
        congr 1 <;> omega
    · rw [hN', hlen]
      simpa [V, reverseParameter] using
        (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_c
          α₁ α₂ β₁ β₂ c (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))
  · rcases hprev with ⟨hzeroone, -⟩
    norm_num at hzeroone

theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk) (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))
    (hN : (N : ℂ) =
      oldA (ρA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  have hqL : α₁.length + 1 + α₂.length <
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length := by simp; omega
  have hend : s₀.1 = 0 ∨ s₀.1 = 1 := by
    apply orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA_end
      (p := 0) (q := α₁.length + 1 + α₂.length) (by omega) hqL s₀
    rw [← D.oldA_chord s₀, ← hP]
    exact PolygonMoves.norm_edgePoint _ _ _
  rcases hend with hs | hs
  · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA_aux_zero
      α₁ α₂ β₁ β₂ y c oldA oldB ρA ρB D e he τ N s₀ hP hN hs
  · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA_aux_one
      α₁ α₂ β₁ β₂ y c oldA oldB ρA ρB D e he τ N s₀ hP hN hs

open PolygonMoves in
/-- **Leaf (piece `B`, arc, next-name case).**  The point is the end of side `e`
(`τ = 1`) and the start of side `e₀ = (e+1) % L` (`s₀ = 0`).  Seams: `e₀ = q`
(so `e = q - 1` is the last side of piece `A`) and the two ends of `inv y`
(`e₀ = q + β₁.length`, `q + β₁.length + 1`), where the chord meets `c`; the wrap
`e₀ = 0` is excluded by `q ≤ e₀`.
Model: `PolygonMoves.cut_transfer_consistency_B_arc_aux_next`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcB_aux_next
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : α₁.length + 1 + α₂.length ≤ e₀)
    (he₀L : e₀ < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))
    (hN : (N : ℂ) =
      oldB (ρB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)))
    (hτ : τ.1 = 1) (hs₀ : s₀.1 = 0)
    (hadj : e₀ = (e + 1) % (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  sorry

open PolygonMoves in
/-- **Leaf (piece `B`, arc, prev-name case).**  The point is the end of side `e₀`
(`s₀ = 1`) and the start of side `e = (e₀+1) % L` (`τ = 0`).  Seams at
`q + β₁.length` (the chord) and the wrap `e₀ = L-1`, `e = 0`: vertex 0 as the end of
`β₂` transfers to the start of `c`, while `α₁`'s start is the end of `c⁻¹`; `_aux_c`
joins them.  Model: `PolygonMoves.cut_transfer_consistency_B_arc_aux_prev`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcB_aux_prev
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : α₁.length + 1 + α₂.length ≤ e₀)
    (he₀L : e₀ < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))
    (hN : (N : ℂ) =
      oldB (ρB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)))
    (hs₀ : s₀.1 = 1) (hτ : τ.1 = 0)
    (hadj : e = (e₀ + 1) % (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  sorry

open PolygonMoves in
/-- **Leaf (piece `B`, arc).**  As `_aux_arcA`, for an old side `q ≤ e₀ < L`.
Model: `PolygonMoves.cut_transfer_consistency_B_arc`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcB
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : α₁.length + 1 + α₂.length ≤ e₀)
    (he₀L : e₀ < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))
    (hN : (N : ℂ) =
      oldB (ρB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀))) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  let LL := (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
  let p := α₁.length
  let q := α₁.length + 1 + α₂.length
  have hlen := D.length
  have hLL : 2 ≤ LL := by simp [LL]; omega
  have hedges : edgePoint LL e τ = edgePoint LL e₀ s₀ := by
    apply Subtype.ext
    exact hP.trans (D.oldB_arc e₀ s₀ he₀ he₀L)
  have hNform :
      (N : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        LL p α₂.length β₁.length β₂.length e₀ s₀ := by
    rw [hN]
    by_cases h₁ : e₀ < q + β₁.length
    · rw [D.ρB_β₁ e₀ s₀ he₀ h₁, D.oldB_arc]
      · change (edgePoint LL (e₀ + β₂.length + 1) s₀ : ℂ) = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos h₁]
      · omega
      · omega
    · by_cases hy₀ : e₀ = q + β₁.length
      · subst e₀
        rw [D.ρB_y, D.oldB_chord]
        change cutChordB LL 0 q s₀ = _
        rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
          if_neg (by omega), if_pos (by omega)]
      · have h₂ : q + β₁.length + 1 ≤ e₀ := by omega
        rw [D.ρB_β₂ e₀ s₀ h₂ he₀L, D.oldB_arc]
        · change (edgePoint LL (e₀ - β₁.length - 1) s₀ : ℂ) = _
          rw [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
            if_neg (by omega), if_neg hy₀, if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
        · omega
        · omega
  rcases cutEdgePoint_eq hLL he he₀L hedges with hs | hf | hb
  · rcases hs with ⟨rfl, rfl⟩
    exact ⟨N, hNform, Relation.EqvGen.refl N⟩
  · rcases hf with ⟨hτ, hs₀, hadj⟩
    exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcB_aux_next
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N e₀ s₀ he₀ he₀L hP hN hτ hs₀ hadj
  · rcases hb with ⟨hs₀, hτ, hadj⟩
    exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcB_aux_prev
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N e₀ s₀ he₀ he₀L hP hN hs₀ hτ hadj

open PolygonMoves in
/-- **Leaf (piece `B`, chord).**  As `_aux_chordA`, with `cutChordB` (endpoints by
`_aux_chordB_end`) and `N` on the new `c` side.
Model: `PolygonMoves.cut_transfer_consistency_B_chord`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordB
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk) (s₀ : Icc (0 : ℝ) 1)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      oldB (cutChordParamB (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))
    (hN : (N : ℂ) =
      oldB (ρB (cutChordParamB (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀))) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  sorry

open PolygonMoves in
/-- **Transfer consistency.**  An old boundary point, read on piece `i`
at circle parameter `z`, has new image `N`; whichever side `e` and parameter `τ`
it is named by, `N` is `EqvGen`-related in the new word to the transferred
point `_aux_transfer … e τ`.  Assembled from the four cover cases `_aux_arcA`, `_aux_chordA`, `_aux_arcB`, `_aux_chordB`; a vertex point
has several names `(e, τ)` and several circle parameters `z`, and their images
are joined through new-word identifications.  Model:
`PolygonMoves.cut_transfer_consistency`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (i : Bool) (z : Circle) (e : ℕ)
    (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (τ : Icc (0 : ℝ) 1) (N : Disk)
    (hP : (edgePoint (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e τ : ℂ) =
      (if i then oldB z else oldA z))
    (hN : (N : ℂ) = (if i then oldB (ρB z) else oldA (ρA z))) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N T := by
  cases i with
  | false =>
    rcases D.coverA z with ⟨e₀, s₀, h1, rfl⟩ | ⟨s₀, rfl⟩
    · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcA
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N e₀ s₀ h1
        (by simpa using hP) (by simpa using hN)
    · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordA
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N s₀
        (by simpa using hP) (by simpa using hN)
  | true =>
    rcases D.coverB z with ⟨e₀, s₀, h1, h2, rfl⟩ | ⟨s₀, rfl⟩
    · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_arcB
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N e₀ s₀ h1 h2
        (by simpa using hP) (by simpa using hN)
    · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency_aux_chordB
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ N s₀
        (by simpa using hP) (by simpa using hN)

/-- **Leaf.** A non-`y` old side moves to a new side with the same letter. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_side
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (e : ℕ)
    (he : e < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (he₁ : e ≠ α₁.length)
    (he₂ : e ≠ α₁.length + 1 + α₂.length + β₁.length) :
    let f := if e < α₁.length then e + α₂.length + 1
      else if e < α₁.length + 1 + α₂.length then e - α₁.length - 1
      else if e < α₁.length + 1 + α₂.length + β₁.length then e + β₂.length + 1
      else e - β₁.length - 1
    ∃ hf : f < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length,
      (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get ⟨f, hf⟩ =
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get ⟨e, he⟩ := by
  intro f
  simp only [List.length_append, List.length_singleton] at he
  have hW : α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂ =
      α₁ ++ (y :: (α₂ ++ (β₁ ++ (inv y :: β₂)))) := by simp
  have hW' : α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁ =
      α₂ ++ (inv c :: (α₁ ++ (β₂ ++ (c :: β₁)))) := by simp
  have hfl : f < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length := by
    simp only [f, List.length_append, List.length_singleton]; split_ifs <;> omega
  refine ⟨hfl, ?_⟩
  simp only [List.get_eq_getElem]
  rw [List.getElem_of_eq hW, List.getElem_of_eq hW']
  simp only [f]
  split_ifs with h1 h2 h3 <;>
    simp only [List.getElem_append, List.getElem_cons] <;>
    (repeat' split) <;> first | omega | rfl | (congr 1; omega)

open PolygonMoves in
/-- **Leaf.** By freshness of `y`, only the two `y` sides carry label `y.1`. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_y_index
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (i : Fin (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (h : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).1 = y.1) :
    (i : ℕ) = α₁.length ∨
      (i : ℕ) = α₁.length + 1 + α₂.length + β₁.length := by
  by_contra hne
  push_neg at hne
  apply hy
  rw [List.mem_map]
  refine ⟨_, ?_, h⟩
  have hi := i.isLt
  simp only [List.get_eq_getElem, List.getElem_append, List.getElem_singleton,
    List.length_append, List.length_singleton] at hi ⊢
  (repeat' split) <;> first | omega | simp [List.getElem_mem]

open PolygonMoves in
/-- **Leaf (y pair).** Both sides are `y` sides (opposite signs, so the
parameter is reversed); both transfers are the same chord point
(`cutChordB L 0 q (1 - τ) = cutChordA L 0 q τ`), so `T = T'`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_ypair
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (i j : Fin (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).1 =
      ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length i τ)
    (hT' : (T' : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length j
      (if ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).2 =
          ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).2
        then τ else reverseParameter τ))
    (hi : (i : ℕ) = α₁.length ∨ (i : ℕ) = α₁.length + 1 + α₂.length + β₁.length)
    (hj : (j : ℕ) = α₁.length ∨ (j : ℕ) = α₁.length + 1 + α₂.length + β₁.length) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) T T' := by
  sorry

open PolygonMoves in
/-- **Leaf (other pairs).** Neither side is a `y` side; both transfer to
`edgePoint` at the new positions (`_aux_side`), which carry the same letters,
so one `WordRel` step with the same parameter choice relates them. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_other
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (i j : Fin (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).1 =
      ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length i τ)
    (hT' : (T' : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length j
      (if ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).2 =
          ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).2
        then τ else reverseParameter τ))
    (hiy : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).1 ≠ y.1)
    (hjy : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).1 ≠ y.1) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) T T' := by
  let W := α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂
  let W' := α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁
  have hi1 : (i : ℕ) ≠ α₁.length := by
    intro h
    apply hiy
    have hi : i = ⟨α₁.length, by simp⟩ := Fin.ext h
    rw [hi]
    simp
  have hi2 : (i : ℕ) ≠ α₁.length + 1 + α₂.length + β₁.length := by
    intro h
    apply hiy
    have hi : i = ⟨α₁.length + 1 + α₂.length + β₁.length, by simp; omega⟩ := Fin.ext h
    rw [hi]
    have hW : α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂ = (α₁ ++ [y] ++ α₂ ++ β₁) ++ (inv y :: β₂) := by
      simp
    simp only [List.get_eq_getElem]
    rw [List.getElem_of_eq hW, List.getElem_append_right (by simp; omega)]
    simp [inv, show α₁.length + 1 + α₂.length + β₁.length -
      (α₁.length + (α₂.length + β₁.length + 1)) = 0 by omega]
  have hj1 : (j : ℕ) ≠ α₁.length := by
    intro h
    apply hjy
    have hj : j = ⟨α₁.length, by simp⟩ := Fin.ext h
    rw [hj]
    simp
  have hj2 : (j : ℕ) ≠ α₁.length + 1 + α₂.length + β₁.length := by
    intro h
    apply hjy
    have hj : j = ⟨α₁.length + 1 + α₂.length + β₁.length, by simp; omega⟩ := Fin.ext h
    rw [hj]
    have hW : α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂ = (α₁ ++ [y] ++ α₂ ++ β₁) ++ (inv y :: β₂) := by
      simp
    simp only [List.get_eq_getElem]
    rw [List.getElem_of_eq hW, List.getElem_append_right (by simp; omega)]
    simp [inv, show α₁.length + 1 + α₂.length + β₁.length -
      (α₁.length + (α₂.length + β₁.length + 1)) = 0 by omega]
  let f (e : ℕ) := if e < α₁.length then e + α₂.length + 1
    else if e < α₁.length + 1 + α₂.length then e - α₁.length - 1
    else if e < α₁.length + 1 + α₂.length + β₁.length then e + β₂.length + 1
    else e - β₁.length - 1
  obtain ⟨hfi, hwi⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_side
      α₁ α₂ β₁ β₂ y c i i.isLt hi1 hi2
  obtain ⟨hfj, hwj⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_side
      α₁ α₂ β₁ β₂ y c j j.isLt hj1 hj2
  let i' : Fin W'.length := ⟨f i, hfi⟩
  let j' : Fin W'.length := ⟨f j, hfj⟩
  have hf_inj : f i = f j → (i : ℕ) = j := by
    have hil := i.isLt
    have hjl := j.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at hil hjl
    intro h
    simp only [f] at h
    split_ifs at h <;> omega
  have hij' : i' ≠ j' := by
    intro h
    apply hij
    apply Fin.ext
    apply hf_inj
    exact congrArg Fin.val h
  apply Relation.EqvGen.rel
  refine ⟨i', j', hij', τ, ?_, ?_, ?_⟩
  · change (W'.get i').1 = (W'.get j').1
    change (W'.get ⟨f i, hfi⟩).1 = (W'.get ⟨f j, hfj⟩).1
    rw [hwi, hwj]
    exact hlab
  · apply Subtype.ext
    change (T : ℂ) = (edgePoint W'.length (f i) τ : ℂ)
    rw [hT]
    simp only [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
      hi1, hi2, if_false]
    simp only [f]
    split_ifs <;> congr 2 <;> simp [W, W'] <;> omega
  · apply Subtype.ext
    change (T' : ℂ) = (edgePoint W'.length (f j)
      (if (W'.get i').2 = (W'.get j').2 then τ else reverseParameter τ) : ℂ)
    rw [hT']
    simp only [orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer,
      hj1, hj2, if_false]
    have hs : (W'.get i').2 = (W'.get j').2 ↔ (W.get i).2 = (W.get j).2 := by
      change (W'.get ⟨f i, hfi⟩).2 = (W'.get ⟨f j, hfj⟩).2 ↔ _
      rw [hwi, hwj]
    rw [if_congr hs rfl rfl]
    simp only [f]
    split_ifs <;> congr 2 <;> simp [W, W'] <;> omega

open PolygonMoves in
/-- **Leaf (transferred generator).**  Two distinct old sides with the same
label, at matching parameters, transfer to new points that the new word
relates.  For the `y` pair both transfers are the same chord point
(`cutChordB L 0 q (1 - τ) = cutChordA L 0 q τ`); every other pair moves to a
pair of new sides with the same labels and signs.  Model:
`PolygonMoves.cut_transfer_generator`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (i j : Fin (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).1 =
      ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length i τ)
    (hT' : (T' : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length j
      (if ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).2 =
          ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get j).2
        then τ else reverseParameter τ)) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) T T' := by
  by_cases hiy : ((α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).get i).1 = y.1
  · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_ypair α₁ α₂ β₁ β₂ y c hy hc i j hij τ hlab T T' hT hT'
      (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_y_index α₁ α₂ β₁ β₂ y hy i hiy)
      (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_y_index α₁ α₂ β₁ β₂ y hy j (hlab ▸ hiy))
  · exact orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator_aux_other α₁ α₂ β₁ β₂ y c hy hc i j hij τ hlab T T' hT hT'
      hiy (fun h => hiy (hlab.trans h))

open PolygonMoves in
/-- **Forward generators** (split 2026-10-25 from lemma-1's partial into `_aux_consistency` and `_aux_generator`).  An old side identification between two
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
  obtain ⟨i₀, j₀, hij, τ, hlab, hP0, hP0'⟩ := h
  obtain ⟨T, hT, hNT⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D i z i₀ i₀.2 τ N (by rw [← hP, hP0]) hN
  obtain ⟨T', hT', hNT'⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_consistency
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D i' z' j₀ j₀.2 _ N' (by rw [← hP', hP0']) hN'
  exact Relation.EqvGen.trans _ _ _ hNT (Relation.EqvGen.trans _ _ _
    (orientablePairing_normalForm_aux_cutPaste_aux_forward_aux_generator
      α₁ α₂ β₁ β₂ y c hy hc i₀ j₀ hij τ hlab T T' hT hT')
    (Relation.EqvGen.symm _ _ hNT'))

/-- Banked (lemma-2, 2026-10-25): equal points are `EqvGen`-related. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_eq
    {L : Type*} [DecidableEq L] (w : List (PolygonMoves.Signed L))
    (P P' : Disk) (h : P = P') :
    Relation.EqvGen (PolygonMoves.WordRel w) P P' := by
  subst P'
  exact Relation.EqvGen.refl _

open PolygonMoves in
/-- Where a new boundary point (side `e` of the new word `α₂ c⁻¹ α₁ β₂ c β₁`,
parameter `s`) comes from: the two `c` sides are the chord (piece `A` reads it
as `cutChordA`, piece `B` as `cutChordB`), every other side moves rigidly back
to its position in the old word `α₁ y α₂ β₁ y⁻¹ β₂`.  Inverse of
`_aux_forward_aux_transfer` (`n₁ = |α₁|`, `n₂ = |α₂|`, `m₁ = |β₁|`,
`m₂ = |β₂|`, `L` the common length). -/
noncomputable def orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
    (L n₁ n₂ m₁ m₂ e : ℕ) (s : Icc (0 : ℝ) 1) : ℂ :=
  if e = n₂ then cutChordA L 0 (n₁ + 1 + n₂) s
  else if e = n₁ + 1 + n₂ + m₂ then cutChordB L 0 (n₁ + 1 + n₂) s
  else if e < n₂ then (edgePoint L (e + n₁ + 1) s : ℂ)
  else if e < n₁ + 1 + n₂ then (edgePoint L (e - n₂ - 1) s : ℂ)
  else if e < n₁ + 1 + n₂ + m₂ then (edgePoint L (e + m₁ + 1) s : ℂ)
  else (edgePoint L (e - m₂ - 1) s : ℂ)

open PolygonMoves in
/-- **Leaf (reverse, piece `A`, arc).**  The piece point is
`cutEdgeCircle L e₀ s₀` on an old `A` side `e₀ < q`, so `P = edgePoint L e₀ s₀`
(`D.oldA_arc`).  Its new image is read by `D.ρA_α₁ / ρA_y / ρA_α₂`; by
`cutEdgePoint_eq` the new name `(e, τ)` is either that image's own name (then the
transfer is `P` itself, or for `e₀ = n₁` the chord point, joined to `P` across the
old `y` pair) or an adjacent vertex name.  Model: reverse of
`PolygonMoves.cut_transfer_consistency_A_arc`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_arcA
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : e₀ < α₁.length + 1 + α₂.length)
    (hN : (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length e τ : ℂ) =
      oldA (ρA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)))
    (hP : (P : ℂ) = oldA (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P T := by
  sorry

open PolygonMoves in
/-- **Leaf (reverse, piece `A`, chord).**  The piece point is
`cutChordParamA L 0 q s₀`; `P = cutChordA L 0 q s₀` (`D.oldA_chord`) and its new
image is `edgePoint L n₂ s₀`, the `c⁻¹` side (`D.ρA_chord`).  If `(e, τ)` is that
name, the transfer is `P`.  Otherwise the point is a vertex, `s₀ ∈ {0, 1}`
(`_aux_forward_aux_consistency_aux_chordA_end` applied to `P` on the boundary) and
`P` is `cutPoint L q` or `cutPoint L 0`, related to the transfer of each other name
of that vertex. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_chordA
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (τ : Icc (0 : ℝ) 1) (P : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hN : (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length e τ : ℂ) =
      oldA (ρA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀)))
    (hP : (P : ℂ) = oldA (cutChordParamA (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀)) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P T := by
  sorry

open PolygonMoves in
/-- **Leaf (reverse, piece `B`, arc).**  As `_aux_arcA`, for an old
side `q ≤ e₀ < L` (`D.oldB_arc`, `D.ρB_β₁ / ρB_y / ρB_β₂`). -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_arcB
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (τ : Icc (0 : ℝ) 1) (P : Disk)
    (e₀ : ℕ) (s₀ : Icc (0 : ℝ) 1) (he₀ : α₁.length + 1 + α₂.length ≤ e₀)
    (he₀L : e₀ < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length)
    (hN : (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length e τ : ℂ) =
      oldB (ρB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)))
    (hP : (P : ℂ) = oldB (cutEdgeCircle (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length e₀ s₀)) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P T := by
  sorry

open PolygonMoves in
/-- **Leaf (reverse, piece `B`, chord).**  As `_aux_chordA`, with
`cutChordB` (`D.oldB_chord`, endpoints by `_aux_forward_aux_consistency_aux_chordB_end`)
and new image on the `c` side `q + m₂` (`D.ρB_chord`). -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_chordB
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (e : ℕ) (he : e < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (τ : Icc (0 : ℝ) 1) (P : Disk)
    (s₀ : Icc (0 : ℝ) 1)
    (hN : (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length e τ : ℂ) =
      oldB (ρB (cutChordParamB (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀)))
    (hP : (P : ℂ) = oldB (cutChordParamB (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length 0
        (α₁.length + 1 + α₂.length) s₀)) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P T := by
  sorry

open PolygonMoves in
/-- **Reverse transfer consistency.**  A piece point `z` on piece `i`
whose new image is the new boundary point `(e, τ)` has old image `P`; `P` is
`EqvGen`-related in the old word to `_aux_reverse_aux_transfer … e τ`.  As in
`_aux_forward_aux_consistency`, the work is at the vertices, which have several
names `(e, τ)` and several circle parameters `z`.  Model:
`PolygonMoves.cut_transfer_consistency` (reverse direction).  Assembled from the
four cover cases `_aux_arcA`, `_aux_chordA`, `_aux_arcB`, `_aux_chordB`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (i : Bool) (z : Circle) (e : ℕ)
    (he : e < (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (τ : Icc (0 : ℝ) 1) (P : Disk)
    (hN : (edgePoint (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length e τ : ℂ) =
      (if i then oldB (ρB z) else oldA (ρA z)))
    (hP : (P : ℂ) = (if i then oldB z else oldA z)) :
    ∃ T : Disk, (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
        (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
        α₁.length α₂.length β₁.length β₂.length e τ ∧
      Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) P T := by
  cases i with
  | false =>
    rcases D.coverA z with ⟨e₀, s₀, h1, rfl⟩ | ⟨s₀, rfl⟩
    · exact orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_arcA
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ P e₀ s₀ h1
        (by simpa using hN) (by simpa using hP)
    · exact orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_chordA
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ P s₀
        (by simpa using hN) (by simpa using hP)
  | true =>
    rcases D.coverB z with ⟨e₀, s₀, h1, h2, rfl⟩ | ⟨s₀, rfl⟩
    · exact orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_arcB
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ P e₀ s₀ h1 h2
        (by simpa using hN) (by simpa using hP)
    · exact orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency_aux_chordB
        α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D e he τ P s₀
        (by simpa using hN) (by simpa using hP)

open PolygonMoves in
/-- **Leaf (proved, lemma-1 + claude-14).** A non-`c` new side moves back to an old side with the same letter. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_side
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed L)) (y c : PolygonMoves.Signed L)
    (e : ℕ)
    (he : e < (α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (he₁ : e ≠ α₂.length)
    (he₂ : e ≠ α₂.length + 1 + α₁.length + β₂.length) :
    let f := if e < α₂.length then e + α₁.length + 1
      else if e < α₂.length + 1 + α₁.length then e - α₂.length - 1
      else if e < α₂.length + 1 + α₁.length + β₂.length then e + β₁.length + 1
      else e - β₂.length - 1
    ∃ hf : f < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).length,
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).get ⟨f, hf⟩ =
        (α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get ⟨e, he⟩ := by
  intro f
  simp only [List.length_append, List.length_singleton] at he
  have hW : α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂ =
      α₁ ++ (y :: (α₂ ++ (β₁ ++ (PolygonMoves.inv y :: β₂)))) := by simp
  have hW' : α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁ =
      α₂ ++ (PolygonMoves.inv c :: (α₁ ++ (β₂ ++ (c :: β₁)))) := by simp
  have hfl : f < (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).length := by
    simp only [f, List.length_append, List.length_singleton]; split_ifs <;> omega
  refine ⟨hfl, ?_⟩
  simp only [List.get_eq_getElem]
  rw [List.getElem_of_eq hW, List.getElem_of_eq hW']
  simp only [f]
  split_ifs with h1 h2 h3 <;>
    simp only [List.getElem_append, List.getElem_cons] <;>
    (repeat' split) <;> first | omega | rfl | (congr 1; omega)

open PolygonMoves in
/-- **Leaf (proved).** By freshness of `c`, only the two `c` sides carry label `c.1`. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_c_index
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed L)) (y c : PolygonMoves.Signed L)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).map Prod.fst)
    (i : Fin (α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length)
    (hi : ((α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).1 = c.1) :
    (i : ℕ) = α₂.length ∨
      (i : ℕ) = α₂.length + 1 + α₁.length + β₂.length := by
  by_contra h
  push_neg at h
  obtain ⟨hf, hw⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_side
      α₁ α₂ β₁ β₂ y c i i.isLt h.1 h.2
  apply hc
  rw [List.mem_map]
  refine ⟨(α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).get ⟨_, hf⟩,
    List.get_mem _ _, ?_⟩
  exact congrArg Prod.fst hw |>.trans hi

open PolygonMoves in
/-- **Leaf (c pair).** Both sides are `c` sides (`c⁻¹` at `n₂`, `c` at `q + m₂`;
opposite signs, so the parameter is reversed).  Both transfers are the same old
chord point, `cutChordB L 0 q (1 - τ) = cutChordA L 0 q τ` (use
`cut_retransfer_consistency_aux_chords` / `_aux_reverse_aux_eq`), so `T = T'`;
`i = j` is excluded by `hij`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_cpair
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (i j : Fin (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).1 = ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length i τ)
    (hT' : (T' : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length j
      (if ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).2 = ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).2 then τ else reverseParameter τ))
    (hi : (i : ℕ) = α₂.length ∨ (i : ℕ) = α₂.length + 1 + α₁.length + β₂.length)
    (hj : (j : ℕ) = α₂.length ∨ (j : ℕ) = α₂.length + 1 + α₁.length + β₂.length) :
    Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) T T' := by
  sorry

open PolygonMoves in
/-- **Leaf (other pairs).** Neither side is a `c` side; both transfer back to
`edgePoint` at the old positions given by `_aux_side`, which carry the same
letters, so one old `WordRel` step with the same parameter choice relates them. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_other
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (i j : Fin (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).1 = ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length i τ)
    (hT' : (T' : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length j
      (if ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).2 = ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).2 then τ else reverseParameter τ))
    (hi : ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).1 ≠ c.1)
    (hj : ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).1 ≠ c.1) :
    Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) T T' := by
  sorry

open PolygonMoves in
/-- **Reverse transferred generator** (split 2026-10-25 after lemma-1 PARTIAL into
`_aux_side`, `_aux_c_index`, `_aux_cpair`, `_aux_other`).  Two distinct new sides with the
same label, at matching parameters, pull back to old points that the old word
relates.  For the `c` pair (`c⁻¹` at `n₂`, `c` at `q + m₂`, opposite signs) both
pull back to the same chord point, `cutChordB L 0 q (1 - τ) = cutChordA L 0 q τ`
(use `_aux_reverse_aux_eq`); every other pair moves back to a pair of old sides
with the same labels and signs.  Model: `PolygonMoves.cut_transfer_generator`. -/
theorem orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator
    {L : Type*} [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (i j : Fin (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).length) (hij : i ≠ j)
    (τ : Icc (0 : ℝ) 1)
    (hlab : ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).1 = ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).1)
    (T T' : Disk)
    (hT : (T : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length i τ)
    (hT' : (T' : ℂ) = orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_transfer
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length j
      (if ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).2 = ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get j).2 then τ else reverseParameter τ)) :
    Relation.EqvGen (WordRel (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂)) T T' := by
  by_cases hic : ((α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁).get i).1 = c.1
  · exact orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_cpair α₁ α₂ β₁ β₂ y c hy hc i j hij τ hlab T T' hT hT'
      (orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_c_index α₁ α₂ β₁ β₂ y c hc i hic)
      (orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_c_index α₁ α₂ β₁ β₂ y c hc j (hlab ▸ hic))
  · exact orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator_aux_other α₁ α₂ β₁ β₂ y c hy hc i j hij τ hlab T T' hT hT'
      hic (fun h => hic (hlab.trans h))

open PolygonMoves in
/-- **Reverse generators** (split 2026-10-25 from lemma-2's partial into
`_aux_consistency` and `_aux_generator`).  Converse of `_aux_forward`: a new
side identification pulls back to an old chain.  The `c` pair lands on the old
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
  obtain ⟨i₀, j₀, hij, τ, hlab, hN0, hN0'⟩ := h
  obtain ⟨T, hT, hPT⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D i z i₀ i₀.2 τ P (by rw [← hN, hN0]) hP
  obtain ⟨T', hT', hPT'⟩ :=
    orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_consistency
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D i' z' j₀ j₀.2 _ P' (by rw [← hN', hN0']) hP'
  exact Relation.EqvGen.trans _ _ _ hPT (Relation.EqvGen.trans _ _ _
    (orientablePairing_normalForm_aux_cutPaste_aux_reverse_aux_generator
      α₁ α₂ β₁ β₂ y c hy hc i₀ j₀ hij τ hlab T T' hT hT')
    (Relation.EqvGen.symm _ _ hPT'))

open PolygonMoves in
/-- **Leaf (forward fibre).**  A point on both old pieces lies on the chord
`c` (or is one of its end vertices).  Its two new images are on the new sides
`c⁻¹` (position `n₂`, parameter `s`) and `c` (position `q + m₂`, parameter
`1 - s`), which the new word identifies.  Model: `cut_forward_fibre`. -/
lemma orientablePairing_normalForm_aux_cutPaste_aux_fibreForward_aux_chord {L : Type*}
    [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (z z' : Circle) (N N' : Disk) (h : oldA z = oldB z')
    (hne : ‖oldA z‖ ≠ 1)
    (hN : (N : ℂ) = oldA (ρA z)) (hN' : (N' : ℂ) = oldB (ρB z')) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N N' := by
  let W := α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂
  let W' := α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁
  have hlen : W.length = W'.length := by simp [W, W']; omega
  obtain (⟨e, s, he, hz⟩ | ⟨s, hz⟩) := D.coverA z
  · exfalso
    apply hne
    rw [hz, D.oldA_arc e s he]
    exact PolygonMoves.norm_edgePoint W.length e s
  obtain (⟨e, s', he₀, he₁, hz'⟩ | ⟨s', hz'⟩) := D.coverB z'
  · exfalso
    apply hne
    rw [h, hz', D.oldB_arc e s' he₀ he₁]
    exact PolygonMoves.norm_edgePoint W.length e s'
  have hchord : cutChordA W.length 0 (α₁.length + 1 + α₂.length) s =
      cutChordB W.length 0 (α₁.length + 1 + α₂.length) s' := by
    rw [← D.oldA_chord s, ← D.oldB_chord s', ← hz, ← hz']
    exact h
  have hq : α₁.length + 1 + α₂.length < W.length := by
    dsimp [W]
    simp
    omega
  have hPQ : cutPoint W.length 0 - cutPoint W.length (α₁.length + 1 + α₂.length) ≠ 0 :=
    sub_ne_zero.mpr (cutPoint_ne (by omega) (by omega))
  have hcoefC : ((s.1 : ℂ) + (s'.1 : ℂ) - 1) = 0 := by
    apply (mul_eq_zero.mp (show ((s.1 : ℂ) + (s'.1 : ℂ) - 1) *
        (cutPoint W.length 0 - cutPoint W.length (α₁.length + 1 + α₂.length)) = 0 by
      rw [cutChordA, cutChordB] at hchord
      calc
        _ = (cutPoint W.length (α₁.length + 1 + α₂.length) +
              (s.1 : ℂ) * (cutPoint W.length 0 - cutPoint W.length (α₁.length + 1 + α₂.length))) -
            (cutPoint W.length 0 + (s'.1 : ℂ) *
              (cutPoint W.length (α₁.length + 1 + α₂.length) - cutPoint W.length 0)) := by ring
        _ = 0 := sub_eq_zero.mpr hchord)).resolve_right hPQ
  have hs : s' = reverseParameter s := by
    apply Subtype.ext
    simp [reverseParameter]
    have hr : s.1 + s'.1 - 1 = 0 := by exact_mod_cast hcoefC
    linarith
  have hNN : N = edgePoint W'.length α₂.length s := by
    apply Subtype.ext
    rw [hN, hz, D.ρA_chord, D.oldA_arc]
    · rw [hlen]
    · simpa [W] using hq
  have hNN' : N' = edgePoint W'.length
      (α₂.length + 1 + α₁.length + β₂.length) (reverseParameter s) := by
    apply Subtype.ext
    rw [hN', hz', D.ρB_chord, D.oldB_arc]
    · rw [hlen, hs]
      congr 2
      omega
    · omega
    · rw [D.length]
      omega
  rw [hNN, hNN']
  apply Relation.EqvGen.rel
  let i : Fin W'.length := ⟨α₂.length, by simp [W']⟩
  let j : Fin W'.length := ⟨(α₂ ++ [inv c] ++ α₁ ++ β₂).length, by simp [W']⟩
  have hj : W'.get j = c := by
    simp [j, W', List.get_eq_getElem]
  refine ⟨i, j, ?_, s, ?_, rfl, ?_⟩
  · intro hij
    have := congrArg Fin.val hij
    simp [i, j] at this
  · change (W'.get i).1 = (W'.get j).1
    rw [hj]
    simp [i, W', List.get_eq_getElem, inv]
  · have hind : α₂.length + 1 + α₁.length + β₂.length =
        (α₂ ++ [inv c] ++ α₁ ++ β₂).length := by simp; omega
    rw [hind, hj]
    simp [i, j, W', List.get_eq_getElem, inv]

open PolygonMoves in
lemma orientablePairing_normalForm_aux_cutPaste_aux_fibreForward_aux_boundary {L : Type*}
    [DecidableEq L]
    (α₁ α₂ β₁ β₂ : List (Signed L)) (y c : Signed L)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).map Prod.fst)
    (oldA oldB : Circle → ℂ) (ρA ρB : Circle → Circle)
    (D : orientablePairing_normalForm_aux_cutPaste_aux_Data
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [inv y] ++ β₂).length
      α₁.length α₂.length β₁.length β₂.length oldA oldB ρA ρB)
    (z z' : Circle) (N N' : Disk) (h : oldA z = oldB z')
    (hu : ‖oldA z‖ = 1)
    (hN : (N : ℂ) = oldA (ρA z)) (hN' : (N' : ℂ) = oldB (ρB z')) :
    Relation.EqvGen (WordRel (α₂ ++ [inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)) N N' := by
  sorry

open PolygonMoves in
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
  by_cases hu : ‖oldA z‖ = 1
  · exact orientablePairing_normalForm_aux_cutPaste_aux_fibreForward_aux_boundary
      α₁ α₂ β₁ β₂ y c hy hc oldA oldB ρA ρB D z z' N N' h hu hN hN'
  · exact orientablePairing_normalForm_aux_cutPaste_aux_fibreForward_aux_chord
      α₁ α₂ β₁ β₂ y c oldA oldB ρA ρB D z z' N N' h hu hN hN'

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
theorem orientablePairing_normalForm_aux_normalize_aux_interlock_aux_rotate
    {N : ℕ} [NeZero N] (i j p : Fin N) :
    (i < finRotate N p ∧ finRotate N p ≤ j) ↔ (i ≤ p ∧ p < j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  cases n with
  | zero =>
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    have hp : p = 0 := Subsingleton.elim _ _
    constructor
    · intro h
      have hf : False := by simpa [hi, hp] using h.1
      exact hf.elim
    · intro h
      have hf : False := by simpa [hp, hj] using h.2
      exact hf.elim
  | succ n =>
    rw [finRotate_succ_apply]
    change (i.1 < (p.1 + 1) % (n + 2) ∧ (p.1 + 1) % (n + 2) ≤ j.1) ↔
      (i.1 ≤ p.1 ∧ p.1 < j.1)
    by_cases hp : p.1 + 1 < n + 2
    · rw [Nat.mod_eq_of_lt hp]
      omega
    · have hlast : p.1 + 1 = n + 2 := by omega
      rw [hlast, Nat.mod_self]
      omega

theorem orientablePairing_normalForm_aux_normalize_aux_interlock
    (w : List (PolygonMoves.Signed ℕ)) (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w)
    (i j : Fin w.length) (hij : i < j) (hlab : (w.get i).1 = (w.get j).1) :
    ∃ k l : Fin w.length, i < k ∧ k < j ∧ (j < l ∨ l < i) ∧
      (w.get k).1 = (w.get l).1 := by
  classical
  by_contra hcross
  push_neg at hcross
  let A : Fin w.length → Prop := fun p => i ≤ p ∧ p < j
  let C : Fin w.length → Prop := fun p => i < p ∧ p ≤ j
  have hmate : ∀ p q : Fin w.length, p ≠ q →
      (w.get p).1 = (w.get q).1 → (C p ↔ A q) := by
    intro p q hpq hpql
    have hui := orientablePairing_normalForm_aux_normalize_aux_uniqueMate w hw hor i
    have hjpred : j ≠ i ∧ (w.get j).1 = (w.get i).1 ∧
        (w.get j).2 ≠ (w.get i).2 :=
      ⟨ne_of_gt hij, hlab.symm, hor j i (ne_of_gt hij) hlab.symm⟩
    have hqi : q = i ↔ p = j := by
      constructor
      · intro h; subst q
        exact hui.unique ⟨hpq, hpql, hor p i hpq hpql⟩ hjpred
      · intro h; subst p
        have huj := orientablePairing_normalForm_aux_normalize_aux_uniqueMate w hw hor j
        exact huj.unique ⟨hpq.symm, hpql.symm, hor q j hpq.symm hpql.symm⟩
          ⟨ne_of_lt hij, hlab, hor i j (ne_of_lt hij) hlab⟩
    have hqj : q = j ↔ p = i := by
      constructor
      · intro h; subst q
        have huj := orientablePairing_normalForm_aux_normalize_aux_uniqueMate w hw hor j
        exact huj.unique ⟨hpq, hpql, hor p j hpq hpql⟩
          ⟨ne_of_lt hij, hlab, hor i j (ne_of_lt hij) hlab⟩
      · intro h; subst p
        exact hui.unique ⟨hpq.symm, hpql.symm,
          hor q i hpq.symm hpql.symm⟩ hjpred
    constructor <;> intro hp
    · by_cases hpi : p = j
      · subst p
        have hq : q = i := hqi.mpr rfl
        subst q
        exact ⟨le_rfl, hij⟩
      have hip : i < p := hp.1
      have hpj : p < j := lt_of_le_of_ne hp.2 hpi
      have hnout : ¬ (j < q ∨ q < i) := fun hout => (hcross p q hip hpj hout) hpql
      have hqi' : q ≠ i := by intro h; exact hpi (hqi.mp h)
      have hqj' : q ≠ j := by intro h; exact (ne_of_gt hip) (hqj.mp h)
      have hqle : i ≤ q := by
        by_contra h; have := lt_of_not_ge h
        exact hnout (Or.inr this)
      have hqlt : q < j := by
        by_contra h
        have hjq : j ≤ q := le_of_not_gt h
        exact hnout (Or.inl (lt_of_le_of_ne hjq (Ne.symm hqj')))
      exact ⟨hqle, hqlt⟩
    · let hq := hp
      by_cases hqi0 : q = i
      · exact ⟨by simpa [hqi.mp hqi0] using hij, by simp [hqi.mp hqi0]⟩
      have hiq : i < q := lt_of_le_of_ne hq.1 (Ne.symm hqi0)
      have hqj' : q < j := hq.2
      have hnout : ¬ (j < p ∨ p < i) := fun hout => (hcross q p hiq hqj' hout) hpql.symm
      have hpi' : p ≠ i := by intro h; exact (ne_of_gt hqj') (hqj.mpr h).symm
      have hpj' : p ≠ j := by intro h; exact hqi0 (hqi.mpr h)
      have hple : p ≤ j := by
        by_contra h; exact hnout (Or.inl (lt_of_not_ge h))
      have hpil : i < p := by
        by_contra h
        have hpi_le := le_of_not_gt h
        have hlt : p < i := lt_of_le_of_ne hpi_le hpi'
        exact hnout (Or.inr hlt)
      exact ⟨hpil, hple⟩
  have hrot : ∀ p : Fin w.length, C (finRotate _ p) ↔ A p := by
    intro p
    have hn : 0 < w.length := Nat.zero_lt_of_lt p.2
    letI : NeZero w.length := ⟨hn.ne'⟩
    exact orientablePairing_normalForm_aux_normalize_aux_interlock_aux_rotate i j p
  have hstep : ∀ a b : Fin w.length,
      orientablePairing_normalForm_aux_WordCornerRel w a b → (C a ↔ C b) := by
    intro a b hab
    rcases hab with ⟨p, q, hpq, hpql, hab⟩
    rw [if_neg (hor p q hpq hpql)] at hab
    rcases hab with (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rw [ha, hb]
      exact (hmate p q hpq hpql).trans (hrot q).symm
    · rw [ha, hb]
      exact (hrot p).trans (hmate q p hpq.symm hpql.symm).symm
  have hinv : ∀ a b : Fin w.length,
      Relation.EqvGen (orientablePairing_normalForm_aux_WordCornerRel w) a b →
        (C a ↔ C b) := by
    intro a b hab
    induction hab with
    | rel a b h => exact hstep a b h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hc := hinv i j (hv i j)
  have hCi : ¬ C i := by simp [C]
  have hCj : C j := by simp [C, hij]
  exact hCi (hc.mpr hCj)

/-- **Leaf.**  Every `Step` keeps the word a polygon word: rotation and
relabelling (by an equivalence) permute the label counts, and `cutPaste`
trades the pair `y, y⁻¹` for the fresh pair `c⁻¹, c`. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w) : PolygonMoves.IsPolygonWord w' := by
  cases hs with
  | rotation u v h =>
      refine ⟨?_, ?_, ?_⟩
      · intro he
        have : u ++ v = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          have : x ∈ v ++ u := by
            simpa [List.mem_append, or_comm] using hx
          simpa [he] using this
        exact h.1 this
      · simpa [List.length_append, Nat.add_comm] using h.2.1
      · intro a ha
        simpa [List.map_append, List.count_append, Nat.add_comm] using h.2.2 a (by
          simpa [List.map_append, List.mem_append, or_comm] using ha)
  | relabel w e flip h =>
      refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
      intro a ha
      simp only [List.map_map, Function.comp_def] at ha ⊢
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      rw [show List.map (fun x => e x.1) w =
        List.map e (List.map Prod.fst w) by simp [List.map_map, Function.comp_def]]
      rw [List.count_map_of_injective _ e e.injective]
      exact h.2.2 b.1 (List.mem_map.mpr ⟨b, hb, rfl⟩)
  | cutPaste α₁ α₂ β₁ β₂ y c hy hc h =>
      refine ⟨by simp, ?_, ?_⟩
      · simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using h.2.1
      · intro a ha
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, not_or, PolygonMoves.inv] at hy hc ha ⊢
        by_cases hac : a = c.1
        · subst a
          simp only [List.count_append, List.count_cons, List.count_nil, Nat.add_zero]
          simp_all [List.count_eq_zero_of_not_mem]
        · simp [hac] at ha
          have hold := h.2.2 a (by aesop)
          simp only [List.map_append, List.map_cons, List.map_nil, List.count_append,
            List.count_cons, List.count_nil, Nat.add_zero, PolygonMoves.inv] at hold ⊢
          have hay : y.1 ≠ a := by
            intro hea
            subst a
            simp_all
          have hca : c.1 ≠ a := Ne.symm hac
          simp [hay, hca] at hold ⊢
          omega

/-- **Leaf.**  Every `Step` keeps the word orientable: `flip` changes both arcs
of a label together, and `cutPaste` gives the new pair the signs `false, true`. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_orientable_aux_nodup
    {w : List (PolygonMoves.Signed ℕ)} :
    orientablePairing_normalForm_aux_WordOrientable w ↔ w.Nodup := by
  rw [List.nodup_iff_injective_get]
  constructor
  · intro h i j hij
    by_contra hne
    have hl : (w.get i).1 = (w.get j).1 := congrArg Prod.fst hij
    exact (h i j hne hl) (congrArg Prod.snd hij)
  · intro h i j hij hl hs
    apply hij
    apply h
    exact Prod.ext hl hs

theorem orientablePairing_normalForm_aux_normalize_aux_step_orientable
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w) :
    orientablePairing_normalForm_aux_WordOrientable w' := by
  rw [orientablePairing_normalForm_aux_normalize_aux_step_orientable_aux_nodup] at hor ⊢
  cases hs with
  | rotation u v h =>
      rw [List.nodup_append] at hor ⊢
      obtain ⟨hu, hv, huv⟩ := hor
      refine ⟨hv, hu, ?_⟩
      intro a ha b hb hab
      exact huv b hb a ha hab.symm
  | relabel w e flip h =>
      apply hor.map
      intro x y hxy
      have hl : x.1 = y.1 := e.injective (congrArg Prod.fst hxy)
      have hs : xor x.2 (flip x.1) = xor y.2 (flip y.1) := congrArg Prod.snd hxy
      apply Prod.ext hl
      rcases x with ⟨xl, xs⟩
      rcases y with ⟨yl, ys⟩
      simp only at hl hs ⊢
      subst yl
      cases xs <;> cases ys <;> simp_all
  | cutPaste α₁ α₂ β₁ β₂ y c hy hc h =>
      set_option maxHeartbeats 1000000 in
        simp only [PolygonMoves.inv] at hor ⊢
      set_option maxHeartbeats 1000000 in
        simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, not_or] at hor ⊢
      set_option maxHeartbeats 1000000 in
        grind

/-- **Leaf.**  Rotating a word shifts every corner by `u.length` (mod the
length) and every `WordCornerRel` step with it. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_rotation_aux
    (w : List (PolygonMoves.Signed ℕ)) (n : ℕ)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w) :
    orientablePairing_normalForm_aux_WordOneVertex (w.rotate n) := by
  sorry

theorem orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_rotation
    (u v : List (PolygonMoves.Signed ℕ))
    (hv : orientablePairing_normalForm_aux_WordOneVertex (u ++ v)) :
    orientablePairing_normalForm_aux_WordOneVertex (v ++ u) := by
  have hrot : (u ++ v).rotate u.length = v ++ u := by simp
  rw [← hrot]
  exact
    orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_rotation_aux
      (u ++ v) u.length hv

/-- **Leaf.**  Relabelling by an equivalence and flipping signs label-wise keeps
"same label" and "same sign within a label", so `WordCornerRel` is unchanged. -/
theorem orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_relabel
    (w : List (PolygonMoves.Signed ℕ)) (σ : ℕ ≃ ℕ) (flip : ℕ → Bool)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w) :
    orientablePairing_normalForm_aux_WordOneVertex
      (w.map fun x => (σ x.1, xor x.2 (flip x.1))) := by
  unfold orientablePairing_normalForm_aux_WordOneVertex at hv ⊢
  have hl : (w.map fun x => (σ x.1, xor x.2 (flip x.1))).length = w.length :=
    List.length_map _
  have hrot : ∀ {n m : ℕ} (h : n = m) (i : Fin n),
      finRotate m (Fin.cast h i) = Fin.cast h (finRotate n i) := by
    intro n m h i; subst h; rfl
  have key : ∀ c d : Fin w.length,
      Relation.EqvGen (orientablePairing_normalForm_aux_WordCornerRel w) c d →
        Relation.EqvGen
          (orientablePairing_normalForm_aux_WordCornerRel
            (w.map fun x => (σ x.1, xor x.2 (flip x.1))))
          (Fin.cast hl.symm c) (Fin.cast hl.symm d) := by
    intro c d h
    induction h with
    | rel c d hcd =>
        apply Relation.EqvGen.rel
        rcases hcd with ⟨i, j, hij, hlab, hcorners⟩
        refine ⟨Fin.cast hl.symm i, Fin.cast hl.symm j,
          fun h => hij (Fin.cast_injective _ h), ?_, ?_⟩
        · simp only [List.get_eq_getElem] at hlab ⊢
          simp [hlab]
        · simp only [List.get_eq_getElem] at hlab hcorners ⊢
          simp only [Fin.coe_cast, List.getElem_map, hrot, Fin.cast_inj]
          have hflip : flip (w[i].1) = flip (w[j].1) := congrArg flip hlab
          have hsign :
              (xor w[i].2 (flip w[i].1) = xor w[j].2 (flip w[j].1)) ↔
                w[i].2 = w[j].2 := by
            rw [hflip]
            cases w[i].2 <;> cases w[j].2 <;> cases flip (w[j].1) <;> simp
          simp only [Fin.getElem_fin] at hsign hcorners ⊢
          by_cases hs : w[(i : ℕ)].2 = w[(j : ℕ)].2
          · rw [if_pos (hsign.mpr hs)]; rw [if_pos hs] at hcorners; exact hcorners
          · rw [if_neg (mt hsign.mp hs)]; rw [if_neg hs] at hcorners; exact hcorners
    | refl c => exact Relation.EqvGen.refl _
    | symm c d _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans c d e _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro a b
  simpa using key (Fin.cast hl a) (Fin.cast hl b) (hv _ _)

/-- **Leaf.**  Cut-and-paste keeps the word one-vertex.  Send each corner of the
new word to the corner of the old word at the same point of the cut polygon (the
corners at the ends of `c` go to the corners at the ends of `y`) and check that
each old `WordCornerRel` step maps to a chain of new steps.  The hypotheses are
the `Step.cutPaste` ones; without `hy` it is false (`[y, inv y, y]` is
one-vertex, `[inv c, y, c]` is not). -/
lemma orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste_aux_yFresh
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed ℕ)) (y : PolygonMoves.Signed ℕ)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst) :
    y.1 ∉ α₁.map Prod.fst ∧ y.1 ∉ α₂.map Prod.fst ∧
      y.1 ∉ β₁.map Prod.fst ∧ y.1 ∉ β₂.map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or] at hy
  rcases hy with ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
  exact ⟨h₁, h₂, h₃, h₄⟩

lemma orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste_aux_cFresh
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed ℕ))
    (y c : PolygonMoves.Signed ℕ)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).map Prod.fst) :
    c.1 ∉ α₁.map Prod.fst ∧ c.1 ≠ y.1 ∧ c.1 ∉ α₂.map Prod.fst ∧
      c.1 ∉ β₁.map Prod.fst ∧ c.1 ∉ β₂.map Prod.fst := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or, PolygonMoves.inv] at hc
  grind

lemma orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste_aux_transport
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed ℕ)) (y c : PolygonMoves.Signed ℕ)
    (hy : y.1 ∉ α₁.map Prod.fst ∧ y.1 ∉ α₂.map Prod.fst ∧
      y.1 ∉ β₁.map Prod.fst ∧ y.1 ∉ β₂.map Prod.fst)
    (hc : c.1 ∉ α₁.map Prod.fst ∧ c.1 ≠ y.1 ∧ c.1 ∉ α₂.map Prod.fst ∧
      c.1 ∉ β₁.map Prod.fst ∧ c.1 ∉ β₂.map Prod.fst)
    (hw : PolygonMoves.IsPolygonWord (α₁ ++ [y] ++ α₂ ++ β₁ ++
      [PolygonMoves.inv y] ++ β₂))
    (hv : orientablePairing_normalForm_aux_WordOneVertex
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂)) :
    orientablePairing_normalForm_aux_WordOneVertex
      (α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁) := by
  sorry

theorem orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed ℕ)) (y c : PolygonMoves.Signed ℕ)
    (hy : y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst)
    (hc : c.1 ∉ (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂).map Prod.fst)
    (hw : PolygonMoves.IsPolygonWord (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂))
    (hv : orientablePairing_normalForm_aux_WordOneVertex
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂)) :
    orientablePairing_normalForm_aux_WordOneVertex
      (α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁) := by
  exact orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste_aux_transport
    α₁ α₂ β₁ β₂ y c
    (orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste_aux_yFresh
      α₁ α₂ β₁ β₂ y hy)
    (orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste_aux_cFresh
      α₁ α₂ β₁ β₂ y c hc) hw hv

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
  cases hs with
  | rotation u v h =>
      exact orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_rotation u v hv
  | relabel w e flip h =>
      exact orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_relabel w e flip hv
  | cutPaste α₁ α₂ β₁ β₂ y c hy hc h =>
      exact orientablePairing_normalForm_aux_normalize_aux_step_oneVertex_aux_cutPaste
        α₁ α₂ β₁ β₂ y c hy hc h hv

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

theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_tail_length
    (k m : ℕ) (r : List (PolygonMoves.Signed ℕ))
    (hlen : (orientablePairing_normalForm_aux_standardWord k ++ r).length = 4 * (k + m)) :
    r.length = 4 * m := by
  rw [List.length_append,
    orientablePairing_normalForm_aux_normalize_aux_standardWord_length] at hlen
  omega

theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_tail_nonempty
    (k m : ℕ) (hm : 1 ≤ m) (r : List (PolygonMoves.Signed ℕ))
    (hlen : (orientablePairing_normalForm_aux_standardWord k ++ r).length = 4 * (k + m)) :
    r ≠ [] := by
  intro hr
  have hrl := orientablePairing_normalForm_aux_normalize_aux_block_aux_tail_length
    k m r hlen
  simp [hr] at hrl
  omega

/-- **Leaf (first pair).**  The tail starts with a label whose two arcs are
interlocked with a second label of the tail: `r = x A y B x⁻¹ C y⁻¹ D`.  The
labels of the standard prefix are `< 2k` and those of `r` are `≥ 2k`, so `r`
is closed under mates; `r ≠ []` (`_aux_tail_nonempty`); the mate of the first
letter `x` of `r` is `inv x` by orientability (`_aux_uniqueMate`); and
`_aux_interlock` at `i = 4k` gives `y` strictly between them whose mate lies
outside.  The mate cannot lie before `i` (that is the prefix), so it lies after
`x⁻¹`, and it is `inv y` by orientability. -/
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_pair_aux_prefix
    (k : ℕ) (z : PolygonMoves.Signed ℕ)
    (hz : z ∈ orientablePairing_normalForm_aux_standardWord k) : z.1 < 2 * k := by
  simp only [orientablePairing_normalForm_aux_standardWord, List.mem_flatMap,
    List.mem_range] at hz
  obtain ⟨a, ha, hz⟩ := hz
  simp only [List.mem_cons, List.mem_singleton] at hz
  rcases hz with hz | hz | hz | hz
  · subst z; simp; omega
  · subst z; simp; omega
  · subst z; simp; omega
  · rcases hz with hz | hz
    · subst z; simp; omega
    · contradiction

theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_pair_aux_split
    {α : Type*} (r : List α) (i j l : ℕ)
    (hi : 0 < i) (hij : i < j) (hjl : j < l) (hl : l < r.length) :
    ∃ A B C D : List α,
      r = [r[0]] ++ A ++ [r[i]] ++ B ++ [r[j]] ++ C ++ [r[l]] ++ D := by
  let A := (r.drop 1).take (i - 1)
  let B := (r.drop (i + 1)).take (j - i - 1)
  let C := (r.drop (j + 1)).take (l - j - 1)
  let D := r.drop (l + 1)
  refine ⟨A, B, C, D, ?_⟩
  have h0 : 0 < r.length := by omega
  have hii : i < r.length := by omega
  have hjj : j < r.length := by omega
  have s0 := List.take_append_drop 1 r
  have s1 := List.take_append_drop (i - 1) (r.drop 1)
  have s2 := List.take_append_drop (j - i - 1) (r.drop (i + 1))
  have s3 := List.take_append_drop (l - j - 1) (r.drop (j + 1))
  rw [List.drop_eq_getElem_cons (by simp; omega : i - 1 < (r.drop 1).length)] at s1
  rw [List.drop_eq_getElem_cons (by simp; omega : j - i - 1 < (r.drop (i + 1)).length)] at s2
  rw [List.drop_eq_getElem_cons (by simp; omega : l - j - 1 < (r.drop (j + 1)).length)] at s3
  simp only [List.take_one, List.head?_eq_getElem?, h0, ↓reduceDIte, Option.toList_some,
    List.singleton_append, List.drop_drop] at s0 s1 s2 s3
  have t0 : r = r[0] :: r.drop 1 := by
    simpa using (List.drop_eq_getElem_cons h0)
  have t1 : r.drop 1 = A ++ (r[i] :: r.drop (i + 1)) := by
    have e1 : 1 + (i - 1) = i := by omega
    have e2 : 1 + (i - 1 + 1) = i + 1 := by omega
    dsimp [A]
    calc
      r.drop 1 = (r.drop 1).take (i - 1) ++ (r.drop 1)[i - 1]'(by simp; omega) ::
          r.drop (1 + (i - 1 + 1)) := s1.symm
      _ = (r.drop 1).take (i - 1) ++ r[i] :: r.drop (i + 1) := by
        congr 2
        · rw [List.getElem_drop]
          exact getElem_congr rfl e1 _
        · rw [e2]
  have t2 : r.drop (i + 1) = B ++ (r[j] :: r.drop (j + 1)) := by
    have e1 : i + 1 + (j - i - 1) = j := by omega
    have e2 : i + 1 + (j - i - 1 + 1) = j + 1 := by omega
    dsimp [B]
    calc
      r.drop (i + 1) = (r.drop (i + 1)).take (j - i - 1) ++
          (r.drop (i + 1))[j - i - 1]'(by simp; omega) ::
            r.drop (i + 1 + (j - i - 1 + 1)) := s2.symm
      _ = (r.drop (i + 1)).take (j - i - 1) ++ r[j] :: r.drop (j + 1) := by
        congr 2
        · rw [List.getElem_drop]
          exact getElem_congr rfl e1 _
        · rw [e2]
  have t3 : r.drop (j + 1) = C ++ (r[l] :: D) := by
    have e1 : j + 1 + (l - j - 1) = l := by omega
    have e2 : j + 1 + (l - j - 1 + 1) = l + 1 := by omega
    dsimp [C, D]
    calc
      r.drop (j + 1) = (r.drop (j + 1)).take (l - j - 1) ++
          (r.drop (j + 1))[l - j - 1]'(by simp; omega) ::
            r.drop (j + 1 + (l - j - 1 + 1)) := s3.symm
      _ = (r.drop (j + 1)).take (l - j - 1) ++ r[l] :: r.drop (l + 1) := by
        congr 2
        · rw [List.getElem_drop]
          exact getElem_congr rfl e1 _
        · rw [e2]
  generalize hx0 : r[0] = x0 at t0 t1 t2 t3 ⊢
  generalize hxi : r[i] = xi at t0 t1 t2 t3 ⊢
  generalize hxj : r[j] = xj at t0 t1 t2 t3 ⊢
  generalize hxl : r[l] = xl at t0 t1 t2 t3 ⊢
  rw [t0, t1, t2, t3]
  simp

theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_pair (k m : ℕ) (hm : 1 ≤ m)
    (r : List (PolygonMoves.Signed ℕ))
    (hw : PolygonMoves.IsPolygonWord (orientablePairing_normalForm_aux_standardWord k ++ r))
    (hor : orientablePairing_normalForm_aux_WordOrientable
      (orientablePairing_normalForm_aux_standardWord k ++ r))
    (hv : orientablePairing_normalForm_aux_WordOneVertex
      (orientablePairing_normalForm_aux_standardWord k ++ r))
    (hlen : (orientablePairing_normalForm_aux_standardWord k ++ r).length = 4 * (k + m))
    (hr : ∀ x ∈ r, 2 * k ≤ x.1) :
    ∃ (x y : PolygonMoves.Signed ℕ) (A B C D : List (PolygonMoves.Signed ℕ)),
      r = [x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D := by
  classical
  let w := orientablePairing_normalForm_aux_standardWord k ++ r
  have hrne := orientablePairing_normalForm_aux_normalize_aux_block_aux_tail_nonempty
    k m hm r hlen
  have hwlen : (orientablePairing_normalForm_aux_standardWord k).length = 4 * k :=
    orientablePairing_normalForm_aux_normalize_aux_standardWord_length k
  have hwlenall : w.length = 4 * k + r.length := by simp [w, hwlen]
  have hi_lt : 4 * k < w.length := by
    simp only [w, List.length_append, hwlen]
    have : 0 < r.length := by
      have : r.length ≠ 0 := by simpa using hrne
      omega
    omega
  let i : Fin w.length := ⟨4 * k, hi_lt⟩
  obtain ⟨j, hj, hjuniq⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_uniqueMate w hw hor i
  have hij : i < j := by
    have hnot : ¬ j < i := by
      intro hji
      have hjpre : w.get j ∈ orientablePairing_normalForm_aux_standardWord k := by
        rw [List.get_eq_getElem]
        simp only [w]
        rw [List.getElem_append_left]
        · apply List.getElem_mem
        · simpa [i, hwlen] using hji
      have hjlow := orientablePairing_normalForm_aux_normalize_aux_block_aux_pair_aux_prefix
        k (w.get j) hjpre
      have hi_tail : w.get i = r[0]'(by
          have : 0 < r.length := by
            have : r.length ≠ 0 := by simpa using hrne
            omega
          omega) := by
        rw [List.get_eq_getElem]
        simp only [w]
        rw [List.getElem_append_right]
        · congr 1; simp [i, hwlen]
        · simp [i, hwlen]
      have hhigh : 2 * k ≤ (w.get i).1 := by
        rw [hi_tail]
        apply hr
        apply List.getElem_mem
      omega
    exact lt_of_le_of_ne (le_of_not_gt hnot) hj.1.symm
  obtain ⟨p, q, hip, hpj, hout, hpql⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_interlock w hw hor hv i j hij hj.2.1.symm
  have hiq : i < q := by
    rcases hout with hjq | hqi
    · exact lt_trans hij hjq
    · exfalso
      have hqpre : w.get q ∈ orientablePairing_normalForm_aux_standardWord k := by
        rw [List.get_eq_getElem]
        simp only [w]
        rw [List.getElem_append_left]
        · apply List.getElem_mem
        · simpa [i, hwlen] using hqi
      have hqlow := orientablePairing_normalForm_aux_normalize_aux_block_aux_pair_aux_prefix
        k (w.get q) hqpre
      have hp_tail : w.get p ∈ r := by
        rw [List.get_eq_getElem]
        simp only [w]
        rw [List.getElem_append_right]
        · apply List.getElem_mem
        · simpa [i, hwlen] using le_of_lt hip
      have hphigh := hr (w.get p) hp_tail
      omega
  have hjq : j < q := by omega
  let ip := p.1 - 4 * k
  let ij := j.1 - 4 * k
  let iq := q.1 - 4 * k
  have hpR : ip < r.length := by simp [ip]; omega
  have hjR : ij < r.length := by simp [ij]; omega
  have hqR : iq < r.length := by simp [iq]; omega
  have hpi : 0 < ip := by simp [ip, i] at hip ⊢; omega
  have hpij : ip < ij := by simp [ip, ij, i] at hip hpj ⊢; omega
  have hijq : ij < iq := by simp [ij, iq]; omega
  obtain ⟨A, B, C, D, hrsplit⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_pair_aux_split
      r ip ij iq hpi hpij hijq hqR
  have wget (a : Fin w.length) (ha : i ≤ a) :
      w.get a = r[a.1 - 4 * k]'(by omega) := by
    rw [List.get_eq_getElem]
    simp only [w]
    rw [List.getElem_append_right]
    · congr 1; simp [hwlen]
    · simpa [i, hwlen] using ha
  have hxj : w.get j = PolygonMoves.inv (w.get i) := by
    apply Prod.ext
    · simpa [PolygonMoves.inv] using hj.2.1
    · simp only [PolygonMoves.inv]
      exact Bool.eq_not_of_ne hj.2.2
  have hypq : w.get q = PolygonMoves.inv (w.get p) := by
    apply Prod.ext
    · simpa [PolygonMoves.inv] using hpql.symm
    · simp only [PolygonMoves.inv]
      exact Bool.eq_not_of_ne (hor q p (ne_of_gt (lt_trans hpj hjq)) hpql.symm)
  refine ⟨r[0], r[ip], A, B, C, D, ?_⟩
  have hiR : w.get i = r[0] := by simpa [i] using wget i le_rfl
  have hpget : w.get p = r[ip] := by simpa [ip] using wget p (le_of_lt hip)
  have hjget : w.get j = r[ij] := by simpa [ij] using wget j (le_of_lt hij)
  have hqget : w.get q = r[iq] := by simpa [iq] using wget q (le_of_lt hiq)
  calc
    r = [r[0]] ++ A ++ [r[ip]] ++ B ++ [r[ij]] ++ C ++ [r[iq]] ++ D := hrsplit
    _ = [r[0]] ++ A ++ [r[ip]] ++ B ++ [PolygonMoves.inv r[0]] ++ C ++
        [PolygonMoves.inv r[ip]] ++ D := by
      rw [← hiR, ← hpget, ← hjget, ← hqget, hxj, hypq]

/-- **Leaf (commutator).**  Steps take `P x A y B x⁻¹ C y⁻¹ D` to
`P c d c⁻¹ d⁻¹ E` with the labels of `c`, `d`, `E` still `≥ n` (Massey, ch. 1
§7: two `cutPaste` steps with fresh labels `c`, `d` chosen above every label of
the word, and rotations to bring each configuration into the
`α₁ y α₂ β₁ y⁻¹ β₂` shape and finally to put `P` back in front; `P` is never
cut, it stays inside one of the four pieces).  `hy` of each `cutPaste` comes
from `hw`; `_aux_step_isPolygonWord` carries `hw` along. -/
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_le_fold
    (a n : ℕ) (l : List ℕ) (ha : a ∈ l) :
    a ≤ l.foldr max n := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.foldr_cons]
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_max_left _ _
      · exact (ih ha).trans (le_max_right _ _)

theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_fresh
    (n : ℕ) (l : List (PolygonMoves.Signed ℕ)) :
    let a := (l.map Prod.fst).foldr max n + 1
    n ≤ a ∧ a ∉ l.map Prod.fst := by
  dsimp only
  constructor
  · have : n ≤ (l.map Prod.fst).foldr max n := by
      induction l with
      | nil => simp
      | cons x l ih =>
          simp only [List.map_cons, List.foldr_cons]
          exact ih.trans (le_max_right _ _)
    omega
  · intro ha
    have := orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_le_fold
      _ n _ ha
    omega

theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_exists_fresh
    (n : ℕ) (l : List (PolygonMoves.Signed ℕ)) :
    ∃ a, n ≤ a ∧ a ∉ l.map Prod.fst :=
  ⟨_, orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_fresh n l⟩

/-- In a polygon word `α₁ y α₂ β₁ y⁻¹ β₂` the label of `y` occurs nowhere else. -/
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_absent
    (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed ℕ)) (y : PolygonMoves.Signed ℕ)
    (hw : PolygonMoves.IsPolygonWord
      (α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂)) :
    y.1 ∉ (α₁ ++ α₂ ++ β₁ ++ β₂).map Prod.fst := by
  intro hm
  have h2 := hw.2.2 y.1 (by simp)
  have hpos := List.count_pos_iff.mpr hm
  simp only [List.map_append, List.count_append, List.map_cons, List.map_nil,
    PolygonMoves.inv, List.count_cons_self, List.count_nil] at h2 hpos
  omega

/-- A rotation step, with the two words given by equations. -/
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_rot
    {w w' : List (PolygonMoves.Signed ℕ)} (u v : List (PolygonMoves.Signed ℕ))
    (h1 : w = u ++ v) (h2 : w' = v ++ u) (hw : PolygonMoves.IsPolygonWord w) :
    orientablePairing_normalForm_aux_Step w w' := by
  subst h1 h2
  exact orientablePairing_normalForm_aux_Step.rotation u v hw

/-- A cut-and-paste step, with the two words given by equations and the
uniqueness of `y` read off from the polygon word. -/
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_cut
    {w w' : List (PolygonMoves.Signed ℕ)} (α₁ α₂ β₁ β₂ : List (PolygonMoves.Signed ℕ))
    (y c : PolygonMoves.Signed ℕ)
    (h1 : w = α₁ ++ [y] ++ α₂ ++ β₁ ++ [PolygonMoves.inv y] ++ β₂)
    (h2 : w' = α₂ ++ [PolygonMoves.inv c] ++ α₁ ++ β₂ ++ [c] ++ β₁)
    (hc : c.1 ∉ w.map Prod.fst) (hw : PolygonMoves.IsPolygonWord w) :
    orientablePairing_normalForm_aux_Step w w' := by
  subst h1 h2
  exact orientablePairing_normalForm_aux_Step.cutPaste α₁ α₂ β₁ β₂ y c
    (orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_absent
      α₁ α₂ β₁ β₂ y hw) hc hw

set_option maxHeartbeats 4000000 in
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator (n : ℕ)
    (P A B C D : List (PolygonMoves.Signed ℕ)) (x y : PolygonMoves.Signed ℕ)
    (hw : PolygonMoves.IsPolygonWord (P ++ ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++
      [PolygonMoves.inv y] ++ D)))
    (hr : ∀ z ∈ [x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D,
      n ≤ z.1) :
    ∃ (c d : PolygonMoves.Signed ℕ) (E : List (PolygonMoves.Signed ℕ)),
      Relation.ReflTransGen orientablePairing_normalForm_aux_Step
        (P ++ ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D))
        (P ++ ([c, d, PolygonMoves.inv c, PolygonMoves.inv d] ++ E)) ∧
      ∀ z ∈ c :: d :: E, n ≤ z.1 := by
  -- x A y B x⁻¹ C y⁻¹ D P  →(cut on y, new c)  B x⁻¹ c⁻¹ x A D P c C
  -- → C B x⁻¹ c⁻¹ x A D P c  →(cut on x⁻¹, new d)  d⁻¹ C B A D P c d c⁻¹
  -- → P c d c⁻¹ d⁻¹ C B A D.
  obtain ⟨cl, hcn, hcf⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_exists_fresh n
      (P ++ ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D))
  let c : PolygonMoves.Signed ℕ := (cl, false)
  have s0 : orientablePairing_normalForm_aux_Step
      (P ++ ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D))
      ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D ++ P) :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_rot P
      ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D)
      rfl (by simp) hw
  have hw1 := orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord s0 hw
  have s1 : orientablePairing_normalForm_aux_Step
      ([x] ++ A ++ [y] ++ B ++ [PolygonMoves.inv x] ++ C ++ [PolygonMoves.inv y] ++ D ++ P)
      (B ++ [PolygonMoves.inv x] ++ [PolygonMoves.inv c] ++ [x] ++ A ++ D ++ P ++ [c] ++ C) :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_cut
      ([x] ++ A) (B ++ [PolygonMoves.inv x]) C (D ++ P) y c (by simp) (by simp)
      (by
        intro h
        apply hcf
        simp only [List.map_append, List.mem_append] at h ⊢
        tauto)
      hw1
  have hw2 := orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord s1 hw1
  have s2 : orientablePairing_normalForm_aux_Step
      (B ++ [PolygonMoves.inv x] ++ [PolygonMoves.inv c] ++ [x] ++ A ++ D ++ P ++ [c] ++ C)
      (C ++ B ++ [PolygonMoves.inv x] ++ [PolygonMoves.inv c] ++ [x] ++ A ++ D ++ P ++ [c]) :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_rot
      (B ++ [PolygonMoves.inv x] ++ [PolygonMoves.inv c] ++ [x] ++ A ++ D ++ P ++ [c]) C
      (by simp) (by simp) hw2
  have hw3 := orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord s2 hw2
  obtain ⟨dl, hdn, hdf⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_exists_fresh n
      (C ++ B ++ [PolygonMoves.inv x] ++ [PolygonMoves.inv c] ++ [x] ++ A ++ D ++ P ++ [c])
  let d : PolygonMoves.Signed ℕ := (dl, false)
  have s3 : orientablePairing_normalForm_aux_Step
      (C ++ B ++ [PolygonMoves.inv x] ++ [PolygonMoves.inv c] ++ [x] ++ A ++ D ++ P ++ [c])
      ([PolygonMoves.inv d] ++ C ++ B ++ A ++ D ++ P ++ [c] ++ [d] ++ [PolygonMoves.inv c]) :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_cut
      (C ++ B) [] [PolygonMoves.inv c] (A ++ D ++ P ++ [c]) (PolygonMoves.inv x) d
      (by simp) (by simp) hdf hw3
  have hw4 := orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord s3 hw3
  have s4 : orientablePairing_normalForm_aux_Step
      ([PolygonMoves.inv d] ++ C ++ B ++ A ++ D ++ P ++ [c] ++ [d] ++ [PolygonMoves.inv c])
      (P ++ ([c, d, PolygonMoves.inv c, PolygonMoves.inv d] ++ (C ++ B ++ A ++ D))) :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator_aux_rot
      ([PolygonMoves.inv d] ++ C ++ B ++ A ++ D) (P ++ [c] ++ [d] ++ [PolygonMoves.inv c])
      (by simp) (by simp) hw4
  refine ⟨c, d, C ++ B ++ A ++ D, ?_, ?_⟩
  · exact (((((Relation.ReflTransGen.single s0).tail s1).tail s2).tail s3).tail s4)
  · intro z hz
    simp only [List.mem_cons, List.mem_append] at hz
    rcases hz with rfl | rfl | hz
    · exact hcn
    · exact hdn
    · apply hr
      simp only [List.mem_append, List.mem_cons]
      tauto

/-- **Leaf (relabel).**  One `relabel` step sends `c ↦ 2k`, `d ↦ 2k + 1` with
signs `true`, and the tail above `2k + 1`: take `e = swap (2k+1) d' ∘ swap 2k c'`
for fresh `c'`, `d'` above every label (with `c.1 ↦ 2k`, `d.1 ↦ 2k+1`), fixing
everything below `2k` (the prefix), and `flip` making `c`, `d` positive.
`c.1 ≠ d.1` and neither occurs in `E` by `hw` (each label occurs twice). -/
theorem orientablePairing_normalForm_aux_normalize_aux_block_aux_relabel (k : ℕ)
    (c d : PolygonMoves.Signed ℕ) (E : List (PolygonMoves.Signed ℕ))
    (hw : PolygonMoves.IsPolygonWord (orientablePairing_normalForm_aux_standardWord k ++
      ([c, d, PolygonMoves.inv c, PolygonMoves.inv d] ++ E)))
    (hr : ∀ z ∈ c :: d :: E, 2 * k ≤ z.1) :
    ∃ E' : List (PolygonMoves.Signed ℕ),
      orientablePairing_normalForm_aux_Step
        (orientablePairing_normalForm_aux_standardWord k ++
          ([c, d, PolygonMoves.inv c, PolygonMoves.inv d] ++ E))
        (orientablePairing_normalForm_aux_standardWord (k + 1) ++ E') ∧
      ∀ z ∈ E', 2 * (k + 1) ≤ z.1 := by
  let a := c.1
  let b := d.1
  let p := 2 * k
  let q := 2 * k + 1
  have hab : a ≠ b := by
    intro h
    have hc := hw.2.2 a (by simp [a])
    simp only [List.map_append, List.count_append] at hc
    simp [a, b, h, PolygonMoves.inv] at hc
    omega
  let s₁ : ℕ ≃ ℕ := Equiv.swap a p
  let b₁ := s₁ b
  let s₂ : ℕ ≃ ℕ := Equiv.swap b₁ q
  let e : ℕ ≃ ℕ := s₁.trans s₂
  have hb₁p : b₁ ≠ p := by
    intro h
    have h' : s₁ b = s₁ a := by simpa [b₁, s₁] using h
    exact hab (s₁.injective h').symm
  have he_a : e a = p := by
    change s₂ (s₁ a) = p
    rw [show s₁ a = p by simp [s₁]]
    exact Equiv.swap_apply_of_ne_of_ne hb₁p.symm (by omega)
  have he_b : e b = q := by
    simp [e, b₁, s₂]
  have he_fix {x : ℕ} (hx : x < p) : e x = x := by
    have hxa : x ≠ a := by intro h; subst x; exact (Nat.not_lt_of_ge (hr c (by simp)) hx)
    have hxp : x ≠ p := Nat.ne_of_lt hx
    have hxb : x ≠ b := by intro h; subst x; exact (Nat.not_lt_of_ge (hr d (by simp)) hx)
    have hb₁ge : p ≤ b₁ := by
      by_cases hbp : b = p
      · simp [b₁, s₁, hbp, a]
        exact hr c (by simp)
      · simpa [b₁, s₁, Equiv.swap_apply_of_ne_of_ne hab.symm hbp] using hr d (by simp)
    have hxb₁ : x ≠ b₁ := by
      exact (Nat.ne_of_lt (lt_of_lt_of_le hx hb₁ge))
    have hxq : x ≠ q := by omega
    simp [e, s₁, s₂, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne,
      hxa, hxp, hxb₁, hxq]
  have hEc : ∀ z ∈ E, z.1 ≠ a := by
    intro z hz hza
    have hc := hw.2.2 a (by simp [a])
    have hpos : 0 < (E.map Prod.fst).count a := List.count_pos_iff.mpr (by
      exact List.mem_map.mpr ⟨z, hz, hza⟩)
    dsimp [a] at hpos
    have hcd : c.1 ≠ d.1 := by simpa [a, b] using hab
    dsimp [a] at hc
    simp only [List.map_append, List.count_append] at hc
    simp only [List.map_cons, List.map_nil, Prod.fst, PolygonMoves.inv] at hc
    simp only [List.count_cons] at hc
    simp [hcd, hcd.symm] at hc
    have hzero : (E.map Prod.fst).count c.1 = 0 := by omega
    omega
  have hEd : ∀ z ∈ E, z.1 ≠ b := by
    intro z hz hzb
    have hd := hw.2.2 b (by simp [b])
    have hpos : 0 < (E.map Prod.fst).count b := List.count_pos_iff.mpr (by
      exact List.mem_map.mpr ⟨z, hz, hzb⟩)
    dsimp [b] at hpos
    simp only [List.map_append, List.count_append] at hd
    simp [a, b, hab, PolygonMoves.inv, hzb] at hd
    omega
  let flip : ℕ → Bool := fun x => if x = a then !c.2 else if x = b then !d.2 else false
  let f : PolygonMoves.Signed ℕ → PolygonMoves.Signed ℕ :=
    fun x => (e x.1, xor x.2 (flip x.1))
  have hprefix_general : ∀ (L : List (PolygonMoves.Signed ℕ)),
      (∀ x ∈ L, x.1 < p) → L.map f = L := by
    intro L hL
    induction L with
    | nil => simp
    | cons x xs ih =>
        have hxlt := hL x (by simp)
        have hxa : x.1 ≠ a := by
          intro h
          exact (Nat.not_lt_of_ge (hr c (by simp))) (by simpa [a, p, h] using hxlt)
        have hxb : x.1 ≠ b := by
          intro h
          exact (Nat.not_lt_of_ge (hr d (by simp))) (by simpa [b, p, h] using hxlt)
        simp only [List.map_cons]
        rw [ih (fun y hy => hL y (by simp [hy]))]
        simp [f, flip, he_fix hxlt, hxa, hxb]
  have hprefix : (orientablePairing_normalForm_aux_standardWord k).map f =
      orientablePairing_normalForm_aux_standardWord k := by
    apply hprefix_general
    intro x hx
    simp only [orientablePairing_normalForm_aux_standardWord, List.mem_flatMap,
      List.mem_range] at hx
    obtain ⟨j, hj, hx⟩ := hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [p] <;> omega
  refine ⟨E.map f, ?_, ?_⟩
  · have hmap :
        (orientablePairing_normalForm_aux_standardWord k ++
          ([c, d, PolygonMoves.inv c, PolygonMoves.inv d] ++ E)).map
            (fun x => (e x.1, xor x.2 (flip x.1))) =
          orientablePairing_normalForm_aux_standardWord (k + 1) ++ E.map f := by
      simp only [List.map_append]
      rw [orientablePairing_normalForm_aux_standardWord,
        orientablePairing_normalForm_aux_standardWord, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      rw [show ((List.range k).flatMap fun j =>
        [(2 * j, true), (2 * j + 1, true), (2 * j, false), (2 * j + 1, false)]).map f =
          (List.range k).flatMap (fun j =>
        [(2 * j, true), (2 * j + 1, true), (2 * j, false), (2 * j + 1, false)]) by
          exact hprefix]
      simp [f, flip, a, b, p, q, hab, hab.symm, he_a, he_b, PolygonMoves.inv]
    rw [← hmap]
    exact orientablePairing_normalForm_aux_Step.relabel _ e flip hw
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    simp only [f, Prod.fst]
    have hxp : p ≤ x.1 := hr x (by simp [hx])
    have hxc := hEc x hx
    have hxd := hEd x hx
    have hlow : p ≤ e x.1 := by
      by_contra h
      have helow : e x.1 < p := Nat.lt_of_not_ge h
      have hfix := he_fix helow
      have hxe : x.1 = e x.1 := e.injective hfix.symm
      exact (Nat.not_lt_of_ge hxp) (hxe.symm ▸ helow)
    have hnep : e x.1 ≠ p := by
      intro h
      exact hxc (e.injective (h.trans he_a.symm))
    have hneq : e x.1 ≠ q := by
      intro h
      exact hxd (e.injective (h.trans he_b.symm))
    dsimp [p, q] at hlow hnep hneq ⊢
    omega

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
  have hpw : ∀ {u u' : List (PolygonMoves.Signed ℕ)},
      Relation.ReflTransGen orientablePairing_normalForm_aux_Step u u' →
        PolygonMoves.IsPolygonWord u → PolygonMoves.IsPolygonWord u' := by
    intro u u' h hu
    induction h with
    | refl => exact hu
    | tail _ hs ih => exact orientablePairing_normalForm_aux_normalize_aux_step_isPolygonWord hs ih
  obtain ⟨x, y, A, B, C, D, rfl⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_pair k m hm r hw hor hv hlen hr
  obtain ⟨c, d, E, hch, hE⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_commutator (2 * k)
      (orientablePairing_normalForm_aux_standardWord k) A B C D x y hw hr
  obtain ⟨E', hs, hE'⟩ :=
    orientablePairing_normalForm_aux_normalize_aux_block_aux_relabel k c d E (hpw hch hw) hE
  exact ⟨E', hch.tail hs, hE'⟩

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

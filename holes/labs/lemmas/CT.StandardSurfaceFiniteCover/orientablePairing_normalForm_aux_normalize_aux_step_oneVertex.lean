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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Leaf: the corner `⟨i, k⟩` goes to `L i (edgePoint (4g) k 0)`, and one
`CornerRel` step preserves it.  The signs always differ, so the step is
`s ~ nextCorner (pair s)` or `nextCorner s ~ pair s`; both are `hside` at
`t = 0` or `t = 1`, with `edgePoint m k 1 = edgePoint m ((k + 1) % m) 0`
(`PolygonBoundaryVertexClasses.edgePoint_one_eq_succ_zero` and periodicity
of `Complex.exp`). -/
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
  sorry

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
  sorry

/-- **Leaf (sides of the merged complex).**  Given the faces of `C'` (all faces
of `C` but `(C.pair s).1`, with `merged` in place of `s.1`) and their side
counts, the sides of `C'` correspond to the sides of `C` other than `s` and
`C.pair s`: unmerged faces keep their sides, and the merged face walks round
`s.1` from just after `s`, then round `(C.pair s).1` from just after
`C.pair s`. -/
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
  sorry

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
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_next
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) (t : C'.Side) :
    Relation.EqvGen C.CornerRel (D.toOld (C'.nextCorner t))
      (C.nextCorner (D.toOld t)) := by
  sorry

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
theorem standardCover_pairingData_aux_glueStep_aux_vertexCount_aux_back
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_glueStep_aux_GlueData C C' s)
    (hor : C.IsOrientable) :
    ∃ g : C.Side → C'.Side, (∀ t, g (D.toOld t) = t) ∧
      (∀ u, Relation.EqvGen C.CornerRel (D.toOld (g u)) u) ∧
      (∀ a b, C.CornerRel a b → Relation.EqvGen C'.CornerRel (g a) (g b)) := by
  sorry

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

/-- **Leaf (geometry).**  The half charts exist.  Route: `PolygonMoves`
already has the two pieces `cutPiece` of a disk cut along a chord, their
boundary maps `cutOldA`/`cutOldB` (with `L = p + q - 2`, chord corners `0` and
`p - 1`) and the cone chart `cutAndPaste_aux_boundary_chart`; what is new is the
circle reparametrization from the `p`-gon (resp. `q`-gon) to those boundary
parameters. -/
theorem standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_halves
    (p q i j : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hi : i < p) (hj : j < q) :
    ∃ hL hR : Disk → Disk,
      standardCover_pairingData_aux_glueStep_aux_homeomorph_aux_HalfCharts
        p q i j hL hR := by
  sorry

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

/-- **Leaf (fibres).**  Two points of the disks of `C` are identified in `C`
exactly when their images are identified in `C'`.  The step along `s` becomes
equality (`seam`; `hor` makes the paired parameter `reverseIcc`), steps along
other sides become `C'` steps through `toOld` (`edge_left`, `edge_right`,
`toOld_merged_*`, `toOld_fst`, `toOld_val`, `pair_toOld`, `sign_toOld`). -/
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
  sorry

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
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_mergeCount
    {α : Type} [Finite α] (r : α → α → Prop) (a b : α)
    (hab : ¬ Relation.EqvGen r a b) :
    Nat.card (Quotient (Relation.EqvGen.setoid
        (fun x y => r x y ∨ (x = a ∧ y = b)))) + 1 =
      Nat.card (Quotient (Relation.EqvGen.setoid r)) := by
  sorry

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
  sorry

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
theorem standardCover_pairingData_aux_contractStep_aux_vertexCount_aux_back
    {C C' : PolygonComplex} {s : C.Side}
    (D : standardCover_pairingData_aux_contractStep_aux_ContractData C C' s)
    (h1 : C.faceCount = 1) (h5 : 5 ≤ C.totalSides) (hor : C.IsOrientable) :
    ∃ g : C.Side → C'.Side, (∀ t, g (D.toOld t) = t) ∧
      (∀ u, Relation.EqvGen
        (fun x y => C.CornerRel x y ∨ (x = s ∧ y = C.nextCorner s)) (D.toOld (g u)) u) ∧
      (∀ a b, (C.CornerRel a b ∨ (a = s ∧ b = C.nextCorner s)) →
        Relation.EqvGen C'.CornerRel (g a) (g b)) := by
  sorry

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
lemma orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_props
    (L n₁ n₂ : ℕ) (hL : n₁ + 1 + n₂ < L) :
    let p := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_p L n₁ n₂
    let q := orientablePairing_normalForm_aux_cutPaste_aux_reparamA_aux_angular_q L n₁ n₂
    Continuous p ∧ Continuous q ∧ Function.LeftInverse q p ∧ Function.RightInverse q p ∧
      p 0 = 0 ∧ p L = L ∧ q 0 = 0 ∧ q L = L ∧
      Set.MapsTo p (Set.Icc 0 L) (Set.Icc 0 L) ∧
      Set.MapsTo q (Set.Icc 0 L) (Set.Icc 0 L) := by
  sorry

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
  sorry

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
/-- **Leaf (transfer consistency).**  An old boundary point, read on piece `i`
at circle parameter `z`, has new image `N`; whichever side `e` and parameter `τ`
it is named by, `N` is `EqvGen`-related in the new word to the transferred
point `_aux_transfer … e τ`.  The endpoint cases are the work: a vertex point
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
  sorry

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
  sorry

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
/-- **Leaf (reverse transfer consistency).**  A piece point `z` on piece `i`
whose new image is the new boundary point `(e, τ)` has old image `P`; `P` is
`EqvGen`-related in the old word to `_aux_reverse_aux_transfer … e τ`.  As in
`_aux_forward_aux_consistency`, the work is at the vertices, which have several
names `(e, τ)` and several circle parameters `z`.  Model:
`PolygonMoves.cut_transfer_consistency` (reverse direction). -/
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
  sorry

open PolygonMoves in
/-- **Leaf (reverse transferred generator).**  Two distinct new sides with the
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
  sorry

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
-- BEGIN SEAT AREA
theorem orientablePairing_normalForm_aux_normalize_aux_step_oneVertex
    {w w' : List (PolygonMoves.Signed ℕ)}
    (hs : orientablePairing_normalForm_aux_Step w w')
    (hw : PolygonMoves.IsPolygonWord w)
    (hor : orientablePairing_normalForm_aux_WordOrientable w)
    (hv : orientablePairing_normalForm_aux_WordOneVertex w) :
    orientablePairing_normalForm_aux_WordOneVertex w' := by
  sorry
-- END SEAT AREA

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

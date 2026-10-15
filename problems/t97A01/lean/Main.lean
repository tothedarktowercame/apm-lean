import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.t97A01Closure

/-!
# APM t97A01 — the nonorientable genus-three surface

## Statement repairs

None.

## Encoding note

Both requested surfaces are actual polygon quotients of the closed unit disk.
The first glues the six boundary edges with word `a a b b c c`; the second
uses `a b a⁻¹ b⁻¹ c c`, the torus connected-summed with `ℝP²`. The conclusion
uses singular homology of these spaces and the fundamental group of the
second quotient, rather than detached cellular arithmetic.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97a01_Disk := Metric.closedBall (0 : ℂ) 1

/-- The point at parameter `t` on edge `j` of a regular hexagonal boundary
parameterization of the disk. -/
def apm_t97a01_edgePoint (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_Disk :=
  ⟨Complex.exp (Complex.I * (2 * Real.pi * ((j : ℝ) + t.1) / 6)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

/-- Edge identifications for the word `a a b b c c`. -/
inductive apm_t97a01_RelX : apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 0 t) (apm_t97a01_edgePoint 1 t)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 2 t) (apm_t97a01_edgePoint 3 t)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 4 t) (apm_t97a01_edgePoint 5 t)

/-- Edge identifications for the word `a b a⁻¹ b⁻¹ c c`. -/
inductive apm_t97a01_RelTorusRP2 :
    apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 0 t)
        (apm_t97a01_edgePoint 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 1 t)
        (apm_t97a01_edgePoint 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 4 t)
        (apm_t97a01_edgePoint 5 t)

def apm_t97a01_X := Quotient (Relation.EqvGen.setoid apm_t97a01_RelX)
def apm_t97a01_TorusRP2 :=
  Quotient (Relation.EqvGen.setoid apm_t97a01_RelTorusRP2)

noncomputable instance : TopologicalSpace apm_t97a01_X :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

noncomputable instance : TopologicalSpace apm_t97a01_TorusRP2 :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t97a01_quotientX : apm_t97a01_Disk → apm_t97a01_X :=
  fun x => Quotient.mk _ x

def apm_t97a01_quotientTorusRP2 : apm_t97a01_Disk → apm_t97a01_TorusRP2 :=
  fun x => Quotient.mk _ x

lemma apm_t97a01_continuous_quotientX : Continuous apm_t97a01_quotientX := by
  exact continuous_coinduced_rng

lemma apm_t97a01_surjective_quotientX :
    Function.Surjective apm_t97a01_quotientX := by
  exact Quotient.mk_surjective

lemma apm_t97a01_continuous_quotientTorusRP2 :
    Continuous apm_t97a01_quotientTorusRP2 := by
  exact continuous_coinduced_rng

lemma apm_t97a01_surjective_quotientTorusRP2 :
    Function.Surjective apm_t97a01_quotientTorusRP2 := by
  exact Quotient.mk_surjective

lemma apm_t97a01_quotientX_identifies_a (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_quotientX (apm_t97a01_edgePoint 0 t) =
      apm_t97a01_quotientX (apm_t97a01_edgePoint 1 t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.a t))

lemma apm_t97a01_quotientTorusRP2_identifies_c (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 4 t) =
      apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 5 t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.c t))

/-- Every generating identification for `X` is a generating identification
in the repository's canonical nonorientable genus-three polygon. -/
lemma apm_t97a01_RelX_to_standardN3 {x y : apm_t97a01_Disk}
    (h : apm_t97a01_RelX x y) :
    ConstructionTargets.Surfaces.SurfaceRel false 3 x y := by
  cases h with
  | a t =>
      refine ⟨0, by omega, t, ?_, ?_⟩
      · rfl
      · rfl
  | b t =>
      refine ⟨1, by omega, t, ?_, ?_⟩
      · rfl
      · rfl
  | c t =>
      refine ⟨2, by omega, t, ?_, ?_⟩
      · rfl
      · rfl

/-- Conversely, the canonical genus-three relation has exactly the three
generators used in `apm_t97a01_RelX`. -/
lemma apm_t97a01_standardN3_to_RelX {x y : apm_t97a01_Disk}
    (h : ConstructionTargets.Surfaces.SurfaceRel false 3 x y) :
    apm_t97a01_RelX x y := by
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  interval_cases j
  · exact .a t
  · exact .b t
  · exact .c t

/-- The `aa bb cc` quotient is definitionally equivalent to the reusable
canonical polygon presentation of the nonorientable genus-three surface. -/
def apm_t97a01_X_equiv_standardN3 :
    apm_t97a01_X ≃ ConstructionTargets.Surfaces.Surface false 3 := by
  apply Quotient.congrRight
  intro x y
  have hrel : apm_t97a01_RelX =
      ConstructionTargets.Surfaces.SurfaceRel false 3 := by
    funext u v
    apply propext
    exact ⟨apm_t97a01_RelX_to_standardN3, apm_t97a01_standardN3_to_RelX⟩
  rw [hrel]

/-- The quotient equivalence with the canonical nonorientable genus-three
surface respects the coinduced topologies on both polygon quotients. -/
def apm_t97a01_X_homeomorph_standardN3 :
    apm_t97a01_X ≃ₜ ConstructionTargets.Surfaces.Surface false 3 where
  toEquiv := apm_t97a01_X_equiv_standardN3
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : apm_t97a01_Disk =>
      apm_t97a01_X_equiv_standardN3 (Quotient.mk _ x))
    simpa [apm_t97a01_X_equiv_standardN3] using
      (ConstructionTargets.Surfaces.continuous_surfaceQuotient false 3)
  continuous_invFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : ConstructionTargets.Surfaces.Disk =>
      apm_t97a01_X_equiv_standardN3.symm (Quotient.mk _ x))
    simpa [apm_t97a01_X_equiv_standardN3] using apm_t97a01_continuous_quotientX

/-- The first frozen quotient is the exact pairing-space input to the banked
polygon homology theorem. -/
def apm_t97a01_X_homeomorph_pairingSpace :
    apm_t97a01_X ≃ₜ
      ConstructionTargets.t97A01Closure.aabbccPairingData.Space :=
  apm_t97a01_X_homeomorph_standardN3.trans
    (ConstructionTargets.PolygonSurfacePiOne.standardPairingData_space_homeomorph
      false 3 (by omega)).symm

/-- The frozen torus-crosscap generators are the canonical literal
torus-crosscap generators used by the polygon library. -/
lemma apm_t97a01_RelTorusRP2_to_canonical {x y : apm_t97a01_Disk}
    (h : apm_t97a01_RelTorusRP2 x y) :
    ConstructionTargets.PolygonTorusCrosscapRelation.TorusCrosscapRel x y := by
  cases h with
  | a t => exact .a t
  | b t => exact .b t
  | c t => exact .c t

/-- Conversely, every canonical literal torus-crosscap generator is one of
the frozen generators. -/
lemma apm_t97a01_canonical_to_RelTorusRP2 {x y : apm_t97a01_Disk}
    (h : ConstructionTargets.PolygonTorusCrosscapRelation.TorusCrosscapRel x y) :
    apm_t97a01_RelTorusRP2 x y := by
  cases h with
  | a t => exact .a t
  | b t => exact .b t
  | c t => exact .c t

theorem apm_t97a01_torusRP2_eqvGen_iff (x y : apm_t97a01_Disk) :
    Relation.EqvGen apm_t97a01_RelTorusRP2 x y ↔
      Relation.EqvGen
        ConstructionTargets.PolygonTorusCrosscapRelation.TorusCrosscapRel x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact .rel _ _ (apm_t97a01_RelTorusRP2_to_canonical h)
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact .rel _ _ (apm_t97a01_canonical_to_RelTorusRP2 h)
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

/-- The second frozen quotient is the exact pairing-space input to the
banked polygon homology theorem. -/
def apm_t97a01_TorusRP2_homeomorph_pairingSpace :
    apm_t97a01_TorusRP2 ≃ₜ
      ConstructionTargets.t97A01Closure.torusRP2PairingData.Space :=
  ConstructionTargets.t97A01Closure.quotientHomeomorphOfEqvGenIff
    apm_t97a01_RelTorusRP2
    ConstructionTargets.t97A01Closure.torusRP2PairingData.Rel
    isQuotientMap_quotient_mk' isQuotientMap_quotient_mk'
    (fun x y => (apm_t97a01_torusRP2_eqvGen_iff x y).trans
      (ConstructionTargets.PolygonSurfacePiOne.torusRP2_eqvGen_iff x y).symm)

abbrev apm_t97a01_H (k : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

/-- Homology transport from the frozen `aabbcc` quotient to the pairing-space
model used by the polygon Mayer--Vietoris calculation. -/
noncomputable def apm_t97a01_X_homologyIsoPairingSpace (k : ℕ) :
    apm_t97a01_H k apm_t97a01_X ≅
      ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.aabbccPairingData k :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo apm_t97a01_X_homeomorph_pairingSpace)

/-- Homology transport from the frozen torus-crosscap quotient to the
pairing-space model used by the polygon Mayer--Vietoris calculation. -/
noncomputable def apm_t97a01_TorusRP2_homologyIsoPairingSpace (k : ℕ) :
    apm_t97a01_H k apm_t97a01_TorusRP2 ≅
      ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.torusRP2PairingData k :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo apm_t97a01_TorusRP2_homeomorph_pairingSpace)

theorem apm_t97a01_aabbcc_homology_isZero (k : ℕ) (hk : 2 ≤ k) :
    Limits.IsZero
      (ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.aabbccPairingData k) := by
  rcases ConstructionTargets.t97A01Closure.aabbccPolygonHomology with
    ⟨_, _, ⟨h2⟩, hhi⟩
  rcases eq_or_lt_of_le hk with rfl | hk'
  · have hz : Limits.IsZero
        (ModuleCat.of ℤ
          (ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel
            ConstructionTargets.t97A01Closure.aabbccPairingData)) := by
      rw [ConstructionTargets.t97A01Closure.aabbccBoundaryKernel_eq_bot]
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.of_iso h2
  · exact hhi k (by omega)

theorem apm_t97a01_torusRP2_homology_isZero (k : ℕ) (hk : 2 ≤ k) :
    Limits.IsZero
      (ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.torusRP2PairingData k) := by
  rcases ConstructionTargets.t97A01Closure.torusRP2PolygonHomology with
    ⟨_, _, ⟨h2⟩, hhi⟩
  rcases eq_or_lt_of_le hk with rfl | hk'
  · have hz : Limits.IsZero
        (ModuleCat.of ℤ
          (ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel
            ConstructionTargets.t97A01Closure.torusRP2PairingData)) := by
      rw [ConstructionTargets.t97A01Closure.torusRP2BoundaryKernel_eq_bot]
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.of_iso h2
  · exact hhi k (by omega)

/-- The integral singular homology of both frozen six-edge quotients. -/
theorem apm_t97a01_polygon_singular_homology :
    (Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
        ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
      ∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    (Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
        ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
      ∀ k : ℕ, 2 ≤ k → Limits.IsZero
        (apm_t97a01_H k apm_t97a01_TorusRP2)) := by
  rcases ConstructionTargets.t97A01Closure.aabbccPolygonHomology with
    ⟨⟨hX0⟩, ⟨hX1⟩, _, _⟩
  rcases ConstructionTargets.t97A01Closure.torusRP2PolygonHomology with
    ⟨⟨hT0⟩, ⟨hT1⟩, _, _⟩
  refine ⟨⟨⟨apm_t97a01_X_homologyIsoPairingSpace 0 ≪≫ hX0⟩,
    ⟨apm_t97a01_X_homologyIsoPairingSpace 1 ≪≫ hX1 ≪≫
      ConstructionTargets.t97A01Closure.aabbccBoundaryCokernelSmithEquiv.toModuleIso⟩,
    ?_⟩,
    ⟨⟨apm_t97a01_TorusRP2_homologyIsoPairingSpace 0 ≪≫ hT0⟩,
    ⟨apm_t97a01_TorusRP2_homologyIsoPairingSpace 1 ≪≫ hT1 ≪≫
      ConstructionTargets.t97A01Closure.torusRP2BoundaryCokernelSmithEquiv.toModuleIso⟩,
    ?_⟩⟩
  · intro k hk
    exact (apm_t97a01_aabbcc_homology_isZero k hk).of_iso
      (apm_t97a01_X_homologyIsoPairingSpace k)
  · intro k hk
    exact (apm_t97a01_torusRP2_homology_isZero k hk).of_iso
      (apm_t97a01_TorusRP2_homologyIsoPairingSpace k)

#print axioms apm_t97a01_polygon_singular_homology

def apm_t97a01_baseX : apm_t97a01_X := Quotient.mk _ (0 : apm_t97a01_Disk)
def apm_t97a01_baseTorusRP2 : apm_t97a01_TorusRP2 :=
  Quotient.mk _ (0 : apm_t97a01_Disk)

def apm_t97a01_relator : FreeGroup (Fin 3) :=
  (.of 0) * (.of 1) * (.of 0)⁻¹ * (.of 1)⁻¹ * (.of 2) * (.of 2)

theorem apm_t97a01 :
    Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_TorusRP2)) ∧
    Nonempty
      (FundamentalGroup apm_t97a01_TorusRP2 apm_t97a01_baseTorusRP2 ≃*
        PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) := by
  /-
  Boundary (closer hop 1): the intended finite cellular calculation has one
  vertex, three one-cells, and one two-cell.  For `X` its cellular boundary is
  `1 ↦ (2,2,2)`, while the torus-crosscap word gives the same Smith normal
  form; Van Kampen gives the displayed one-relator group.  The frozen goals,
  however, concern *singular homology of the actual `EqvGen` polygon
  quotients* and their actual `FundamentalGroup`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's singular
  homology and presented-group sources, and closed siblings `t01J03`,
  `t02A03`, `t92J05`, and `t97J04` found no cellular-to-singular comparison
  for polygon quotients, singular Mayer--Vietoris sequence, or topological
  Seifert--van Kampen theorem.  Abstractly calculating the chain complex or
  the presented group locally therefore does not bridge to any conjunct of
  this frozen theorem.  Closure requires developing one of those missing
  topology bridges, including continuity/quotient identifications for these
  concrete edge relations.

  CLOSER HOP 2: the canonical polygon projections are now explicit as
  `apm_t97a01_quotientX` and `apm_t97a01_quotientTorusRP2`; their continuity
  and surjectivity are compiled from the coinduced topology. Representative
  gluing equations are compiled in `apm_t97a01_quotientX_identifies_a` and
  `apm_t97a01_quotientTorusRP2_identifies_c`, confirming that generating edge
  relations become actual quotient equalities. These are the raw inputs a
  future cellular comparison or van Kampen theorem would consume.

  Going beyond the previous search, I compared the newer cocone layers in
  `t02A03` and `t01J03` and inspected Mathlib's `IsQuotientMap` lifting APIs.
  They prove continuity of descended relation-respecting maps but do not
  compute singular homology or fundamental groups. The covering-quotient API
  concerns properly discontinuous group actions, not these boundary-pairing
  `EqvGen` relations. Thus all frozen invariant computations still require
  cellular-to-singular comparison or topological van Kampen; the statement is
  unchanged.

  CLOSER HOP 3: `ConstructionTargets.Surfaces` is now imported and the first
  polygon is connected to its canonical classified-surface encoding.
  `apm_t97a01_RelX_to_standardN3` and its converse prove that the concrete
  `aa bb cc` relation is exactly `SurfaceRel false 3`; consequently
  `apm_t97a01_X_equiv_standardN3` gives an actual quotient equivalence with
  `ConstructionTargets.Surfaces.Surface false 3`. This removes ambiguity
  about the first quotient's polygon normal form. The reusable module,
  however, intentionally stops at quotient presentations and elementary
  Euler data: it has no singular-homology or fundamental-group theorem, and
  an equivalence of underlying quotient types alone cannot transport the
  topological invariants. Renewed inspection of quotient-congruence,
  coinduced-topology, `TopCat`, singular-homology invariance, cellular, and
  van Kampen APIs found no bridge completing any frozen invariant conjunct.
  The remaining work is to upgrade the relation equivalence to the required
  topological comparison and then supply cellular-to-singular homology and
  van Kampen computations. The frozen statement is unchanged.
  -/
  sorry

import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.KleinPlaneActionFree
import ConstructionTargets.KleinPlaneOrbitQuotientTopology
import ConstructionTargets.DeckGroupQuotientFundamentalGroup

/-! # Generic closing lemmas for t93J03

The Klein-bottle-specific library obligations supply a cover and an exact
subgroup equality.  These lemmas contain the already proved generic lifting
and embedding arguments used after that equality is available.
-/

open ConstructionTargets.StatementSurfaceModels Set
noncomputable section
namespace ConstructionTargets.t93J03Closure

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm
open KleinPlaneAffineAction
open KleinCoordinateInversionPower

/-- An orbit intersection determines both integer normal-form coordinates by
the source and target points.  These are the equations used to bound the
possible deck transformations meeting two compact subsets of the plane. -/
theorem coordinate_equations_of_smul_eq
    (g : PresentedKleinGroup) (p q : ℝ × ℝ) (h : g • p = q) :
    (((Multiplicative.toAdd (coordinateEquiv g).2 : ℤ) : ℝ) = q.2 - p.2) ∧
      (((Multiplicative.toAdd (coordinateEquiv g).1 : ℤ) : ℝ) =
        q.1 -
          ((Multiplicative.toAdd
            (action (coordinateEquiv g).2 (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * p.1) := by
  change coordinateAct (coordinateEquiv g) p = q at h
  constructor
  · have hy := congrArg Prod.snd h
    dsimp [coordinateAct] at hy
    linarith
  · have hx := congrArg Prod.fst h
    dsimp [coordinateAct] at hx
    linarith

/-- Only finitely many presented Klein-group elements have their two normal
form coordinates in prescribed finite sets. -/
theorem finite_of_coordinatePair_mem {S T : Set ZMul}
    (hS : S.Finite) (hT : T.Finite) :
    {g : PresentedKleinGroup | coordinatePairEquiv g ∈ S ×ˢ T}.Finite :=
  (hS.prod hT).preimage coordinatePairEquiv.injective.injOn

/-- Integer coordinates whose real casts lie in a continuous image of a
compact set form a finite set. -/
theorem finite_zmul_cast_mem_compact_image
    {A : Type*} [TopologicalSpace A] {K : Set A} (hK : IsCompact K)
    (f : A → ℝ) (hf : Continuous f) :
    {z : ZMul | ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}.Finite := by
  let S : Set ZMul :=
    {z | ((Multiplicative.toAdd z : ℤ) : ℝ) ∈ f '' K}
  have hc : IsCompact (f '' K) := hK.image hf
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  obtain ⟨za : ℤ, hza : (za : ℝ) ≤ a⟩ := exists_int_le a
  obtain ⟨zb : ℤ, hzb : b ≤ (zb : ℝ)⟩ := exists_int_ge b
  have hbelow : BddBelow S := by
    refine ⟨Multiplicative.ofAdd za, ?_⟩
    intro z hz
    change za ≤ Multiplicative.toAdd z
    rw [← Int.cast_le (R := ℝ)]
    exact hza.trans (ha hz)
  have habove : BddAbove S := by
    refine ⟨Multiplicative.ofAdd zb, ?_⟩
    intro z hz
    change Multiplicative.toAdd z ≤ zb
    rw [← Int.cast_le (R := ℝ)]
    exact (hb hz).trans hzb
  exact hbelow.finite_of_bddAbove habove

/-- For two compact plane sets, only finitely many vertical integer
translations can occur in an orbit intersection. -/
theorem finite_vertical_coordinates_of_compact
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) :
    {n : ZMul |
      ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
        (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}.Finite := by
  apply finite_zmul_cast_mem_compact_image (hK.prod hL)
  fun_prop

/-- After fixing the vertical normal-form coordinate, compactness permits only
finitely many horizontal coordinates.  The multiplier is kept in its literal
`action n 1` form, so no parity surrogate for the affine action is introduced. -/
theorem finite_horizontal_coordinates_of_compact
    {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) (n : ZMul) :
    {m : ZMul |
      ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
        (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
          pq.2.1 -
            ((Multiplicative.toAdd
              (action n (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) ''
          (K ×ˢ L)}.Finite := by
  apply finite_zmul_cast_mem_compact_image (hK.prod hL)
  fun_prop

/-- Compact subsets of the plane meet only finitely many translates under the
literal affine Klein action. -/
theorem finite_klein_actors_of_compact {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : PresentedKleinGroup | ((g • ·) '' K ∩ L).Nonempty}.Finite := by
  let V : Set ZMul := {n |
    ((Multiplicative.toAdd n : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => pq.2.2 - pq.1.2) '' (K ×ˢ L)}
  let H : ZMul → Set ZMul := fun n => {m |
    ((Multiplicative.toAdd m : ℤ) : ℝ) ∈
      (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        pq.2.1 -
          ((Multiplicative.toAdd
            (action n (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * pq.1.1) ''
        (K ×ˢ L)}
  have hV : V.Finite := finite_vertical_coordinates_of_compact hK hL
  have hH : ∀ n, (H n).Finite := fun n =>
    finite_horizontal_coordinates_of_compact hK hL n
  have hPairs : (⋃ n ∈ V, H n ×ˢ ({n} : Set ZMul)).Finite :=
    hV.biUnion fun n _ => (hH n).prod (Set.finite_singleton n)
  apply (hPairs.preimage coordinatePairEquiv.injective.injOn).subset
  intro g hg
  obtain ⟨q, ⟨p, hp, hgp⟩, hq⟩ := hg
  have heq := coordinate_equations_of_smul_eq g p q hgp
  apply Set.mem_iUnion₂.mpr
  refine ⟨(coordinateEquiv g).2, ?_, ?_⟩
  · exact ⟨⟨p, q⟩, ⟨hp, hq⟩, heq.1.symm⟩
  · change (coordinateEquiv g).1 ∈ H (coordinateEquiv g).2 ∧
      (coordinateEquiv g).2 ∈ ({(coordinateEquiv g).2} : Set ZMul)
    exact ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, heq.2.symm⟩, Set.mem_singleton _⟩

noncomputable instance kleinPlaneProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul PresentedKleinGroup (ℝ × ℝ) where
  finite_disjoint_inter_image hK hL :=
    finite_klein_actors_of_compact hK hL

/-- The literal affine Klein action is continuous in the plane variable. -/
noncomputable instance kleinPlaneContinuousConstSMul :
    ContinuousConstSMul PresentedKleinGroup (ℝ × ℝ) where
  continuous_const_smul := KleinPlaneOrbitQuotient.continuous_smul

/-- Once proper discontinuity of the explicit affine action is supplied, the
banked deck-group theorem computes the fundamental group at the canonical
orbit of the origin. -/
theorem kleinPlaneOrbit_pi1_at_origin
    [ProperlyDiscontinuousSMul PresentedKleinGroup (ℝ × ℝ)] :
    Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient PresentedKleinGroup (ℝ × ℝ))
          (Quotient.mk _ (0, 0)) ≃* PresentedKleinGroup) :=
  ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      eq_one_of_smul_eq (0, 0)

/-- Transport a computed fundamental group from one basepoint to every
basepoint of a path-connected space.  This is the final basepoint adapter in
C1: the orbit calculation may use the image of `(0, 0)`, while the registered
statement quantifies over an arbitrary point of the Klein bottle. -/
theorem fundamentalGroupEquiv_every_basepoint
    {Y G : Type*} [TopologicalSpace Y] [PathConnectedSpace Y] [Group G]
    (y₀ : Y) (h₀ : Nonempty (FundamentalGroup Y y₀ ≃* G)) :
    ∀ y : Y, Nonempty (FundamentalGroup Y y ≃* G) := by
  intro y
  obtain ⟨e₀⟩ := h₀
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y y₀).trans e₀⟩

def subspaceInclusion (X : Set KleinBottle) : C(X, KleinBottle) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Rewrite an exact covering subgroup computation and apply the standard
covering-space lifting criterion. -/
theorem coveringLift_of_subgroup_le
    {G C : Type} [Group G] [TopologicalSpace C] {p : C → KleinBottle}
    (hp : IsCoveringMap p) (c : C) {k : KleinBottle} (hpc : p c = k)
    (e : FundamentalGroup KleinBottle k ≃* G) (H : Subgroup G)
    (hcover :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range =
        Subgroup.comap e.toMonoidHom H)
    (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X]
    (x : X) (hx : (x : KleinBottle) = k)
    (hX : ∀ g ∈ (FundamentalGroup.mapOfEq (subspaceInclusion X) hx).range,
      e g ∈ H) :
    ∃ l : C(X, C), p ∘ l = subspaceInclusion X := by
  cases hx
  have hle :
      (FundamentalGroup.map (subspaceInclusion X) x).range ≤
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range := by
    rintro g ⟨y, rfl⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective y
    rw [hcover]
    apply hX
    refine ⟨FundamentalGroup.fromPath (.mk γ), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    congr
  obtain ⟨l, ⟨_, hl⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts_of_range_le hpc hle
  exact ⟨l, hl⟩

/-- A lift of a subtype inclusion is an embedding by cancellation; composing
with an embedding of the covering space preserves embedding. -/
theorem lift_isEmbedding_assembly
    {C : Type} [TopologicalSpace C] {p : C → KleinBottle}
    (hp : Continuous p) (jC : C(C, ℝ × ℝ))
    (hjC : Topology.IsEmbedding jC)
    (X : Set KleinBottle) (l : C(X, C))
    (hl : p ∘ l = subspaceInclusion X) :
    ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j := by
  have hl' : Topology.IsEmbedding l := by
    apply Topology.IsEmbedding.of_comp l.continuous hp
    rw [hl]
    exact Topology.IsEmbedding.subtypeVal
  exact ⟨jC.comp l, hjC.comp hl'⟩

#print axioms coveringLift_of_subgroup_le
#print axioms lift_isEmbedding_assembly
#print axioms fundamentalGroupEquiv_every_basepoint
#print axioms kleinPlaneContinuousConstSMul
#print axioms kleinPlaneOrbit_pi1_at_origin
#print axioms coordinate_equations_of_smul_eq
#print axioms finite_of_coordinatePair_mem
#print axioms finite_zmul_cast_mem_compact_image
#print axioms finite_vertical_coordinates_of_compact
#print axioms finite_horizontal_coordinates_of_compact
#print axioms finite_klein_actors_of_compact
#print axioms kleinPlaneProperlyDiscontinuousSMul

end ConstructionTargets.t93J03Closure

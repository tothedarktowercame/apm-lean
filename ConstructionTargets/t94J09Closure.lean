import ConstructionTargets.PolygonSurfaceHomology
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Data.ZMod.Basic

/-! Compiled closure infrastructure for t94J09. -/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.t94J09Closure

open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology

/-- The standard one-vertex twelve-gon for the nonorientable genus-six
surface. -/
def n6PairingData : PairingData :=
  nonorientableStandardPairingData 6 (by omega)

/-! ## The frozen fourteen-edge pairing

The consumer's polygon has two vertex classes, so it does not satisfy the
`PairingData.oneVertex` field used by the existing radial homology theorem.
We nevertheless record its exact edge involution and seven edge orbits.  This
is the degree-one coordinate system for the required two-vertex extension of
that theorem. -/

/-- The edge involution read literally from the frozen fourteen-edge word. -/
def frozenPairIndex (i : Fin 14) : Fin 14 :=
  ![12, 7, 8, 9, 11, 10, 13, 1, 2, 3, 5, 4, 0, 6] i

theorem frozenPairIndex_involutive : Function.Involutive frozenPairIndex := by
  intro i
  fin_cases i <;> rfl

/-- The frozen edge pairing as a permutation. -/
def frozenPair : Equiv.Perm (Fin 14) where
  toFun := frozenPairIndex
  invFun := frozenPairIndex
  left_inv := frozenPairIndex_involutive
  right_inv := frozenPairIndex_involutive

@[simp] theorem frozenPair_apply (i : Fin 14) :
    frozenPair i = frozenPairIndex i := rfl

theorem frozenPair_pair (i : Fin 14) : frozenPair (frozenPair i) = i :=
  frozenPairIndex_involutive i

theorem frozenPair_ne (i : Fin 14) : frozenPair i ≠ i := by
  fin_cases i <;> decide

/-- The seven labels of the frozen edge-pairing orbits, ordered `a` through
`g`. -/
def frozenOrbitLabel (i : Fin 14) : Fin 7 :=
  ![0, 2, 3, 6, 5, 4, 1, 2, 3, 6, 4, 5, 0, 1] i

/-- The frozen fourteen edges have exactly seven pairing orbits. -/
def frozenOrbitEquiv : PairingOrbit frozenPair ≃ Fin 7 where
  toFun := Quotient.lift frozenOrbitLabel (by
    intro a b h
    induction h with
    | rel a b h =>
        rcases h with ⟨rfl⟩
        fin_cases a <;> rfl
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun j => Quotient.mk _ (![0, 6, 1, 2, 5, 4, 3] j : Fin 14)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
  right_inv := by
    intro j
    fin_cases j <;> rfl

/-! ## The frozen two-vertex graph boundary -/

/-- The degree-one boundary of the frozen quotient graph in the orbit order
`a,b,c,d,e,f,g`.  Only `d` and `g` join the two vertex classes. -/
def frozenGraphBoundary : (Fin 7 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ![v 6 - v 3, v 3 - v 6]
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro n x
    funext i
    fin_cases i <;> simp <;> ring

/-- Six independent cycle coordinates for the frozen two-vertex graph. -/
noncomputable def frozenGraphBoundaryKernelEquiv :
    LinearMap.ker frozenGraphBoundary ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun x i := x.1 i.castSucc
  invFun w :=
    ⟨fun i => ![w 0, w 1, w 2, w 3, w 4, w 5, w 3] i,
      by
        rw [LinearMap.mem_ker]
        ext i
        fin_cases i <;> simp [frozenGraphBoundary]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    have h63 := congrFun hx (0 : Fin 2)
    have h63' : x.1 6 = x.1 3 := by
      change x.1 6 - x.1 3 = 0 at h63
      exact sub_eq_zero.mp h63
    fin_cases i <;> simp [h63']
  right_inv := by
    intro w
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro x y
    funext i
    rfl
  map_smul' := by
    intro n x
    funext i
    rfl

/-! ## The frozen face boundary in graph-cycle coordinates -/

/-- Signed degree of the fourteen-edge attaching word in orbit order
`a,b,c,d,e,f,g`. -/
def frozenAttachingDegree : Fin 7 → ℤ :=
  ![2, 2, 0, -2, -2, 2, -2]

/-- The attaching degree is a cycle for the two-vertex graph boundary. -/
theorem frozenGraphBoundary_attachingDegree_zero :
    frozenGraphBoundary frozenAttachingDegree = 0 := by
  funext i
  fin_cases i <;> rfl

/-- The frozen attaching cycle as an element of the graph-cycle module. -/
def frozenAttachingCycle : LinearMap.ker frozenGraphBoundary :=
  ⟨frozenAttachingDegree, frozenGraphBoundary_attachingDegree_zero⟩

/-- In the six independent graph-cycle coordinates, the face boundary is
`(2,2,0,-2,-2,2)`. -/
theorem frozenGraphBoundaryKernelEquiv_attachingCycle :
    frozenGraphBoundaryKernelEquiv frozenAttachingCycle =
      ![2, 2, 0, -2, -2, 2] := by
  funext i
  fin_cases i <;> rfl

/-- A unimodular change of graph-cycle coordinates sending the frozen face
cycle to the standard genus-six face cycle. -/
def frozenCycleToN6Coordinates :
    (Fin 6 → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun x i := ![x 0, x 1, x 2 + x 0, -x 3, -x 4, x 5] i
  invFun y i := ![y 0, y 1, y 2 - y 0, -y 3, -y 4, y 5] i
  left_inv := by intro x; funext i; fin_cases i <;> simp
  right_inv := by intro y; funext i; fin_cases i <;> simp
  map_add' := by intro x y; funext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro n x; funext i; fin_cases i <;> simp <;> ring

theorem frozenCycleToN6Coordinates_attachingCycle :
    frozenCycleToN6Coordinates
        (frozenGraphBoundaryKernelEquiv frozenAttachingCycle) =
      fun _ => 2 := by
  rw [frozenGraphBoundaryKernelEquiv_attachingCycle]
  funext i
  fin_cases i <;> rfl

/-- The face boundary written in the six independent cycle coordinates. -/
def frozenFaceBoundaryCoordinates : ℤ →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun n := n • frozenGraphBoundaryKernelEquiv frozenAttachingCycle
  map_add' := by intros; simp [add_smul]
  map_smul' := by intros; simp [mul_smul]

theorem n6PolygonHomology :
    Nonempty (H n6PairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H n6PairingData 1 ≅
        ModuleCat.of ℤ (BoundaryCokernel n6PairingData)) ∧
      Nonempty (H n6PairingData 2 ≅
        ModuleCat.of ℤ (BoundaryKernel n6PairingData)) ∧
      ∀ k : ℕ, 3 ≤ k → IsZero (H n6PairingData k) :=
  polygonQuotient_homology n6PairingData

/-- The six standard edge-orbit coordinates. -/
def n6OrbitCoordinates :
    (PairingOrbit n6PairingData.pair → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  { toFun := fun f j => f ((nonorientableOrbitEquiv 6).symm j)
    invFun := fun v q => v (nonorientableOrbitEquiv 6 q)
    left_inv := by intro f; funext q; simp
    right_inv := by intro v; funext j; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem n6OrbitEquiv_orbit (i : Fin 12) :
    nonorientableOrbitEquiv 6 (n6PairingData.orbit i) =
      nonorientableOrbitLabel 6 i := rfl

@[simp] theorem n6_orbit_eq_named (i : Fin 12) (j : Fin 6) :
    n6PairingData.orbit i = (nonorientableOrbitEquiv 6).symm j ↔
      nonorientableOrbitEquiv 6 (n6PairingData.orbit i) = j :=
  (nonorientableOrbitEquiv 6).eq_symm_apply

theorem n6_attachingDegree_named (j : Fin 6) :
    attachingDegree n6PairingData ((nonorientableOrbitEquiv 6).symm j) = -2 := by
  rw [attachingDegree_apply]
  simp_rw [edgeOrbitContribution, n6_orbit_eq_named]
  simp_rw [n6OrbitEquiv_orbit]
  fin_cases j <;>
    simp [n6PairingData, nonorientableStandardPairingData,
      standardPairingDataOfOneVertex, standardPair, standardSign,
      nonorientableOrbitLabel, nonorientableCoord, edgeAttachingDegree] <;>
      decide

theorem n6OrbitCoordinates_attachingDegree :
    n6OrbitCoordinates (attachingDegree n6PairingData) = fun _ => -2 := by
  funext j
  exact n6_attachingDegree_named j

/-- Smith-normal boundary vector for the standard genus-six polygon. -/
def n6BoundaryLinear : ℤ →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun n := fun _ => 2 * n
  map_add' := by intros; funext; simp [mul_add]
  map_smul' := by intros; funext; simp [mul_left_comm]

theorem frozenCycleToN6Coordinates_comp_faceBoundary :
    frozenCycleToN6Coordinates.toLinearMap.comp
        frozenFaceBoundaryCoordinates = n6BoundaryLinear := by
  apply LinearMap.ext
  intro n
  funext i
  change frozenCycleToN6Coordinates
      (n • frozenGraphBoundaryKernelEquiv frozenAttachingCycle) i = 2 * n
  rw [map_smul, frozenCycleToN6Coordinates_attachingCycle]
  simp [mul_comm]

theorem frozenCycleToN6Coordinates_map_faceBoundaryRange :
    Submodule.map frozenCycleToN6Coordinates.toLinearMap
        (LinearMap.range frozenFaceBoundaryCoordinates) =
      LinearMap.range n6BoundaryLinear := by
  rw [← LinearMap.range_comp,
    frozenCycleToN6Coordinates_comp_faceBoundary]

theorem n6OrbitCoordinates_comp_attachingBoundary :
    n6OrbitCoordinates.toLinearMap.comp (attachingBoundary n6PairingData) =
      -n6BoundaryLinear := by
  apply LinearMap.ext
  intro n
  funext j
  change n * attachingDegree n6PairingData
      ((nonorientableOrbitEquiv 6).symm j) = _
  rw [n6_attachingDegree_named]
  simp [n6BoundaryLinear]
  ring

theorem n6BoundaryLinear_injective : Function.Injective n6BoundaryLinear := by
  intro a b h
  have h0 := congrFun h (0 : Fin 6)
  dsimp [n6BoundaryLinear] at h0
  omega

/-- Smith coordinates for the quotient of six integral coordinates by the
constant even vector: five differences and the parity of the first entry. -/
abbrev N6Smith := (Fin 5 → ℤ) × ZMod 2

def n6SmithCoordinate : (Fin 6 → ℤ) →ₗ[ℤ] N6Smith where
  toFun v := (fun j => v j.succ - v 0, v 0)
  map_add' := by
    intro x y
    ext j
    · simp
      ring
    · simp
  map_smul' := by
    intro m x
    ext j <;> simp [mul_sub]

theorem n6SmithCoordinate_surjective :
    Function.Surjective n6SmithCoordinate := by
  rintro ⟨a, c⟩
  let v : Fin 6 → ℤ := Fin.cases c.val (fun j => a j + c.val)
  refine ⟨v, ?_⟩
  ext j
  · simp [n6SmithCoordinate, v]
  · simp [n6SmithCoordinate, v]

theorem n6BoundaryLinear_range_eq_ker :
    LinearMap.range n6BoundaryLinear = LinearMap.ker n6SmithCoordinate := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    rw [LinearMap.mem_ker]
    ext j
    · simp [n6SmithCoordinate, n6BoundaryLinear]
    · change ((2 * n : ℤ) : ZMod 2) = 0
      rw [Int.cast_mul]
      change (2 : ZMod 2) * (n : ZMod 2) = 0
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hdiff : ∀ j : Fin 5, v j.succ - v 0 = 0 := by
      intro j
      simpa [n6SmithCoordinate] using
        congrArg (fun q : N6Smith => q.1 j) hv
    have hparity : ((v 0 : ℤ) : ZMod 2) = 0 := by
      simpa [n6SmithCoordinate] using congrArg (fun q : N6Smith => q.2) hv
    have heven : (2 : ℤ) ∣ v 0 := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hparity
    rcases heven with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [n6BoundaryLinear] using hn.symm
    · have hj := hdiff j
      simp only [sub_eq_zero] at hj
      simpa [n6BoundaryLinear, hj] using hn.symm

def n6BoundaryMap : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (Fin 6 → ℤ) :=
  ModuleCat.ofHom n6BoundaryLinear

/-- The explicit Smith cokernel used by the frozen degree-one answer. -/
noncomputable def n6SmithCokernelIso :
    cokernel n6BoundaryMap ≅ ModuleCat.of ℤ N6Smith :=
  ModuleCat.cokernelIsoRangeQuotient n6BoundaryMap ≪≫
    ((Submodule.quotEquivOfEq _ _ n6BoundaryLinear_range_eq_ker) ≪≫ₗ
      n6SmithCoordinate.quotKerEquivOfSurjective
        n6SmithCoordinate_surjective).toModuleIso

theorem n6AttachingBoundary_injective :
    Function.Injective (attachingBoundary n6PairingData) := by
  intro a b h
  apply n6BoundaryLinear_injective
  have hc := congrArg n6OrbitCoordinates h
  have ha := LinearMap.congr_fun n6OrbitCoordinates_comp_attachingBoundary a
  have hb := LinearMap.congr_fun n6OrbitCoordinates_comp_attachingBoundary b
  simpa [LinearMap.comp_apply] using ha.symm.trans (hc.trans hb)

theorem n6BoundaryKernel_eq_bot : BoundaryKernel n6PairingData = ⊥ :=
  LinearMap.ker_eq_bot.mpr n6AttachingBoundary_injective

theorem n6OrbitCoordinates_map_boundaryRange :
    Submodule.map n6OrbitCoordinates.toLinearMap
        (LinearMap.range (attachingBoundary n6PairingData)) =
      LinearMap.range n6BoundaryLinear := by
  rw [← LinearMap.range_comp,
    n6OrbitCoordinates_comp_attachingBoundary, LinearMap.range_neg]

/-- A coordinate equivalence carrying one boundary range onto another
descends to the corresponding quotient modules. -/
noncomputable def quotientLinearEquivOfMapEq
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) (p : Submodule ℤ M) (q : Submodule ℤ N)
    (h : Submodule.map e.toLinearMap p = q) :
    (M ⧸ p) ≃ₗ[ℤ] (N ⧸ q) := by
  let f : (M ⧸ p) →ₗ[ℤ] (N ⧸ q) :=
    p.mapQ q e.toLinearMap (by
      intro x hx
      change e x ∈ q
      rw [← h]
      exact ⟨x, hx, rfl⟩)
  let g : (N ⧸ q) →ₗ[ℤ] (M ⧸ p) :=
    q.mapQ p e.symm.toLinearMap (by
      intro y hy
      change e.symm y ∈ p
      have hy' : y ∈ Submodule.map e.toLinearMap p := h.symm ▸ hy
      rcases hy' with ⟨x, hx, hxy⟩
      simpa [← hxy] using hx)
  exact LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn x ?_
      intro x
      change (Quotient.mk _ (e (e.symm x))) = Quotient.mk _ x
      rw [e.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro y
      refine Quotient.inductionOn y ?_
      intro y
      change (Quotient.mk _ (e.symm (e y))) = Quotient.mk _ y
      rw [e.symm_apply_apply])

/-- The actual polygon boundary cokernel in explicit Smith coordinates. -/
noncomputable def n6BoundaryCokernelSmithEquiv :
    BoundaryCokernel n6PairingData ≃ₗ[ℤ] N6Smith :=
  quotientLinearEquivOfMapEq n6OrbitCoordinates _ _
      n6OrbitCoordinates_map_boundaryRange ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ n6BoundaryLinear_range_eq_ker ≪≫ₗ
      n6SmithCoordinate.quotKerEquivOfSurjective
        n6SmithCoordinate_surjective)

/-- The cokernel of the literal frozen two-vertex face boundary has the
required five free coordinates and one parity coordinate. -/
noncomputable def frozenFaceCokernelSmithEquiv :
    ((Fin 6 → ℤ) ⧸ LinearMap.range frozenFaceBoundaryCoordinates) ≃ₗ[ℤ]
      N6Smith :=
  quotientLinearEquivOfMapEq frozenCycleToN6Coordinates _ _
      frozenCycleToN6Coordinates_map_faceBoundaryRange ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ n6BoundaryLinear_range_eq_ker ≪≫ₗ
      n6SmithCoordinate.quotKerEquivOfSurjective
        n6SmithCoordinate_surjective)

/-- The final algebraic step of the Mayer--Vietoris calculation: any
surjective degree-one map whose kernel is the literal frozen face boundary
has the required Smith-form target. -/
noncomputable def frozenH1SmithEquivOfSurjectiveKernel
    {D : Type*} [AddCommGroup D] [Module ℤ D]
    (g : (Fin 6 → ℤ) →ₗ[ℤ] D) (hg : Function.Surjective g)
    (hker : LinearMap.ker g =
      LinearMap.range frozenFaceBoundaryCoordinates) :
    D ≃ₗ[ℤ] N6Smith :=
  (g.quotKerEquivOfSurjective hg).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
      frozenFaceCokernelSmithEquiv

/-- Integral homology of the standard genus-six nonorientable polygon in the
explicit groups required by the frozen problem. -/
theorem n6PolygonHomologyExplicit :
    Nonempty (H n6PairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H n6PairingData 1 ≅ ModuleCat.of ℤ N6Smith) ∧
      ∀ k : ℕ, 2 ≤ k → IsZero (H n6PairingData k) := by
  rcases n6PolygonHomology with ⟨h0, h1, h2, hhigh⟩
  refine ⟨h0, ?_, ?_⟩
  · rcases h1 with ⟨e1⟩
    exact ⟨e1 ≪≫ n6BoundaryCokernelSmithEquiv.toModuleIso⟩
  · intro k hk
    by_cases hk2 : k = 2
    · subst k
      rcases h2 with ⟨e2⟩
      have hz : IsZero (ModuleCat.of ℤ (BoundaryKernel n6PairingData)) := by
        rw [n6BoundaryKernel_eq_bot]
        rw [IsZero.iff_id_eq_zero]
        ext x
      exact hz.of_iso e2
    · exact hhigh k (by omega)

#print axioms n6PolygonHomology
#print axioms n6AttachingBoundary_injective
#print axioms n6BoundaryKernel_eq_bot
#print axioms n6SmithCokernelIso
#print axioms n6BoundaryCokernelSmithEquiv
#print axioms n6PolygonHomologyExplicit
#print axioms frozenPair_pair
#print axioms frozenPair_ne
#print axioms frozenOrbitEquiv
#print axioms frozenGraphBoundaryKernelEquiv
#print axioms frozenGraphBoundary_attachingDegree_zero
#print axioms frozenGraphBoundaryKernelEquiv_attachingCycle
#print axioms frozenFaceCokernelSmithEquiv
#print axioms frozenH1SmithEquivOfSurjectiveKernel

end ConstructionTargets.t94J09Closure

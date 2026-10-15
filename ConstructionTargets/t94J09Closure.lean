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

#print axioms n6PolygonHomology
#print axioms n6AttachingBoundary_injective
#print axioms n6BoundaryKernel_eq_bot
#print axioms n6SmithCokernelIso
#print axioms n6BoundaryCokernelSmithEquiv

end ConstructionTargets.t94J09Closure

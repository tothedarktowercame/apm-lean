import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.Basic

open CategoryTheory Limits

namespace ConstructionTargets.T97A01SmithQuotients

abbrev Z3 := ℤ × ℤ × ℤ
abbrev Smith := ℤ × ℤ × ZMod 2

def standardN3BoundaryLinear : ℤ →ₗ[ℤ] Z3 where
  toFun n := (2 * n, 2 * n, 2 * n)
  map_add' := by intro; simp [mul_add]
  map_smul' := by intro; simp [mul_left_comm]

def torusCrosscapBoundaryLinear : ℤ →ₗ[ℤ] Z3 where
  toFun n := (0, 0, 2 * n)
  map_add' := by intro; simp [mul_add]
  map_smul' := by intro; simp [mul_left_comm]

def standardN3Coordinate : Z3 →ₗ[ℤ] Smith where
  toFun v := (v.2.1 - v.1, v.2.2 - v.1, v.1)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro m x; ext <;> simp [mul_sub]

def torusCrosscapCoordinate : Z3 →ₗ[ℤ] Smith where
  toFun v := (v.1, v.2.1, v.2.2)
  map_add' := by intro x y; ext <;> simp
  map_smul' := by intro m x; ext <;> simp

theorem standardN3BoundaryLinear_injective :
    Function.Injective standardN3BoundaryLinear := by
  intro a b h
  have h' := congrArg (fun v : Z3 => v.1) h
  dsimp [standardN3BoundaryLinear] at h'
  omega

theorem torusCrosscapBoundaryLinear_injective :
    Function.Injective torusCrosscapBoundaryLinear := by
  intro a b h
  have h' := congrArg (fun v : Z3 => v.2.2) h
  dsimp [torusCrosscapBoundaryLinear] at h'
  omega

theorem standardN3Coordinate_surjective :
    Function.Surjective standardN3Coordinate := by
  rintro ⟨a, b, c⟩
  refine ⟨((c.val : ℤ), a + c.val, b + c.val), ?_⟩
  ext <;> simp [standardN3Coordinate]

theorem torusCrosscapCoordinate_surjective :
    Function.Surjective torusCrosscapCoordinate := by
  rintro ⟨a, b, c⟩
  refine ⟨(a, b, (c.val : ℤ)), ?_⟩
  ext <;> simp [torusCrosscapCoordinate]

theorem standardN3_range_eq_ker :
    LinearMap.range standardN3BoundaryLinear =
      LinearMap.ker standardN3Coordinate := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    rw [LinearMap.mem_ker]
    ext <;> simp [standardN3Coordinate, standardN3BoundaryLinear]
    change (2 : ZMod 2) * (n : ZMod 2) = 0
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]
  · intro hv
    simp only [LinearMap.mem_ker, standardN3Coordinate] at hv
    rcases v with ⟨x, y, z⟩
    change (y - x, z - x, (x : ZMod 2)) = 0 at hv
    have hy : y - x = 0 := by
      simpa using congrArg (fun q : Smith => q.1) hv
    have hz : z - x = 0 := by
      simpa using congrArg (fun q : Smith => q.2.1) hv
    have hx : (x : ZMod 2) = 0 := by
      simpa using congrArg (fun q : Smith => q.2.2) hv
    have heven : (2 : ℤ) ∣ x := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hx
    rcases heven with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    ext <;> simp [standardN3BoundaryLinear, ← hn] at hy hz ⊢ <;> omega

theorem torusCrosscap_range_eq_ker :
    LinearMap.range torusCrosscapBoundaryLinear =
      LinearMap.ker torusCrosscapCoordinate := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    rw [LinearMap.mem_ker]
    ext <;> simp [torusCrosscapCoordinate, torusCrosscapBoundaryLinear]
    change (2 : ZMod 2) * (n : ZMod 2) = 0
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]
  · intro hv
    simp only [LinearMap.mem_ker, torusCrosscapCoordinate] at hv
    rcases v with ⟨x, y, z⟩
    change (x, y, (z : ZMod 2)) = 0 at hv
    have hx : x = 0 := by
      simpa using congrArg (fun q : Smith => q.1) hv
    have hy : y = 0 := by
      simpa using congrArg (fun q : Smith => q.2.1) hv
    have hz : (z : ZMod 2) = 0 := by
      simpa using congrArg (fun q : Smith => q.2.2) hv
    have heven : (2 : ℤ) ∣ z := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hz
    rcases heven with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    ext <;> simp [torusCrosscapBoundaryLinear, hx, hy, ← hn]

def standardN3BoundaryMap : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ Z3 :=
  ModuleCat.ofHom standardN3BoundaryLinear

def torusCrosscapBoundaryMap : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ Z3 :=
  ModuleCat.ofHom torusCrosscapBoundaryLinear

theorem standardN3BoundaryMap_injective :
    Function.Injective standardN3BoundaryMap :=
  standardN3BoundaryLinear_injective

theorem torusCrosscapBoundaryMap_injective :
    Function.Injective torusCrosscapBoundaryMap :=
  torusCrosscapBoundaryLinear_injective

noncomputable def standardN3SmithCokernelIso :
    cokernel standardN3BoundaryMap ≅ ModuleCat.of ℤ Smith :=
  ModuleCat.cokernelIsoRangeQuotient standardN3BoundaryMap ≪≫
    ((Submodule.quotEquivOfEq _ _ standardN3_range_eq_ker) ≪≫ₗ
      standardN3Coordinate.quotKerEquivOfSurjective
        standardN3Coordinate_surjective).toModuleIso

noncomputable def torusCrosscapSmithCokernelIso :
    cokernel torusCrosscapBoundaryMap ≅ ModuleCat.of ℤ Smith :=
  ModuleCat.cokernelIsoRangeQuotient torusCrosscapBoundaryMap ≪≫
    ((Submodule.quotEquivOfEq _ _ torusCrosscap_range_eq_ker) ≪≫ₗ
      torusCrosscapCoordinate.quotKerEquivOfSurjective
        torusCrosscapCoordinate_surjective).toModuleIso

#print axioms standardN3SmithCokernelIso
#print axioms torusCrosscapSmithCokernelIso

end ConstructionTargets.T97A01SmithQuotients

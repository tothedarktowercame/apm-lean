import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Fundamental groups of products

This file specializes Mathlib's path-class product and projection operations
to the vertex groups of the fundamental groupoid.
-/

noncomputable section

namespace ConstructionTargets.FundamentalGroupProduct

open CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The fundamental group of a product is the product of the two based
fundamental groups.  The forward map is induced by the coordinate projections,
and the inverse takes the product of the two loop classes. -/
def fundamentalGroupProdMulEquiv (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y where
  toFun p := (Path.Homotopic.projLeft p, Path.Homotopic.projRight p)
  invFun p := Path.Homotopic.prod p.1 p.2
  left_inv p := Path.Homotopic.prod_projLeft_projRight p
  right_inv p := by
    ext
    · exact Path.Homotopic.projLeft_prod p.1 p.2
    · exact Path.Homotopic.projRight_prod p.1 p.2
  map_mul' p q := by
    ext
    · exact map_mul
        (FundamentalGroup.map ⟨Prod.fst, continuous_fst⟩ (x, y)) p q
    · exact map_mul
        (FundamentalGroup.map ⟨Prod.snd, continuous_snd⟩ (x, y)) p q

@[simp] theorem fundamentalGroupProdMulEquiv_apply (x : X) (y : Y)
    (p : FundamentalGroup (X × Y) (x, y)) :
    fundamentalGroupProdMulEquiv x y p =
      (Path.Homotopic.projLeft p, Path.Homotopic.projRight p) := rfl

@[simp] theorem fundamentalGroupProdMulEquiv_symm_apply (x : X) (y : Y)
    (p : FundamentalGroup X x × FundamentalGroup Y y) :
    (fundamentalGroupProdMulEquiv x y).symm p =
      Path.Homotopic.prod p.1 p.2 := rfl

#print axioms fundamentalGroupProdMulEquiv

end ConstructionTargets.FundamentalGroupProduct

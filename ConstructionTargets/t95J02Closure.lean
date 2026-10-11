import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.SingularHomologyHomotopy

/-!
# Reusable homology input for the t95J02 closure

The point-set construction of the Klein bottle and its core circles remains in
the consumer module because those are definitions pinned by the registered
statement.  This module records the reusable coefficient-homology fact used by
the final calculation: reflection in the second coordinate of the Euclidean
circle acts as negative identity on integral first homology.
-/

noncomputable section

namespace ConstructionTargets.t95J02Closure

open CategoryTheory

theorem integral_circle_coordinate_one :
    (CoefficientCoordinateReflections.H ℤ 1).map
        (TopCat.ofHom
          (CoefficientCoordinateReflections.reflectionMap (1 : Fin 2))) =
      -𝟙 _ :=
  CoefficientFirstReflection.integral_circle (1 : Fin 2)

end ConstructionTargets.t95J02Closure

#print axioms ConstructionTargets.t95J02Closure.integral_circle_coordinate_one

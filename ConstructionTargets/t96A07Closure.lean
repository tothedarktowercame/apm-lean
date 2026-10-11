import ConstructionTargets.RealProjectiveSmoothTarget

open ConstructionTargets.RealProjectiveSmoothTarget

noncomputable section

namespace ConstructionTargets.T96A07Closure

def crossTermSphereMap (p : Sphere 2) : E 3 :=
  WithLp.toLp 2 ![p.val 1 * p.val 2, p.val 0 * p.val 2,
    p.val 0 * p.val 1]

/-- The cross-term quadratic sphere map is invariant under the antipodal map. -/
theorem crossTermSphereMap_antipodal (p : Sphere 2) :
    crossTermSphereMap (sphereAntipodalN 2 p) = crossTermSphereMap p := by
  ext i
  fin_cases i <;> simp [crossTermSphereMap, sphereAntipodalN]

#print axioms crossTermSphereMap_antipodal

end ConstructionTargets.T96A07Closure

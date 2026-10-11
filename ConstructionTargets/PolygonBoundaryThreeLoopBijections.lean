import ConstructionTargets.PolygonBoundaryThreeLoopDecoderLeftInverse
import ConstructionTargets.PolygonSixEdgeCircleCover

open ConstructionTargets

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeLoopBijections

open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryThreeLoopDecoderLeftInverse
open PolygonSixEdgeCircleCover

theorem injective_n3ThreeLoops : Function.Injective n3ThreeLoops :=
  n3QuotientDecode_leftInverse.injective

theorem injective_torusCrosscapThreeLoops :
    Function.Injective torusCrosscapThreeLoops :=
  torusCrosscapQuotientDecode_leftInverse.injective

theorem bijective_n3ThreeLoops : Function.Bijective n3ThreeLoops :=
  ⟨injective_n3ThreeLoops, surjective_n3ThreeLoops⟩

theorem bijective_torusCrosscapThreeLoops :
    Function.Bijective torusCrosscapThreeLoops :=
  ⟨injective_torusCrosscapThreeLoops, surjective_torusCrosscapThreeLoops⟩

#print axioms injective_n3ThreeLoops
#print axioms injective_torusCrosscapThreeLoops
#print axioms bijective_n3ThreeLoops
#print axioms bijective_torusCrosscapThreeLoops

end ConstructionTargets.PolygonBoundaryThreeLoopBijections

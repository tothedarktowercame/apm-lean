# Fixed ball-boundary relative lift

Over an arbitrary Type 0 commutative ring R, the model is EuclideanSpace ℝ (Fin (m+2)). The fixed domain is the closed ball of positive radius r, with its literal subtype boundary defined by norm(z)=r. `ballContractible` proves contractibility using radius positivity. `sphere` sends a unit-sphere point to r • z in this boundary, proving both subtype memberships and continuity.

`lift` follows the actual sphere homology map in degree m+1 by the inverse contractible ball-pair connecting isomorphism. Its parameters are R, m, r and the positivity proof; it is independent of the moving interior point p. No relative class or isomorphism is supplied.

For norm(p)<r, `recenter` is the actual map z ↦ z-p. `recenter_mapsTo` proves that the fixed boundary maps into the punctured model. `relativeMap` is its actual subtype-cokernel pair map, and `projection` gives the degreewise cokernel-projection equation. `boundary_composite` identifies sphere inclusion followed by restricted recentering with the reviewed scaled recentered boundary map.

`connecting_equation` follows the lift with relative recentering homology in degree m+2 and the punctured-model connecting arrow. Actual pair connecting naturality and the proved connecting inverse law identify this composite with the actual scaled recentered boundary homology map. `normalization` then uses the model forward composite and the reviewed scaled-boundary radial inverse to identify lift followed by relative recentering and CoefficientModelLocal.localIso.hom with CoefficientSphereAntipodal.normalization.hom.

Integer and rational examples and ten standard-only axiom audits are included. The source exactly matches fixture SHA256 d116bc9cdec7e777a7fbe22a205fb3aeab7658ce61d40584c9895337ce7aca01. No orientation or nontriviality hypothesis is imposed.

Transporting this fixed ball and boundary through the actual chart overlap, identifying the transported relative class with chart normalizations, and applying compact-boundary motion remain downstream. Nonlinear chart transport, transition-unit local constancy, orientation compatibility and consumer closure are not claimed.

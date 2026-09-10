# Coefficient-general low-dimensional sphere endpoints

Promoted unchanged from `/tmp/CoefficientSphereEndpoints.lean`, SHA256 `115d7b73752f1ab988149c43021ca178a97b1a64c61120aaa9e6df6d07cac82c`.

R and all spaces are Type 0; R is a commutative ring with no field, domain or nontriviality assumption. Actual chains and homology use ModuleCat R with coefficient object `ModuleCat.of R R`.

`boundaryHomeo` sends the negative one-dimensional disk endpoint to false and the positive endpoint to true. Ordinary H0 retains both coordinates. `boundarySigmaIso` and `boolModuleIso` construct the boundary coordinates, while `diskIso` constructs the disk coordinate through its homotopy equivalence with a point. `inclusion_coordinates` proves that the actual subtype-inclusion H0 map becomes the codiagonal. No geometric map identification is assumed.

`boundaryKernelIso` transports the actual categorical kernel to the reviewed codiagonal kernel. Its forward map is specified explicitly. Its inverse followed by kernel inclusion and boundary coordinates equals the signed map, with false coordinate r and true coordinate -r.

The reviewed sphere-to-kernel comparison gives `circleH1`; the reviewed shift followed by this comparison gives `sphereH2`. Their exact forward composites and both inverse laws are proved. `sphereH1` identifies actual S2 H1 with `ModuleCat.of R (Fin 0 → R)` using the reviewed vanishing result. `sphereH0` reuses augmentation. Integer S1 H1 and S2 H1/H2 and rational S2 H0/H1/H2 specializations are included. The rational identity-induced maps conjugate to identities in all three degrees; these equations do not assert general sphere-map naturality or antipodal signs. Twenty-five standard-only audits are included.

Dependencies are `CoefficientSphereShift` (PASS `invoke-1789014962618-17854-ab60e27b`), `CoefficientCodiagonalKernel` (PASS `invoke-1789015773700-17882-20e0b4cb`), `CoefficientConnectedH0Map` (PASS `invoke-1789016186975-17898-3f68774d`) and the discrete H0 geometry/API in `SphereZeroCoefficients`. No integral homology conclusion is reinterpreted as R-linear.

Exact transport to the frozen sphere-identity branch and trace evaluation remain downstream. Independent Klein-product and fold-fiber obligations prevent full t00J01 closure. No general signed naturality, antipodal sign, frozen closure or change to historical refutations is claimed. This implementation changes no consumer placeholders.

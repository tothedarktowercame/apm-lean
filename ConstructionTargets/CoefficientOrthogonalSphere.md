# Height-preserving orthogonal sphere comparison

`ConstructionTargets.CoefficientOrthogonalSphere` constructs the sphere action that applies a real linear isometry equivalence Q to the first n coordinates and fixes height. The geometry is over ℝ; coefficients independently use an arbitrary Type 0 commutative ring R and `ModuleCat.of R R`. All dimensions include zero.

`sphereAction` is defined on the actual sphere subtype, with norm preservation proved from the coordinate norm identity. `height` proves height invariance. The north-pole complement, closed lower hemisphere, open upper hemisphere and punctured upper hemisphere preservation lemmas construct the actual restrictions. This action preserves hemispheres; it does not exchange them.

`coordinate_square` proves commutation with the open-disk hemisphere coordinates. `upperInclusion` is the actual subtype inclusion, and `excision_geometric_square` proves its compatibility with the sphere and upper-hemisphere actions. `excision_actual` identifies the reviewed excision map with this inclusion-induced pair map. Pair-map composition gives the actual relative coordinate and excision squares. Their homology equations and inverse equations retain the reviewed exact comparison maps. `upper_projection` and `sphere_projection` state the categorical cokernel-projection equations in every chain degree.

`sphereHomologyMap` is the actual sphere action on singular homology. `projection_naturality`, inverse excision, inverse coordinate comparison and reviewed inverse radial naturality give `sphereToDisk_naturality`: sphere action followed by `sphereToDiskIso.hom` equals that comparison followed by the actual closed-disk pair action. Its inverse equation is proved. These statements require positive homology degree j.

`boundaryHomologyMap` is the actual Q-induced unit-sphere action. The boundary-homeomorphism equation and actual pair connecting naturality extend the comparison to `sphereShift_naturality` and its inverse: the degree k+1 sphere action intertwines the degree k boundary action. The hypothesis k ≠ 0 remains explicit. Ordinary-H0 endpoints are not replaced by these positive-degree statements.

Integer, rational, zero-dimensional and reflection specializations are included. `reflection_disk_action` identifies the one-dimensional disk action with the reviewed literal negation. The source is promoted byte-for-byte from `/tmp/CoefficientOrthogonalSphere.lean`, SHA256 `8f89caff7fd8a19e09bdf99c7c76f921f99fbad28033e13ee037b6345e440de4`, including twenty-eight axiom audits.

Transport of reflection signs and coordinate-permutation or hemisphere-exchange comparisons remain before full antipodal action and frozen uptake. No determinant sign, hemisphere exchange, orientation coherence or consumer closure is claimed. Degree realization, localization/gluing and nonbounding retain independent obligations.

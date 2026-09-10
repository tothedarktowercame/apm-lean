# Actual disk-reflection sign over a commutative ring

`ConstructionTargets.CoefficientDiskReflection` proves that literal negation of the actual one-dimensional Euclidean closed disk induces minus identity on relative H1. R is any Type 0 commutative ring, without field, nontriviality or characteristic restrictions. Chains and homology use `ModuleCat.of R R` and the actual boundary subtype cokernel.

The imported `CoefficientBoundaryReflection` constructs negation, its boundary restriction, the absolute and relative chain maps, and the cokernel-projection equation in every degree. It identifies the actual boundary H0 map with coordinate exchange under `boundaryIso`. Ordinary boundary H0 retains both coordinates: the negative endpoint is false and the positive endpoint is true.

`kernelMap` is the categorical kernel map induced by the actual boundary inclusion square. `kernel_projection` identifies its composite with the kernel inclusion. The reviewed signed generator has coordinates (r,-r); `signed_swap` negates it. `kernel_inverse_action` and `kernel_conjugation` prove the resulting action is minus identity in `boundaryKernelIso` coordinates.

`relativeMap` is the actual reflection-induced relative H1 map. `connectingIso` is the reviewed contractible relative-H1 comparison with the actual inclusion kernel. `connecting_kernel_naturality` derives its compatibility with reflection from pair connecting naturality in degree zero and the exact kernel-projection equation. No kernel naturality or reflection sign is assumed.

`normalization` composes `connectingIso` with `boundaryKernelIso`. Its exact forward composite and both inverse laws are proved. `relative_conjugation` gives minus identity in these coordinates, `relative_forward` states the forward equation, and `relative_eq_neg_id` proves the actual relative H1 map equals minus identity. Integer and rational examples are included.

The Lean source is promoted byte-for-byte from `/tmp/CoefficientDiskReflection.lean`, SHA256 `37083e8bc9d62d53b7b607e2f5bcd157c6259c35c477cfb439d3bb9a78d63888`, including fourteen axiom audits.

Higher-dimensional hemisphere exchange and compatibility with sphere suspension remain before antipodal action and t94J08 uptake. The original S0 refutation is preserved; this packet claims no higher-sphere sign, orientation coherence or consumer closure. Degree realization, localization/gluing and nonbounding retain their geometric obligations.

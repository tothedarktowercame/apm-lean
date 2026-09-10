# Actual coefficient-general pair sequence

Promoted unchanged from `/tmp/CoefficientPairSequence.lean`, SHA256 `ffec25e86774ae2004eaf819a94025a333de451ba0b4e61434004b2422cde28e`.

For a Type 0 commutative ring R, a Type 0 topological space X and arbitrary subset A, the module constructs the short exact sequence of actual ModuleCat R chains from the subtype inclusion and its categorical cokernel. The coefficient object is `ModuleCat.of R R`. There is no nonemptiness or contractibility assumption on exactness.

`connecting n` runs from H_(n+1)(X,A;R) to H_n(A;R). The three exact segments are the connecting map followed by the inclusion-induced map, the inclusion-induced map followed by projection, and projection followed by the connecting map.

`connectingIso` explicitly requires `IsZero` for H_(n+1)(X;R) and H_n(X;R). Its forward arrow is the connecting map, with both inverse laws proved. `relativeH1IsoKernel` explicitly requires `IsZero` for H_1(X;R), and identifies H_1(X,A;R) with the kernel of H_0(A;R) → H_0(X;R). Its forward arrow followed by kernel inclusion is the connecting map. These vanishing assumptions remain obligations for the geometric consumer.

Integer and rational disk-boundary sequence and exactness examples reuse `T02A06DiskPairShift.diskBoundarySubset`; they make no disk homology calculation. Ten standard-only axiom audits are included.

Dependencies are the reviewed `CoefficientExcision` (PASS `invoke-1789012319312-17791-9d2bd335`) and `CoefficientCokernelComparison` (PASS `invoke-1789010115230-17742-ed1a544c`). The sequence is constructed over R, without reinterpreting an integral conclusion.

Contractible-space positive-degree vanishing over R, contractible-subspace H0 monicity, and the contractible projection and disk-pair endpoints remain downstream. This module claims no sphere suspension or consumer closure and changes no consumer placeholders.

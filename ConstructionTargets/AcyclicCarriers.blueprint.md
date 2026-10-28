# Acyclic carriers for affine comparisons

## Triage

The comparison-uniqueness statement is true as registered.  Its missing input
is precisely the acyclic-carrier theorem.  A face has `k+1` vertices, hence is
never empty; its convex hull is a nonempty convex subset of Euclidean space.
The point case makes the homotopy zero.  For an edge, the difference of the two
realizations is a carried 1-cycle in an interval and the filling leaf supplies
the carried 2-chain.  Boundaries of faces are carried by the same face because
the hull of every deleted subface is contained in the original hull.

## Leaves

| Leaf | Claim and intended proof | Estimate | Dependencies |
|---|---|---:|---|
| `faceHull_rationallyPointlike` | A face hull has rational homology of a point. Use `convex_convexHull`, `convexHull_nonempty_iff`, `Convex.contractibleSpace`, `ContractibleSpace.toHomotopyEquiv`, `rationallyPointlike_of_homotopyEquiv`, and `rationallyPointlike_unit`. | 50--90 | independent |
| `faceCarriedChain_boundary` | Boundary preserves the finite carrier presentation. Use `CoefficientH0.singularGenerator_boundary`, `singularSimplexOfContinuousMap_face`, and range monotonicity under precomposition. | 80--130 | independent |
| `affineComparison_generator_carried` | The comparison image of a basis face has the required one-generator presentation; unpack `IsAffineComparison`. | 25--45 | independent |
| `faceCarriedChain_mono` | Enlarge a carrier using `convexHull_mono`. | 20--35 | independent |
| `faceCarriedCycle_bounds` | Lift a carried cycle to chains on the hull subtype, kill its positive-degree homology class, obtain a boundary, then push forward. Use `HomologicalComplex.exact_iff`, `homologyπ`, and `singularGenerator_singularPostcomposition`. | 150--220 | builds on the supplied `hpoint`; **LIBRARY** at the categorical lift boundary |
| `affineComparison_degreeZero_eq` | A vertex hull is a singleton, so both degree-zero simplices are the same constant map; extend from `Finsupp.single` using `Finsupp.lhom_ext'`. | 70--110 | independent |
| `carried_chainHomotopy_exists` | Induct on degree and faces, choosing a carried filling for the usual difference cycle and extending linearly; verify `Homotopy.comm`. | 180--280 | takes `hfill` and `hzero` explicitly; **LIBRARY** if categorical bookkeeping exceeds 200 |

Dependency layers: first all leaves except `carried_chainHomotopy_exists`; then
the inductive homotopy leaf; finally the sorry-free assembly in
`SimplicialSingularComparison.affineComparison_homologyMap_eq`.

## C1--C10 checks

- `faceHull_rationallyPointlike`: C1 nonempty follows from `s.card=k+1`; C2 no conclusion hypothesis; C3 only contractibility/homology bridge; C4 direct; C5 subtype is the exact hull used later; C6 no extra assumption; C7 coefficients are `ℚ`; C8 `k=0` is a singleton hull; C9 not the comparison theorem; C10 matches.
- `faceCarriedChain_boundary`: C1 faces of a carried simplex stay carried; C2--C3 concrete boundary claim only; C4 generator expansion covers finite sums; C5 output uses the same carrier predicate; C6--C7 exact production chains/signs; C8 degree zero is not requested (`k+1` boundary); C9 distinct; C10 matches.
- `affineComparison_generator_carried`: C1 is exactly the range clause of `IsAffineComparison`; C2--C3 no restatement; C4 one-generator witness; C5 same carrier; C6--C8 includes vertices; C9 distinct; C10 matches.
- `faceCarriedChain_mono`: C1 `convexHull_mono`; C2 hypothesis is strict subset data, not conclusion; C3 small; C4 direct; C5 exact predicate; C6--C8 empty finite sets also valid; C9 distinct; C10 matches.
- `faceCarriedCycle_bounds`: C1 positive degree and rational pointlikeness imply exactness; C2 `hpoint` does not restate a chain filling; C3 isolates only the lift/exactness step; C4 finite presentations lift; C5 returns exactly a carried primitive; C6 no injectivity assumption hidden; C7 `k-1` is safe because `hk`; C8 excludes degree zero intentionally; C9 not the ancestor equality; C10 matches.
- `affineComparison_degreeZero_eq`: C1 a `FaceIndex K 0` has exactly one vertex; C2 no equality hypothesis; C3 only base case; C4 basis extensionality; C5 exact maps consumed by induction; C6--C8 covers complexes with no vertices vacuously and point complexes concretely; C9 not ancestor; C10 matches.
- `carried_chainHomotopy_exists`: C1 standard acyclic-carrier induction; C2 `hfill` is local cycle filling, not homotopy existence; C3 topology is removed and the leaf contains only induction/linear extension; C4 base is `hzero`, successor is `hfill`; C5 returns Mathlib `Homotopy`; C6 uses all registered hypotheses; C7 downward `ComplexShape` signs follow `Homotopy.comm`; C8 degree zero handled separately; C9 strictly stronger intermediate structure, not repeated homology equality; C10 matches.

## Doubts / library boundary

The likely hard library boundary is not convex contractibility but converting a
finite generator presentation in `K.space` into a categorical singular chain
on the hull subtype and back.  If Mathlib's coproduct extensionality makes that
exceed 200 lines, `faceCarriedCycle_bounds` should remain explicitly LIBRARY.
The inductive choice leaf may likewise cross 200 lines because the source is a
categorical `ModuleCat` morphism over a `Finsupp` basis; its mathematical claim
is nevertheless the exact consumed acyclic-carrier induction, not the final
homology equality.

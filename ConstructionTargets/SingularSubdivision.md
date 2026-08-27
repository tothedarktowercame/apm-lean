# Excision trunk — progress ledger

Singular-chain barycentric subdivision, the small-chain theorem, and excision.
Built to close APM `t02A06` conjunct 2 (`bridge_2`: no homeomorphism
`S² × S² ≃ₜ S⁴`), which needs `H₂(S²) ≠ 0` and `H₂(S⁴) = 0`.

**This is the largest single build in the programme.** This file exists so its
progress is inspectable without reading agent reports. Update it at every
checkpoint.

## Why this trunk is unavoidable

Both candidate routes to sphere homology reduce to the same machinery
(codex-3 discovery, 2026-08-19, verified independently):

- hemispherical excision `Hₖ(Sⁿ, Dⁿ) ≅ Hₖ(Dⁿ, Sⁿ⁻¹)` requires it directly;
- the good-pair quotient theorem `H̃ₖ(X/A) ≅ Hₖ(X,A)` is CLASSICALLY PROVED VIA
  EXCISION, so the quotient formulation relocates the subdivision argument
  rather than removing it. A homeomorphism `Dⁿ/Sⁿ⁻¹ ≅ Sⁿ` handles only the
  topological half.

At the pinned revision Mathlib has no barycentric subdivision, no small-chain
theorem, and no excision. Every "barycentric" hit is affine/convex coordinates.

## Step status

- [x] **0. Affine-simplex realization layer** — NOT IN THE ORIGINAL PLAN; found
      at checkpoint 1, closed at checkpoint 1a (`5d8251a`, 273 lines).
      Continuous affine realization of ordered vertices; face restriction
      through Mathlib's ULifted singular simplicial set; a generator API on the
      real `Limits.Sigma.ι` summands; the alternating boundary formula for
      generators; and coning with the proved identity
      `∂(b ⋆ c) = c - b ⋆ ∂c` (`coneGenerator_boundary`), anti-vacuity-checked
      against the production map by `∂[b,p] = [p] - [b]`
      (`coneGenerator_vertex_boundary`).
- [x] **1. Barycentric subdivision on standard simplices, hence on affine
      singular chains** (`vertexSubdivision`, `affineSubdivision`). The
      arbitrary-space version is obtained downstream by postcomposition with
      each singular simplex; its naturality interface is deliberately left to
      the smallness slice where support is tracked.
- [x] **2. Signed boundary formula: `sd` is a chain map**
      (`vertexSubdivision_comm_d`, `affineSubdivision_boundary`). The corrected
      edge check proves `∂sd[0,1] = sd∂[0,1] = [1]-[0]`
      (`affineSubdivision_edge_boundary`).
- [x] **3. Prism operator: `sd` chain-homotopic to the identity**
      (`vertexPrism`, `vertexPrism_identity`).  The production prism is defined
      by the same prepend-cone recursion as subdivision, and the standard-edge
      generator check `vertexPrism_standardEdge_identity` evaluates
      `∂T + T∂ = sd - id` without imposing a representative normal form.
- [x] **4. Iterated smallness subordinate to an open cover (Lebesgue number).**
      Slice 4a supplied an actual finite `Finsupp` support
      (`finiteVertexSubdivisionSupport`) realizes to the production map
      (`finiteVertexSubdivision_realize`), and every supported simplex obeys
      the explicit contraction
      `diam(sd σ) ≤ n/(n+1) · diam(σ)`
      (`finiteVertexSubdivision_diameter_le`). Slice 4b compounds that bound
      under iteration and applies the metric Lebesgue-number lemma to obtain
      open-cover subordination (`iteratedFiniteVertexSubdivision_diameter_le`,
      `exists_iteratedFiniteVertexSubdivision_subordinate`).
- [ ] **5. Small-chain subcomplex; its inclusion is a quasi-isomorphism.**
      Slice 5a is complete: finite support transports through postcomposition
      with an arbitrary singular simplex
      (`postcomposedIteratedSubdivision_small`); a finite chain admits one
      common subdivision depth (`Finsupp.exists_uniform_depth`); and the prism
      has a finite presentation realizing exactly to the production map and
      preserves the original cover member (`finiteVertexPrism_realize`,
      `postcomposedPrism_small`). The quasi-isomorphism remains for slice 5b.
      The small complex is now defined concretely as the singular chains of the
      simplicial subcomplex `coverSmallSSet`: the supremum of the ranges of the
      cover inclusions.  Thus each degree is a coproduct/direct sum over the
      subtype of subordinate simplices, and face closure is structural.  The
      earlier categorical-image definition was removed; it mixed image objects
      with concrete finite-support arguments and repeatedly demanded comparison
      bridges.
- [ ] 6. Excision, derived algebraically from small chains.
- [ ] 7. The `(Dⁿ, Sⁿ⁻¹)` instance, and thence `Hₖ(Sⁿ)`.

## Progress criterion

A checkpoint counts as progress if it does ONE of:

1. lands compiling, axiom-clean code, or
2. moves the wall — stops with an obstruction DIFFERENT from the previous one.

A checkpoint that does neither — the same obstruction twice — is the stop
signal, and the trunk gets re-scoped or parked rather than retried.
(Joe's rule, 2026-08-19: continue while the obstruction moves, stop when it
repeats. Attempt-counting is the wrong variable.)

## Wall log

| # | wall | found at | status |
|---|---|---|---|
| W1 | Mathlib's singular chains are a coproduct over simplices with only VERTEX-REINDEXING maps for `stdSimplex`; subdivision needs ARBITRARY AFFINE simplices with barycentre vertices. No realization of an ordered vertex family as a continuous affine simplex, and nothing linking such a realization to the coproduct differential. | checkpoint 1 | **CLOSED** at 1a (`5d8251a`). ULifted simplicial face coherence was real but tractable: once unfolded it reduced to the affine precomposition theorem. |
| W2 | The accepted recursive cone convention prepends the barycentre and proves `∂(b ⋆ c) = c - b ⋆ ∂c`. Applied to the standard edge, it computes `sd[0,1] = [1/2,1] - [1/2,0]`, not the geometrically drawn representative `[0,1/2] + [1/2,1]`; these are distinct free singular chains. | checkpoint 2 | **RESOLVED by specification correction.** The prepend-cone result is the standard recursion and has the required boundary. The rejected bar over-specified a representative instead of testing the chain-map property. No machinery change was needed; 348 correct experimental lines were nevertheless reverted before the correction, so that dispatch remains charged below. |

| W3 | The finite-support/production bridge exists only for VERTEX CHAINS IN A STANDARD SIMPLEX. `finiteVertexSubdivision_realize` and `finiteVertexPrism_realize` do not cover the POSTCOMPOSED operations on an arbitrary space: `postcomposedIteratedSubdivision` and `postcomposedPrism` are `Finsupp` values with no realization lemma identifying them with operations on `SingularChains (TopCat.of X)`. There is no global subdivision endomorphism or prism homotopy on arbitrary `X`, so the prism identity cannot show a production cycle homologous to its subdivision. `Finsupp.exists_uniform_depth` additionally needs monotonicity: nothing yet states that subordination persists under further subdivision. | checkpoint 5b | **CLOSED.** `singularSubdivision` is a genuine production chain endomorphism, `singularPrism_identity` transports the prism homotopy, and `productionCycle_homologous_to_subdivision` proves the consuming production-cycle statement. |

| W4 | **Affine naturality of subdivision/prism is missing.** The production-level DEGREE operators are definable cleanly — represent each production generator by its continuous simplex, subdivide the identity standard simplex, postcompose through the singular-chain functor, extend via the coproduct — and the generator/postcomposition realization lemma compiles. The obstruction is proving those degree maps commute with the production DIFFERENTIAL, which needs `subdivision(face σ) = postcompose(face inclusion, subdivision σ)`: affine subdivision must be natural under standard-simplex face maps. Neither slice 5a nor Mathlib provides it, and the same equivariance is needed for the global prism identity. Without it the "global subdivision" is only a family of degree morphisms, not an endomorphism of the production complex. | checkpoint 5a-bis | **OPEN.** New wall, distinct from W3: realization INTO production chains is constructible; what is missing is compatibility of that realization with affine reparameterization. |

| W5 | Naturality of the affine REALIZATION itself: the square connecting `VertexChains --vertexMap--> VertexChains` to `SingularChains --functor map--> SingularChains`. Without it, affine naturality proved inside `VertexChains` could not be transported into the production complex. | checkpoint 5a-ter | **CLOSED** at `b6be2f6` (`vertexRealization_affine_natural`), together with the prism analogue. |
| W6 | Face compatibility for an ARBITRARY singular simplex through `TopCat.toSSetObjEquiv`. The file proved it only where the original simplex was itself affine into a standard simplex. Needed to rewrite the production boundary facewise. | checkpoint 5c | **CLOSED** at `35d1007` (`singularSimplexOfContinuousMap_face`), general in `X` and in the continuous simplex. Generalising the existing affine proof worked; the ULift coherence unfolded to standard-simplex face coordinates. |
| W7 | Coherence between the TWO CONCRETE PRESENTATIONS of a standard face. The production boundary presents a face as precomposition by the affine basis-face map (W6); the vertex naturality theorem presents the same operation as `vertexMapDegree faceAffine` applied to the standard identity vertex family. Assembly needs two explicit equalities: (a) affine realization of the standard basis vertices IS the identity simplex; (b) mapping those vertices through `faceAffine` gives exactly the deleted standard vertex family the production boundary uses. Both are finite-index computations rather than missing theory. | checkpoint W6-closure | **CLOSED** at `9f28524`; both were finite-coordinate computations. |
| W8 | The injectivity correction consumes `singularPrismDegree` on an arbitrary production chain, but `postcomposedPrism_small` describes only the `Finsupp` support of the prism on one represented generator. | checkpoint 5b after concrete redesign | **CLOSED at the support/factorization boundary.** `singularPrismDegree_eq_realization` identifies the global prism with finite prisms; `finiteProductionChainRealize_comp_coproductIso` proves coordinate reassembly by `DFinsupp` induction; and `productionChain_factors_coverSmallChains` now factors every arbitrary production-chain element with subordinate support through the small-chain inclusion. The quasi-isomorphism itself remains to be assembled. |

**Prediction record, recorded deliberately.** The claude-10 review has predicted
"this is the last wall" at checkpoints 5a-bis, 5a-ter, 5c and W6 — wrong four
times out of four. The walls ARE strictly narrowing (missing theory, then missing
commuting squares, now missing finite computations) and three of the last four
checkpoints landed axiom-clean code, but that narrowing is the evidence, not the
review's optimism. Discount accordingly.
**Review miss, recorded deliberately.** At checkpoint 5a the claude-10 review
verified that `_realize` lemmas EXISTED, and grepped three of them, but did not
check WHAT they realized. `postcomposedPrism_small` was accepted as the bridge;
codex-3 has since self-reported it as a wrapper for 5b's purposes. The correct
check would have been "does a realization lemma exist for the operations the NEXT
slice consumes", not "does a realization lemma exist". Recorded so the review
standard is auditable alongside the work it reviews.

## Cost account: where building on Mathlib's singular chains is expensive

Recorded at the assembly checkpoint (`70642ef`, 2,034 lines), after nine
checkpoints on this trunk. This is the generalisable finding, independent of
subdivision.

**Cheap, contrary to expectation:**

- Coproduct ergonomics. `Sigma.desc` defined both degreewise operations directly
  and `Sigma.ι_desc` gave their generator formulas without difficulty.
- ULift / universe friction. Real at W1, but absorbed once and for all by W6.
- Alternating-sign bookkeeping. `singularGenerator_boundary` packages it.

For the surface intersection program, the degree-two
Alexander--Whitney foundation is now explicit.  `alexanderWhitneyFrontEdge`
and `alexanderWhitneyBackEdge` select `[0,1]` and `[1,2]`; their maps extend
linearly over the free singular-chain coproduct.  The generator boundary is
proved to be back edge minus middle edge plus front edge, and the front-edge
generator is proved natural under continuous postcomposition.

**Expensive: proving a generator-linear operation is a CHAIN MAP.**

The generator-level differential square crosses FOUR representations of the same
face:

1. the production simplicial face;
2. precomposition by `faceAffine`;
3. `vertexMapDegree faceAffine`;
4. postcomposition through the singular-chain functor.

W5, W6 and W7 each prove one comparison square, but Mathlib does not normalise
their composite. Every term needs deliberate reassociation of categorical
composition, rewriting through affine realization naturality, then functorial
postcomposition, before the alternating sums can be identified.

**The cost is categorical composition/rewrite ergonomics, not mathematics or
geometry.** All the required equalities exist and are proved; assembling them
through deeply nested morphism expressions with the correct orientations is what
is expensive.

**The transferable lesson:** on Mathlib's singular-chain encoding, DEFINING
generator-linear operations is cheap and PROVING them chain maps is not — the
expense concentrates at the boundary where simplicial faces, continuous-map
representatives, and categorical functor maps meet. Budget for that boundary
rather than for the mathematics.

### Completed finding, after testing the intended tooling (`5258e99`)

Two further results sharpen this, both established by actually trying the fix
rather than by inspection:

1. **The face boundary costs ONE general lemma, not `n+1`.**
   `subdividedFace_transport` is uniform in `n`, `i`, `X` and the represented
   simplex and crosses all four representations, so the alternating sum needs no
   per-face reassociation proofs.

2. **Use `slice`, not `reassoc`, for middle-pair rewriting.** `@[reassoc]`
   preserves material on the RIGHT and is therefore appropriate for suffix
   transport. The failing expression was

       vertexGenerator ≫ vertexSubdivision ≫ vertexRealization ≫ d ≫ postcomposition

   where the needed rewrite changes the MIDDLE pair `vertexRealization ≫ d`
   underneath an arbitrary LEFT prefix. `slice_lhs` reassociated around that
   contiguous range and rewrote it directly; no hand-written prefix-whiskered
   lemma was needed.

The transferable tooling rule is: **`reassoc` for suffix transport; `slice_lhs`
or `slice_rhs` for rewriting a contiguous middle range under a long prefix or
suffix.**


## Cost ledger

Estimates are revised as evidence arrives; both the original and the revision
are kept so the drift is visible.

| slice | estimate | actual | dispatches | commits |
|---|---|---|---|---|
| whole trunk (original, 2026-08-19) | 1,500–3,000 lines / 6–10 checkpoints | — | — | — |
| whole trunk (revised after checkpoint 1) | **2,200–4,000 lines** | — | — | — |
| slice 1 — subdivision + boundary formula | (rolled into revision) | did not close; found W1 | 1 | 0 |
| slice 1a — step 0 foundation | 700–1,200 lines | **273 lines, closed** | 1 | 1 |
| slice 2 — subdivision + chain-map proof | inherited from whole-trunk revision | **did not close; 348 experimental lines reverted after W2 exposed a convention mismatch** | 1 | 0 code / 1 ledger-only |
| slice 2 retry — corrected property bar | inherited from whole-trunk revision | **377 lines landed; module now 650 lines** | 1 | 1 |
| slice 3 — prism operator | inherited from whole-trunk revision | **128 lines landed; module now 778 lines** | 1 | 1 |
| slice 4a — finite support + diameter contraction | inherited from whole-trunk revision | **520 lines landed; module now 1,298 lines** | 1 | 1 |
| slice 4b — iteration + Lebesgue subordination | inherited from whole-trunk revision | **161 lines landed; module now 1,459 lines** | 1 | 1 |
| slice 5a — transport + uniform depth + small prism | inherited from whole-trunk revision | **223 lines landed; module now 1,682 lines** | 1 | 1 |
| slice 5 production assembly | inherited from whole-trunk revision | **production chain endomorphism, prism identity, and cycle-homology statement landed; module now 2,282 lines** | 9 | 8 code + ledger commits |

The previously deferred support API is now **CLOSED** at slice 4a.  The
categorical coproduct did impose a real cost: its chosen object does not expose
finite support, so the slice introduced a `Finsupp` presentation and proved
that its realization is exactly `vertexSubdivision`.  That bridge prevents the
geometric argument from becoming a decorative parallel construction.  Once
the bridge existed, recursive support became a nested-face barycentre flag and
the quantitative diameter proof was direct induction.  No new wall was found.

Slice 4b reused the 4a interface without re-deriving contraction: nested
`Finsupp.bind` support gives the inductive diameter estimate, and affine-image
containment follows by placing the realized simplex in the convex hull of its
vertices.  The concrete quarter-ball cover of the standard edge exercises the
full subordination theorem.  Step 4 is now **CLOSED**; no new wall was found.

Slice 5a moves the support presentation to arbitrary singular simplices by
postcomposition, packages the finite-maximum depth argument, and gives the
recursive prism its own finite presentation with a proof that it realizes to
`vertexPrism`. The smallness proof then uses the decisive factorization:
every transported prism simplex still factors through its original singular
simplex. Item 3 behaved cleanly; no new wall was found.

**Estimate drift is TWO-SIDED, which is the reassuring finding.** Checkpoint 1
revised the trunk UP by 30–45% on an omitted foundation layer; checkpoint 1a then
came in at 273 lines against a 700–1,200 estimate for that layer — well under.
So the estimates are noisy rather than systematically optimistic, and the
slicing surfaces both directions cheaply. Neither revision cost more than one
dispatch.

## How to check progress without asking the agent

```sh
# what has landed
cd /home/joe/code/apm-singular-homology && git log --oneline infra/SingularHomologyConcrete

# does it compile, and is it axiom-clean
lake env lean ConstructionTargets/SingularSubdivision.lean
grep -c "sorry" ConstructionTargets/SingularSubdivision.lean

# this ledger
sed -n '/## Step status/,/## Cost ledger/p' ConstructionTargets/SingularSubdivision.md
```

## Comparable completed build, for calibration

The covering-space track (`SimplyConnectedSpace S³` for `t02A06` bridge 3) is
the closest reference: estimated 7–14 commits, delivered in 11 commits across
11 dispatches with 2 no-commit stops and **5 distinct walls**, all closed. Four
of the five fell to the same move — resolve choices where the types are simple
(inside a `Prop`, at `ℕ`, before indexing), then reindex by composition rather
than transporting proofs across index equalities. That build's estimate held.
This one's has already moved once.

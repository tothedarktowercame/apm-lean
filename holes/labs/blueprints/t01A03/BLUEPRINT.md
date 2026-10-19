# Blueprint for t01A03

## Triage verdict

**True and faithful; no statement repair.** The theorem concludes that none of
the three pictured inclusions has a retraction. Its three geometric predicates
encode exactly the picture data in `problem.md`: the middle circle has two
punctured-torus complementary components, the torus wedge has disk complement,
and the two circles leave a four-punctured sphere.

Attempts to break the statement:

- The ambient surface cannot be empty because `PathConnectedSpace S` is
  inhabited. Thus the connected-image argument in part (c) is genuine.
- `Circle` is nonempty and has nonzero integral `H₁`; the compiled class
  `ConstructionTargets.SingularHomologyConcrete.circleSingularH1Generator`
  rules out the zero-space degeneration in part (a).
- The two summands of `Sum Circle Circle` are genuinely distinct, so part (c)
  does not collapse to a connected target.
- A constant middle map or wedge map cannot satisfy `IsEmbedding`, while an
  arbitrary map of the nonabelian wedge group into the abelian torus group
  still cannot be injective. Thus no endpoint or constant-map case refutes the
  claims.
- The genus hypothesis is stronger than the middle-circle proof needs, but it
  agrees with the stated two-holed torus and is not used to smuggle in any
  obstruction conclusion.

The solve-loop records contain no counterexample. The topology audit instead
identifies the same two mathematical boundaries used below: point-wedge van
Kampen and the null-homology theorem for a separating embedded surface curve.

## Definitions and already compiled work

`Blueprint.lean` repeats all definitions from the registered statement. It
also carries over, with proofs, the functorial facts already proved in
`Main.lean`:

- a retraction makes the induced `π₁` and `H₁` maps injective;
- a zero `H₁` map from a circle forbids a retraction;
- a connected space cannot retract onto `Circle ⊔ Circle`.

The circle's nonzero homology class comes from the sorry-free module
`ConstructionTargets.CircleSingularHomology`. The searches
`grep -L sorry ConstructionTargets/*.lean` and `rg` over `ConstructionTargets`
also found the sorry-free `PointWedgeVanKampen`, `FundamentalGroupProduct`,
`ThreeRetractionObstructionAdapter`, and surface-related modules. The first two
are imported because they are the nearest APIs for the wedge seats. The
adapter merely repackages the already-proved obstruction implications and
does not prove either missing induced-map fact.

## Lemmas

### `apm_t01a03_wedge_homeomorph_finiteWedge_two`

**Statement.** The problem's quotient of `Circle ⊕ Circle` is homeomorphic to
the banked `FiniteWedge (Fin 2)`, and the left basepoint goes to
`wedgeCircle 0 1`.

**Route / Mathlib tools.** Use the equivalence
`Sum Circle Circle ≃ Fin 2 × Circle` (left goes to index `0`, right to index
`1`) and descend it through the two quotient relations with `Quotient.map`.
For well-definedness, induct on `Relation.EqvGen`; the only generator on each
side identifies `(0,1)` and `(1,1)`. Prove the inverse laws by
`Quotient.inductionOn`. Continuity in both directions follows from
`Continuous.quotient_lift`, `continuous_coinduced_rng`, and continuity on the
two summands (`continuous_sum_dom`). The existing comparison theorem
`ConstructionTargets.PointWedgeQuotient.quotientHomeomorphOfRelIff` is also a
useful template, though here the prequotient types differ.

**Estimate.** 50–90 lines. **Independent.** Yes.

**Truth check.** Neither quotient is empty. Both identify exactly the two
circle basepoints and no other points; the explicit basepoint equation rules
out a hidden basepoint rotation.

### `apm_t01a03_freeGroup_finTwo_noncommutative`

**Statement.** `FreeGroup (Fin 2)` contains two noncommuting elements.

**Route / Mathlib tools.** Take `FreeGroup.of 0` and `FreeGroup.of 1`. A short
way to separate the products is `FreeGroup.lift` into
`Equiv.Perm (Fin 3)`, sending the generators to the transpositions `(01)` and
`(12)`; `decide`/`native_decide` checks that the two permutation products
differ. Alternatively use the reduced-word API in
`Mathlib.GroupTheory.FreeGroup.Basic` (`FreeGroup.toWord`) to distinguish the
two length-two words.

**Estimate.** 15–30 lines (the algebraic leaf is already at the Mathlib
primitive layer). **Independent.** Yes.

**Truth check.** `Fin 2` has two provably distinct elements; this is not the
rank-zero or rank-one free group degeneration.

### `apm_t01a03_circleWedge_pi1_noncommutative` — sorry-free assembly

**Statement.** There are two based loop classes in the concrete two-circle
wedge which do not commute.

**Why true.** Transport `π₁` across the preceding homeomorphism using
`PolygonSurfaceHomology.fundamentalGroupEquivOfHomeomorphEq`. The sorry-free
banked theorem `finiteWedge_finSucc_fundamentalGroup_free 1` identifies the
target group with `FreeGroup (Fin 2)`. Pull the preceding noncommuting pair
back through the composite `MulEquiv`; injectivity gives the contradiction if
their products commute.

**Estimate.** Compiled in about 15 lines. **Depends on.** The two conclusions
above, plus only sorry-free banked work.

### `apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective`

**Statement.** Given the preceding noncommuting source loops, the induced
fundamental-group map of the typical wedge into the torus is not injective.

**Why true.** The torus fundamental group is abelian. Use
`ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv` to
identify a torus loop with its two circle projections; each circle fundamental
group is commutative (via the circle winding-number equivalence in the
point-wedge foundation). Hence the images of the supplied `a,b` commute. If
the map were injective, equality of their products would imply
`a*b = b*a`, contradicting the supplied witness. The disk-complement component
of `IsTypicalWedge` is not needed for this purely target-side obstruction; it
faithfully describes the picture but is harmless surplus.

**Estimate.** 30–60 lines.

**Depends on.** Receives the conclusion of
`apm_t01a03_circleWedge_pi1_noncommutative` as an explicit hypothesis, so its
body can be proved in parallel.

**Truth check.** Tested algebraically: an injective homomorphism from a group
with noncommuting `a,b` into an abelian group is impossible. Constant maps are
also covered (their induced map is visibly noninjective), although they do not
satisfy the geometric predicate.

### `apm_t01a03_separating_circle_H1_zero` — assembly over five leaves (split 2026-10-19)

**Statement.** In a compact connected surface with the genus-two homology, an
embedded circle whose complement is the disjoint union of two punctured tori
induces the zero map on integral first singular homology.

**Route (no collar).** lemma-1's partial (backup
`~/notes/packets/lemmas/t01A03-separating_circle-partial.lean.bak`) left the
whole collar/fundamental-class theorem as one `sorry`. The split avoids the
collar. Write Y for the two punctured tori and e for the complement
homeomorphism. Define ρ : S → OnePoint Y to be e off the circle and ∞ on it.
Then:
1. ρ is continuous (`_aux_collapse`): the preimage of the complement of a
   compact K ⊆ Y is S minus a compact, hence closed, set.
2. ρ ∘ middle is constant, so (ρ ∘ middle)_* = 0 on H₁ (`_aux_const`).
3. On the complement ρ agrees with coe ∘ e. Since e_* is bijective and
   coe_* : H₁(Y) → H₁(OnePoint Y) is surjective (`_aux_model_surj`), ρ_* is
   surjective.
4. H₁(S) ≅ ℤ⁴ (from `hasGenusTwo`) and H₁(OnePoint Y) ≅ ℤ⁴
   (`_aux_model_free`), so the surjection ρ_* is injective (`_aux_hopf`).
5. ρ_* ∘ middle_* = 0 with ρ_* injective, so middle_* = 0.

The assembly and the homeomorphism-surjectivity helper are proved in
`Blueprint.lean`. The leaves are independent of one another:
- `_aux_collapse` (point-set, ~40 lines)
- `_aux_const` (H₁ of a constant map; factor through `PUnit`)
- `_aux_hopf` (`OrzechProperty.injective_of_surjective_endomorphism` after
  transporting along the two isomorphisms)
- `_aux_model_free`, `_aux_model_surj` (homology of the wedge of two tori,
  stated on `OnePoint (Sum PuncturedTorus PuncturedTorus)`; Mayer–Vietoris
  over the point at infinity, see `notes/` in the lemma packets)

**`_aux_model_surj` split (2026-10-19, after a PARTIAL from lemma-1).** It is
proved in `Blueprint.lean` from `IntegralMV.integralMayerVietoris`
(`ConstructionTargets/IntegralOpenCoverMayerVietoris.lean`, now imported) on
the cover `U = range coe`, `V = (coe '' Nsumᶜ)ᶜ`, where `N` is the punctured
open square `dist x₁ 1 < 1 ∧ dist x₂ 1 < 1` around the puncture. The assembly
shows `δ₀ = 0` from injectivity of `H₀(U∩V) → H₀U`, so `mvJ` is onto in degree
1, and `H₁V = 0` reduces `mvJ` to `H₁U → H₁X`. Four leaves:
- `_aux_V_open`: `Nsumᶜ` is closed in two compact tori, so compact;
  `OnePoint.isOpen_compl_image_coe`.
- `_aux_V_H1_zero`: `V` is two open squares wedged at `∞`, hence contractible;
  `CoefficientContractiblePair.higher_zero`.
  Split 2026-10-19 (lemma-1 PARTIAL, nothing banked; it stalled on continuity
  of a direct contraction at `∞`). Assembly proved: `V ≃ₜ W` with `W` two open
  sup-norm unit squares in `(Fin 2 → ℝ)²` meeting at `0`, star-shaped. Leaves,
  independent: `_aux_W_contractible` (`StarConvex.contractibleSpace`),
  `_aux_chart` (`N ≃ₜ` punctured unit square by scaled angles, plus two
  compactness clauses), `_aux_homeomorph` (glue two charts at `∞ ↦ 0`; the
  chart and its clauses are hypotheses).
- `_aux_inter_H0_inj`: `U ∩ V` is the two punctured squares, each path
  connected, in different summands of `U`; `TopologicalSumSingularHomology`,
  `CoefficientConnectedH0Map`.
- `_aux_U_bridge`: `coe` is a homeomorphism onto `U`
  (`OnePoint.isOpenEmbedding_coe`), and `IntegralMV.HZ 1` is definitionally
  `apm_t01a03_H1`; match `mvToX` (a `homologyMap`) with `apm_t01a03_H1map`
  (a functor map) as in `t00J01/Blueprint.lean` near line 1161.

Only the two model leaves need algebraic topology. No leaf needs Schoenflies or
tameness of the embedding. The `surface-curve-collar` boundary named in
TOPOLOGY-ROUTES is not needed for this problem.

**Truth check.** The model is T ∨ T with H₁ = ℤ⁴, generated by loops away from
the wedge point. The argument used genus two only for the rank of H₁(S). For a
nonseparating circle the complement is connected, so the complement hypothesis
fails, as it should.

## Main assembly

The main theorem obtains the zero `H₁` map and the noninjective `π₁` map from
the three obligations, then applies the already-compiled functorial
obstructions. Part (c) is discharged directly by connectedness. The main proof
contains no `sorry`.

## Dependency layers

- Layer 1 (parallel):
  `apm_t01a03_wedge_homeomorph_finiteWedge_two`,
  `apm_t01a03_freeGroup_finTwo_noncommutative`,
  `apm_t01a03_typicalWedge_fundamentalGroupMap_not_injective`, and
  `apm_t01a03_separating_circle_H1_zero` (LIBRARY). The wedge adapter takes the
  source noncommutativity conclusion as a hypothesis, so all four lemma bodies
  are independently assignable.
- Layer 2: `apm_t01a03_circleWedge_pi1_noncommutative`, a sorry-free assembly
  of the two new wedge leaves and the banked rank-two van Kampen theorem.
- Layer 3: `apm_t01a03`, a sorry-free assembly from those conclusions and the
  proved obstruction lemmas.

## Axiom gate

Compilation command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A03/Blueprint.lean
```

Output:

```text
holes/labs/blueprints/t01A03/Blueprint.lean:181:6: warning: declaration uses `sorry`
holes/labs/blueprints/t01A03/Blueprint.lean:191:6: warning: declaration uses `sorry`
holes/labs/blueprints/t01A03/Blueprint.lean:252:8: warning: declaration uses `sorry`
'apm_t01a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

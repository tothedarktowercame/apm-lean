# Statement encoding: second tranche, 2026-09-10

Five more of the original 31 missing statements are now encoded. The current
source-stem count is **477/491 with Lean material**, with **14 remaining**.
Together with the first tranche, this is 17 newly encoded statements. Each of
these five has one explicit `sorry`: these are construction and statement
specifications, not completed problem proofs. Independent review is pending.

## New statements

| Bundle | What is now stated |
|---|---|
| [t93A06](../problems/t93A06/lean/Main.lean) | Actual R²/Z² torus, required quotient smooth atlas, unique descent of the printed form, torus integral 1/4, explicit primitive upstairs, nonexactness downstairs, and integral 1/4 on the four printed parallelogram edges. |
| [t97A05](../problems/t97A05/lean/Main.lean) | Nonzero oriented intersection number forces Y minus W to be connected. All four manifold dimensions, orientations, embeddings, compactness and connectedness conditions are retained. |
| [t97A06](../problems/t97A06/lean/Main.lean) | A volume form on the compact positive-dimensional embedded manifold extends smoothly; every extension is nonclosed when the inclusion is null-homotopic. |
| [t98J06](../problems/t98J06/lean/Main.lean) | Actual graph/diagonal transversality implies invertibility of df-I and the stated local orientation sign. |
| [t99J05](../problems/t99J05/lean/Main.lean) | Construct the diagonal map on CPⁿ, its affine charts and homotopy; identify all fixed points and indices; compute χ(CPⁿ)=n+1 through the rational-homology Lefschetz sum. n=2 is the exact printed map. |

## Construction work made explicit

Four new modules are imported by the library root, build as named Lake targets,
and contain no `sorry`. Their companion documents specify the open theorems:

- [ManifoldFormTargets](../ConstructionTargets/ManifoldFormTargets.md): genuine
  alternating tangent covectors, chart smoothness, pullback and exterior
  differentiation. Chart independence, naturality and calculus identities
  remain to prove.
- [TorusFormTargets](../ConstructionTargets/TorusFormTargets.md): the actual
  quotient, a required compatible smooth atlas, printed form, explicit
  primitive, fundamental-square integral and four segment integrals. Prove
  the atlas exists and that these computations have the claimed values.
- [ComplexProjectiveChartTargets](../ConstructionTargets/ComplexProjectiveChartTargets.md):
  exact affine ratio maps, explicit inverses and required open-chart
  certificates on the fixed quotient topology. Prove chart compatibility,
  local-index comparison and the global trace formula.
- [ManifoldIntersectionTargets](../ConstructionTargets/ManifoldIntersectionTargets.md):
  actual coincidence loci and tangent maps, orientation signs from the supplied
  volume forms, and a finite signed count after homotopy to a transverse map.
  Prove existence and independence of representatives and agreement with
  geometric intersection number.

In particular, t97A05 does **not** assume its original submanifolds are
transverse. Its number is defined using a transverse representative, with an
exact enumeration of all coincidences. No free tangent matrix, index, integral
operator or problem conclusion is supplied by the caller.

For t98J06 the local intersection sign comes from the actual tangent-sum map
ordered diagonal then graph, independently of the expression df-I. For t99J05
the fixed-point index instead uses id-Df in real affine coordinates. The two
orientation conventions are kept distinct.

## Validation

All five statements compile with `autoImplicit=false`; each final theorem has
exactly one deliberate proof hole. All four construction modules build and
have root imports and `.olean` files. Axiom inspection finds no `sorryAx` in
the construction declarations; final problem theorems do contain it.

The mechanical quality screen initially did not recognize the symbolic model
`Fin n → ℝ` as dimension evidence in t97A06. Its positive-dimension hypothesis
is now stated directly as `0 < Module.finrank ℝ (Fin n → ℝ)`, equivalent to
`0 < n`. The source condition is unchanged and the checker was not modified.
The affected statement was recompiled and rescreened. Final result: **5/5 pass**. See the saved
[validation record](statement-encoding-validation-round2-2026-09-10.json) for
final results and exact compiler/axiom output.

The global construction reachability gate remains red on **766 pre-existing
modules**. Running the same gate against HEAD's root and tracked module names
at `6c53872c88b6f9f19459d0344d8644a129bb6aa2` gives the identical failure set;
these changes add zero failures. All four new modules satisfy that gate's
import requirement. The discrepancy was neither bypassed nor suppressed.

## Remaining fourteen

| Bundles | Next concrete work |
|---|---|
| t93A05 | Extend actual intersection definitions to mod-2 counts and construct the specified projective submanifold witnesses. |
| t95A05 | Manifolds with boundary, oriented boundary integration and the separation construction. The new forms vocabulary supplies the interior operations. |
| t95A01 | Nonorientability and explicit surface self-cover witnesses, preserving all three existence questions. |
| t00J05, t99J02 | Explicit cell attachments, universal-cover/CW and connected-sum models, and comparison maps. Existing Mathlib CW definitions are available. |
| t98J05 | Concrete genus-two involution, its orbit quotient and smooth structure; resolve the printed non-equivalence relation explicitly. |
| a98J05 | Recover the absent conclusion. |
| lts-derived-induction-lem3, lts-monadic-integration | Recover the intended spectrum and measure-monad definitions. |
| t93J05 | Resolve the unbounded cylinder in the source versus the closed capped surface in the informal solution. |
| t97A07 | Resolve the positive-target-dimension convention; the printed nonemptiness claim fails for n=0. |
| t98J04 | Recover the missing knot diagram or exact embedding. |
| t99A05, t99A06 | Resolve compactness/properness conventions before asserting the advertised conclusions. |

The source files were not edited. Their hashes, per-clause mappings and proof
status are recorded in each bundle and the updated
[backlog](statement-construction-backlog-2026-09-10.json). The first tranche's
report is retained as a dated record rather than rewritten as if it had always
contained these five additional statements.

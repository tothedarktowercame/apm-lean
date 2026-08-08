# Proof Outline: b96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

Closer hop 1 compiles nilpotent implies solvable and the converse
counterexample `S₃`. The latter reuses the closed `b97J01` sign-extension and
self-normalizing-transposition-subgroup proofs from git commit `f453ba3`.
The concrete presented group remains open. Contrary to the imported plan,
there is no relation between `b` and `c`: the presentation describes a central
`C₂` factor together with the free product `C₃ * C₇`, rather than the claimed
semidirect product. Closure requires formalizing that presentation conversion
and the nonsolvability of the free product (or constructing a suitable
nonsolvable quotient). Nonnilpotence then follows from nilpotent implies
solvable.

## Closer hop 2 (2026-08-08)

A route around the free-product isomorphism is now concrete. The file defines
an explicit 3-cycle and 7-cycle in `A₇`, checks by computation that killing
`a` and mapping `b,c` to these elements respects every relation, and bundles
the resulting homomorphism `apm_b96j03_toA7` from the frozen presented group.

Closure along this route now requires proving those two permutations generate
`A₇` and proving `A₇` nonsolvable. The latter could be reduced to `A₅` by a
subgroup embedding, but that embedding and the required generation theorem
are not packaged in the searched corpus.

## Closer hop 3 (2026-08-08)

The quotient-range assembly is complete. The images of the presented
generators explicitly contain `b7` and `c7`; consequently their subgroup
closure lies in the homomorphism range, and equality of that closure with
`⊤` immediately gives surjectivity. Direct `native_decide` cannot establish
the equality because `Subgroup.closure` has no computable decidability
instance. The remaining finite route is exactly the concrete generation
equality and nonsolvability of `A₇`.

## Imported Proof Plan

```clojure
{:goal "Clarify how nilpotent and solvable groups are related and determine whether the presented group G=<a,b,c | a^2=b^3=c^7=e, ab=ba, ac=ca> is solvable or nilpotent by supplying the definitions, the hierarchy proofs, the counterexamples, and the group analysis."
 :terms [{:name "lower central series"
          :meaning "Descending sequence gamma_1(G)=G, gamma_{i+1}(G)=[gamma_i(G),G]"
          :needed-because "Nilpotence is defined via this filtration; comparing it with the derived series establishes nilpotent => solvable."}
         {:name "derived series"
          :meaning "G^(0)=G and G^(i+1)=[G^(i),G^(i)]"
          :needed-because "Solvability is phrased using this series, so relating the two series gives the hierarchy and highlights why the converses fail."}
         {:name "semidirect product view of G"
          :meaning "Treat G as (<a,b> isomorphic to C2 x C3) semidirect_phi <c> with phi:<c>->Aut(<b>)"
          :needed-because "Checking how phi acts on the Sylow subgroups decides nilpotence and solvability for the concrete presentation."}]
 :strategy [{:id :s1
             :formal-dependency "Lower central vs derived series inequalities"
             :informal-dependency "Stage 1 definitions of nilpotent/solvable"
             :why-this-now "Prove that every nilpotent group is solvable, giving the main direction demanded in part (b)."
             :lean-target "lemma nilpotent_implies_solvable (G : Type*) [Group G] : IsNilpotent G -> IsSolvable G"
             :mathlib-status "Provided by mathlib (`IsNilpotent.solvable`), so Lean proof is direct."}
            {:id :s2
             :formal-dependency "Explicit small groups (S3, dihedral, Prufer)"
             :informal-dependency "Output of :s1"
             :why-this-now "Supply the required counterexamples (solvable but not nilpotent, Noetherian vs UFD contrasts) and note why each property fails."
             :lean-target "example : IsSolvable (Permutation (Fin 3)) /\\ not IsNilpotent (Permutation (Fin 3))"
             :mathlib-status "Facts about S3 and small abelian groups already exist; Lean work should be routine."}
            {:id :s3
             :formal-dependency "Characterization of finite nilpotent groups as direct products of Sylow subgroups"
             :informal-dependency "Semidirect-product description from the terms"
             :why-this-now "Analyze the given presentation: determine the action of b on c, conclude the group is a solvable semidirect product, and decide whether the Sylow 7-subgroup is central (hence whether the group is nilpotent)."
             :lean-target "theorem presented_group_soluble_not_nilpotent : Solvable G /\\ not IsNilpotent G"
             :mathlib-status "Requires custom arguments (the presentation is not already in mathlib), but relies on standard Sylow theory."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'b96J03'
  :frame-id 'apm-v2-b96J03-1775006849349'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

[Fill in the authoritative reader-facing proof.]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

[Record formal dependency, informal dependency, why-this-now, intended Lean target, and search terms.]

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/b96J03/apm-v2-b96J03-1775006849349/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/b96J03/apm-v2-b96J03-1775006849349/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/B96J03/Apm_v2_b96J03_1775006849349/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/B96J03/Apm_v2_b96J03_1775006849349/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

[Back-port calibrated difficulty and local blockers into the reader-facing proof.]

# Blueprints for topology foundations

Joe, 2026-10-11: "blueprints could follow the audits, when those exist, as
this builds increasing clarity". The order is

1. route audit (`~/notes/closer/audits/<P>.md`, `<P>.edn`): what is missing
   between what exists and the frozen theorem, with Lean types and sizes;
2. blueprint: the mathematics of one foundation the audits named, written
   out so the formalisation has a fixed path;
3. formalisation, one blueprint node per row or program milestone.

A blueprint is written only for a FOUNDATION (a multi-day theorem one or more
audits name). READY and NEAR problems go straight from audit to closure.

## File

`ConstructionTargets/<Foundation>.blueprint.md`, committed with the
foundation's Lean files. It opens with the audits it follows (problem ids and
the audit step names it covers) and the Mathlib API it builds on.

## Nodes

One node per future Lean declaration, numbered `B1`, `B2`, ...:

    ### B3. Path lifting in the quotient covering
    lean: `DeckGroupQuotient.pathLift` : <intended Lean type>
    uses: B1, B2, Mathlib `IsCoveringMap.liftPath`
    status: planned | proved <commit> | revised (see B3')

    Statement, in ordinary mathematics.

    Proof, at the level of detail of one Lean lemma: every case, every
    hypothesis used, and where it is used. Name the Lean representation
    (which quotient, which model of the space, which equivalence) wherever
    a choice exists; most formalisation friction so far was a representation
    choice, not a mathematical one.

A node whose proof needs more than about a page is split. Every hypothesis of
the final theorem must be used by some node; a hypothesis no node uses, or a
use no hypothesis supplies, is a finding. The exception is a hypothesis of a
registered (STATEMENTS.json) theorem that problem.md states: it may go
unused, and the blueprint says so ("unused, mandated by problem.md").
Never STOP a row for it.

## Review

A blueprint is reviewed for its mathematics by a seat other than its author
before any formalisation row cites it: are the statements true as written,
do the proofs use only `uses:` nodes and stated hypotheses, are the Lean types
the statements' faithful forms. A false or unprovable node is FAILed with the
counterexample or the missing hypothesis.

## DAG

Once reviewed, the nodes are entered in the owning ledger's lemma DAG
(`build_step.bb add-lemmas`), one lemma per node, `:depends-on` from `uses:`,
`:area` the foundation's area. A formalisation STOP names the node it is stuck
on; if the node's proof turns out wrong, the blueprint is revised and
re-reviewed before work continues.

# Route triage for registered open topology problems (read-only)

Repo: /home/joe/code/apm-lean. You are an outside reviewer re-planning the dependency DAG that guides
the topology build loops. Do NOT edit, stage or commit anything in the repo. You may write scratch Lean
files under /tmp and compile them with `cd /home/joe/code/apm-lean && lake env lean /tmp/X.lean`
(slow: use sparingly, only to settle a DIRECT/ADAPTER claim).

Background. Each problem has problems/<id>/problem.md (the prelim question) and
problems/<id>/lean/Main.lean, whose `theorem apm_<id lowercase>` statement has been approved by an
outside grader (problems/STATEMENTS.json). The statement is FROZEN: never propose changing it.
The loops build infrastructure in ConstructionTargets/ (≈1600 modules) guided by
TOPOLOGY-DEPENDENCY-DAG.md, which is stale (names only ~31 open problems). An audit
(/home/joe/topo-watch/dag-audit.md, read it first) found: work drifted into long foundation chains
attributed to problems that do not need them, elementary problems were never elected, and nothing
tested whether a row actually reduces a problem's `sorry`. Your route is what the loop will use
instead, so be concrete and honest about size.

For EACH problem in your list (id and comment-stripped sorry count given):
1. Read problem.md and Main.lean. Identify each remaining `sorry` and what it must prove.
2. Search ConstructionTargets/ (rg on names/keywords) and Mathlib for results that already supply
   steps. Name the exact declarations/modules you would reuse.
3. Write the route: the ordered missing steps between what exists and a closed `sorry`, each as a
   one-line theorem statement sketch.
4. Classify:
   - DIRECT: closable now from Mathlib + banked results, roughly ≤ 3 lemmas. Elect a closure probe.
   - ADAPTER: 1–5 bounded missing steps, each a single coherent theorem.
   - FOUNDATION: needs shared infrastructure (name it as a short kebab-case tag, e.g.
     `mayer-vietoris-open-cover`, so shared needs can be grouped across problems).
   - HEAVY: needs a large programme (say which, and a rough size); say whether a lighter route exists.
5. Note any doubt about the statement's truth or provability as frozen (report only; do not fix).

Output: write your results to the file named in your task, as markdown, one section per problem:

```
### <id> — <CLASS> — sorries: N
Needs: <what the sorry(ies) must prove, one line each>
Reuse: <exact banked/Mathlib declarations, or "none found">
Route:
1. <step>
2. ...
Shared tags: <tags or none>
Doubts: <or none>
```

End the file with a table: id | class | #steps | shared tags. Write the file incrementally (append after
each problem) so partial work survives. When finished, reply with the table only.

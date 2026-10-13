# Blueprint: t97J02

## Triage

**Verdict: true and faithful.** The registered theorem exactly formalizes the
requested list of connected compact surface covers of `N₄`: only `N₁₂` in
degree five, and `Σ₇` and `N₁₄` in degree six, including existence witnesses
and universal exclusion clauses.

The usual degenerate failures do not apply: the degrees are fixed positive
numbers 5 and 6, the source in each universal clause is connected and compact,
and exact fibre cardinality is required at every base point. The arithmetic
checks compile: `χ(N₄)=-2`, hence degree five has `χ=-10` and degree six has
`χ=-12`.

The topology-loop STOP report was also checked. It identifies the genuine
missing infrastructure: polygon quotients as surfaces, permutation polygon
covers, their normal forms, finite-cover Euler multiplicativity/orientation
parity, and compact-surface classification. Searches of all sorry-free
`ConstructionTargets` found scaffolding in `Surfaces.lean` and partial
triangulation work in `SurfaceClassification.lean`, but no theorem connecting
those modules to these concrete quotients or proving the required cover and
classification conclusions. Accordingly, the five remaining declarations are
marked **LIBRARY** rather than misleadingly split into small fake lemmas.

## Already proved definitions and arithmetic

The definitions are copied unchanged from `Main.lean`. Continuity and
surjectivity of the quotient map, the candidate Euler-characteristic
calculation, and both general genus equations retain their compiled proofs.

## Library lemmas

### `apm_t97J02_exists_nonorientable_five_cover` — LIBRARY

Construct an exact five-sheeted cover `N₁₂ → N₄` between the concrete polygon
quotients. Use the cyclic permutation representation obtained from the surface
group map `a₁↦1, a₂↦-1, a₃,a₄↦0 (mod 5)`, prove covering charts and fibre
cardinality, and identify the lifted polygon with `Surface false 12`.

- Estimate: 700–2500 lines (program-scale).
- Dependencies: none among blueprint lemmas.
- Truth check: the relator maps to `2(1-1)=0`; the map is surjective; Euler
  characteristic gives `-10`, hence nonorientable genus 12. The kernel contains
  the orientation-reversing generator `a₃`, so the cover is nonorientable.

### `apm_t97J02_exists_orientable_six_cover` — LIBRARY

Construct `Σ₇ → N₄` as a three-sheeted cyclic cover of the orientation double
cover `Σ₃ → N₄`, and verify the composite has six-point fibres.

- Estimate: 1000–2500 lines (program-scale).
- Dependencies: none among blueprint lemmas.
- Truth check: `χ(Σ₃)=2χ(N₄)=-4` and the 3-cover has characteristic `-12`,
  so its orientable genus is 7; fibre degrees multiply to 6.

### `apm_t97J02_exists_nonorientable_six_cover` — LIBRARY

Construct the degree-six cyclic polygon cover `N₁₄ → N₄` by the same
permutation-cover method as the degree-five construction.

- Estimate: 700–2500 lines (program-scale).
- Dependencies: none among blueprint lemmas.
- Truth check: reduction modulo 6 is surjective, `a₃` remains in the kernel
  and reverses orientation, and `χ=-12` gives nonorientable genus 14.

### `apm_t97J02_classify_five_cover` — LIBRARY

Every connected compact 2-manifold giving an exact five-cover of `N₄` is
homeomorphic to `N₁₂`. Apply finite-cover Euler multiplicativity and compact
surface classification; rule out the orientable candidate by orientation
parity for odd-degree covers of a nonorientable surface.

- Estimate: 2000–5000 lines, plus the shared finite-cover foundations.
- Dependencies: none among blueprint lemmas; intended shared program:
  `ConstructionTargets.SurfaceClassification` together with the missing
  finite-cover Euler/orientation program named in the topology worklist.
- Truth check: the only Euler candidates are `Σ₆` and `N₁₂`; an orientable
  connected cover factors through the orientation double cover, so its degree
  is even, excluding `Σ₆` at degree 5.

### `apm_t97J02_classify_six_cover` — LIBRARY

Every connected compact 2-manifold giving an exact six-cover of `N₄` is
homeomorphic to either `Σ₇` or `N₁₄`.

- Estimate: 2000–5000 lines, plus the shared finite-cover foundations.
- Dependencies: none among blueprint lemmas; same shared surface
  classification and finite-cover Euler programs as above.
- Truth check: multiplicativity gives `χ=-12`; compact-surface classification
  then gives precisely orientable genus 7 or nonorientable genus 14. Degree 6
  passes the parity test.

## Dependency layers

- Layer 1 (all parallel): the five LIBRARY lemmas above. Each has a standalone
  statement and none assumes another blueprint lemma's conclusion.
- Layer 2: `apm_t97j02`, a sorry-free tuple assembly from the five results.

The three construction lemmas will likely share a future permutation-polygon
cover program internally, and the two classification lemmas share the surface
classification/Euler program. They remain separate consumer contracts so the
programs can expose degree-specific adapters without making one conclusion a
hypothesis of another.

## Axiom gate

Compiler output:

```text
'apm_t97j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem contains no `sorry`; `sorryAx` enters only through the five
top-level LIBRARY lemmas.

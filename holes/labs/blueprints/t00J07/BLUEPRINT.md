# Blueprint for t00J07

## Triage

Verdict: **true and faithful**. No statement repair is needed.

The source asks for the fundamental group and integral homology after attaching
a disk to `RP²` along an embedded circle, separately for the null and essential
homotopy classes. The Lean statement constructs that literal quotient and gives
exactly the source answers: `π₁ = Z/2`, `H₁ = Z/2` in the null case and trivial
`π₁`, trivial `H₁` in the essential case; in both cases `H₀ = H₂ = Z` and
all higher groups vanish. `Multiplicative (ZMod 1)` and `ModuleCat.of ℤ
(ZMod 1)` are the trivial group and zero module respectively.

Degenerate checks: the domain `Circle` and target `RP²` are nonempty, so there
is no empty-space vacuity. The embedding hypothesis excludes a constant map,
but does not make the null case empty: a small circle bounding a disk in `RP²`
is a null-homotopic embedding. For a null attaching class, the relative long
exact sequence has zero map `Z → Z/2`, giving `H₂ = Z` and `H₁ = Z/2`. For an
essential class it has reduction mod 2, which is surjective with kernel `2Z ≅
Z`, giving `H₂ = Z` and `H₁ = 0`. Van Kampen respectively adds no relation or
kills the generator of `π₁(RP²) = Z/2`. These checks agree with the informal
solution. The topology ledgers and route audit record no counterexample or
statement doubt.

The proved quotient infrastructure from `Main.lean` is retained verbatim:
boundary inclusion and norm, the glue equality, singleton center equivalence
class, and separation of the chosen basepoint from the `RP²` summand.
`ConstructionTargets.DeckGroupQuotientFundamentalGroup` is imported because it
is the existing sorry-free foundation needed for the `RP²` fundamental-group
part of either library computation.

## Remaining lemmas

### `apm_t00J07_bridge_nullhomotopic_attachment_invariants` — LIBRARY

**Statement in words.** For the exact quotient and disk-center basepoint used
by the problem, attaching along a null-homotopic embedded circle gives
fundamental group `Z/2`, integral homology `Z, Z/2, Z` in degrees `0,1,2`, and
zero homology above degree two.

**Why true.** Build an open-cover package in which the punctured attached disk
retracts onto the attaching circle and the other leg retracts onto `RP²`.
Van Kampen says a null attaching loop adds no relation. Mayer–Vietoris (or the
relative homology sequence for one attached 2-cell) has zero connecting map
`Z → Z/2`, yielding the displayed homology. Basepoint transport must end at
`apm_t00j07_basepoint f`; the already proved singleton-center lemma supplies
the necessary point-set separation.

**Expected size.** LIBRARY, approximately 800–1500 lines including the absent
open-cover, van Kampen, and Mayer–Vietoris infrastructure. This intentionally
is not split into pretend 30–150 line lemmas: Mathlib currently lacks the
general attaching-cell computation.

**Dependencies.** The definitions and proved quotient lemmas in this file;
the sorry-free `ConstructionTargets.DeckGroupQuotientFundamentalGroup`;
development of the `RP²` double-cover fundamental group, `RP²` integral
homology, and exact attachment open-cover package.

**Truth check.** Hand computation with the cellular boundary matrix `[2 0]`:
its cokernel is `Z/2` and kernel is the second `Z`. The fundamental-group
presentation remains `⟨a | a²⟩`. A small contractible embedded circle is a
geometric instance.

### `apm_t00J07_bridge_essential_attachment_invariants` — LIBRARY

**Statement in words.** For the same exact quotient, attaching along an
essential embedded circle gives trivial fundamental group, homology `Z, 0, Z`
in degrees `0,1,2`, and zero homology above degree two.

**Why true.** Use the same attachment/open-cover infrastructure. Van Kampen
adds the relation `a = 1` to `⟨a | a²⟩`. In the relative/cellular homology
sequence the new cell maps to the nonzero class in `Z/2`. Equivalently, the
two cellular 2-boundaries form the matrix `[2 1]`; it is surjective and has a
rank-one kernel.

**Expected size.** LIBRARY, approximately 800–1500 lines if developed alone;
most infrastructure should be shared with the preceding contract.

**Dependencies.** The same foundations as the null contract. It does not
depend on the null contract's conclusion, so the two contracts can be assigned
in parallel once their common topology foundation exists.

**Truth check.** The matrix `[2 1] : Z² → Z` has image `Z` and kernel generated
by `(1,-2)`, hence `H₁=0` and `H₂≅Z`. The group presentation
`⟨a | a², a⟩` is trivial. This also agrees with the geometric sphere model.

## Dependency layers

- **Layer 0 (existing/shared foundation):** exact quotient point-set lemmas in
  this file and `ConstructionTargets.DeckGroupQuotientFundamentalGroup`.
- **Layer 1 (foundation programs):** `RP²` double-cover/`π₁`, `RP²` integral
  homology, and the disk-attachment open-cover package. These are the stopped
  topology-loop obligations; the audit specifically identifies the missing
  positive-hemisphere two-sheet trivialization on the `RP²` route.
- **Layer 2 (parallel LIBRARY contracts):** the null and essential bridge
  theorems above, each stated independently with the common definitions.
- **Layer 3 (already proved):** `apm_t00j07` pairs the two implications and has
  no direct `sorry`.

## Confidence and remaining doubt

There is no mathematical doubt about either contract. The risk is engineering
scope: neither Mathlib nor the current sorry-free construction targets contain
the required general van Kampen/cellular-attachment bridge. The route audit
estimates its general van Kampen component alone at 500–900 lines. These two
admitted declarations therefore mark genuine library-program boundaries, not
ordinary lemma-seat work.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00J07/Blueprint.lean
```

The final output of `#print axioms apm_t00j07` was:

```text
'apm_t00j07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only two `sorry` warnings are the two Layer 2 LIBRARY contracts. The main
theorem contains no `sorry`.

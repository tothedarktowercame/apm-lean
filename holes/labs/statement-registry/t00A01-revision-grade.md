# t00A01: grade of the proposed revision (RevisedMain.lean)

Read-only fidelity grade. Sources: `problems/t00A01/problem.md`,
`problems/t00A01/lean/Main.lean` (registered), `holes/labs/blueprints/t00A01/RevisedMain.lean`
(proposed), `holes/labs/blueprints/t00A01/BLUEPRINT.md` and `Blueprint.lean` (rationale and lemma layer).
No build was run.

| id | statement | grade | one-line reason | change classification |
|---|---|---|---|---|
| t00A01 | registered `Main.lean` | stronger (not shown false) | It quantifies over all topological embeddings `φᵢ`, wild ones included, which drops problem.md's "you may assume φᵢ(D³) is a 3-simplex". No counterexample is known or given, and the classical wild case (Bing 1952) satisfies the conclusion. | n/a |
| t00A01 | proposed `RevisedMain.lean` | faithful | `HasBallCollar` is a genuine tameness (bicollar) condition that a 3-simplex in a triangulated 3-manifold satisfies. It gives no π₁ or homology information, and all of the van Kampen, Mayer-Vietoris and puncture work stays in the proof. | improvement (narrows an over-strong statement exactly to problem.md's scope; not a correction) |

## Evidence

### 1. Is the registered statement false or unfaithful because of wild balls?

It is **not shown false**. It is **stronger than asked**, so "unfaithful" in BLUEPRINT.md's triage overstates the case.

Registered hypotheses on the balls (Main.lean):

```lean
(φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
(hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
```

The conclusion concerns only `X = A ∪_{S²} B`, the quotient of the two punctured pieces
`Mᵢ \ φᵢ(int D³)` (`apm_t00A01_punctured`). Wildness does break the *intermediate* facts used by the
standard proof. For an Alexander horned ball, the complementary piece is not a manifold with
boundary, the sphere has no collar on that side, and the open wild side has a non-finitely-generated
π₁. So the puncture lemmas ("π₁ of the punctured piece = π₁(M)", the open cover with an `S²` overlap)
fail or are unavailable. BLUEPRINT.md's argument stops at those intermediate facts. It does not show
that the *conclusion* fails:

- **Only one ball wild:** say φ₂ is standard. The punctured piece B is then a tame closed ball whose boundary
  parametrisation is φ₂|S². By the Alexander trick the map X → M₁ (identity on A, φ₁∘ρ on B) is a
  continuous bijection from a compact space to a Hausdorff space. So X ≅ M₁ and the conclusion holds
  (π₁(M₁) * 1, homology sphere).
- **Both balls horned, M₁ = M₂ = S³, φ₁ = φ₂:** X is the sum of two solid Alexander horned spheres
  glued by the identity. Bing (Ann. of Math. 1952) proved this is homeomorphic to S³, so the conclusion holds.
- For arbitrary pairs of wild balls I know no counterexample and no proof. The repo has no `Refute.lean`
  for t00A01, and BLUEPRINT.md says none is feasible. The truth of the registered statement is therefore
  open as far as this audit can tell. It is certainly outside what the prelim asks for and outside
  the informal proof's reach.

So the registered statement is a *strengthening*. problem.md permits the simplex (tame) assumption, and
Main.lean removes it. That makes it a poor target, possibly unprovable by any prelim-level argument,
but it is not refuted. ("Triangulated" vs `IsManifold … ∞` is a legitimate encoding choice in
dimension 3 (Moise), so it is not part of the issue.)

### 2. Grade of the revised statement

The only change to `theorem apm_t00a01` is two added hypotheses. Every original hypothesis and the
full conclusion are kept, as the diff confirms.

```lean
(hcollar₁ : apm_t00A01_HasBallCollar φ₁)
(hcollar₂ : apm_t00A01_HasBallCollar φ₂) :
```

with

```lean
def apm_t00A01_HasBallCollar {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) : Prop :=
  ∃ Φ : apm_t00A01_LargeDisk3 → M,
    Topology.IsEmbedding Φ ∧
    Φ ∘ apm_t00A01_unitToLarge = φ ∧
    IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})
```

- **Genuine tameness condition.** It says φ extends to an embedding of the radius-2 ball, which means
  φ(∂D³) is bicollared. By Brown's generalized Schoenflies theorem this is exactly tameness of the ball.
  The `IsOpen` clause already follows from invariance of domain, so it is redundant but harmless.
- **Satisfied by the problem's simplex.** Suppose φ(D³) = σ is a 3-simplex of a triangulation of a closed
  3-manifold. Every triangulation is combinatorial in dimension 3. ∂σ is then a PL, hence locally flat,
  2-sphere, or equivalently σ lies in the interior of its second-derived regular neighbourhood
  N ≅ D³ with N \ int σ ≅ S² × [0,1]. Define Φ(r·s) = c(φ(s), r−1) for 1 ≤ r ≤ 2, where c is that
  outer collar. This Φ satisfies all three clauses for *any* homeomorphism φ onto σ. Conversely, every
  collared ball is tame, so by Moise it is a simplex of some triangulation up to ambient homeomorphism.
  The hypothesis therefore picks out exactly the class problem.md allows.
- **Does not carry the core.** `HasBallCollar` says nothing about π₁, homology, connectedness of the
  punctured piece, or the quotient cover. Those remain four separate `sorry` LIBRARY lemmas in
  `Blueprint.lean`: `apm_t00A01_punctured_pathConnected`, `…_punctured_fundamentalGroup` (van Kampen with
  an `S²` overlap), `…_punctured_isHomologyBall` (the pair long exact sequence plus the
  fundamental-class/local-generator comparison, which is where hM is actually used), and
  `…_collared_standardCover`. All four take `hcollar` as input and derive their conclusions, and none
  is a hypothesis of the main theorem. This is the opposite of `apm_t00a01_previous_encoding`, which
  assumed `hA`, `hB`, `hπA`, `hπB` and was rightly marked as superseded.
- **Not vacuous.** For example, take M = S³ (a smooth manifold in Mathlib and a homology sphere) and
  let Φ be a chart inverse on a small round ball. All hypotheses hold, and the conclusion is non-trivial.

Grade: **faithful**. The Lean encoding of "you may assume φᵢ(D³) is a simplex" is reasonable.

### 3. Classification

**Improvement.** In the rubric's sense it is a narrowing of the *registered* statement, since it says
less than Main.lean. But it narrows only the part where Main.lean claimed more than problem.md, and it
lands exactly on the prelim's scope. It is not a **correction**, because Main.lean is not shown false
(see 1). It is not a **narrowing** relative to problem.md, because nothing the prelim asks is lost.

### Housekeeping (not affecting the grade)

- The module comment just before `theorem apm_t00a01` in RevisedMain.lean is stale. It says "the repair
  exposes exactly the three standard puncture consequences used by the informal proof for each piece,
  together with the standard two-piece cover". That describes the earlier circular repair, not
  `HasBallCollar`, and it should be rewritten before registration. Main.lean's header "Encoding
  questions" paragraph has the same staleness ("The presentation hypotheses expose ... homology ball
  ... fundamental group").
- BLUEPRINT.md's triage verdict "unfaithful" should read "stronger than asked (wild embeddings allowed);
  not refuted". Its claim that "complements need not have the fundamental group or collar" is true of
  the punctured pieces but does not show that the theorem's conclusion fails.

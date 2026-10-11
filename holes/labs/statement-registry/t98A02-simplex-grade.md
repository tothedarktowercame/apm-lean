# t98A02 re-grade (simplex assumption restored)

Record check: commit `1c4f0bc21` (`git diff HEAD~1 -- problems/t98A02/lean/Main.lean`) adds the header section "The source's simplex assumption", the definitions `T98A02CollarBall` and `t98A02DiskInCollarBall`, and four premises in `apm_t98a02`: the two `∃ ψᵢ` collar clauses and the two `IsZero (t98A02H k Xᵢ)` clauses for `k ≥ 5`. The conclusion, the quotient construction and the remaining premises are unchanged. I did not build. Read-only, apart from this file.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t98A02 | faithful | `apm_t98a02` (lowercase a) | Both new premises are consequences of "φᵢ(D⁴) is a 4-simplex of a triangulation of the closed manifold Xᵢ", for every parametrisation φᵢ. So no source instance is lost. The Lean domain still admits collared balls that are not literally simplices, but these are true instances and, up to homeomorphism, the same configurations as the source's. Wild balls, which made the old grade `stronger`, are now excluded. Hypotheses are consistent (S⁴), not vacuous; conclusion unchanged and true | yes, mild (unchanged): "closed" omitted by the source; the compactness repair is forced |

## Evidence notes

### Collar premise: implied by the source, for every φᵢ
- **Triangulations in dimension 4 are combinatorial.** Links of simplices of dimension ≥ 1 are combinatorial spheres of dimension ≤ 2. So a vertex link L is a closed 3-manifold. The cone on L is a neighbourhood of the vertex, so L is a homotopy 3-sphere and therefore S³ (Perelman). The header compresses this to "vertex links are simply connected 3-manifolds, hence S³". That is the standard argument, and the prior grade relied on it too.
- **The top simplex σ has an exterior collar.** In the first derived subdivision K′, the closed star of the barycentre b̂ of σ is σ itself, because σ is top-dimensional. So σ is a derived (regular) neighbourhood of b̂. Let N be a regular neighbourhood of σ. Then N is also a regular neighbourhood of b̂ with σ ⊂ int N. By the collar theorem for nested regular neighbourhoods (Rourke–Sanderson, ch. 3), N ∖ int σ ≅ ∂σ × [0,1] (PL), with ∂σ × {0} = ∂σ. Write c : ∂σ × [0,1] → X for this collar. The header's "bicollared by its PL regular neighbourhood" is correct.
- **Radial extension works for every parametrisation.** Let φ : D⁴ → σ be any homeomorphism. Set ψ(v) = φ(v) for ‖v‖ ≤ 1, and ψ(v) = c(φ(v/‖v‖), ‖v‖ − 1) for 1 ≤ ‖v‖ ≤ 2.
  - The two pieces agree on ‖v‖ = 1 because c(x,0) = x.
  - ψ is injective, because c meets σ only in ∂σ × {0}.
  - The closed radius-2 ball is compact and Xᵢ is T2, so ψ is an embedding.

  So the `∃ ψᵢ` clause holds. The header's claim is correct.

### Dimension premise: implied, and redundant
- Hₖ(Xᵢ; ℤ) = 0 for k ≥ 5 holds for every triangulated compact 4-manifold, by simplicial = singular homology. In fact it holds for every 4-manifold, compact or not (Hatcher Prop. 3.29). The premise is therefore true in all intended instances. It only spares the prover a fact that Mathlib lacks; it cannot exclude anything.

### Lean well-formedness and match with the docstring
- `T98A02CollarBall := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 2`.
- `t98A02DiskInCollarBall u := ⟨u, closedBall_subset_closedBall (by norm_num) u.property⟩` is the inclusion of the unit ball. `norm_num` discharges `(1:ℝ) ≤ 2`.
- `∃ ψ, IsEmbedding ψ ∧ ∀ u, ψ (incl u) = φ u` says exactly "φ extends to a topological embedding of the radius-2 ball". Injectivity of ψ forces ψ(1 ≤ ‖v‖ ≤ 2) to meet φ(D⁴) only in φ(S³), so this is an exterior collar of φ(∂D⁴), as the docstring says.
- `∀ k : ℕ, 5 ≤ k → Limits.IsZero (t98A02H k Xᵢ)`, in `ModuleCat ℤ`, is "Hₖ = 0 for k ≥ 5". It matches.
- No new binder captures or shadows anything. The premises are well-typed as read.

### Not vacuous, not false, not weaker
- **Consistency.** Take X₁ = X₂ = S⁴ = the unit sphere in ℝ⁵. Mathlib has its charted-space and smooth-manifold instances modelled on `EuclideanSpace ℝ (Fin 4)`, and it is compact, T2 and path-connected. Let ψ = inverse stereographic projection restricted to the closed radius-2 ball, and φ = ψ ∘ incl.
  - ψ is a continuous injection from a compact space into a T2 space, hence an embedding.
  - H₄(S⁴) ≅ ℤ and Hₖ(S⁴) = 0 for k ≥ 5.

  So all premises are satisfiable, and Y ≅ S⁴.
- **Not weaker.** Every source instance yields a Lean instance:
  - A triangulated 4-manifold is PL, and PL = smooth in dimension 4 (π_k(PL/O) = 0 for k ≤ 6), so it carries some `IsManifold ⊤` structure. The topological φᵢ is untouched.
  - "Oriented" and "closed" are carried by compactness plus H₄ ≅ ℤ, as before.
  - The two new premises hold by the notes above.
- **Not false.** The previous grade showed that the conclusion holds for arbitrary, even wild, embeddings via Borsuk ANR facts and Mayer–Vietoris. Adding premises cannot make it false. With the collar, the ordinary open-cover Mayer–Vietoris argument (collars overlapping in S³ × (−ε, ε)) proves it directly.
- **Why `faithful` and not `stronger`.** The Lean domain still contains collared balls in smooth Xᵢ that are not literally simplices of a given triangulation. In dimension 4, any two collared (locally flat) 4-balls in a connected manifold are ambiently homeomorphic (annulus theorem, Quinn 1982). So each such instance is homeomorphic to a source instance, and the homology statement is invariant under that homeomorphism. The extra generality is presentational, not mathematical. The genuinely extra wild-ball cases, which the earlier `stronger` grade rested on, are now excluded.

### Defects
- None in the revision.
- Nit: the k ≥ 5 premise is redundant, being true for all 4-manifolds. It is harmless. The header could say "a consequence that Mathlib cannot yet derive" rather than present it as a special consequence of triangulability.
- The PRELIM-DEFECT is unchanged: "closed" is omitted by the source, and the compactness repair is forced and stated in the header.

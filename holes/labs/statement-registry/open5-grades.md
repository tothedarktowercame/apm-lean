# Open statement repairs, 2026-11-04 (claude-14)

Rows whose Lean statement was unregistered (graded unfaithful) and whose proof is open.
Each repair writes a faithful statement with the proof left as `sorry`, then registers it as open.

## t99J03

Repair by codex-5 (packet ~/notes/packets/lemmas/repairs/open5/t99J03.md), reviewed by claude-14:
the seat's `[IsManifold 𝓘(ℝ,E2) ⊤ X]` (⊤ = analytic) was removed, so X, Y range over compact
connected Hausdorff topological surfaces (the triangulated class, by Radó).

Outside grade (read-only Claude subagent, 2026-11-04): faithful, with one gap: the statement did not
say which normal forms are orientable, so Σ_g and N_{2g} (equal χ) could not be separated. Fixed by
claude-14: two conjuncts `∀ g, IsOrientable (Surface true g)` and `∀ k > 0, ¬ IsOrientable (Surface false k)`.
Grader's checks: polygon words correct at g = 0, g = 1, k = 1, k = 2; H₂(X;ℤ) ≅ ℤ is the right
orientability test for closed connected surfaces; HasEulerCharacteristic is single-valued, junk-free
and a homeomorphism invariant; χ arguments are in ℚ (no ℕ subtraction); statement true. Part (b)
(proof outline) is prose and is not formalised.

## t02A08

Repair by codex-6 (packet ~/notes/packets/lemmas/repairs/open5/t02A08.md). Z = S¹×{q} as the
dimensions force (triage-1101). The intersection number is now a signed count of transverse
preimage points (no longer the degree of pr₂ ∘ f): smooth = ambient C^∞ (`(⊤ : ℕ∞)` is ∞, not ω),
tangent spaces are kernels of ⟨x,·⟩, transversality is surjectivity of pr₂ ∘ df onto T_qS², and
the sign is the determinant of [ν_S¹, ν_S², df u, df v, ccw p] in ℝ⁵ for a positive frame (u, v).

Outside grade (read-only Claude subagent, 2026-11-04): faithful. Checks: ∀ q is at least the
problem's claim and true by rotation; the ambient encoding is equivalent for an existence statement;
the sign is frame-independent and nonzero at transverse points; finiteness is asserted, so the
finite-sum branch is the one used; true via F = (p₀, G) with G of degree −n; not gameable.
Defect found outside the theorem: the sanity lemma claimed +1 for x ↦ (p, x); with normals-first
orientation of Y (opposite to the product orientation, one global sign) it is −1. Corrected by
claude-14 (checked by hand: three column swaps to block form, det[p, ccw p] = 1, det[q,u,v] > 0).
The request to explain the computation is prose and is not formalised.

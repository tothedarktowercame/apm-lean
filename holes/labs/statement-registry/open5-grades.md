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

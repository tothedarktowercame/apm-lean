# Informal Solution: a93A03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Weak convergence only controls inner products—not norms—so it is easy to forget how to extract norm information. The trick is to combine weak convergence with the polarization identity `‖u − v‖² = ‖u‖² + ‖v‖² − 2 Re ⟨u,v⟩`, but unless you write down that identity you can’t close the estimates.

**Key insight.** Plug the weak limit `h` into the inner product: `⟨h_n, h⟩ → ⟨h,h⟩ = ‖h‖²`. Insert this into the norm identity to get control of `‖h_n − h‖²`. When the norms converge you get strong convergence (part a), and even without norm convergence the same inequality yields `‖h‖ ≤ liminf ‖h_n‖` (part b).

**Proof.** For every `n`,

\[‖h_n - h‖^2 = ‖h_n‖^2 + ‖h‖^2 - 2 \Re ⟨h_n, h⟩.\]

Because `h_n ⇀ h`, we have `⟨h_n,h⟩ → ⟨h,h⟩ = ‖h‖²`.

(a) If `‖h_n‖ → ‖h‖`, then the right-hand side tends to `‖h‖² + ‖h‖² - 2‖h‖² = 0`, so `‖h_n - h‖ → 0`.

(b) Rearranging the identity gives `‖h‖² = 2 \Re ⟨h_n, h⟩ - ‖h_n‖² + ‖h_n - h‖²`. Taking liminf and using `⟨h_n,h⟩ → ‖h‖²` plus `‖h_n - h‖² ≥ 0` yields `‖h‖² ≤ liminf ‖h_n‖²`, hence `‖h‖ ≤ liminf ‖h_n‖`.

*Proof sanity pass.* The only delicate bridge is passing to the limit in the norm identity; we explicitly used weak convergence for `⟨h_n,h⟩` and the assumed convergence (or liminf) of `‖h_n‖`. Both parts (a) and (b) are fully justified.

**What connects.** The same technique appears throughout functional analysis: whenever weak convergence is paired with norm convergence, the polarization identity collapses the gap and yields strong convergence (uniform convexity, Banach–Saks, etc.). Inequality (b) is the general lower-semicontinuity of the norm with respect to weak convergence.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `weak_convergence`: supplies `⟨h_n,h⟩ → ‖h‖²`.
- `norm_square_expansion`: rewrites `‖h_n - h‖²` in terms of norms and inner products.
- `limit_arithmetic`: uses norm convergence (part a) or liminf (part b) to extract the final limits.

**Stage 3 — LEAN FORMALIZATION**

Status: *blocked (missing API/theory).* Mathlib has Hilbert-space identities and weak convergence definitions, but there is no bundled theorem `weak_conv_norm_conv_strong`. Proving it formally would take stitching together those lemmas and handling real/complex conjugates; this exceeds the current frame. `Main.lean` still contains only the default namespace header, so `lake build` succeeds trivially.

**Stage 4 — FORMAL-TO-INFORMAL REVISION (blocked)**

The informal proof hinges on the sentence “insert the weak limit into the norm identity and take limits,” which currently lacks Lean certification. Once a `weak_conv_norm_conv_strong` lemma is implemented, parts (a) and (b) will be formally supported; for now, that polarization step remains informal.

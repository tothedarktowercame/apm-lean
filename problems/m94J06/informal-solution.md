<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94J06: Fréchet differentiability of operator inversion T ↦ T⁻¹

## Why It's Hard

This is the operator-valued, infinite-dimensional generalization of the scalar fact
`\frac{d}{dx}\,x^{-1} = -x^{-2}`, and two things make it genuinely harder than its scalar shadow.
First, the domain `GL(X)` is a subset of the *infinite-dimensional* Banach space `B(X)`, and before
one can even speak of a Fréchet derivative one must know `GL(X)` is **open** — that a small
perturbation of an invertible operator stays invertible. Second, `B(X)` is **noncommutative**, so the
naive guess `-T^{-2}H` is wrong; the correct derivative must keep `H` *sandwiched* between two copies
of `T^{-1}` as `-T^{-1}HT^{-1}`, and you only see this by expanding `(T+H)^{-1}` carefully.

The crux is to get a usable formula for `(T+H)^{-1}` and to control the *entire* tail of its
expansion uniformly. A first-order Taylor guess is easy; proving the remainder is genuinely
`o(\|H\|)` requires summing an operator geometric series and bounding it in operator norm.

## The Key Insight

Factor `T + H = T(I + T^{-1}H)`. For `\|H\|` small, `\|T^{-1}H\| \le \|T^{-1}\|\,\|H\| < 1`, so
`I + T^{-1}H` is invertible by the **Neumann series**, and

$$(T+H)^{-1} = (I + T^{-1}H)^{-1}T^{-1} = \sum_{k=0}^\infty (-T^{-1}H)^k\, T^{-1}
= T^{-1} - T^{-1}H\,T^{-1} + \underbrace{\sum_{k\ge 2}(-T^{-1}H)^k T^{-1}}_{\text{remainder}}.$$

The single Neumann expansion does everything at once: its `k=0` term is `F(T) = T^{-1}`; its `k=1`
term is the linear map `H \mapsto -T^{-1}HT^{-1}` (the derivative); and its `k\ge 2` tail is a
geometric series of size `O(\|H\|^2)`, hence `o(\|H\|)`. The noncommutativity is encoded exactly in
the order `T^{-1}\,H\,T^{-1}` — `H` is flanked, not squared.

## Complete Proof

Let `X` be a Banach space, `B(X)` the bounded operators with the operator norm, and
`GL(X) = \{T \in B(X) : T \text{ has a bounded inverse}\}`. Define `F(T) = T^{-1}`.

**Step 1 — `GL(X)` is open.** Let `T \in GL(X)` and let `H \in B(X)` with `\|H\| < 1/\|T^{-1}\|`. Then
`\|T^{-1}H\| \le \|T^{-1}\|\,\|H\| < 1`, so `I + T^{-1}H` is invertible with inverse given by the
convergent Neumann series `\sum_{k\ge 0}(-T^{-1}H)^k` (it converges in operator norm because
`B(X)` is a Banach algebra and `\sum \|T^{-1}H\|^k < \infty`). Hence

$$T + H = T\,(I + T^{-1}H)$$

is a product of invertibles, so `T+H \in GL(X)` with `(T+H)^{-1} = (I+T^{-1}H)^{-1}T^{-1}`. Thus the
open ball of radius `1/\|T^{-1}\|` about `T` lies in `GL(X)`, and `GL(X)` is open — so Fréchet
differentiability is meaningful there.

**Step 2 — The candidate derivative.** Define `\Lambda_T : B(X) \to B(X)` by
`\Lambda_T(H) = -T^{-1}H\,T^{-1}`. It is linear in `H` and bounded:

$$\|\Lambda_T(H)\| = \|T^{-1}H\,T^{-1}\| \le \|T^{-1}\|^2\,\|H\|,$$

so `\Lambda_T \in B(B(X))` with `\|\Lambda_T\| \le \|T^{-1}\|^2`.

**Step 3 — Expand and identify the remainder.** For `\|H\| < 1/\|T^{-1}\|`, using the Neumann series
from Step 1,

$$(T+H)^{-1} = \sum_{k=0}^\infty (-T^{-1}H)^k\,T^{-1}
= T^{-1} - T^{-1}H\,T^{-1} + \sum_{k=2}^\infty (-T^{-1}H)^k\,T^{-1}.$$

Therefore the Fréchet remainder is

$$R(H) := F(T+H) - F(T) - \Lambda_T(H)
= (T+H)^{-1} - T^{-1} + T^{-1}H\,T^{-1} = \sum_{k=2}^\infty (-T^{-1}H)^k\,T^{-1}.$$

**Step 4 — Bound the remainder.** Set `q := \|T^{-1}H\| \le \|T^{-1}\|\,\|H\| < 1`. Summing the
geometric tail,

$$\|R(H)\| \le \sum_{k=2}^\infty \|T^{-1}H\|^k\,\|T^{-1}\|
= \|T^{-1}\|\,\frac{q^2}{1 - q}
\le \frac{\|T^{-1}\|^3\,\|H\|^2}{1 - \|T^{-1}\|\,\|H\|}.$$

Hence

$$\frac{\|R(H)\|}{\|H\|} \le \frac{\|T^{-1}\|^3\,\|H\|}{1 - \|T^{-1}\|\,\|H\|}
\xrightarrow[\ \|H\| \to 0\ ]{} 0.$$

**Conclusion.** The remainder is `o(\|H\|)`, so `F` is Fréchet differentiable at every `T \in GL(X)`,
with derivative

$$\boxed{\ DF(T)\,H = -\,T^{-1}\,H\,T^{-1}, \qquad \|DF(T)\| \le \|T^{-1}\|^2.\ }$$

Since `T \in GL(X)` was arbitrary, `F` is Fréchet differentiable on all of `GL(X)`. ∎

**Remarks.** (i) This is the exact operator analogue of `\frac{d}{dx}x^{-1} = -x^{-2}`: in the
commutative scalar case `-T^{-1}HT^{-1} = -T^{-2}H`, but in `B(X)` the two inverses must flank `H`.
(ii) The map `T \mapsto DF(T)` is itself continuous (indeed `F` is `C^\infty`): each higher derivative
is read off from the next term of the same Neumann expansion, e.g. the second derivative is the
symmetric bilinear map `(H,K) \mapsto T^{-1}H T^{-1} K T^{-1} + T^{-1}K T^{-1} H T^{-1}`. (iii) The
single tool — the Neumann series — simultaneously proves the domain is open, produces the derivative,
and quantifies the error, which is why it is the natural engine for this problem.

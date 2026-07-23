<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J04: No continuous surjection from ℝ×ℚ onto the irrationals

## Why It's Hard

The statement is a non-existence claim about *all* continuous maps, so one needs a property preserved by
continuity that the domain has and the target cannot accommodate. The two spaces look superficially similar
in size (both have cardinality continuum), so a naive cardinality argument fails. The right invariant is
**connectivity structure**: the domain `\mathbb R \times \mathbb Q` decomposes into *countably many* connected
pieces (the horizontal lines `\mathbb R \times \{q\}`, because `\mathbb Q` is totally disconnected), while the
target `\mathbb R \setminus \mathbb Q` is *totally disconnected* (between any two irrationals sits a rational
that disconnects them). A continuous map must send each connected piece to a connected subset of the target —
which can only be a single point — so the whole image is a *countable* set. The clash is then countable image
vs. **uncountable** target. The difficulty is spotting that "count the connected components" is the lever, not
raw cardinality.

## The Key Insight

- `\mathbb R \times \mathbb Q` has connected components exactly `\mathbb R \times \{q\}`, `q \in \mathbb Q` —
  **countably many** — since `\mathbb Q` is totally disconnected.
- `\mathbb R \setminus \mathbb Q` is **totally disconnected**: its connected subsets are single points.
- A continuous `f` sends each component `\mathbb R \times \{q\}` to a connected subset of `\mathbb R \setminus \mathbb Q`,
  hence to a **single point**. So `f(\mathbb R \times \mathbb Q)` is a union of countably many points —
  **countable**.
- But `\mathbb R \setminus \mathbb Q` is **uncountable**, so `f` cannot be onto.

## Complete Proof

Suppose, for contradiction, that `f : \mathbb R \times \mathbb Q \to \mathbb R \setminus \mathbb Q` is a
continuous surjection.

**Step 1 — The components of `\mathbb R \times \mathbb Q` are the lines `\mathbb R \times \{q\}`.** Let
`C \subseteq \mathbb R \times \mathbb Q` be connected. The projection `\pi_2 : \mathbb R \times \mathbb Q \to \mathbb Q`
is continuous, so `\pi_2(C)` is a connected subset of `\mathbb Q`. But `\mathbb Q` is **totally disconnected**
(any subset with two points `q < q'` is split by an irrational `r \in (q,q')`), so `\pi_2(C)` is a single
point `\{q\}`; thus `C \subseteq \mathbb R \times \{q\}`. Conversely each `\mathbb R \times \{q\} \cong \mathbb R`
is connected. Hence the connected components are exactly `\{\mathbb R \times \{q\} : q \in \mathbb Q\}`, and
since `\mathbb Q` is **countable**, there are countably many of them.

**Step 2 — `\mathbb R \setminus \mathbb Q` is totally disconnected.** Let `S \subseteq \mathbb R \setminus \mathbb Q`
contain two points `a < b`. By density of `\mathbb Q`, pick a rational `r \in (a,b)`; then `r \notin S` (as `r`
is rational), and `S = \big(S \cap (-\infty, r)\big) \cup \big(S \cap (r, \infty)\big)` is a separation of `S`
into two nonempty relatively open pieces (`a` in the first, `b` in the second). So `S` is disconnected. Hence
the only connected subsets of `\mathbb R \setminus \mathbb Q` are singletons (and `\varnothing`).

**Step 3 — `f` is constant on each component.** For each `q`, the image `f(\mathbb R \times \{q\})` is the
continuous image of the connected set `\mathbb R \times \{q\}`, hence connected (continuous images of
connected sets are connected). By Step 2 it is a single point, say `y_q \in \mathbb R \setminus \mathbb Q`.

**Step 4 — The image is countable, but the target is uncountable.** Therefore

$$f(\mathbb R \times \mathbb Q) = \bigcup_{q \in \mathbb Q} f(\mathbb R \times \{q\}) = \{\, y_q : q \in \mathbb Q \,\},$$

a set indexed by the countable `\mathbb Q`, hence **countable**. But `\mathbb R \setminus \mathbb Q` is
**uncountable** (its complement `\mathbb Q` is countable, while `\mathbb R` is uncountable). A countable set
cannot equal an uncountable one, so `f` is **not** surjective — contradicting the assumption.

$$\boxed{\ \text{There is no continuous surjection } \mathbb R \times \mathbb Q \to \mathbb R \setminus \mathbb Q.\ }\qquad\blacksquare$$

**Remark.** The obstruction is the *number of connected components* of the domain versus the *total
disconnectedness* of the target. `\mathbb R \times \mathbb Q` looks `2`-dimensional, but the `\mathbb Q`-factor
shatters it into countably many lines, each of which a continuous map must crush to a point inside the
spaceless (totally disconnected) irrationals. So any continuous image is countable, far too small for the
uncountable target — even though both spaces have cardinality continuum as *sets*. The same argument rules out
continuous surjections from any space with countably many components onto any uncountable totally disconnected
space.

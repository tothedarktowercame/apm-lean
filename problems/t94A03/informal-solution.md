<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A03: The real line is not a countable union of Cantor sets (Baire category)

## Why It's Hard

The statement forbids covering all of `\mathbb R` by countably many Cantor sets, and the difficulty is
choosing the *right* smallness notion to make the obstruction bite. The tempting first idea — measure — does
**not** work directly: while the standard middle-thirds Cantor set has measure zero, there exist "fat"
Cantor sets of *positive* measure, so a countable union of Cantor sets could in principle have infinite
measure (indeed `\mathbb R = \bigcup_n [n, n+1]` shows countable unions of positive-measure sets can be
everything). So measure cannot be the invariant.

The correct notion is **topological smallness**: every Cantor set, fat or thin, is **nowhere dense** — it is
compact and totally disconnected, so it contains no interval and has empty interior. The Baire Category
Theorem then says a complete metric space cannot be a countable union of nowhere-dense sets. Recognizing
that "Cantor set" forces nowhere-density (not measure-zero) and that Baire category is the operative tool is
the whole insight.

## The Key Insight

A Cantor set `C \subseteq \mathbb R` (a homeomorph of the standard Cantor set — compact, perfect, totally
disconnected) is **nowhere dense**: it is compact hence closed, and totally disconnected hence contains no
interval, so it has empty interior. If `\mathbb R = \bigcup_n C_n` with each `C_n` a Cantor set, then
`\mathbb R` is a countable union of nowhere-dense sets — i.e. **meager** (first category) in itself. But
`\mathbb R` is a complete metric space, so by the **Baire Category Theorem** it is *not* meager in itself
(it is of second category). Contradiction. Hence no such covering exists.

## Complete Proof

Recall a **Cantor set** in `\mathbb R` is a subset homeomorphic to the standard middle-thirds Cantor set;
equivalently, a nonempty compact, perfect, totally disconnected subset. The only property we need is:

**Lemma — every Cantor set is nowhere dense.** Let `C \subseteq \mathbb R` be a Cantor set.
- `C` is **closed**: it is compact (homeomorphic to the compact standard Cantor set), and compact subsets of
  the Hausdorff space `\mathbb R` are closed.
- `C` has **empty interior**: `C` is totally disconnected, so it contains no nonempty interval (an interval
  is connected). Since every nonempty open subset of `\mathbb R` contains an interval, `C` contains no
  nonempty open set, i.e. `\operatorname{int} C = \varnothing`.

A closed set with empty interior is nowhere dense (`\overline C = C` has empty interior). So `C` is nowhere
dense. ∎ (Lemma)

**Main argument.** Suppose, for contradiction, that

$$\mathbb R = \bigcup_{n=1}^\infty C_n$$

with each `C_n` a Cantor set. By the Lemma each `C_n` is nowhere dense, so `\mathbb R` is a **countable union
of nowhere-dense sets**, i.e. `\mathbb R` is meager (of first category) in itself.

However, `\mathbb R` with its usual metric is a **complete** metric space, hence a **Baire space**: by the
**Baire Category Theorem**, a complete metric space is not the union of countably many nowhere-dense sets
(equivalently, it is of second category in itself; equivalently, a countable intersection of dense open sets
is dense, so the complement — a countable union of nowhere-dense sets — cannot be everything). This
contradicts `\mathbb R` being meager in itself.

Therefore no such countable family of Cantor sets covers `\mathbb R`:

$$\boxed{\ \mathbb R \text{ is not a countable union of Cantor sets.}\ }\qquad\blacksquare$$

**Remark.** The proof hinges on using the *right* notion of smallness. Cantor sets are **nowhere dense**
regardless of their measure, so **Baire category** — not Lebesgue measure — is the correct tool; a measure
argument fails because fat Cantor sets have positive measure. The same Baire argument shows `\mathbb R` is not
a countable union of *any* closed nowhere-dense sets (e.g. not a countable union of single points — `\mathbb R`
is uncountable — nor of nowhere-dense compact sets generally). The essential point is that completeness makes
`\mathbb R` "topologically large": it cannot be exhausted by countably many sets each of which is full of
holes.

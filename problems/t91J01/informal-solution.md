<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91J01: No continuous surjection C ↠ irrationals (compactness), but a continuous injection exists

## Why It's Hard

The two parts have *opposite* answers, and the trap is to assume they go the same way. The discriminating
fact is a single topological obstruction — **compactness** — which blocks the surjection but says nothing
about injections:

- **(a)** The Cantor set `C` is compact, so any continuous image `f(C)` is compact. The irrationals
  `X = (0,1)\setminus\mathbb Q` are **not** compact (not closed in `\mathbb R`: rational limit points are
  missing). A non-compact space cannot be the continuous image of a compact one, so **no surjection exists**.
  The work is recognizing this is the *only* relevant fact.
- **(b)** Compactness gives no obstruction to an *injection* (an injective continuous image need not be all
  of `X`, only a compact subset of it). So one expects "yes" — but must actually **produce** a continuous
  injection landing in the irrationals. The subtlety: `C` itself *contains rationals* (e.g. the endpoints
  `0, 1, \tfrac13, \tfrac23,\dots`), so the inclusion `C\hookrightarrow[0,1]` does *not* land in `X`. One
  must **perturb** `C` off the rationals — and the right tool is that the "bad" translation parameters form
  a small (measure-zero / meager) set, so a good one exists.

## The Key Insight

- **(a) No.** Continuous image of compact is compact; `C` is compact but `X` is not (it is not closed in
  `\mathbb R`). So `f(C)\ne X` for any continuous `f`.
- **(b) Yes.** Take the affine map `f(x) = \tfrac12 x + b`. It is automatically a continuous injection, and
  `f([0,1]) = [b, b+\tfrac12]\subseteq(0,1)` for `b\in(0,\tfrac12)`. The set of "bad" `b` (those making some
  `f(c)` rational, `c\in C`) is `\bigcup_{q\in\mathbb Q}(q - \tfrac12 C)`, a countable union of
  measure-zero (nowhere-dense) Cantor translates, hence not all of `(0,\tfrac12)`. Choosing `b` outside it
  makes `f(C)\subseteq X`.

## Complete Proof

`C\subseteq[0,1]` is the standard Cantor set (compact, being closed and bounded), and
`X = \{x : x\text{ irrational},\ 0<x<1\} = (0,1)\setminus\mathbb Q` carries the subspace topology from
`\mathbb R`.

### (a) There is **no** continuous surjection `f : C \to X`

**`X` is not compact.** A subset of `\mathbb R` is compact iff it is closed and bounded (Heine–Borel). `X`
is bounded (`X\subseteq(0,1)`) but **not closed**: for instance, a sequence of irrationals `x_n\to\tfrac12`
lies in `X`, yet its limit `\tfrac12\in\mathbb Q` is not in `X`. So `X` contains a sequence whose limit
escapes `X`; `X` is not closed, hence not compact.

**Conclusion.** Suppose `f : C\to X` were a continuous surjection. The Cantor set `C` is compact, and the
continuous image of a compact space is compact, so `f(C)` is a compact subset of `\mathbb R`. Surjectivity
gives `f(C) = X`, forcing `X` to be compact — contradicting the previous paragraph. Therefore **no
continuous surjection `C\to X` exists.** ∎

### (b) There **is** a continuous injection `f : C \to X`

We exhibit an affine map and choose its constant term to dodge the rationals.

**The map.** For a constant `b\in(0,\tfrac12)` to be chosen, define
$$
f : \mathbb R \to \mathbb R, \qquad f(x) = \tfrac12 x + b .
$$
This is affine with nonzero slope, hence a **continuous injection** (indeed a homeomorphism onto its image),
and its restriction `f|_C` is a continuous injection. Moreover, since `C\subseteq[0,1]`,
$$
f(C)\subseteq f([0,1]) = \big[b,\ b+\tfrac12\big] \subseteq (0,1),
$$
because `b>0` and `b+\tfrac12<1`. It remains to choose `b` so that `f(C)` avoids the rationals, i.e.
`f(C)\subseteq X`.

**Choosing `b` to avoid rationals.** Call `b` *bad* if `f(c) = \tfrac12 c + b\in\mathbb Q` for some `c\in
C`. Solving, `b = q - \tfrac12 c` for some `q\in\mathbb Q`, `c\in C`, so the set of bad parameters is
$$
B = \bigcup_{q\in\mathbb Q}\Big(q - \tfrac12 C\Big).
$$
Each `q - \tfrac12 C` is an affine image of the Cantor set, hence (like `C`) **closed with empty interior
and Lebesgue measure zero** (`C` has measure `0`, so `\tfrac12 C` has measure `0`, and translation
preserves this). Therefore `B` is a **countable union of measure-zero sets, hence has measure zero** (and
by Baire it is meager). In particular `B` cannot contain the interval `(0,\tfrac12)`, so
$$
(0,\tfrac12)\setminus B \ne \varnothing .
$$
Pick any `b\in(0,\tfrac12)\setminus B`.

**Verification.** With this `b`: `f|_C` is a continuous injection; `f(C)\subseteq[b,b+\tfrac12]\subseteq
(0,1)`; and since `b\notin B`, no `f(c)` is rational, so `f(C)\subseteq\mathbb R\setminus\mathbb Q`.
Combining, `f(C)\subseteq(0,1)\setminus\mathbb Q = X`. Hence
$$
f|_C : C \to X
$$
is a **continuous injection**. **Yes, such an injection exists.** ∎

**Remark.** The asymmetry between the parts is exactly the asymmetry between surjections and injections under
compactness: compactness is preserved by continuous *surjective* images, so it obstructs (a) — `X` is "too
big and not closed" to be a compact image — but it places no obstruction on injective images, which need only
land in *some* compact subset of `X`. Part (b) realizes this: `f(C)` is a Cantor set sitting inside the
irrationals, obtained by sliding `\tfrac12 C` to a position `b` avoiding the meager/null set of rationals it
could otherwise hit. (Conceptually, the irrationals `(0,1)\setminus\mathbb Q` are homeomorphic to Baire space
`\mathbb N^{\mathbb N}`, which contains homeomorphic copies of the Cantor set — so `C` embeds in `X` — but
the explicit affine translate gives a self-contained injection.)

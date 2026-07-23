<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91A07: Fixed points with no eigenvalue 1 are isolated (inverse function theorem)

## Why It's Hard

The hypothesis is spectral — `df_x` has no eigenvalue `+1` at each fixed point — and the conclusion is
topological — fixed points don't accumulate. Bridging these requires translating "no eigenvalue `1`" into a
statement the inverse function theorem can use, and then setting up the right local function whose *zeros*
are the fixed points. The natural candidate, `f(x) - x`, is exactly what the hint suggests, but as the
parenthetical admits, it "doesn't make sense" globally: on a manifold there is no subtraction, and `f(x)`
and `x` are just two points with no difference. The real content is recognizing that this is harmless —
**in a single coordinate chart** the local representative of `f` does map into a vector space, so
`g(u) = F(u) - u` is a legitimate map `\mathbb R^n \to \mathbb R^n`, its zeros are the fixed points, and its
derivative at the fixed point is `df_p - I`.

The key identity is then `\det(df_p - I) \ne 0 \iff +1 \text{ is not an eigenvalue of } df_p`. That is
exactly the nondegeneracy the inverse function theorem needs.

## The Key Insight

In a chart around a fixed point `p` (sending `p \mapsto 0`), let `F` be the local representative of `f` and
set `g(u) = F(u) - u`. Then:

- fixed points of `f` near `p` `\leftrightarrow` zeros of `g`, and `g(0) = 0`;
- `dg_0 = dF_0 - I = df_p - I` (in coordinates), which is **invertible** precisely because `+1` is not an
  eigenvalue of `df_p`.

By the **inverse function theorem**, `g` is a local diffeomorphism near `0`, hence injective there; so `g`
has *no zero other than `0`* nearby. Thus `p` is the only fixed point in a neighborhood — fixed points are
isolated.

## Complete Proof

Let `f : X \to X` be smooth (`\dim X = n`), and let `p \in X` be a fixed point, `f(p) = p`, with `+1` not an
eigenvalue of `df_p`.

**Step 1 — Localize in a chart.** Choose a coordinate chart `\varphi : U \to \mathbb R^n` with `p \in U` and
`\varphi(p) = 0`. By continuity of `f` and `f(p) = p \in U`, shrink `U` so that `f(U) \subseteq U`. Let

$$F = \varphi \circ f \circ \varphi^{-1} : \varphi(U) \to \mathbb R^n$$

be the local representative of `f`. A point `x \in U` is fixed by `f` iff its coordinate `u = \varphi(x)`
satisfies `F(u) = u`. Note `F(0) = \varphi(f(p)) = \varphi(p) = 0`.

**Step 2 — The fixed-point function and its derivative.** Define

$$g : \varphi(U) \to \mathbb R^n, \qquad g(u) = F(u) - u.$$

(This subtraction is legitimate: `F(u)` and `u` both lie in the *vector space* `\mathbb R^n` of the chart —
the resolution of the hint's "doesn't make sense.") Then `g(u) = 0 \iff F(u) = u`, so **zeros of `g`
correspond exactly to fixed points of `f` in `U`**, and `g(0) = 0`. Differentiating,

$$dg_0 = dF_0 - I.$$

Now `dF_0` is the matrix of `df_p` in these coordinates (the chart is a diffeomorphism, so `dF_0` and `df_p`
are similar and have the same eigenvalues). Since `+1` is not an eigenvalue of `df_p`, it is not an
eigenvalue of `dF_0`, i.e.

$$\det(dF_0 - I) \ne 0 \quad\Longrightarrow\quad dg_0 = dF_0 - I \text{ is invertible.}$$

**Step 3 — Inverse function theorem.** As `g` is smooth with `dg_0` invertible, the **inverse function
theorem** gives a neighborhood `V \ni 0` on which `g` is a diffeomorphism onto its image; in particular `g`
is **injective** on `V`. Since `g(0) = 0`, injectivity forces `g(u) \ne 0` for every `u \in V \setminus \{0\}`.
Hence `0` is the only zero of `g` in `V`.

**Step 4 — Conclusion.** Translating back via `\varphi`, `p` is the only fixed point of `f` in the open set
`\varphi^{-1}(V) \ni p`. Thus `p` is an **isolated** fixed point. Since `p` was an arbitrary fixed point,
every fixed point of `f` is isolated.

$$\boxed{\ \text{The fixed points of } f \text{ are isolated.}\ }\qquad\blacksquare$$

**Remark.** The eigenvalue condition is exactly the **nondegeneracy** of the fixed point: `+1 \notin \mathrm{spec}(df_p)`
is the same as `df_p - I` being invertible, which is the same as the graph of `f` meeting the diagonal
transversally at `p` (equivalently, the section `x \mapsto (x, f(x))` is transverse to the diagonal). This
transversality is precisely what makes the intersection — the fixed-point set — `0`-dimensional, i.e.
discrete. The hint's `f(x) - x` is the affine shadow of this: it is not globally defined, but in any chart it
is the displacement map whose nonsingular derivative `df_p - I` triggers the inverse function theorem. (These
nondegenerate fixed points are the ones that contribute `\pm 1` to the Lefschetz number.)

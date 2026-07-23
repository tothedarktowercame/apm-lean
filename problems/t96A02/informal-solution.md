<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96A02: A wedge of two projective planes has the fixed-point property

## Why It's Hard

The claim is that *every* continuous self-map of `X = \mathbb{RP}^2 \vee \mathbb{RP}^2` has a fixed point —
a universal statement over all maps `f`, so no explicit construction can work; one needs an invariant that is
nonzero for every `f`. The natural tool is the **Lefschetz fixed-point theorem** (`L(f) \ne 0 \Rightarrow f`
has a fixed point), but computing `L(f)` for an *arbitrary* `f` seems to require knowing how `f` acts on
homology — which varies with `f`. The resolution is a slick observation: over the **rationals**,
`\mathbb{RP}^2` is invisible. Its integral homology in positive degrees is all torsion or zero
(`H_1 = \mathbb Z/2`, `H_2 = 0`), which dies under `\mathbb Q`-coefficients, so `X` has the rational homology
of a *point*. Then the Lefschetz number is forced to equal `1` for every map, regardless of `f`. Seeing that
working over `\mathbb Q` trivializes the computation is the key.

## The Key Insight

With rational coefficients, `H_*(\mathbb{RP}^2; \mathbb Q) = \mathbb Q` in degree `0` and `0` in higher
degrees (the `\mathbb Z/2 = H_1` and the `0 = H_2` contribute nothing rationally). For a wedge, reduced
homology adds, so

$$H_0(X; \mathbb Q) = \mathbb Q, \qquad H_k(X; \mathbb Q) = 0 \ (k \ge 1).$$

`X` has the rational homology of a point. Hence for *any* continuous `f : X \to X`, the Lefschetz number is

$$L(f) = \sum_k (-1)^k \operatorname{tr}\big(f_* : H_k(X;\mathbb Q) \to H_k(X;\mathbb Q)\big) = \operatorname{tr}(f_*|_{H_0}) = 1 \ne 0,$$

since only `H_0` survives and `f_*` is the identity on `H_0(X;\mathbb Q) = \mathbb Q` (`X` is connected). By
the **Lefschetz fixed-point theorem**, `f` has a fixed point.

## Complete Proof

`X = \mathbb{RP}^2 \vee \mathbb{RP}^2` (one point of `P` identified with one point of `P'`) is a compact,
connected finite CW complex (a wedge of two finite complexes), so the Lefschetz fixed-point theorem applies:
*for any continuous `f : X \to X`, if `L(f) \ne 0` then `f` has a fixed point*, where `L(f) = \sum_k (-1)^k \operatorname{tr}(f_*|_{H_k(X;\mathbb Q)})`.

**Step 1 — Rational homology of `\mathbb{RP}^2`.** The integral homology is
`H_0(\mathbb{RP}^2) = \mathbb Z`, `H_1(\mathbb{RP}^2) = \mathbb Z/2`, `H_2(\mathbb{RP}^2) = 0`. Tensoring with
`\mathbb Q` (or by the universal coefficient theorem, since `\mathbb Q` is flat and torsion dies):

$$H_0(\mathbb{RP}^2; \mathbb Q) = \mathbb Q, \qquad H_1(\mathbb{RP}^2; \mathbb Q) = (\mathbb Z/2)\otimes\mathbb Q = 0, \qquad H_2(\mathbb{RP}^2; \mathbb Q) = 0,$$

and `0` above. So `\mathbb{RP}^2` is `\mathbb Q`-acyclic in positive degrees: `\widetilde H_*(\mathbb{RP}^2; \mathbb Q) = 0`.

**Step 2 — Rational homology of `X`.** For a wedge of well-pointed spaces, reduced homology splits:
`\widetilde H_*(A \vee B) \cong \widetilde H_*(A) \oplus \widetilde H_*(B)`. Hence

$$\widetilde H_*(X; \mathbb Q) = \widetilde H_*(\mathbb{RP}^2; \mathbb Q) \oplus \widetilde H_*(\mathbb{RP}^2; \mathbb Q) = 0,$$

so `H_0(X; \mathbb Q) = \mathbb Q` and `H_k(X; \mathbb Q) = 0` for all `k \ge 1`. `X` has the rational
homology of a point.

**Step 3 — The Lefschetz number is `1`.** Let `f : X \to X` be any continuous map. On `H_k(X; \mathbb Q)`:

- for `k \ge 1`, `H_k(X; \mathbb Q) = 0`, so `\operatorname{tr}(f_*|_{H_k}) = 0`;
- for `k = 0`, `X` is connected so `H_0(X; \mathbb Q) = \mathbb Q` and `f_*` is the identity (any map induces
  the identity on `H_0` of a connected space), so `\operatorname{tr}(f_*|_{H_0}) = 1`.

Therefore

$$L(f) = \operatorname{tr}(f_*|_{H_0}) - 0 + 0 - \cdots = 1 \ne 0.$$

**Step 4 — Conclude.** Since `L(f) = 1 \ne 0` for every continuous `f : X \to X`, the **Lefschetz
fixed-point theorem** gives that every such `f` has a fixed point.

$$\boxed{\ \text{Every continuous } f : X \to X \text{ has a fixed point.}\ }\qquad\blacksquare$$

**Remark.** The point is that `\mathbb{RP}^2` is *rationally* a point, so `X = \mathbb{RP}^2 \vee \mathbb{RP}^2`
is rationally acyclic and the Lefschetz number can never be anything but `1` — `X` has the **fixed-point
property**. This works for any wedge (or more general gluing) of `\mathbb Q`-acyclic spaces: rational homology
ignores the torsion (`\mathbb Z/2` in `H_1`) and the non-orientability (`H_2 = 0`) that distinguish
`\mathbb{RP}^2` from a disk, leaving only the degree-`0` class that forces `L(f) = 1`. (Contrast: a torus or a
sphere can have fixed-point-free self-maps precisely because they carry nontrivial *rational* homology in
positive degrees, allowing `L(f) = 0`.)

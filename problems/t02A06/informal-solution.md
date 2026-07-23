<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t02A06: Three true/false assertions — all false, by homology, Künneth, and degree

## Why It's Hard

Each part is a plausible-sounding claim whose refutation hinges on the *right invariant*, and the trap in
every case is to trust the naïve geometric count instead of the homotopy-invariant one:

- **(a)** Two great circles really do meet in **two** points, so "absolute value 2" looks right — but the
  *oriented* intersection number is **signed** and homological. Since `H_1(S^2) = 0`, every circle on `S^2`
  is null-homologous, forcing the oriented intersection number to **0**: the two crossings cancel. Confusing
  the unsigned point-count with the oriented number is exactly the intended error.
- **(b)** `S^2\times S^2` and `S^4` are both closed oriented `4`-manifolds, so dimension and compactness give
  no obstruction; one must reach for **middle homology** (`H_2`), where Künneth makes them differ.
- **(c)** "Is there a degree (nonzero) map `S^3 \to T^3`?" — maps certainly exist, but the question is degree,
  and a nonzero-degree map forces `f^*` to be **injective on rational cohomology**, which collides with
  `H^1(T^3;\mathbb Q) = \mathbb Q^3` mapping into `H^1(S^3;\mathbb Q) = 0`. The subtlety is knowing that
  nonzero degree is detected on *all* of cohomology, not just the top.

## The Key Insight

- **(a) FALSE.** `H_1(S^2) = 0`, so `[C_1] = [C_2] = 0` and the oriented intersection number is `0`, not `2`.
  (Geometrically: the two antipodal crossings have *opposite* signs.)
- **(b) FALSE.** `H_2(S^2\times S^2) = \mathbb Z^2` (Künneth) but `H_2(S^4) = 0`; different homology ⇒ not even
  homeomorphic.
- **(c) FALSE.** A nonzero-degree map of closed oriented `n`-manifolds is injective on `H^*(-;\mathbb Q)`; but
  `H^1(T^3;\mathbb Q) = \mathbb Q^3 \ne 0 = H^1(S^3;\mathbb Q)` admits no injection, so every map `S^3\to T^3`
  has degree `0`.

## Complete Proof

### (a) "The oriented intersection number of two great circles on `S^2` has absolute value `2`." — **FALSE**

The oriented intersection number `I_{S^2}(C_1, C_2)` of two closed `1`-submanifolds of complementary
dimension (`\dim C_1 + \dim C_2 = 1 + 1 = 2 = \dim S^2`) is a **homological invariant**: it depends only on
the classes `[C_1], [C_2] \in H_1(S^2)`. But
$$
H_1(S^2) = 0,
$$
so `[C_1] = [C_2] = 0` (every great circle is null-homologous — indeed it bounds each of the two disks it
cuts `S^2` into). The intersection number of a null-homologous cycle with anything is `0`. Hence
$$
I_{S^2}(C_1, C_2) = 0, \qquad |I_{S^2}(C_1,C_2)| = 0 \ne 2 .
$$

*Concretely:* two distinct great circles are the equator and a meridian-type great circle; they meet at two
**antipodal** points `\pm p`, transversally. At `p` the second circle crosses the first in one rotational
sense, and at the antipodal point `-p` it crosses in the *opposite* sense, so the local signs are `+1` and
`-1` and the signed total is `+1 + (-1) = 0`. The unsigned count is `2`, but the *oriented* number is `0`.
The assertion is **false**. ∎

### (b) "There is a diffeomorphism `f : S^2\times S^2 \to S^4`." — **FALSE**

If such `f` existed it would be in particular a homeomorphism, hence induce isomorphisms on all homology
groups. Compare second homology. By the **Künneth formula**,
$$
H_2(S^2\times S^2) \cong \bigoplus_{i+j=2} H_i(S^2)\otimes H_j(S^2) = \big(H_2\otimes H_0\big)\oplus\big(H_1\otimes H_1\big)\oplus\big(H_0\otimes H_2\big) = \mathbb Z \oplus 0 \oplus \mathbb Z = \mathbb Z^2 ,
$$
whereas a sphere has homology only in degrees `0` and `4`:
$$
H_2(S^4) = 0 .
$$
Since `\mathbb Z^2 \not\cong 0`, `S^2\times S^2` and `S^4` are not homeomorphic, a fortiori not
diffeomorphic. (Intuitively, `S^2\times S^2` contains two essential `2`-spheres `S^2\times\{pt\}` and
`\{pt\}\times S^2` that cannot be filled in, while `S^4` has no `2`-dimensional homology at all.) The
assertion is **false**. ∎

### (c) "There is a degree (nonzero-degree) map `f : S^3 \to S^1\times S^1\times S^1`." — **FALSE**

Write `T^3 = S^1\times S^1\times S^1`; both `S^3` and `T^3` are closed oriented `3`-manifolds. Suppose
`f : S^3 \to T^3` has degree `d \ne 0`. Then on top cohomology `f^*` is multiplication by `d` on the
generators, and more usefully:

> **Claim.** A degree-`d` map (`d\ne 0`) of closed oriented `n`-manifolds is **injective** on
> `H^*(-;\mathbb Q)`.

*Proof of claim.* Let `\alpha \in H^k(T^3;\mathbb Q)` be nonzero. By Poincaré duality there is
`\beta\in H^{n-k}(T^3;\mathbb Q)` with `\alpha\cup\beta` a generator of `H^n(T^3;\mathbb Q)\cong\mathbb Q`.
Since `f` has degree `d`, `f^*` is multiplication by `d` on `H^n`, so
$$
f^*\alpha \cup f^*\beta = f^*(\alpha\cup\beta) = d\cdot(\text{generator of } H^n(S^3;\mathbb Q)) \ne 0 .
$$
Hence `f^*\alpha \ne 0`. So `f^*` is injective. ∎(claim)

Now apply the claim in degree `k = 1`:
$$
f^* : H^1(T^3;\mathbb Q) = \mathbb Q^3 \ \longhookrightarrow\ H^1(S^3;\mathbb Q) = 0 .
$$
An injective linear map from `\mathbb Q^3` into `0` is impossible. This contradiction shows no map
`f : S^3 \to T^3` can have nonzero degree; **every** such map has degree `0`. The assertion is **false**. ∎

*(Equivalently and even more directly: `T^3` is aspherical, a `K(\mathbb Z^3, 1)` with contractible
universal cover `\mathbb R^3`, so `\pi_3(T^3) = 0`. Thus every map `S^3 \to T^3` is null-homotopic, and a
null-homotopic map has degree `0`.)*

### Summary

| Part | Assertion | Verdict | Refuting invariant |
|:----:|:----------|:-------:|:-------------------|
| (a) | great circles have oriented intersection `\pm 2` | **False** | `H_1(S^2)=0` ⇒ signed number `=0` |
| (b) | `S^2\times S^2 \cong S^4` | **False** | `H_2 = \mathbb Z^2` vs `0` (Künneth) |
| (c) | nonzero-degree `S^3 \to T^3` exists | **False** | `f^*` injective on `H^1`; `\mathbb Q^3 \not\hookrightarrow 0` |

**Remark.** All three are the same lesson — *replace the naïve geometric count by the homotopy-invariant
one*. (a) warns that "oriented" means signed, and signs cancel on a space with no `H_1`; (b) and (c) are
degree/Künneth obstructions showing that homology and the multiplicativity of degree rigidly constrain which
manifolds and maps can exist. In each case the false statement is the one that ignores cancellation
(`H_1(S^2)=0`), differing Betti numbers (`H_2`), or the cohomological footprint of nonzero degree
(`H^1(T^3)\ne 0`).

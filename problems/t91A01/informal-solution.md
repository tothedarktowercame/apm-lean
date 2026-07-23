<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91A01: An index +3 zero forces a second zero — a parity obstruction from Poincaré–Hopf

## Why It's Hard

The two parts test the same circle of ideas — the **index** of a vector-field zero (a winding number) and
its global constraint via **Poincaré–Hopf** — from the concrete and the abstract side:

- **(a)** "Draw an index `+3` zero" requires understanding that the index is the **winding number of the
  field direction** as you traverse a small loop once around the zero. The clean model is the complex map
  `z\mapsto z^3`, whose direction winds *three times* — but one must know that `z^k` realizes index `k`, and
  be able to depict the resulting "three-fold-spin" phase portrait.
- **(b)** is a slick global argument, and the trap is to reach for an inequality (`\chi \le 2`) when the
  decisive fact is **parity**. Poincaré–Hopf says the indices sum to `\chi(F)`; if the index-`3` zero were
  the *only* zero, then `\chi(F) = 3`. But a closed oriented surface has `\chi = 2 - 2g`, which is **even**.
  Three is odd — contradiction. Recognizing that the obstruction is "odd `\ne` even," not magnitude, is the
  insight; it works no matter how large the genus.

## The Key Insight

- **(a)** The planar field `V(z) = z^3` (`z = x+iy`) has an isolated zero at the origin of index `+3`,
  because as `z = re^{i\theta}` runs once around the origin, `z^3 = r^3 e^{3i\theta}` spins the field
  direction through **three** full turns.
- **(b)** By **Poincaré–Hopf**, `\sum_p \operatorname{ind}_p(V) = \chi(F)`. A single index-`3` zero would
  give `\chi(F) = 3`; but a closed oriented surface has `\chi(F) = 2 - 2g`, an **even** number. Since `3` is
  odd, the index-`3` zero cannot be the only one — `V` has another zero.

## Complete Proof

### (a) A local picture of an index `+3` zero

Identify `\mathbb R^2 \cong \mathbb C` via `z = x + iy`, and take the smooth vector field
$$
V(z) = z^3, \qquad\text{i.e.}\qquad V(x,y) = \big(x^3 - 3xy^2,\ 3x^2y - y^3\big).
$$
Its only zero is the origin (`z^3 = 0 \iff z = 0`), and it is isolated.

**Index `= +3`.** The index of an isolated zero is the degree of the *direction map*
`\theta \mapsto V/|V|` on a small circle around the zero — equivalently, the winding number of `V` as you go
once around. On the circle `z = r e^{i\theta}`,
$$
V = r^3 e^{3i\theta},
$$
so the field direction is the angle `3\theta`. As the position angle `\theta` increases by `2\pi` (one
counterclockwise loop), the direction `3\theta` increases by `6\pi` — **three** full revolutions. Hence
$$
\operatorname{ind}_0(V) = 3 .
$$

**The picture.** Draw a small circle about the origin and place arrows around it; the arrow at position
angle `\theta` points in direction `3\theta`, spinning three times as fast as the position:

| position `\theta` | `0^\circ` | `30^\circ` | `60^\circ` | `90^\circ` | `120^\circ` | `\cdots` |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| arrow direction `3\theta` | `\to` (E) | `\uparrow` (N) | `\leftarrow` (W) | `\downarrow` (S) | `\to` (E) | `\cdots` |

Over each `120^\circ` sector of the circle the arrows sweep one complete `360^\circ` turn, so over the whole
circle they make three turns. The resulting phase portrait is a symmetric "three-fold" pattern (a
higher-order monkey-saddle: sectors of inflow and outflow repeating with three-fold symmetry), the
hallmark of an index-`+3` singularity. *(Reversing to `V(z) = \bar z^3` would instead spin the field the
other way, giving index `-3`.)*

### (b) `V` must have a second zero

Let `F` be a closed, compact, oriented surface (so `\chi(F) = 2 - 2g` for its genus `g`), and let `V` be a
smooth vector field on `F` with isolated zeros, one of which has index `3`.

**Poincaré–Hopf theorem.** For a smooth vector field with (finitely many) isolated zeros on a closed
oriented surface,
$$
\sum_{p\,:\,V(p)=0} \operatorname{ind}_p(V) = \chi(F).
$$
(The zeros are finite because they are isolated and `F` is compact.)

**Suppose, for contradiction, that the index-`3` zero is the only zero of `V`.** Then the sum has a single
term, so
$$
\chi(F) = \operatorname{ind}_p(V) = 3 .
$$
But `F` is a closed oriented surface, so its Euler characteristic is
$$
\chi(F) = 2 - 2g \in \{2, 0, -2, -4, \dots\},
$$
which is **even** (and at most `2`). Since `3` is **odd**, `\chi(F) = 3` is impossible. This contradiction
shows the index-`3` zero cannot be the only zero.

**Conclusion.** Therefore `V` has at least one further zero besides the given index-`3` zero. ∎

**Remark.** The argument is purely a parity (and size) count: the *total* index is pinned to the even
number `\chi(F)` by Poincaré–Hopf, so the odd contribution `+3` from one zero must be balanced by the
indices of other zeros (their sum being `\chi(F) - 3`, an odd number, hence nonzero — in particular there is
at least one more zero). For instance on the sphere (`\chi = 2`) the remaining zeros would have to contribute
index `-1` in total; on the torus (`\chi = 0`), index `-3`; and so on — but in every case "even total minus
odd contribution" is nonzero, forbidding a lone index-`3` zero. The result is the local-to-global rigidity of
vector fields: you cannot place a single high-index singularity on a surface without the global topology
demanding compensating zeros elsewhere.

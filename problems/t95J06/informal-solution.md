<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95J06: Invariant surfaces of the Hopf flow on S⁵ are tori

## Why It's Hard

The vector field `v(\mathbf z) = i\mathbf z` looks like a mild perturbation, but its flow is the **Hopf
circle action** on `S^5`, and the whole problem is about recognizing that and exploiting its key property:
the action is **free**. Part (a) is a direct computation once you solve the ODE. Part (b) is the conceptual
core: an `H`-invariant surface `F` is a union of flow-orbits, i.e. an `S^1`-invariant closed surface on which
`S^1` acts *freely*. The difficulty is to convert "free circle action" into a topological constraint —
namely that `F` fibers in circles over a `1`-manifold, forcing `\chi(F) = 0`, so that the classification of
surfaces (plus orientability) pins `F` down to the torus. The trap is to forget freeness (which rules out
`S^2`: any circle action on `S^2` has fixed points) or orientability (which rules out the Klein bottle).

## The Key Insight

Solving `\dot{\mathbf z} = i\mathbf z` gives the flow

$$H(\mathbf z, t) = e^{it}\mathbf z,$$

the diagonal `S^1`-action on `S^5 \subset \mathbb C^3`. It is **free**: `e^{it}\mathbf z = \mathbf z` with
`\mathbf z \ne 0` forces `e^{it} = 1`.

- **(a)** On `T`, `e^{it}(\cos\theta\, e^{i\varphi}, \sin\theta\, e^{i\varphi}, 0) = (\cos\theta\, e^{i(\varphi+t)}, \sin\theta\, e^{i(\varphi+t)}, 0)`,
  the same `\theta` with `\varphi \mapsto \varphi + t` — still in `T`. So `T` is invariant.
- **(b)** An invariant closed orientable surface `F` is a union of (circle) orbits, so `S^1` acts **freely**
  on `F`; then `F \to F/S^1` is a circle bundle over a closed `1`-manifold (a union of circles), giving
  `\chi(F) = 0`. A closed **orientable** surface with `\chi = 0` is the **torus** `T^2`. So every connected
  invariant orientable surface is a torus (and `F` in general is a disjoint union of tori).

## Complete Proof

The integral curves of `v(\mathbf z) = i\mathbf z` solve `\dfrac{d\mathbf z}{dt} = i\mathbf z`, hence
`\mathbf z(t) = e^{it}\mathbf z(0)`. So the flow is

$$H(\mathbf z, t) = e^{it}\mathbf z \qquad (\mathbf z \in S^5,\ t \in \mathbb R),$$

which preserves `S^5` (`|e^{it}\mathbf z| = |\mathbf z| = 1`) and is the standard diagonal circle action.

### (a) `T` is invariant

Let `\mathbf z = (\cos\theta\, e^{i\varphi},\ \sin\theta\, e^{i\varphi},\ 0) \in T`. Then for any `t`,

$$H(\mathbf z, t) = e^{it}\mathbf z = \big(\cos\theta\, e^{i(\varphi + t)},\ \sin\theta\, e^{i(\varphi+t)},\ 0\big),$$

which is again of the defining form with parameters `\theta` (unchanged) and `\varphi' = \varphi + t`. Hence
`H(\mathbf z, t) \in T`, so `H(T \times \mathbb R) \subseteq T`: `T` is invariant. (The flow simply rotates
the `\varphi`-circle of `T` at unit speed while fixing `\theta`.) ∎

### (b) Possible diffeomorphism types of an invariant compact orientable surface

Let `F \subseteq S^5` be a compact orientable `2`-manifold (closed, `\partial F = \varnothing`) invariant
under `H`.

**Step 1 — The action is free on `F`.** The flow `H(\cdot, t) = e^{it}(\cdot)` is a circle action of
`S^1 = \mathbb R/2\pi\mathbb Z`, and it is **free** on `S^5`: if `e^{it}\mathbf z = \mathbf z` for some
`\mathbf z \in S^5` (so some coordinate `z_j \ne 0`), then `e^{it}z_j = z_j` forces `e^{it} = 1`. Restricting
to the invariant `F`, the action of `S^1` on `F` is still free, and each orbit is a circle.

**Step 2 — `F` is a circle bundle over a closed `1`-manifold.** A free smooth `S^1`-action on the closed
manifold `F` makes the orbit projection `\pi : F \to B := F/S^1` a **principal `S^1`-bundle**. The base `B` is
a closed `1`-manifold (`\dim B = \dim F - 1 = 1`, compact, without boundary since `F` is closed), hence a
disjoint union of circles.

**Step 3 — `\chi(F) = 0`.** For a fiber bundle with fiber `S^1` over `B`, multiplicativity of the Euler
characteristic gives

$$\chi(F) = \chi(S^1)\,\chi(B) = 0 \cdot \chi(B) = 0.$$

**Step 4 — Classify.** A closed surface with `\chi = 0` is either the torus `T^2` (orientable) or the Klein
bottle `K` (non-orientable). Since `F` is **orientable**, `K` is excluded. Therefore each connected component
of `F` is diffeomorphic to

$$\boxed{\ T^2 \quad(\text{the torus}).\ }$$

Equivalently: the only diffeomorphism type of a connected compact orientable invariant surface is the torus
`T^2`, and a general (possibly disconnected) invariant `F` is a disjoint union of tori. ∎

**Remark.** The engine is freeness. The Hopf flow `e^{it}\mathbf z` acts freely on `S^5` (quotient
`\mathbb{CP}^2`), so any invariant surface inherits a free circle action; a free `S^1`-action forces the
surface to fiber in circles over a `1`-manifold, killing the Euler characteristic. Orientability then selects
the torus over the Klein bottle. Two near-misses are excluded for structural reasons: `S^2` cannot occur
because a circle action on `S^2` *must* have fixed points (`\chi(S^2) = 2 \ne 0`), so the action could not be
free; and the Klein bottle is the non-orientable `\chi = 0` surface, ruled out by the hypothesis. The torus
`T` exhibited in part (a) is the prototype — indeed *the* example — of such an invariant surface.

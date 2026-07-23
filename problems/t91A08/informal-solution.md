<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91A08: A torus form integral, its pullback, and degree as a homotopy obstruction

## Why It's Hard

The three parts build a small but complete argument: compute a `2`-form integral on the torus, see how a
linear self-map scales it, and turn that scaling into a *homotopy* obstruction. The conceptual hurdle is
connecting three different objects — the integral `\int_{T^2}\beta` (analysis), the determinant of the matrix
(linear algebra), and the homotopy class of `g` (topology). The bridge is **degree theory**: a self-map of a
closed oriented manifold scales the integral of any top-form by its degree, the degree of a linear torus map
is the determinant of its integer matrix, and degree is a homotopy invariant. Recognizing that `\int_{T^2}g^*\beta`
*is* `(\deg g)\cdot\int_{T^2}\beta`, and that this number cannot change under homotopy, is the whole game.

## The Key Insight

`T^2 = \mathbb R^2/\mathbb Z^2` with fundamental domain `[0,1]^2`, and `\beta` is the descent of `\alpha = 3\,dx\wedge dy`.

- **(a)** `\int_{T^2}\beta = \int_{[0,1]^2} 3\,dx\,dy = 3`.
- **(b)** For a linear map with matrix `A`, `f^*(dx\wedge dy) = (\det A)\,dx\wedge dy`. Here
  `\det A = \det\begin{psmallmatrix}5&2\\4&3\end{psmallmatrix} = 7`, so `g^*\beta = 7\beta` and
  `\int_{T^2}g^*\beta = 7\cdot 3 = 21`. (Equivalently `\int_{T^2}g^*\beta = (\deg g)\int_{T^2}\beta` with `\deg g = \det A = 7`.)
- **(c)** Homotopic maps induce equal maps on `H^2_{\mathrm{dR}}(T^2)`, so they give equal integrals of the
  closed form `\beta`. But `\int_{T^2}g^*\beta = 21 \ne 3 = \int_{T^2}\mathrm{id}^*\beta`, so `g \not\simeq \mathrm{id}`.

## Complete Proof

Model the torus as `T^2 = \mathbb R^2/\mathbb Z^2` with the orientation and coordinates inherited from
`\mathbb R^2`; a fundamental domain is the unit square `[0,1]^2`. Since `\alpha = 3\,dx\wedge dy` is invariant
under integer translations, it descends to a smooth `2`-form `\beta` on `T^2` (the "induced" form), closed
because it is top-degree.

### (a) `\int_{T^2}\beta`

$$\int_{T^2}\beta = \int_{[0,1]^2} 3\,dx\,dy = 3\cdot \mathrm{area}([0,1]^2) = 3.$$

$$\boxed{\ \int_{T^2}\beta = 3.\ }$$

### (b) `\int_{T^2}g^*\beta`

`f(x,y) = (5x+2y,\ 4x+3y)` is linear with matrix `A = \begin{pmatrix}5&2\\4&3\end{pmatrix}`. Since `A` has
integer entries, `f` descends to a well-defined smooth map `g : T^2 \to T^2`. For a linear map, pullback of
the area form scales by the determinant:

$$g^*(dx\wedge dy) = (\det A)\,dx\wedge dy, \qquad \det A = 5\cdot 3 - 2\cdot 4 = 7,$$

so `g^*\beta = g^*(3\,dx\wedge dy) = 3\cdot 7\,dx\wedge dy = 21\,dx\wedge dy = 7\beta`. Therefore

$$\int_{T^2}g^*\beta = \int_{[0,1]^2} 21\,dx\,dy = 21.$$

$$\boxed{\ \int_{T^2}g^*\beta = 21.\ }$$

(Equivalently, `\int_{T^2}g^*\beta = (\deg g)\int_{T^2}\beta`, and the degree of the linear torus map `g` is
`\det A = 7`, giving `7\cdot 3 = 21`.)

### (c) `g` is not homotopic to the identity

`\beta` is a closed `2`-form, so its integral over `T^2` depends only on its de Rham cohomology class
`[\beta] \in H^2_{\mathrm{dR}}(T^2)`, and more precisely `\int_{T^2} h^*\beta = \langle h^*[\beta], [T^2]\rangle`
for any smooth `h : T^2 \to T^2`. **Homotopic maps induce the same map on de Rham cohomology**, so if
`g \simeq \mathrm{id}` then `g^*[\beta] = \mathrm{id}^*[\beta] = [\beta]`, hence

$$\int_{T^2}g^*\beta = \int_{T^2}\mathrm{id}^*\beta = \int_{T^2}\beta.$$

But by parts (a) and (b),

$$\int_{T^2}g^*\beta = 21 \ne 3 = \int_{T^2}\beta.$$

This contradiction shows

$$\boxed{\ g \text{ is not homotopic to the identity.}\ }\qquad\blacksquare$$

**Remark.** The integral `\int_{T^2}h^*\beta = (\deg h)\cdot 3` reads off the **degree** of `h`, a homotopy
invariant. Here `\deg g = \det A = 7 \ne 1 = \deg(\mathrm{id})`, which is exactly why `g` cannot be deformed to
the identity. The form `\beta` is just a convenient detector — any closed `2`-form with nonzero integral would
do — and the underlying fact is that a self-map of a closed oriented `n`-manifold scales the integral of every
`n`-form by its degree, while homotopy leaves the degree (and the induced map on top cohomology) unchanged.
For linear torus maps the degree is the determinant of the defining integer matrix, making this obstruction a
one-line determinant computation.

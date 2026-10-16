**Why it's hard:** The hypothesis is one-sided ($\mathrm{Re}(f)$ bounded above and below) but $f$ itself need not be bounded — $\mathrm{Im}(f)$ can be arbitrarily large. We need to manufacture two bounded analytic functions whose ratio is $f$, and there's no obvious choice without exploiting a conformal map of a half-plane to a disk.

**The key insight:** Shift $f$ horizontally so that $\mathrm{Re}(f)$ lies in the right half-plane $\{\mathrm{Re}(w) > 0\}$, then apply the Cayley-type Möbius transformation $w \mapsto (w - 1)/(w + 1)$, which maps the right half-plane onto the open unit disk. This produces a bounded analytic function $\varphi \circ f$ on $H$, and inverting the relation gives $f$ as a ratio of two bounded analytic functions.

**Proof:**

By hypothesis, there exists $M > 0$ such that $|\mathrm{Re}(f(z))| \leq M$ for all $z \in H$. Set $f_{1}(z) = f(z) + (M + 1)$. Then $\mathrm{Re}(f_{1}(z)) = \mathrm{Re}(f(z)) + M + 1 \geq -M + M + 1 = 1 > 0$ for all $z \in H$, so $f_{1}$ maps $H$ into the right half-plane $R = \{w \in \mathbb{C} : \mathrm{Re}(w) > 0\}$. Note $f_{1}$ is analytic on $H$ (translate of $f$).

Consider the Möbius transformation $\varphi(w) = (w - 1)/(w + 1)$, which maps $R$ onto the open unit disk $\Delta = \{|\zeta| < 1\}$. (Standard: $|w - 1|^{2} = |w|^{2} - 2\mathrm{Re}(w) + 1 < |w|^{2} + 2\mathrm{Re}(w) + 1 = |w + 1|^{2}$ when $\mathrm{Re}(w) > 0$.) Since $\mathrm{Re}(f_{1}(z)) \geq 1 > 0$, the denominator $f_{1}(z) + 1$ never vanishes on $H$, so

$$\psi(z) := \varphi(f_1(z)) = \frac{f_1(z) - 1}{f_1(z) + 1}$$

is analytic on $H$, and $|\psi(z)| < 1$ for all $z \in H$. So $\psi$ is analytic and bounded on $H$.

Now solve for $f$. From $\psi = (f_{1} - 1)/(f_{1} + 1)$:
$$\psi(f_1 + 1) = f_1 - 1 \implies f_1(\psi - 1) = -\psi - 1 \implies f_1 = \frac{1 + \psi}{1 - \psi}$$

(The denominator $1 - \psi$ is nonzero since $|\psi| < 1$.) Therefore:
$$f = f_1 - (M + 1) = \frac{1 + \psi}{1 - \psi} - (M + 1) = \frac{(1 + \psi) - (M+1)(1 - \psi)}{1 - \psi} = \frac{(M + 2)\psi - M}{1 - \psi}$$

Define:
- $g(z) = (M + 2)\psi(z) - M$
- $h(z) = 1 - \psi(z)$

Both $g$ and $h$ are analytic on $H$ (linear combinations of $\psi$ and constants).

**Boundedness of $g$:** $|g(z)| = |(M+2)\psi(z) - M| \leq (M+2)|\psi(z)| + M < (M+2) + M = 2M + 2$.

**Boundedness of $h$:** $|h(z)| = |1 - \psi(z)| \leq 1 + |\psi(z)| < 2$.

So both $g$ and $h$ are bounded analytic functions on $H$, and $f(z) = g(z)/h(z)$. ∎

**What connects:** This is the standard one-sided-bound trick in complex analysis: a one-sided bound on $\mathrm{Re}(f)$ (or on $\log|f|$, etc.) is upgraded to a two-sided bound on a Möbius-transformed quantity, producing membership in a "nice" function class. The same construction shows that any analytic function on $H$ with positive real part is the Cayley pullback of a Schur function (analytic and bounded by 1 on $\Delta$ via the conformal map between $H$ and $\Delta$), which underlies the Herglotz-Riesz integral representation of analytic functions with positive real part. The decomposition $f = g/h$ with $g, h \in H^{\infty}(H)$ is a baby case of the inner-outer factorization in the theory of the Hardy space $H^{p}$.

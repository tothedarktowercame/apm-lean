# APM a03J07: A bounded analytic function on a half-plane is controlled by its boundary values

## Why It's Hard

The maximum modulus principle applies to bounded regions, and the half-plane is not
bounded. Passing to a large half-disc does not immediately help: on the circular part of
its boundary there is no bound better than the global bound $K$, which may be much larger
than the boundary bound $M$. So the naive argument yields $|f| \le \max(M, K) = K$, which is
the hypothesis, not the conclusion. Some device is needed to make the circular arc
contribute nothing in the limit. The boundedness hypothesis is essential and not merely
technical: $f(z) = e^{-iz}$ is analytic on $H$, continuous on $\bar H$, has modulus $1$ on
$\mathbb{R}$, and is unbounded on $H$.

## The Key Insight

Multiply $f$ by a factor that is harmless on the real axis but decays on the arc. The
function

$$g_\varepsilon(z) = \frac{f(z)}{1 - i\varepsilon z}, \qquad \varepsilon > 0,$$

does this. Writing $z = x + iy$ with $y \ge 0$ gives $1 - i\varepsilon z = (1 + \varepsilon y) - i\varepsilon x$,
so $|1 - i\varepsilon z| \ge 1$ everywhere on $\bar H$ — the denominator never helps $f$ grow — while
$|1 - i\varepsilon z| \ge \varepsilon|x|$ and $|1 - i\varepsilon z| \ge \varepsilon y$ force the denominator to be
large when $|z|$ is large. So $g_\varepsilon$ inherits the boundary bound $M$ on $\mathbb{R}$ and
tends to $0$ at infinity. Now the half-disc argument closes, and $\varepsilon \to 0$ removes the
device.

## Complete Proof

**Theorem.** Let $H = \{z : \operatorname{Im} z > 0\}$ and let $f : \bar H \to \mathbb{C}$ be bounded and
continuous, with $f|_H$ analytic. Suppose $|f(x)| \le M < \infty$ for every $x \in \mathbb{R}$.
Then $|f(z)| \le M$ for all $z \in H$.

**Proof.**

Let $K = \sup_{z \in \bar H} |f(z)| < \infty$, which is finite by hypothesis. Fix $\varepsilon > 0$ and set

$$g_\varepsilon(z) = \frac{f(z)}{1 - i\varepsilon z} \qquad (z \in \bar H).$$

**Step 1: $g_\varepsilon$ is well defined, continuous on $\bar H$ and analytic on $H$.** For
$z = x + iy \in \bar H$ we have $y \ge 0$ and

$$1 - i\varepsilon z = 1 - i\varepsilon(x + iy) = (1 + \varepsilon y) - i\varepsilon x,$$

so that

$$|1 - i\varepsilon z| = \sqrt{(1 + \varepsilon y)^2 + \varepsilon^2 x^2} \ \ge\ 1 . \tag{1}$$

In particular the denominator has no zero in $\bar H$, so $g_\varepsilon$ is continuous on $\bar H$
and analytic where $f$ is, namely on $H$.

**Step 2: $|g_\varepsilon| \le M$ on the real axis.** For $z = x$ real, $(1)$ gives $|1 - i\varepsilon x| \ge 1$, so

$$|g_\varepsilon(x)| = \frac{|f(x)|}{|1 - i\varepsilon x|} \le |f(x)| \le M .$$

**Step 3: $g_\varepsilon$ is small far out.** From $(1)$, $|1 - i\varepsilon z| \ge 1 + \varepsilon y \ge \varepsilon y$ and
$|1 - i\varepsilon z| \ge \varepsilon|x|$, hence

$$|1 - i\varepsilon z| \ \ge\ \tfrac{1}{2}\bigl(\varepsilon y + \varepsilon |x|\bigr) \ \ge\ \tfrac{\varepsilon}{2}|z| ,$$

using $|x| + y \ge |z|$ for $z = x + iy$ with $y \ge 0$. Therefore

$$|g_\varepsilon(z)| \le \frac{K}{(\varepsilon/2)|z|} = \frac{2K}{\varepsilon |z|} \qquad (z \in \bar H,\ z \ne 0). \tag{2}$$

**Step 4: Maximum modulus on a large half-disc.** Fix $z_0 \in H$. Choose $R > |z_0|$ so large
that $2K/(\varepsilon R) \le M$, which is possible since the left side tends to $0$ as $R \to \infty$.
Let

$$D_R = \{z : |z| < R,\ \operatorname{Im} z > 0\},$$

a bounded region whose boundary consists of the segment $[-R, R]$ of the real axis and the
semicircular arc $\Gamma_R = \{|z| = R, \operatorname{Im} z \ge 0\}$. The function $g_\varepsilon$ is continuous on
$\overline{D_R}$ and analytic on $D_R$. On the segment, Step 2 gives $|g_\varepsilon| \le M$; on
$\Gamma_R$, estimate $(2)$ gives $|g_\varepsilon| \le 2K/(\varepsilon R) \le M$. So $|g_\varepsilon| \le M$ on all of
$\partial D_R$, and the maximum modulus principle yields

$$|g_\varepsilon(z)| \le M \qquad \text{for all } z \in D_R .$$

In particular $|g_\varepsilon(z_0)| \le M$, since $|z_0| < R$.

**Step 5: Remove the auxiliary factor.** The point $z_0 \in H$ and the bound
$|g_\varepsilon(z_0)| \le M$ hold for every $\varepsilon > 0$, that is,

$$|f(z_0)| \le M\,|1 - i\varepsilon z_0| \qquad \text{for all } \varepsilon > 0 .$$

Letting $\varepsilon \to 0^{+}$, the right-hand side tends to $M \cdot |1| = M$. Hence
$|f(z_0)| \le M$. As $z_0 \in H$ was arbitrary, $|f| \le M$ on $H$. $\blacksquare$

## What Connects

This is the simplest case of the Phragmén–Lindelöf principle: the maximum modulus
principle survives on unbounded regions provided the function's growth at infinity is
controlled. Here the control is the crudest possible — boundedness — and the auxiliary
factor $(1 - i\varepsilon z)^{-1}$ is the crudest possible damping. On sectors of opening
$\pi/\alpha$ one uses $e^{-\varepsilon z^{\alpha}}$ instead, and the admissible growth rate rises
accordingly; the trade-off between the opening angle and the permitted growth is the
content of the general Phragmén–Lindelöf theorems. The example $e^{-iz}$ shows the
trade-off is sharp for the half-plane: growth of order $1$ is already too much.

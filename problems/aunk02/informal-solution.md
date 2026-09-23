# APM aunk02: A holomorphic function that is real on a disc is real — indeed constant

## Why It's Hard

The hypothesis is local (real on one disc) and the conclusion is global (real on all of
$\Omega$), so some propagation mechanism is required; analyticity is the only one
available. The apparent difficulty is that "being real" is a condition on the imaginary
part alone, and it is not obvious that controlling $\operatorname{Im} f$ on a small set controls
$f$ anywhere else. The resolution is that the hypothesis is far stronger than it looks:
a holomorphic function cannot be real on an open set without being constant there, so what
propagates is not merely realness but an exact value.

## The Key Insight

Two short steps. First, Cauchy–Riemann on the disc: if $f = u + iv$ is holomorphic and
$v \equiv 0$ on an open set, then $u_x = v_y = 0$ and $u_y = -v_x = 0$ there, so $u$ is
constant and $f$ is constant on the disc. (Equivalently: $f$ maps the disc into
$\mathbb{R}$, a set with empty interior, so $f$ is not open there, and the open mapping
theorem forces $f$ to be constant.) Second, the identity theorem: two holomorphic
functions on a *connected* open set that agree on a set with an accumulation point agree
everywhere. A disc certainly has accumulation points, so $f$ equals that constant
throughout $\Omega$.

## Complete Proof

**Theorem.** Let $\Omega \subseteq \mathbb{C}$ be a region (a nonempty connected open set), let
$f$ be holomorphic on $\Omega$, and suppose $f(z) \in \mathbb{R}$ for every $z$ in some open disc
$D \subseteq \Omega$. Then $f$ is constant on $\Omega$, and that constant is real; in particular
$f$ is real throughout $\Omega$.

**Proof.**

**Step 1: $f$ is constant on $D$.** Write $f = u + iv$ with $u = \operatorname{Re} f$ and
$v = \operatorname{Im} f$ real-valued. By hypothesis $v \equiv 0$ on $D$. Since $f$ is holomorphic on the
open set $D$, the Cauchy–Riemann equations hold there:

$$u_x = v_y, \qquad u_y = -v_x .$$

Because $v$ is identically zero on the open set $D$, both of its partial derivatives
vanish on $D$, so $u_x = 0$ and $u_y = 0$ on $D$. A real function on a connected open set
with vanishing gradient is constant, and $D$ is connected, so $u \equiv c$ on $D$ for some
$c \in \mathbb{R}$. Hence

$$f \equiv c \quad \text{on } D, \qquad c \in \mathbb{R} .$$

**Step 2: Propagate to $\Omega$ by the identity theorem.** Consider the two functions $f$
and the constant function $z \mapsto c$, both holomorphic on the region $\Omega$. They agree
on $D$. Since $D$ is a nonempty open disc, it has an accumulation point inside $\Omega$
(every point of $D$ is one). The identity theorem for holomorphic functions on a connected
open set therefore gives

$$f(z) = c \qquad \text{for all } z \in \Omega .$$

**Step 3: Conclude.** The constant $c$ is real by Step 1, so $f(z) = c \in \mathbb{R}$ for every
$z \in \Omega$. Thus $f$ is real on all of $\Omega$ — and, more strongly, constant.
$\blacksquare$

## What Connects

The problem is a packaged illustration that holomorphic maps are open: the only way the
image of an open set can miss having interior is for the map to be constant. This is why
"real on an open set" is so much stronger than "real on a curve" — the function
$f(z) = z$ is real on all of $\mathbb{R}$ without being constant, and indeed the conclusion
fails outright if $D$ is replaced by a set with empty interior. Connectedness of $\Omega$
is used only in Step 2 and is necessary: on a union of two disjoint discs one may take $f$
to be $0$ on one and $i$ on the other. The same pair of steps proves the companion facts
that a holomorphic function with constant modulus, or with constant real part, on a region
is constant.

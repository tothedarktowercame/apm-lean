<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J01: Bounded integrals over bounded pieces force global integrability

## Why It's Hard

The hypothesis is unusually indirect. We are *not* handed a bound on $\int_\R |f|$,
nor even on $f$ pointwise. We are only told that whenever we cut out a **bounded**
piece $A$ on which $f$ happens to be **bounded**, the *signed* integral $\int_A f$
stays within a fixed window $[-c, c]$. From this thin, local, sign-sensitive
information we must conclude a global, absolute fact: $f \in L^1(\R)$.

Two traps make this delicate:

1. **Signed vs. absolute.** A uniform bound on $\int_A f$ says nothing on its own
   about $\int_A |f|$: a set could carry a huge positive mass and a huge negative
   mass that cancel, leaving $\int_A f$ tiny while $\int_A |f|$ is enormous. The
   hypothesis as stated would be powerless if we applied it to sets straddling a
   sign change.

2. **Boundedness gating.** The hypothesis only fires on sets where $f$ is bounded,
   so we cannot feed it $\R$, or even an interval, directly — we must approach
   $f$ through an increasing family of "tame" pieces and take a limit, while making
   sure the constant $c$ survives that limit.

A note on the statement. As transcribed, the problem assumes $f$ is Lebesgue
measurable and then asks us to "prove that $f$ is Lebesgue measurable" — which is
circular. The intended (and only well-posed) conclusion, standard for this
UT-Austin prelim, is that **$f$ is Lebesgue integrable**, i.e. $\int_\R |f|\,dm <
\infty$. We prove exactly that, with the explicit bound $\int_\R |f|\,dm \le 2c$.

## The Key Insight

Defeat the cancellation trap by **never integrating across a sign change**. Apply
the hypothesis only to sets contained entirely in $\{f \ge 0\}$ or entirely in
$\{f \le 0\}$. On such a set the signed integral *equals* the absolute integral
(up to a global sign), so the window $[-c,c]$ becomes a genuine bound on
$\int_A |f|$.

Then defeat the boundedness gating by **exhaustion**: the sets

$$A_n = \{\,x : |x| \le n,\ 0 \le f(x) \le n\,\}, \qquad
   B_n = \{\,x : |x| \le n,\ -n \le f(x) \le 0\,\}$$

are bounded, measurable, and $f$ is bounded on each, so the hypothesis applies to
every one of them. As $n \to \infty$ they swell to fill $\{f \ge 0\}$ and
$\{f \le 0\}$ respectively. The Monotone Convergence Theorem then transports the
per-$n$ bound $c$ to the limits $\int f^+$ and $\int f^-$, and adding the two gives
$\int |f| \le 2c$.

## Complete Proof

**Theorem.** Let $f : \R \to \R$ be Lebesgue measurable, and suppose there is a
constant $c > 0$ such that for every bounded measurable set $A \subseteq \R$ on
which $f$ is bounded,
$$\left| \int_A f \, dm \right| \le c .$$
Then $f$ is Lebesgue integrable, and in fact $\displaystyle \int_\R |f| \, dm \le 2c$.

**Proof.** Write $f = f^+ - f^-$ with $f^+ = \max(f, 0)$ and $f^- = \max(-f, 0)$;
both are nonnegative and measurable, and $|f| = f^+ + f^-$.

**Step 1 — Bound the positive part.**
For each integer $n \ge 1$ set
$$A_n = \{\,x : |x| \le n\,\} \cap \{\,x : 0 \le f(x) \le n\,\}.$$
Then $A_n$ is measurable (an intersection of measurable sets, since $f$ is
measurable), it is bounded ($A_n \subseteq [-n, n]$), and $f$ is bounded on $A_n$
(there $0 \le f \le n$). The hypothesis therefore applies:
$$\left| \int_{A_n} f \, dm \right| \le c .$$
On $A_n$ we have $f \ge 0$, so $f = f^+$ there and the integrand is nonnegative;
hence
$$\int_{A_n} f^+ \, dm = \int_{A_n} f \, dm = \left| \int_{A_n} f \, dm \right| \le c .$$
Equivalently, $\displaystyle \int_\R f^+ \, \mathbf{1}_{A_n} \, dm \le c$.

Now let $n \to \infty$. Loosening both constraints only enlarges the set, so
$A_n \subseteq A_{n+1}$, and $\bigcup_n A_n = \{x : f(x) \ge 0\}$ (any $x$ with
$f(x) \ge 0$ eventually satisfies both $|x| \le n$ and $f(x) \le n$). Consequently
the nonnegative functions $f^+ \mathbf{1}_{A_n}$ increase pointwise to $f^+$:
indeed on $\{f \ge 0\}$ each $x$ lies in $A_n$ for all large $n$, where
$f^+ \mathbf{1}_{A_n} = f^+$, while on $\{f < 0\}$ both sides are $0$. By the
**Monotone Convergence Theorem**,
$$\int_\R f^+ \, dm = \lim_{n \to \infty} \int_\R f^+ \mathbf{1}_{A_n} \, dm
  = \lim_{n \to \infty} \int_{A_n} f \, dm \le c .$$

**Step 2 — Bound the negative part.**
Symmetrically, set
$$B_n = \{\,x : |x| \le n\,\} \cap \{\,x : -n \le f(x) \le 0\,\},$$
again bounded, measurable, with $f$ bounded on it. The hypothesis gives
$\left| \int_{B_n} f \, dm \right| \le c$. On $B_n$ we have $f \le 0$, so
$f = -f^-$ there and $\int_{B_n} f \le 0$; thus
$$\int_{B_n} f^- \, dm = -\int_{B_n} f \, dm = \left| \int_{B_n} f \, dm \right| \le c .$$
As before $B_n \subseteq B_{n+1}$ and $\bigcup_n B_n = \{x : f(x) \le 0\}$, so
$f^- \mathbf{1}_{B_n} \uparrow f^-$ pointwise. By the Monotone Convergence Theorem,
$$\int_\R f^- \, dm = \lim_{n \to \infty} \int_{B_n} f^- \, dm \le c .$$

**Step 3 — Combine.**
Since $|f| = f^+ + f^-$, linearity of the integral for nonnegative functions yields
$$\int_\R |f| \, dm = \int_\R f^+ \, dm + \int_\R f^- \, dm \le c + c = 2c < \infty .$$
Therefore $f \in L^1(\R)$; that is, $f$ is Lebesgue integrable, with
$\int_\R |f| \, dm \le 2c$. $\blacksquare$

**Remark (sharpness of the method).** The factor $2$ is an artifact of bounding the
positive and negative parts separately; each is controlled by the same constant
$c$, and the cancellation trap of §"Why It's Hard" is precisely why we cannot hope
to get $c$ directly from a single set straddling both signs. The essential content
is finiteness — that the local, signed, boundedness-gated hypothesis is already
enough to force global absolute integrability.

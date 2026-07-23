<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J03: Smoothness of a Stieltjes-type transform, and why its derivative is integrable only away from 0

## Why It's Hard

The function $h(x)=\int_0^\infty \frac{f(y)}{x+y}\,dy$ (a Stieltjes-type transform of $f\in L^1$) packages three tasks that each turn on the same delicate point: **the kernel and all its $x$-derivatives degenerate as $x\to0$.**

- For **$C^\infty$**, one wants to differentiate under the integral sign, but the legitimacy of that requires an *integrable* bound on $\partial_x^k\frac{1}{x+y}$ that is *uniform in $x$* over a neighborhood. The honest bound $\frac{k!}{(x+y)^{k+1}}$ is fine for $x$ bounded below, but it explodes as $x\to0$ — so the argument must be localized to compact subintervals of $(0,\infty)$, never reaching the endpoint.
- For **$h'\in L^1([a,\infty))$**, the difficulty is that $h'$ is itself an integral, so $\int_a^\infty|h'|$ is a double integral; making it finite needs Tonelli to swap order, after which a clean cancellation $\int_a^\infty (x+y)^{-2}\,dx=(a+y)^{-1}$ appears.
- The final question **"what if $a=0$?"** is a trap: the very same computation produces $\int_0^\infty \frac{|f(y)|}{y}\,dy$, which *diverges* for generic $L^1$ functions with mass near $0$. One must recognize that the result genuinely **fails** at $a=0$ and exhibit a witness — the smoothness on $(0,\infty)$ does not extend to integrability of $h'$ at the boundary.

## The Key Insight

Every $x$-derivative of the kernel is
$$\partial_x^k\frac{1}{x+y}=\frac{(-1)^k\,k!}{(x+y)^{k+1}},$$
and on the half-line $x\ge a>0$ this is bounded by the *constant* $\frac{k!}{a^{k+1}}$ times nothing — so against $f$ it is dominated by $\frac{k!}{a^{k+1}}|f(y)|\in L^1(dy)$. That single uniform-in-$x$, integrable bound does **all** the work: it licenses differentiation under the integral (giving $C^\infty$), and with $k=1$ the same monotone structure gives, via Tonelli,
$$\int_a^\infty|h'(x)|\,dx\le\int_0^\infty\frac{|f(y)|}{a+y}\,dy\le\frac{\|f\|_1}{a}.$$
The factor $1/a$ is the tell: it is finite for every $a>0$ but blows up as $a\downarrow0$ — exactly forecasting that $h'$ need not be integrable near the origin.

## Complete Proof

Throughout, $f\in L^1((0,\infty))$ with $\|f\|_1=\int_0^\infty|f|<\infty$, and $h(x)=\int_0^\infty\frac{f(y)}{x+y}\,dy$ for $x>0$.

### Step 0 — $h$ is well-defined

For $x>0$ and $y>0$ we have $x+y\ge x$, so
$$|h(x)|\le\int_0^\infty\frac{|f(y)|}{x+y}\,dy\le\frac1x\int_0^\infty|f(y)|\,dy=\frac{\|f\|_1}{x}<\infty.$$
Thus the defining integral converges absolutely for each $x>0$.

### Step 1 — $h\in C^\infty(0,\infty)$ via differentiation under the integral

The kernel $K(x,y)=\frac1{x+y}$ is smooth in $x$ on $(0,\infty)$ for each fixed $y>0$, with
$$\partial_x^k K(x,y)=\frac{(-1)^k\,k!}{(x+y)^{k+1}},\qquad k=0,1,2,\dots$$
Fix any $a>0$. For all $x\ge a$ and all $y>0$ we have $x+y\ge a$, hence the **uniform, integrable domination**
$$\Big|\partial_x^k K(x,y)\,f(y)\Big|=\frac{k!}{(x+y)^{k+1}}|f(y)|\le\frac{k!}{a^{k+1}}\,|f(y)|=:G_k(y),\qquad \int_0^\infty G_k=\frac{k!}{a^{k+1}}\|f\|_1<\infty. \tag{$\ast$}$$
The standard theorem on differentiation under the integral sign (Leibniz rule, justified by $(\ast)$ and dominated convergence on difference quotients) then applies inductively: $h$ is $k$-times differentiable on $(a,\infty)$ for every $k$, with
$$h^{(k)}(x)=\int_0^\infty\frac{(-1)^k\,k!}{(x+y)^{k+1}}\,f(y)\,dy. \tag{1}$$
Since $a>0$ was arbitrary, this holds on all of $(0,\infty)$, so $h\in C^\infty(0,\infty)$. In particular, taking $k=1$,
$$h'(x)=-\int_0^\infty\frac{f(y)}{(x+y)^2}\,dy. \tag{2}$$

### Step 2 — $h'\in L^1([a,\infty))$ for each $a>0$

Fix $a>0$. Using $(2)$ and the triangle inequality for integrals,
$$\int_a^\infty|h'(x)|\,dx=\int_a^\infty\left|\int_0^\infty\frac{f(y)}{(x+y)^2}\,dy\right|dx\le\int_a^\infty\!\!\int_0^\infty\frac{|f(y)|}{(x+y)^2}\,dy\,dx.$$
The integrand is nonnegative and measurable, so **Tonelli's theorem** permits swapping the order of integration:
$$\int_a^\infty|h'(x)|\,dx\le\int_0^\infty|f(y)|\left(\int_a^\infty\frac{dx}{(x+y)^2}\right)dy.$$
The inner integral evaluates explicitly:
$$\int_a^\infty\frac{dx}{(x+y)^2}=\left[-\frac{1}{x+y}\right]_{x=a}^{x=\infty}=\frac{1}{a+y}.$$
Therefore
$$\int_a^\infty|h'(x)|\,dx\le\int_0^\infty\frac{|f(y)|}{a+y}\,dy\le\frac1a\int_0^\infty|f(y)|\,dy=\frac{\|f\|_1}{a}<\infty. \tag{3}$$
Hence $h'\in L^1([a,\infty))$ for every $a>0$. $\qquad\checkmark$

### Step 3 — The case $a=0$: the conclusion fails

Setting $a=0$ in the computation of Step 2 (the inner integral becomes $\int_0^\infty(x+y)^{-2}\,dx=1/y$) gives the bound
$$\int_0^\infty|h'(x)|\,dx\le\int_0^\infty\frac{|f(y)|}{y}\,dy,$$
and this majorant **diverges** for typical $f\in L^1$, because $1/y$ is not integrable against mass concentrated near $y=0$. The bound is not merely lost — $h'$ genuinely fails to be integrable on $(0,\infty)$, as the following witness shows.

**Counterexample.** Take $f=\mathbf 1_{(0,1)}$, so $f\in L^1$ with $\|f\|_1=1$. Then
$$h(x)=\int_0^1\frac{dy}{x+y}=\ln(x+1)-\ln x=\ln\frac{x+1}{x},$$
and differentiating directly,
$$h'(x)=\frac{1}{x+1}-\frac1x=\frac{-1}{x(x+1)}.$$
(Consistent with $(2)$.) Now near $x=0$, $|h'(x)|=\dfrac{1}{x(x+1)}\sim\dfrac1x$, which is **not integrable** at the origin:
$$\int_0^\infty|h'(x)|\,dx=\int_0^\infty\frac{dx}{x(x+1)}=\int_0^\infty\Big(\frac1x-\frac1{x+1}\Big)dx=\Big[\ln\tfrac{x}{x+1}\Big]_0^\infty=+\infty.$$
By contrast, for any $a>0$, $\int_a^\infty\frac{dx}{x(x+1)}=\ln\frac{a+1}{a}<\infty$, in agreement with $(3)$.

**Conclusion for $a=0$.** Although $h$ is smooth on $(0,\infty)$ and $h'\in L^1([a,\infty))$ for every $a>0$, the derivative $h'$ need **not** belong to $L^1((0,\infty))$: it can blow up like $1/x$ as $x\to0^+$. The constant $\|f\|_1/a$ in $(3)$ already signals this — it is finite for each $a>0$ but diverges as $a\downarrow0$. $\qquad\blacksquare$

### Remark — where the mass near $0$ goes

The obstruction at $a=0$ is precisely that $h'$ inherits a boundary singularity from the kernel: $\int_0^\infty\frac{dx}{(x+y)^2}=\frac1y$, so the "total variation budget" of $h'$ is $\int_0^\infty\frac{|f(y)|}{y}\,dy$, weighting $f$ by $1/y$. Any $L^1$ function with non-negligible mass near $y=0$ (like the indicator above) makes that budget infinite. Cutting off at $a>0$ replaces $1/y$ by $1/(a+y)\le1/a$, taming the singularity and restoring integrability on the tail.

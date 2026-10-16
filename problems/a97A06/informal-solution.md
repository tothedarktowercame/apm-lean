
**Why it's hard:** The integrand $\sin^{2}(x)/x^{2}$ is even and integrable on $\mathbb{R}$, but the related complex integrand $e^{2iz}/z^{2}$ has a double pole at $z = 0$, so direct contour integration of $e^{2iz}/z^{2}$ fails. The clever choice $(e^{2iz} - 1 - 2iz)/z^{2}$ removes the pole entirely (Taylor expansion gives $e^{2iz} - 1 - 2iz = -2z^{2} - (4i/3)z^{3} + \ldots$, so the integrand is analytic at 0).

**The key insight:** The function $F(z) = (e^{2iz} - 1 - 2iz)/z^{2}$ is entire (the numerator vanishes to order 2 at 0). Integrating $F$ over a large semicircle in the upper half-plane, the contour integral is zero by Cauchy's theorem. The arc contribution requires careful estimation: $e^{2iz}$ on the arc decays exponentially (Jordan's lemma territory) but the $-1 - 2iz$ terms don't — they contribute the answer.

**Proof:**

Let $F(z) = (e^{2iz} - 1 - 2iz)/z^{2}$. Since $e^{2iz} - 1 - 2iz = -2z^{2} + O(z^{3})$ near $z = 0$, $F$ extends to an entire function on $\mathbb{C}$.

**Step 1: Express the target integral via $F$.**

For $x \in \mathbb{R}$, $x \neq 0$:
$$F(x) = \frac{e^{2ix} - 1 - 2ix}{x^2} = \frac{\cos(2x) - 1 + i(\sin(2x) - 2x)}{x^2}$$

Using $\cos(2x) - 1 = -2\sin^{2}(x)$:
$$\Re F(x) = \frac{-2\sin^2(x)}{x^2}, \quad \Im F(x) = \frac{\sin(2x) - 2x}{x^2}$$

So:
$$\int_{-\infty}^\infty \Re F(x)\,dx = -2 \int_{-\infty}^\infty \frac{\sin^2(x)}{x^2}\,dx = -4\int_0^\infty \frac{\sin^2(x)}{x^2}\,dx$$

(The last equality uses that $\sin^{2}(x)/x^{2}$ is even.)

**Step 2: Contour integral.**

Consider the contour $\Gamma_R$: the segment from $-R$ to $R$ on the real axis, followed by the upper semicircle $C_R$ of radius $R$ centered at 0. $F$ is entire, so by Cauchy's theorem:
$$\oint_{\Gamma_R} F(z)\,dz = 0$$

Therefore:
$$\int_{-R}^R F(x)\,dx = -\int_{C_R} F(z)\,dz$$

**Step 3: Evaluate the arc integral.**

Split the arc integrand:
$$\int_{C_R} F(z)\,dz = \int_{C_R} \frac{e^{2iz}}{z^2}\,dz - \int_{C_R} \frac{1}{z^2}\,dz - \int_{C_R} \frac{2i}{z}\,dz$$

*First piece:* On $C_R$, parameterize $z = Re^{i\theta}$, $0 \leq \theta \leq \pi$. Then $|e^{2iz}| = e^{-2R\sin \theta}$, and $|dz/z^{2}| = d\theta/R$. So
$$\left|\int_{C_R} \frac{e^{2iz}}{z^2}\,dz\right| \leq \int_0^\pi \frac{e^{-2R\sin\theta}}{R}\,d\theta \leq \frac{\pi}{R} \to 0$$

(Using Jordan's lemma or just $\sin \theta \geq 0$ on $[0,\pi]$.)

*Second piece:* Direct antiderivative,
$$\int_{C_R} \frac{1}{z^2}\,dz = \left[-\frac{1}{z}\right]_{R}^{-R} = -\frac{1}{-R} + \frac{1}{R} = \frac{2}{R} \to 0$$

*Third piece:* This is the only piece that doesn't vanish.
$$\int_{C_R} \frac{1}{z}\,dz = \int_0^\pi \frac{iRe^{i\theta}}{Re^{i\theta}}\,d\theta = i\pi$$

So $\int_{C_R} \frac{2i}{z}\,dz = 2i \cdot i\pi = -2\pi$.

Combining: as $R \to \infty$,
$$\int_{C_R} F(z)\,dz \to 0 - 0 - (-2\pi) = 2\pi$$

**Step 4: Take the limit.**

$$\int_{-\infty}^\infty F(x)\,dx = \lim_{R \to \infty}\int_{-R}^R F(x)\,dx = -\lim_{R \to \infty}\int_{C_R} F(z)\,dz = -2\pi$$

Taking real parts:
$$\int_{-\infty}^\infty \Re F(x)\,dx = -2\pi$$

From Step 1:
$$-4\int_0^\infty \frac{\sin^2(x)}{x^2}\,dx = -2\pi \implies \int_0^\infty \frac{\sin^2(x)}{x^2}\,dx = \frac{\pi}{2}$$

∎

**What connects:** This is a textbook contour-integration exercise that illustrates the "subtraction trick": when the natural integrand has a pole, subtract enough Taylor terms to remove it, then recover the correct value by carefully tracking what each subtracted term contributes to the contour integral. The same trick evaluates $\int_{0}^\infty \sin(x)/x\, dx = \pi/2$ (use $(e^{iz} - 1)/z$, removing the pole at 0, with arc $\to -i\pi$ on the upper semicircle), and more generally yields $\int_{0}^\infty \sin^n(x)/x^n\, dx$ for various $n$. The answer $\pi/2$ is a special value: $\int_{-\infty}^\infty (\sin(x)/x)^{2}\, dx = \pi$ is also Plancherel applied to the indicator of $[-1,1]$, whose Fourier transform is $2\sin(\xi)/\xi$.


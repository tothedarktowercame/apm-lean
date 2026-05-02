
**Why it's hard:** The integrand sin²(x)/x² is even and integrable on ℝ, but the related complex integrand e^{2iz}/z² has a double pole at z = 0, so direct contour integration of e^{2iz}/z² fails. The clever choice (e^{2iz} - 1 - 2iz)/z² removes the pole entirely (Taylor expansion gives e^{2iz} - 1 - 2iz = -2z² - (4i/3)z³ + ..., so the integrand is analytic at 0).

**The key insight:** The function F(z) = (e^{2iz} - 1 - 2iz)/z² is entire (the numerator vanishes to order 2 at 0). Integrating F over a large semicircle in the upper half-plane, the contour integral is zero by Cauchy's theorem. The arc contribution requires careful estimation: e^{2iz} on the arc decays exponentially (Jordan's lemma territory) but the -1 - 2iz terms don't — they contribute the answer.

**Proof:**

Let F(z) = (e^{2iz} - 1 - 2iz)/z². Since e^{2iz} - 1 - 2iz = -2z² + O(z³) near z = 0, F extends to an entire function on ℂ.

**Step 1: Express the target integral via F.**

For x ∈ ℝ, x ≠ 0:
$$F(x) = \frac{e^{2ix} - 1 - 2ix}{x^2} = \frac{\cos(2x) - 1 + i(\sin(2x) - 2x)}{x^2}$$

Using cos(2x) - 1 = -2sin²(x):
$$\Re F(x) = \frac{-2\sin^2(x)}{x^2}, \quad \Im F(x) = \frac{\sin(2x) - 2x}{x^2}$$

So:
$$\int_{-\infty}^\infty \Re F(x)\,dx = -2 \int_{-\infty}^\infty \frac{\sin^2(x)}{x^2}\,dx = -4\int_0^\infty \frac{\sin^2(x)}{x^2}\,dx$$

(The last equality uses that sin²(x)/x² is even.)

**Step 2: Contour integral.**

Consider the contour Γ_R: the segment from -R to R on the real axis, followed by the upper semicircle C_R of radius R centered at 0. F is entire, so by Cauchy's theorem:
$$\oint_{\Gamma_R} F(z)\,dz = 0$$

Therefore:
$$\int_{-R}^R F(x)\,dx = -\int_{C_R} F(z)\,dz$$

**Step 3: Evaluate the arc integral.**

Split the arc integrand:
$$\int_{C_R} F(z)\,dz = \int_{C_R} \frac{e^{2iz}}{z^2}\,dz - \int_{C_R} \frac{1}{z^2}\,dz - \int_{C_R} \frac{2i}{z}\,dz$$

*First piece:* On C_R, parameterize z = Re^{iθ}, 0 ≤ θ ≤ π. Then |e^{2iz}| = e^{-2R\sin θ}, and |dz/z²| = dθ/R. So
$$\left|\int_{C_R} \frac{e^{2iz}}{z^2}\,dz\right| \leq \int_0^\pi \frac{e^{-2R\sin\theta}}{R}\,d\theta \leq \frac{\pi}{R} \to 0$$

(Using Jordan's lemma or just sin θ ≥ 0 on [0,π].)

*Second piece:* Direct antiderivative,
$$\int_{C_R} \frac{1}{z^2}\,dz = \left[-\frac{1}{z}\right]_{R}^{-R} = -\frac{1}{-R} + \frac{1}{R} = \frac{2}{R} \to 0$$

*Third piece:* This is the only piece that doesn't vanish.
$$\int_{C_R} \frac{1}{z}\,dz = \int_0^\pi \frac{iRe^{i\theta}}{Re^{i\theta}}\,d\theta = i\pi$$

So $\int_{C_R} \frac{2i}{z}\,dz = 2i \cdot i\pi = -2\pi$.

Combining: as R → ∞,
$$\int_{C_R} F(z)\,dz \to 0 - 0 - (-2\pi) = 2\pi$$

**Step 4: Take the limit.**

$$\int_{-\infty}^\infty F(x)\,dx = \lim_{R \to \infty}\int_{-R}^R F(x)\,dx = -\lim_{R \to \infty}\int_{C_R} F(z)\,dz = -2\pi$$

Taking real parts:
$$\int_{-\infty}^\infty \Re F(x)\,dx = -2\pi$$

From Step 1:
$$-4\int_0^\infty \frac{\sin^2(x)}{x^2}\,dx = -2\pi \implies \int_0^\infty \frac{\sin^2(x)}{x^2}\,dx = \frac{\pi}{2}$$

∎

**What connects:** This is a textbook contour-integration exercise that illustrates the "subtraction trick": when the natural integrand has a pole, subtract enough Taylor terms to remove it, then recover the correct value by carefully tracking what each subtracted term contributes to the contour integral. The same trick evaluates ∫₀^∞ sin(x)/x dx = π/2 (use (e^{iz} - 1)/z, removing the pole at 0, with arc → -iπ on the upper semicircle), and more generally yields ∫₀^∞ sin^n(x)/x^n dx for various n. The answer π/2 is a special value: ∫_{-∞}^∞ (sin(x)/x)² dx = π is also Plancherel applied to the indicator of [-1,1], whose Fourier transform is 2sin(ξ)/ξ.


# APM t99J06: A 2-form on a cone

Read the displayed form literally. Since $dz\wedge dz=0$, its last term
vanishes and

$$
\alpha=(z^2+2xz+4)\,dx\wedge dy+(x-x^2)\,dy\wedge dz.
$$

Taking the exterior derivative gives

$$
d\alpha=(2z+2x)\,dx\wedge dy\wedge dz
 +(1-2x)\,dx\wedge dy\wedge dz
 =(2z+1)\,dx\wedge dy\wedge dz.
$$

Parametrize the cone by

$$
\Phi(\theta,z)=((1-z)\cos\theta,(1-z)\sin\theta,z),
\quad0\leq\theta\leq2\pi,quad0\leq z\leq1.
$$

With the parameter orientation $d\theta\wedge dz$,
$\Phi^*(dx\wedge dy)=(1-z)d\theta\wedge dz$, which has the orientation
required in the question. Also
$\Phi^*(dy\wedge dz)=(1-z)\cos\theta\,d\theta\wedge dz$. Substitution gives

$$
\int_C\alpha=\int_0^1\int_0^{2\pi}
\left[(z^2+2z(1-z)\cos\theta+4)(1-z)
+((1-z)\cos\theta-(1-z)^2\cos^2\theta)(1-z)\cos\theta\right]d\theta dz.
$$

The terms with an odd power of $\cos\theta$ integrate to zero, while
$\int_0^{2\pi}\cos^2\theta\,d\theta=\pi$. Hence

$$
\int_C\alpha=int_0^1
\left[2\pi(1-z)(z^2+4)+\pi(1-z)^2\right]dz
=\boxed{\frac{9\pi}{2}}.
$$

The source may contain a typographical error in the final wedge term; if a
nonzero term such as $dx\wedge dz$ was intended, both answers would change.
The calculation above does not silently repair the printed formula.

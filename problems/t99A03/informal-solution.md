# APM t99A03: Fixed points on a wedge and a connected sum

## Four projective planes joined at a point

Let $W=\bigvee_{1}^{4}\mathbb{RP}^2$. With rational coefficients its only
nonzero homology group is $H_0(W;\mathbb Q)\cong\mathbb Q$, since the positive
dimensional homology of $\mathbb{RP}^2$ is torsion. Therefore every self-map
$h:W\to W$ has Lefschetz number

$$
L(h)=\operatorname{tr}(h_*|H_0)=1.
$$

The Lefschetz fixed-point theorem implies that every self-map of $W$ has a
fixed point.

## Four projective planes joined by connected sum

Let $N_4=\#^4\mathbb{RP}^2$. Not every self-map of $N_4$ has a fixed point.
Construct a connected double cover of $N_3=\#^3\mathbb{RP}^2$. Its group has
presentation

$$
\pi_1(N_3)=\langle a,b,c\mid a^2b^2c^2=1\rangle.
$$

Map this group onto $\mathbb Z/2$ by sending $a$ to the nonzero element and
$b,c$ to zero. The relation maps to zero, so this defines an index-two normal
subgroup and hence a regular double cover. The cover has Euler characteristic
$2\chi(N_3)=2(-1)=-2$. It is nonorientable because the kernel contains the
orientation-reversing loop $b$. By classification of closed surfaces, the
cover is therefore $N_4$, since $\chi(N_4)=2-4=-2$.

The nontrivial deck transformation of this double cover is a self-homeomorphism
of $N_4$ and acts freely: a deck transformation fixing one point of a connected
cover is the identity. It is thus a fixed-point-free self-map. The answers are
therefore **yes** for the wedge and **no** for the connected sum.

# Informal Solution: t96J08

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Students often try to guess a potential for $\omega$ or integrate directly on the hemisphere, but here $\omega$ is *not* closed, so there is no primitive, and parametrizing the curved surface is painful. The trick is to observe that a 2-form in $\mathbb{R}^{3}$ of the shape $x\, dy \wedge dz + y\, dx \wedge dz + z\, dx \wedge dy$ is the flux form of a vector field, so classical divergence-theorem computations apply.

**Key insight.** Write $\omega$ as the interior product of the volume form with the vector field $V=(x,-y,z)$. Then $d\omega = (\operatorname{div} V) dx \wedge dy \wedge dz = dx \wedge dy \wedge dz$, so $\omega$ is neither closed nor exact. The integral of $\omega$ over $S$ is the outward flux of $V$ across $S$, which we evaluate by closing $S$ with the flat disk and applying the divergence theorem.

**Complete proof.**
1. **Closed/exact?** Compute $d\omega$ term-by-term. Since $d(x\, dy \wedge dz)=dx \wedge dy \wedge dz$, $d(y\, dx \wedge dz)=dy \wedge dx \wedge dz=-dx \wedge dy \wedge dz$, and $d(z\, dx \wedge dy)=dz \wedge dx \wedge dy=dx \wedge dy \wedge dz$, we get $d\omega=dx \wedge dy \wedge dz \neq 0$. Hence $\omega$ is not closed and therefore not exact.
2. **Flux form.** Note that $\iota_V(dx \wedge dy \wedge dz)=x\, dy \wedge dz + y\, dx \wedge dz + z\, dx \wedge dy$ precisely when $V=(x,-y,z)$. Thus $\int_S \omega = \int_S \iota_V(\mathrm{vol})$ equals the oriented flux of $V$ through $S$.
3. **Divergence theorem.** Let $E$ be the half-ball bounded by $S$ together with the base disk $D$ in the plane $z=1$. Since $\operatorname{div} V = \partial x/\partial x + \partial(-y)/\partial y + \partial z/\partial z = 1-1+1=1$, the flux through the closed surface $S \cup D$ is $\iiint_E 1\, dV = \mathrm{Vol}(E) = (1/2)(4\pi/3)=2\pi/3$. The disk $D$, oriented downward to match the outward orientation, has unit normal $-k$, so $V \cdot (-k)=-z=-1$ on $D$, and its flux is $-\mathrm{Area}(D)=-\pi$. Therefore the flux through $S$ is $\mathrm{flux}(S \cup D)-\mathrm{flux}(D)= (2\pi/3) - (-\pi)=5\pi/3$.
4. This equals $\int_S \omega$ with the specified orientation (outward normal at $(0,0,2)$ paired with the tangent basis $(1,0,0),(0,1,0)$).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Exterior derivative computation.** Shows $d\omega=dx \wedge dy \wedge dz$, so $\omega$ is neither closed nor exact.
- **Interior product interpretation.** Recognizes $\omega$ as the flux form of $V=(x,-y,z)$ and reduces the surface integral to a vector-field flux.
- **Divergence theorem.** Converts the flux over the hemispherical cap into a volume integral minus the flux across the base disk, producing $5\pi/3$.

**Stage 3 — LEAN FORMALIZATION**

Current Mathlib support for differential forms exists, but there is no surface-integration or divergence-theorem API for curved surfaces such as hemispheres. To formalize this problem we would need (i) a definition of $\int_S \iota_V(\mathrm{vol})$ over smooth 2-surfaces, (ii) the divergence theorem relating that flux to $\iiint \operatorname{div} V$, and (iii) an orientation interface for hemispheres. Without these, `/home/joe/code/apm-lean/ApmCanaries/Frames/T96J08/Apm_v2_t96J08_1775012649049/Main.lean` merely records a TODO comment.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once surface integrals and the divergence theorem are available in Mathlib, the formal proof will align with Stage 1: compute $d\omega$, identify $\omega$ with $\iota_V(\mathrm{vol})$, apply the divergence theorem to the half-ball, subtract the disk flux, and obtain $5\pi/3$.

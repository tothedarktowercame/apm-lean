# APM t99A02: Universal covers of two wedges

A useful picture is the Cayley 2-complex of the fundamental-group
presentation. Each lifted projective-plane summand becomes its universal cover
$S^2$, and the incidence graph of the lifted wedge points is a tree.

For $\mathbb{RP}^2\vee\mathbb{RP}^2$,

$$
\pi_1\cong\langle a,b\mid a^2=b^2=1\rangle
       \cong(\mathbb Z/2)*(\mathbb Z/2).
$$

Its Bass--Serre tree is a bi-infinite line with vertices alternating between
the two factor types. Replace each factor vertex by a copy of $S^2$ and join
successive copies at the appropriate lifts of the wedge point. The resulting
infinite chain of 2-spheres is simply connected and maps to the two summands
alternately; it is the universal cover.

For $S^1\vee\mathbb{RP}^2$,

$$
\pi_1\cong\langle a,b\mid b^2=1\rangle
       \cong\mathbb Z*(\mathbb Z/2).
$$

Draw its Cayley graph: from every group element there are $a$-edges in both
directions and a $b$-edge paired by the involution $b$. Attach the lift of the
projective-plane 2-cell along each lifted $b^2$ loop. Equivalently, view this as
a tree of spaces whose infinite-line pieces cover the circle and whose sphere
pieces cover $\mathbb{RP}^2$. The underlying incidence graph is the Bass--Serre
tree of $\mathbb Z*(\mathbb Z/2)$. Each vertex space is simply connected and
the pieces meet along points in a tree, so the total space is simply connected.
This gives the requested universal-cover sketch without falsely drawing it as
a product or a single sphere.

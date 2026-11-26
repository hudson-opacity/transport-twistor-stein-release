# Ten points obstruct convex foliations on a simple four-ball

**AI contribution.** OpenAI Codex agents developed and checked the deductions from Petrunin’s construction credited below and drafted this note.

Assume the four-dimensional construction posted by Anton Petrunin on November 8, 2026. Then there is a nonempty open set of simple metrics on the four-ball for which a nested foliation by strictly convex hypersurfaces cannot cover the interior up to an empty-interior terminal set. Within this open set, an open dense subset of metrics has solenoidally injective rank-two geodesic X-ray transform, in the sufficiently high finite differentiability topology specified below. Boundary distances determine the metric locally near each such reference metric. [Petrunin’s construction, crediting Dmitry Korshunov](https://mathoverflow.net/a/516782) · [Stefanov–Uhlmann, Theorems 1.4–1.6](https://sites.math.washington.edu/~gunther/publications/Papers/jamsfinal.pdf)

## The geometric input

A simple metric has strictly convex boundary and a unique geodesic between each pair of points, depending smoothly on its endpoints. Petrunin’s November 8 modification of a construction by Dmitry Korshunov gives a smooth simple four-ball containing the spherical edges of a regular four-simplex in an equatorial $S^3\subset S^4$. The metric on an open neighborhood of their union $\Gamma$ agrees, up to constant rescaling, with the round metric. Petrunin obtains this neighborhood by putting $\Gamma$ inside a deformed hemisphere and adjusting the metric in a collar disjoint from $\Gamma$. We take his public proof sketch as the geometric input. The doubling of the vertices and the openness argument below are deductions presented here for independent review. Priority for those deductions has not been established. [Original proof sketch](https://mathoverflow.net/a/516782)

## Five directions at each vertex

Write the equatorial simplex vertices as $w_1,\ldots,w_5\in S^3\subset\mathbb R^4$. They have sum zero and $w_i\cdot w_j=\kappa=-1/4$ for $i\ne j$. In $S^4\subset\mathbb R^4\times\mathbb R$, choose the ten points
$$
p_i^\pm=(\cos t\,w_i,\ \pm\sin t).
$$
Join each point to its four neighbors in the same layer, and to its partner in the opposite layer, by the shorter great-circle arcs. As $t$ decreases to zero the same-layer arcs converge uniformly to the original simplex edges, whose endpoints are separated by less than $\pi$. The five vertical arcs shrink to the vertices. Since $\Gamma$ is compact, the finitely many arcs all lie in the round neighborhood for sufficiently small fixed $t>0$. Simplicity makes each arc the unique geodesic between its endpoints.

At $p=p_i^+$ the upward unit meridian vector is $e=(-\sin t\,w_i,\cos t)$. The outgoing tangent toward $q=p_j^+$ is a positive multiple of $q-(p\cdot q)p$. Its component along $e$, before normalization, equals
$$
q\cdot e=\sin t\cos t(1-\kappa)>0.
$$
Its horizontal component, in $w_i^\perp\times\{0\}$, is $\cos t\,(w_j-\kappa w_i,0)$. These four horizontal components sum to zero and span the three-dimensional horizontal tangent space. Indeed their pairwise differences span the affine direction space of the opposite tetrahedral face. All four unnormalized tangents have the same length. Their unit directions therefore have sum equal to a positive multiple of $e$. The fifth outgoing direction is $-e$.

It follows that the five directions span the four-dimensional tangent space and satisfy a linear relation with every coefficient strictly positive. Equivalently, the origin lies in the interior of their convex hull. Reflection gives the same conclusion at every lower vertex. Simplicity is $C^2$-open. For a fixed pair of these vertices, the geodesic equation and invertibility of the endpoint exponential derivative give continuous dependence of the initial direction on the metric in $C^2$. Interior containment in a finite convex hull persists under small perturbations. Intersecting the ten resulting neighborhoods gives one $C^2$-open set of simple metrics with this property at every vertex.

## A fixed open subset lies in every terminal set

Use the following explicit exhaustion convention. There is a continuous $h$ on the ball, with minimum $m$ and terminal set $K=\{h=m\}$. At first allow $K$ to have interior. On $\{h>m\}$ the function is $C^2$, its differential is nonzero and
$$
\nabla^2 h(v,v)>0\qquad(0\ne v\in\ker dh).
$$
Increasing $h$ points outward. This sign makes the value along a geodesic tangent to a regular leaf have a strict local minimum. An inward-increasing smooth level parameter $\rho$ with terminal value $T$ gives this convention by taking $h=-\min(\rho,T)$ whenever the indicated tangential Hessian condition holds. This also allows a single terminal point. [Convex layers in tensor tomography, Theorem 1.2](https://arxiv.org/abs/1410.5145)

Along an interior geodesic segment, $h$ cannot have an interior local maximum above $m$. At such a maximum its first derivative would be zero and its second derivative strictly positive. Choose a vertex where $h$ is largest among the ten. If its value exceeds $m$, the derivative along each outgoing edge must be strictly negative. A positive derivative gives values above both endpoints and forces an interior maximum. A zero derivative does the same by the positive second derivative. No covector can be negative on all five directions, because a strictly positive combination of them is zero. Hence all ten vertices lie in $K$. This argument also directly excludes a globally positive-definite Hessian, by applying strict convexity along each edge at a greatest vertex.

The obstruction has a uniform form. Fix one of the ten vertices, $p$. Joint continuity of the initial directions in the metric and endpoints allows a product neighborhood $\mathcal V\times U$ of the initial metric and $p$. Here $U$ is open in the interior of the four-ball. Use a tangent frame on $U$ at the moving vertex. After shrinking both neighborhoods, for every $g\in\mathcal V$ and every $x\in U$, replacing $p$ by $x$ preserves positive spanning at all ten vertices. Fix any such $g$ and any $h$ satisfying the preceding conditions. Applying the greatest-vertex argument for each $x$ gives
$$
U\subseteq K.
$$
Both neighborhoods were chosen before $h$. Thus every exhaustion in this class leaves the same open subset of the fixed ball in its terminal set, for every metric in $\mathcal V$. In particular the class admits no exhaustion with an empty-interior terminal set there.

The same fixed open set has a consequence even for weak convexity. Let $f\in C^2$ have positive semidefinite Hessian throughout the ball. At a greatest vertex, all outgoing derivatives are nonpositive by convexity along the edges. A positive linear relation among the directions makes all these derivatives zero. On each incident edge the initial derivative is zero, the derivative is nondecreasing, and the endpoint value is at most the starting value. Thus $f$ is constant along the edge. Connectivity propagates this value to every vertex. Replace one vertex by any $x\in U$ while retaining a second, fixed vertex. It follows that **every such $f$ is constant on $U$**. The value can depend on $f$ and the metric. Balancing here uses a separate positive relation at each vertex. The proof requires no edge weights shared by neighboring vertices.

## What the boundary data determine

For sufficiently large $k$, intersect the open set above with the $C^k$-open dense set of simple metrics for which vanishing geodesic integrals of a symmetric two-tensor imply that it is $d^s u$ for a one-form $u$ zero on the boundary. The intersection is open and dense relative to our set. It also contains smooth examples, including analytic approximations in fixed ball coordinates. At the differentiability order in Stefanov–Uhlmann’s local theorem, any two metrics sufficiently close to the same reference metric in this intersection, with equal boundary distances, differ by a boundary-fixing diffeomorphism. The argument leaves injectivity at Petrunin’s particular metric and rigidity for arbitrary simple metrics undecided. [Stefanov–Uhlmann, Theorems 1.4–1.6](https://sites.math.washington.edu/~gunther/publications/Papers/jamsfinal.pdf)

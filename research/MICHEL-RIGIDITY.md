# Michel’s boundary rigidity conjecture

**Status, November 24, 2026.** The general higher-dimensional conjecture remains open in the literature we located. The arguments here establish an obstruction to one proof strategy and explain where two other strategies need additional information. The companion note gives the proof of the obstruction. [Ten points obstruct convex foliations](RIGIDITY-NET.md)

## The question and the state of the problem

Imagine placing synchronized instruments at every point on the boundary of a body. For each pair, one measures the first travel time. Michel asked whether these measurements determine a simple Riemannian metric. A simple metric has strictly convex boundary and a unique minimizing geodesic between points that depends smoothly on its endpoints, with no conjugate points. For two smooth simple metrics on the same compact manifold, the conjectured implication is
$$
d_g(a,b)=d_h(a,b)\quad(a,b\in\partial M)
\quad\Longrightarrow\quad h=F^*g,\qquad F|_{\partial M}=\operatorname{id}.
$$
A change of interior coordinates fixing the boundary preserves every measurement. The question is whether this is the full ambiguity. [Michel, *Inventiones Mathematicae*](https://doi.org/10.1007/BF01389295)

Pestov and Uhlmann proved the surface case. In dimension at least three, Burago and Ivanov proved global rigidity near a flat reference metric. Stefanov, Uhlmann and Vasy proved recovery in a collar and global results under a convexity hypothesis. Stefanov and Uhlmann proved local rigidity near generic simple reference metrics. Here “local” refers to how close the competing metrics are, whereas a collar result describes which spatial region is recovered. [Surface theorem](https://annals.math.princeton.edu/2005/161-2/p12) · [Near-flat theorem](https://annals.math.princeton.edu/2010/171-2/p10) · [Convexity theorem](https://annals.math.princeton.edu/2021/194-1/p01) · [Generic local theorem](https://arxiv.org/abs/math/0408075)

## A robust obstruction to peeling by convex layers

A proposed route would apply the global convex-layer theorem to every simple metric. A 2026 paper described establishing this geometric hypothesis in full generality as a route to Michel’s conjecture. On November 8, Anton Petrunin posted a four-dimensional construction, crediting Dmitry Korshunov, of a simple ball with a geodesic network obstructing a global strictly convex function. We use the author's posted geometric construction as an input. [Ilmavirta, Saksala and Yan, introduction](https://arxiv.org/html/2602.08860v1) · [Petrunin’s construction](https://mathoverflow.net/questions/511201/geodesic-nets-in-simple-manifolds/516782)

Our deduction strengthens this obstruction to an open family. There is a common open subset of the four-ball that every single nested exhaustion of the specified kind leaves in its terminal set, for all metrics in a neighborhood of the constructed metric. The conclusion concerns a global level function, regular off its minimum set and with strictly positive tangential Hessian there. In fact, every smooth function with positive semidefinite Hessian everywhere is constant on that same open set. Other reconstruction methods can still see this region. Indeed, by the generic theorem, metrics with local boundary rigidity are relatively open and dense in this family in sufficiently high regularity. No priority has been established for the strengthening. [Construction, quantifiers, and proof](RIGIDITY-NET.md)

The geometric point is to replace five equatorial simplex vertices by two nearby copies. Join each vertex to four neighbors in its layer and to its partner across the layers. At every vertex the outgoing geodesic directions surround the origin in the full four-dimensional tangent space. This persists under perturbing the metric or moving a vertex. A convex level function cannot have a regular maximum on an edge or at a vertex. The same conclusion applies after moving the chosen vertex anywhere in a small fixed neighborhood, putting that whole neighborhood into the terminal set.

## Can the rays determine the interior points?

Differentiating the measured distance at its two endpoints gives the tangential initial and final unit covectors of the geodesic, by the first variation of length. The induced boundary metric is known from short boundary distances. Thus the data determine the incoming covector, its outgoing partner, and elapsed travel time. In the interior of the unit cotangent bundle, entering covector and time since entry are smooth coordinates along these rays. Matching the two metrics in those coordinates gives a map $C$ intertwining their flows. It preserves the contact form: writing the incoming footpoint as $a$, the tangential covector as $\eta$, and the time as $t$, the tautological form in these coordinates is $dt+\eta\,da$. This follows from invariance under geodesic flow and its value one on the unit-speed flow generator.

If all covectors over an interior point $x$ were carried to covectors over one common point $F(x)$, preservation of the tautological form would give $(dF_x)^*\xi'=\xi$ for every matched pair. The unit cotangent spheres would match by a linear isometry, giving $F^*h=g$. The local isometry, together with the boundary labeling and covering argument, yields the required boundary-fixing isometry. The missing step is to recover this common-footpoint property from the data and the fact that the two norms are Riemannian.

Even a strong triangle test fails to recognize common footpoints. On the Euclidean unit sphere let $a(\omega)=\varepsilon\omega_1^3$ and put
$$
f(p)=\max_{|\omega|=1}\{p\cdot\omega-a(\omega)\}.
$$
For all sufficiently small nonzero $\varepsilon$, this is a smooth positive function on the sphere. Oddness gives $f(p)+f(q)\ge |p-q|$. Each $p$ has a unique partner attaining equality. To see this, any maximizing $\omega$ has $p\cdot\omega>0$ by comparison with $\omega=p$. Stationarity then gives
$$
p=P(\omega)=\nabla_S a(\omega)+\sqrt{1-|\nabla_Sa(\omega)|^2}\,\omega.
$$
The map $P$ is $C^1$-close to the identity, hence a local diffeomorphism of degree one and a diffeomorphism. The maximizing direction depends smoothly on $p$. The partner of $P(\omega)$ is $P(-\omega)$, since the embedded spherical gradients agree at antipodes and the joining chord points along $\omega$. Conversely equality forces the maximizing directions to be opposite to one another along that chord. If $f$ were distance from one point $x$, equality in the Euclidean triangle inequality would put $x$ on every paired chord. Projecting onto $\omega^\perp$ yields $\nabla_S a(\omega)=\operatorname{proj}_{\omega^\perp}x$. Therefore $a(\omega)-x\cdot\omega$ is constant, contradicting our odd nonlinear choice. This rules out a proposed recognition test even with smooth data and unique partners. The Euclidean ball itself is rigid.

## What length and energy comparisons actually give

Let $g$ be simple on $M$, and let a smooth map $F$ into a second manifold $(N,h)$ identify the labeled boundaries. Suppose its target boundary distances are at least the corresponding $g$-distances. Write $d\Sigma_g=dV_g\,d\omega_x$ on the unit tangent bundle, using probability measure on each unit sphere. Then
$$
\int_{S_gM} (|dF(v)|_h-1)^2\,d\Sigma_g
\ \le\
\frac1n\int_M\operatorname{tr}_g(F^*h)\,dV_g-\operatorname{Vol}_g(M).
$$
For each complete unit-speed $g$-chord, the image length is at least the distance of its endpoints, hence at least the chord length. Santaló's formula integrates these inequalities to give $\int(|dF(v)|_h-1)\,d\Sigma_g\ge0$. Expanding the square and averaging the quadratic term in each tangent sphere proves the estimate. Equality of the normalized Dirichlet energy with $\operatorname{Vol}_g(M)$ forces $dF$ to preserve the norm of every tangent vector.

There is an instructive positive test with Euclidean target. Suppose $\partial M$ is identified with the unit sphere and the boundary distances are the Euclidean chord lengths. Each Euclidean coordinate on the sphere is 1-Lipschitz for this boundary metric. Its infimum extension $\inf_{p\in\partial M}(p_i+d_g(x,p))$ is 1-Lipschitz on $M$. Take the smooth harmonic extension $F_i$ with the same boundary values. By Dirichlet minimization each $\int |dF_i|^2\le\operatorname{Vol}_g(M)$. Summing constructs exactly the upper bound the preceding inequality needs. The harmonic map $F=(F_i)$ has image in the closed ball by the maximum principle applied to linear functionals. Its differential is isometric. It is proper, is the identity on the boundary, and maps the interior onto the open ball as a one-sheeted covering, hence is a global isometry. This recovers a known rigidity case. With a general curved target the coordinate extensions land in a Euclidean space, where a chord between endpoint images can be shorter than the distance inside the target. The argument gives no sharp upper bound for a map into that target.

## Linearization and the remaining gap

For a smooth variation $g_t=g+tk+O(t^2)$ at a simple metric and distinct boundary endpoints,
$$
\left.\frac d{dt}\right|_{t=0}d_{g_t}(a,b)
=\tfrac12\int_{\gamma_{ab}}k(\dot\gamma,\dot\gamma)\,ds_g .
$$
The stationarity of the reference geodesic removes the first-order path variation. If $k$ is a symmetrized covariant derivative of a one-form vanishing on the boundary, the integral vanishes by the fundamental theorem of calculus. Proving these are the only invisible tensors on **every** simple manifold in dimension at least three is itself open. The published generic and curvature-dependent estimates do not give that conclusion. Even general infinitesimal uniqueness would still require a nonlinear argument for an arbitrarily separated pair. [Rank-two energy estimates](https://www.repository.cam.ac.uk/bitstream/1810/247258/1/Paternain%20et%20al%202015%20Mathematische%20Annalen.pdf) · [Status in §1 of Holman and Krishnan](https://doi.org/10.1007/s12220-025-02136-8)

The robust network concerns the reach of a reconstruction method. A disproof of Michel would require two simple Riemannian metrics with exactly equal boundary distances and no boundary-fixing isometry between them. A proof would have to rule out every such pair. Neither conclusion follows from these arguments.

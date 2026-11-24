# Stein interiors of transport twistor spaces on simple surfaces

Hudson Headley

Research manuscript · 24 November 2026

For every simple conformal disk, Lean constructs a smooth exhaustion of the full transport twistor interior with a positive definite Levi form everywhere. Grauert’s solution of the Levi problem then gives Steinness. The construction of the exhaustion and its identification with the physical transport equations are checked in Lean. The application of Grauert’s theorem and the passage from an abstract surface to a global isothermal disk use the cited mathematical results. Lean also proves the three ordinary Stein properties for every open base subdomain by constructing holomorphic divisors. [Universal chart and complex-manifold theorems](TransportOkaGrauert/GeneralStein.lean) [Strict exhaustion](TransportOkaGrauert/PhysicalSteinStrict.lean) · [Grauert](https://doi.org/10.2307/1970257) · [Global isothermal coordinates, Theorems 3.4.15–16](https://users.jyu.fi/~salomi/lecturenotes/GIP2D_driver.pdf) · [Formal verification status](STEIN-FORMALIZATION.md)

**AI assistance and review.** Multiple OpenAI Codex agents developed the mathematical arguments, generated the Lean formalization and helped draft this manuscript. No independent human mathematical review is recorded.

## 1. The question and the theorem

Let $(M,g)$ be a smooth compact oriented simple Riemannian surface. Write $Z=\{(x,v)\in TM:|v|_g\leq1\}$ for its transport twistor space and $Y=\{(x,v)\in Z:x\in M^\circ,\ |v|_g<1\}$ for the interior, equipped with the transport complex structure. In particular, the inclusion of each open velocity disk is a holomorphic embedding. Jan Bohr asked whether $Y$ is Stein for every such metric. The earlier flat-domain proof appears in Bohr and Paternain, Lemma 4.10. [Bohr, final slide](https://www.math.uni-bonn.de/people/bohr/linz22_twistor.pdf) · [Bohr and Paternain, §1.2 and §4.4](https://doi.org/10.5802/jep.231)

**Theorem.** $Y$ is a Stein surface. More generally, for every nonempty connected open set $U\subset M^\circ$, the part $Y_U=\{(x,v):x\in U,\ |v|_g<1\}$ is Stein with its induced complex structure.

The first proof constructs one holomorphic function $F_p$ for each $p\in M$. Its zeros pick out the velocity disk over $p$ in the interior and the geodesics through $p$ on the unit tangent bundle. A second proof in §§6–9 uses the scalar Jacobi equation, a boundary Levi form and the area of projected complex curves. It does not require the transport integrating-factor theorem.

**A geometric identity.** Fix $p\in M$. On a slightly larger simple surface containing $M$ in its interior, set

$$s(x)=\tfrac12 d(p,x)^2,\qquad V=\nabla s,\qquad J=\text{rotation through }+\pi/2.$$

Simplicity gives a unique minimizing geodesic depending smoothly on its endpoints. Squared distance is smooth through $p$ by normal coordinates. With this enlargement all calculations at boundary points are ordinary two-sided calculations. For points of $M$ the connecting geodesic agrees with the one in $M$ by uniqueness. [Paternain, Salo and Uhlmann, Theorem 3.8.2 and Propositions 3.8.6–7](https://users.jyu.fi/~salomi/lecturenotes/GIP2D_driver.pdf)

There is a smooth real function $c=c_p$ on $M$ such that, for every tangent vector $u$,

$$\nabla_u V=u+c\langle JV,u\rangle JV. \tag{1}$$

Indeed, $|V|^2=2s$ and $\nabla V$ is self-adjoint. Differentiating gives $(\nabla V)V=V$. Away from $p$ the symmetric endomorphism $T=\nabla V-I$ annihilates $V$ and is therefore a smooth multiple of $JV\otimes(JV)^\flat$. At $p$, normal coordinates give $V(p)=0$ and $\nabla V(p)=I$. In a smooth oriented orthonormal frame the components $(a,b)$ of $V$ are therefore local coordinates at $p$. Write the matrix of $T$ as $\left(\begin{smallmatrix}l&m\\m&n\end{smallmatrix}\right)$. From $la+mb=ma+nb=0$ we get $m(a,0)=m(0,b)=0$. Two applications of smooth coordinate division give $m=abB$ with $B$ smooth. The same equations give $l=-b^2B$ and $n=-a^2B$ by continuity. Thus $c=-B$ extends smoothly through $p$, proving (1).

## 2. A holomorphic function for each geodesic pencil

Choose a global oriented orthonormal frame $(e_1,e_2)$ on $M$, which is diffeomorphic to a disk. Write $w=V^1+iV^2$, and denote the complex coordinate of a velocity vector in the frame by $\mu$. Define a polynomial on each closed fibre by

$$q_p(x,\mu)=w(x)-\mu^2\overline{w(x)}. \tag{2}$$

On $SM=\{|v|_g=1\}$ put $\mu=e^{i\theta}$ and $b=\langle V,Jv\rangle$. Then $q_p=2i\mu b$. Let $X$ be the unit-speed geodesic vector field and let $\omega$ be the real connection one-form specified by $\nabla e_1=\omega e_2$. Parallel transport gives $X\mu=-i\omega(v)\mu$. Along a geodesic, $Jv$ is parallel. Since $\langle JV,v\rangle=-b$ and $\langle JV,Jv\rangle=\langle V,v\rangle$, equation (1) gives

$$Xb=-c\langle V,v\rangle b,\qquad Xq_p=A_p(x,v)q_p,\qquad A_p=-i\omega-cV^\flat. \tag{3}$$

Here $A_p(x,v)$ means the complex one-form evaluated at $v$. In particular its only possible angular Fourier modes are $-1$ and $1$. Equation (3) holds across all the zeros of $q_p$.

Apply the scalar case of the holomorphic integrating-factor theorem to $A_p$. It gives a smooth $H_p:SM\to\mathbb C^*$ satisfying $XH_p=-A_p H_p$, with both $H_p$ and $H_p^{-1}$ fibrewise holomorphic. Their nonnegative Fourier series extend smoothly to functions on the closed velocity disks, holomorphic in each fibre. Their product is identically one by uniqueness on the disk. In particular the extension $\widetilde H_p$ has no zeros anywhere on $Z$. [Bohr and Paternain, Definition 1.2 and Theorem 1.3](https://doi.org/10.5802/jep.231)

Now $H_pq_p$ on $SM$ is fibrewise holomorphic and $X(H_pq_p)=0$. The transport twistor correspondence makes its unique fibrewise extension holomorphic on $Y$ and smooth on $Z$. By uniqueness that extension is

$$F_p(x,\mu)=\widetilde H_p(x,\mu)\big(w(x)-\mu^2\overline{w(x)}\big). \tag{4}$$

Only the product needs to be holomorphic in the transport complex structure. [Bohr and Paternain, Proposition 4.4](https://arxiv.org/pdf/2108.05125)

For $|\mu|<1$, $|w-\mu^2\bar w|\geq(1-|\mu|^2)|w|$. Thus $F_p=0$ exactly when $x=p$. For $|\mu|=1$, (2) gives $F_p=0$ exactly when $\langle V,Jv\rangle=0$. For $x\ne p$ this means $v$ is tangent to the geodesic joining $p$ and $x$, in either orientation. At $x=p$ all directions occur.

## 3. Holomorphic convexity and Steinness

Fix a compact nonempty set $K\subset Y_U$. Its holomorphic hull consists of the $z\in Y_U$ satisfying $|f(z)|\leq\max_K|f|$ for every $f\in\mathcal O(Y_U)$. We show that every point $z_*=(x_*,v_*)\in\overline{Y_U}\setminus Y_U$, with the closure taken in the compact $Z$, has a neighborhood disjoint from this hull.

**Escape through the base.** If $x_*\notin U$, choose $p=x_*$. Formula (4) gives $F_p(z_*)=0$ and $F_p$ is nowhere zero on $Y_U$. This includes points where the base boundary meets the unit tangent bundle.

**Escape through a unit direction.** In the remaining case $x_*\in U$ and $|v_*|=1$. Follow the ambient geodesic from $(x_*,v_*)$ to an endpoint $p\in\partial M$. Such an endpoint exists by nontrapping. The velocity $v_*$ is parallel to the radial line from $p$, so $F_p(z_*)=0$ by (2). Since $p\notin U$, $F_p$ is nowhere zero on $Y_U$.

In either case $m_p=\min_K|F_p|>0$. Applying the hull inequality to $1/F_p\in\mathcal O(Y_U)$ gives $|F_p|\geq m_p$ on the hull. Continuity on $Z$ excludes a whole neighborhood of $z_*$ from its closure. The hull is closed in $Y_U$ by its definition, and its closure in $Z$ has no additional points. It is consequently compact. This proves holomorphic convexity. Each boundary point uses a single choice of $p$ and $H_p$.

Apply the Remmert reduction theorem to $Y_U$. It gives a proper surjection $r:Y_U\to S$ onto a Stein space with connected compact analytic fibres and $r_*\mathcal O_{Y_U}=\mathcal O_S$. Fix such a fibre $E$ and $(x,\mu)\in E$. Every holomorphic function on $Y_U$ is constant on $E$ by this sheaf identity. In particular $F_x$ vanishes on $E$, so (4) forces $E\subset\pi^{-1}(x)\cap Y_U$. This last set is an embedded holomorphic disk. The reduced analytic set underlying $E$ is analytic in that disk by restriction of local defining equations for $E$. A proper analytic subset of a disk is discrete, and the entire open disk is noncompact. Hence $E$ is finite and connected, and consists of a single point. [Remmert reduction, Theorem 9.3](https://www.math.uni-hamburg.de/home/riemenschneider/bookchap09.pdf)

The map $r$ is now a proper continuous bijection of locally compact Hausdorff spaces, hence a homeomorphism. Together with $r_*\mathcal O_{Y_U}=\mathcal O_S$, this makes it an isomorphism of complex spaces. Thus $Y_U$ is Stein. Taking $U=M^\circ$ proves the requested assertion. $\square$

## 4. Prescribing a pattern on one velocity disk

The construction also yields a boundary-regular interpolation statement. Fix $p\in M^\circ$. Every function $h$ holomorphic on the open velocity disk over $p$ and smooth on its closure is the restriction of a function holomorphic on $Y$ and smooth on $Z$ in the sense of the transport correspondence. Thus one can prescribe the full smooth trace on the fibre circle, whose negative Fourier modes vanish.

Choose an oriented orthonormal frame at $p$ and parallel transport it along the unique geodesic from $p$ to each $x$. The frame is smooth even at $p$ because in normal coordinates the transport solves a smooth linear ordinary differential equation along $t\mapsto\exp_p(t\exp_p^{-1}x)$, for $0\leq t\leq1$. Use this frame in (2)–(4). Its connection form satisfies $\omega(V)=0$, so

$$\omega=k(JV)^\flat$$

for a smooth real function $k$. To check smoothness at $p$, use the local coordinates $(a,b)$ from §1 and write $(m,n)$ for the frame components of $\omega$. The equation $ma+nb=0$ gives $m(a,0)=0$. Write $m=-bk$ by smooth division, then $n=ak$ by continuity. Away from $p$, $JV$ spans the perpendicular line and never vanishes.

Regard $h(\mu)$ as a function on all the closed velocity disks in this frame. On $SM$, $\omega(v)=k\langle JV,v\rangle=-k\langle V,Jv\rangle$. The chain rule and (2) therefore give

$$X[h(\mu)]=-i\mu h'(\mu)\omega(v)=\tfrac12 k h'(\mu)q_p.$$

The function $b_h=k h'(\mu)/(2H_p)$ on $SM$ is smooth and fibrewise holomorphic because $H_p^{-1}$ is. The unattenuated case of Bohr and Paternain’s right-inverse theorem gives a smooth fibrewise holomorphic $u$ solving $Xu=b_h$. On $SM$ the function

$$h(\mu)-uF_p$$

is thus fibrewise holomorphic and invariant under $X$. Proposition 4.4 extends it holomorphically over $Y$ and smoothly to $Z$. Since $F_p$ vanishes on the entire velocity disk over $p$, the restriction is exactly $h$. [Bohr and Paternain, Propositions 3.1 and 4.4](https://arxiv.org/pdf/2108.05125)

Taking $h(\mu)=\mu$ produces a global function $G_p$ which is a coordinate on the chosen fibre. This gives a second way to finish §3. Distinct base points are separated by a function $F_p$, and distinct velocities over one point are separated by $G_p$. At a point over $p$, $dF_p$ has real rank two in the base directions by (4) and $\nabla V(p)=I$, since $a\mapsto a-\mu^2\bar a$ is invertible for $|\mu|<1$. It vanishes in fibre directions, whereas $dG_p$ is the identity on the fibre. Hence $(F_p,G_p)$ are holomorphic local coordinates. Together with the compact-hull proof, this verifies the classical Stein axioms directly.

## 5. A strictly plurisubharmonic exhaustion

For the interior $Y$ over all of $M^\circ$, the same functions give a smooth exhaustion whose Levi form is everywhere positive definite. To ensure smooth dependence on $p$, fix a smooth oriented orthonormal frame on the simple enlargement and use its value at $p$ as the initial frame for radial parallel transport. Let $L$ be a fixed continuous linear right inverse of $X$ on smooth functions with modes $\geq-1$, with values in smooth fibrewise holomorphic functions. Proposition 3.1 supplies precisely this operator. [Bohr and Paternain, Proposition 3.1](https://arxiv.org/pdf/2108.05125)

Choose in §§2–4

$$H_p=\exp(-L A_p),\qquad u_p=L\big(k_p/(2H_p)\big),$$

and let $G_p$ be the holomorphic extension of $\mu_p-u_p F_p$, where $\mu_p$ is the velocity coordinate in this radial frame. The construction of §4 applies also for $p\in\partial M$ using the enlargement. Both $F_p(z)$ and $G_p(z)$ are jointly smooth on $M\times Z$. Indeed, radial geodesics and parallel transport depend smoothly on $(p,x)$. Near the diagonal the variables $(p,a,b)$ are coordinates. Smooth division in §§1 and 4 preserves the parameter $p$, as seen from the integral formula for division by a coordinate. The map $p\mapsto A_p$ is thus smooth in the smooth-function topology. The operator $L$ commutes with differentiation in this external parameter by linearity and continuity, and fibrewise holomorphic extension preserves joint smoothness by rapid decay of the angular Fourier coefficients with all parameter derivatives.

Using arclength $d\ell$ on $\partial M$ and Riemannian area $dA$ on $M$, define

$$\Psi(z)=\int_{\partial M}\frac{d\ell(p)}{|F_p(z)|^2}
+\int_M\big(|F_p(z)|^2+|G_p(z)|^2\big)\,dA(p).$$

On every compact subset of $Y$ the denominators are bounded away from zero uniformly in $p\in\partial M$. Both integrals may be differentiated there. Their Levi forms are nonnegative because the integrands are squared moduli of holomorphic functions. At $z=(x,v)$, $(F_x,G_x)$ form holomorphic local coordinates by §4. The two differentials remain independent for all $p$ in a neighborhood of $x$ of positive area. The second integral therefore has positive definite Levi form at $z$.

For properness, let $z_j\to z_*\in Z\setminus Y$. Section 3 provides $p_0\in\partial M$ with $F_{p_0}(z_*)=0$. Put $\delta_j=|F_{p_0}(z_j)|\to0$. On an arclength arc $p(t)$ starting at $p_0$, uniform smoothness gives $|F_{p(t)}(z_j)|\leq\delta_j+Ct$ with fixed $C>0$. The first integral dominates $\int_0^\epsilon(\delta_j+Ct)^{-2}dt$, which diverges as $j\to\infty$. Since $Z$ is compact and $\Psi\geq0$, its sublevel sets are compact in $Y$. This gives the exhaustion formulation of Steinness directly.

## 6. An intrinsic proof from the Jacobi equation

We now prove the theorem using only the definition of the transport complex structure, surface geometry and classical several complex variables. In §§6–9 write $J$ for the transport complex structure, $K$ for Gaussian curvature, $V$ for the infinitesimal positive rotation of a unit velocity, $X$ for the geodesic vector field and $H=[V,X]$. The horizontal fields $X,H$ project to a positively oriented orthonormal pair. Their brackets satisfy $[X,H]=KV$ and $[H,V]=X$. [Bohr, Lefeuvre and Paternain, equations (2.1)–(2.2)](https://arxiv.org/pdf/2301.07391)

Represent a nonzero disk velocity by $rv$, where $v$ is unit and $0<r<1$. Set $s=\log r$, $R=\partial_s$, and $t=(1-r^2)/(1+r^2)$. Then

$$JX=tH,\qquad JR=V. \tag{5}$$

Indeed, under the disk-bundle quotient the horizontal $(0,1)$ generator is $r^2(X-iH)/2+(X+iH)/2$, a positive multiple of $X+itH$. The vertical generator is proportional to $R+iV$. Thus (5) uses the complex structure in the question. [Bohr and Paternain, Lemma 4.1 and equation (4.3)](https://arxiv.org/pdf/2108.05125)

**A strict Jacobi inequality on $SM$.** Enlarge $M$ slightly to a simple surface $N$ as in §1. For each $(x,v)\in SM$, follow its geodesic backwards to the boundary of $N$. The impact is transverse because $x$ lies strictly inside $N$ and its boundary is strictly convex. Thus the entrance point, incoming direction and travel time depend smoothly on $(x,v)$ by the implicit function theorem.

Along the geodesic, using arclength $\tau$ from entry, solve

$$y_\epsilon''+(K+\epsilon)y_\epsilon=0,\qquad y_\epsilon(0)=0,\qquad y_\epsilon'(0)=1.$$

For $\epsilon=0$, the scalar solution is the perpendicular Jacobi field coefficient. It is positive after entry up to each evaluation point because it starts positive and there are no conjugate points in $N$. Evaluation gives a positive smooth function on the compact set $SM$, including velocities based on $\partial M$. Smooth dependence on the data and on $\epsilon$ makes $y=y_\epsilon$ positive on all of $SM$ for a single sufficiently small $\epsilon>0$. Along any flow segment in $M$ the entry data stay fixed, hence

$$X^2 y+Ky=-\epsilon y. \tag{6}$$

This use of a larger disk avoids the zero initial value and any tangential entrance at the boundary of the disk of interest. [Paternain, Salo and Uhlmann, §3.8](https://users.jyu.fi/~salomi/lecturenotes/GIP2D_driver.pdf)

## 7. The Levi form at the unit tangent bundle

Let $u=-\log(1-r^2)$ and $h=-\log y$ on unit directions, extended independently of $r$ near $r=1$. Set $f=u+h$ there. With $d^cf=-df\circ J$ and $\eta=d^cf$, equation (5) gives

$$\eta(X)=-tHh,\quad \eta(H)=Xh/t,\quad \eta(R)=-Vh,\quad \eta(V)=u_s.$$

Define $A=d\eta(X,JX)$, $B=d\eta(R,JR)$, $C=d\eta(X,JR)$ and $D=d\eta(X,R)$. Since $dd^cf$ has type $(1,1)$, strict positivity in complex dimension two amounts to $B>0$ and $A-(C^2+D^2)/B>0$. Using $d\eta(P,Q)=P\eta(Q)-Q\eta(P)-\eta([P,Q])$ gives the four real entries

$$A=X^2h+t^2H^2h-tKu_s,\qquad B=u_{ss}+V^2h,$$

$$C=(1/t-t)Xh+tH(Vh),\qquad D=t_s Hh-X(Vh). \tag{7}$$

For example, the curvature contribution to $A$ is $-t\eta([X,H])=-tKu_s$. The $Xh/t$ term in $C$ comes from $[X,V]=-H$. Direct differentiation gives $t_s=t^2-1$, $tu_s=1-t$ and $t^2u_{ss}=1-t^2$.

Multiply $B$ by $t^2$ and $C,D$ by $t$. The resulting three expressions extend smoothly to $t=0$, with limits $1,Xh,0$. Also $A\to X^2h-K$. These are uniform limits on the compact $SM$. Thus $B>0$ near $t=0$ and the Schur complement extends there with value

$$X^2h-(Xh)^2-K=-\frac{X^2y+Ky}{y}=\epsilon>0. \tag{8}$$

Consequently $u+h$ is strictly plurisubharmonic in a full collar of the unit tangent bundle, even as the base tends to its boundary. Replace the directional summand by $\chi(r)h$, with a smooth cutoff equal to zero near $r=0$ and one near $r=1$. This defines a smooth function $f_0$ throughout the open disk bundle, retains (8) in the collar, and keeps $f_0-u$ uniformly bounded.

## 8. The base boundary and the corner

Let $d$ denote the inward distance to $\partial M$ on a smooth collar. Strict convexity makes its Hessian negative on tangents to the boundary, and $|\nabla d|=1$ gives $\operatorname{Hess}d(\nabla d,\cdot)=0$. For $b=d-C_0d^2$ with $C_0>0$, after shrinking the collar we have $b>0$ inside and $\operatorname{Hess} b\leq-\lambda g$ there for some $\lambda>0$.

Put $h_b=-\log b$. Since $Vh_b=0$, both $X^2b$ and $H^2b$ are the ordinary Hessian on their projected unit directions. In fact $V$ rotates velocities whereas $X,H$ parallel transport them in the respective base directions. Substituting $h_b$ into (7) and using the identities for $u_s,u_{ss}$ gives the exact Schur complement of $u+h_b$ at $0<r<1$, namely

$$-\frac{X^2b+t^2H^2b}{b}
+\frac{t^2(Xb)^2+t^4(Hb)^2}{b^2}-(1-t)K. \tag{9}$$

Here $B=u_{ss}>0$. The first term is at least $\lambda(1+t^2)/b$, so shrinking the collar once more gives strict positivity for every $r$. At $r=0$, the vertical vectors in (7) have length of order $r$. Dividing $R,V$ by $r$ gives $B/r^2\to4$ and $C/r,D/r\to0$. The horizontal entry tends to $\Delta h_b>0$. Along any fixed direction the normalized frames limit to a basis at the zero velocity. Thus strict positivity includes the zero section.

Now glue $f_0$ to $f_1=u-\log b-L$ on the collar. Choose the constant $L$ so that $f_1<f_0-1$ near its inner edge, uniformly in $r$. Near $b=0$ we have $f_1>f_0+1$, again uniformly, because $f_0-u$ is bounded. Take a smooth regularized maximum between them, equal to the larger function where the difference exceeds one, and use $f_0$ elsewhere. Such a maximum is obtained by convolving $|a-b|$ in $(a+b+|a-b|)/2$ with a small even nonnegative mollifier. It is convex and nondecreasing in each variable, and its two partial derivatives sum to one.

The resulting smooth function tends to infinity at either boundary face. Near the base boundary it agrees with $f_1$. Near $r=1$ every participating branch has positive Levi form and the regularized maximum preserves that property. The remaining region lies over a compact subset of $M^\circ$ with $r$ bounded away from one. This proves the existence of a proper exhaustion strictly plurisubharmonic outside a compact set.

## 9. Excluding compact analytic curves

By the strong pseudoconvexity theorem, an exhaustion of the kind just obtained implies that $Y$ is holomorphically convex. To conclude Steinness we must exclude positive-dimensional compact fibres in its Remmert reduction. [Ohsawa, Theorem 6.2](https://ems.press/content/serial-article-files/42176) · [Remmert reduction, Theorem 9.3](https://www.math.uni-hamburg.de/home/riemenschneider/bookchap09.pdf)

Let $\pi:Y\to M^\circ$ be the base projection and $\Omega$ the oriented area form on $M^\circ$. This form is exact because the base is an open disk. Equation (5) implies

$$\pi^*\Omega(W,JW)=t a^2+b^2/t$$

when the horizontal part of $W$ is $aX+bH$. It vanishes exactly in vertical directions. At zero velocity the same formula has $t=1$ in any oriented orthonormal horizontal frame, by continuity.

If $C$ were a compact irreducible analytic curve, its normalization would give a nonconstant holomorphic map $\nu:\Sigma\to Y$ from a compact connected Riemann surface. Stokes gives $\int_\Sigma\nu^*\pi^*\Omega=0$. The integrand is nonnegative pointwise and positive wherever $d(\pi\circ\nu)\ne0$. Thus $\pi\circ\nu$ is constant, so $\nu$ takes values in a holomorphic disk fibre. Its ordinary disk coordinate is then a holomorphic function on $\Sigma$ and is constant as well. This contradicts the choice of $\nu$.

A positive-dimensional compact analytic fibre in the connected noncompact complex surface $Y$ would contain an irreducible curve. Therefore every connected Remmert fibre is a point, and the reduction is an isomorphism as in §3. This proves Steinness of $Y$ without constructing any transport first integrals.

**Arbitrary open base sets.** Since $Y$ retracts to the contractible base, $H^2(Y,\mathbb Z)=0$. On the Stein manifold $Y$, Cartan's theorem B and the exponential sequence give $\operatorname{Pic}(Y)=0$. Each open velocity disk $D_p$ over $p\in M^\circ$ is a closed embedded complex hypersurface in $Y$. Its associated divisor bundle is trivial, so a global holomorphic function has zero locus exactly $D_p$. For compact $K\subset Y_U$, its hull in $Y_U$ is contained in its compact hull in $Y$. For each $p\notin U$ in the interior base, test by the reciprocal of this defining function to exclude $D_p$ from the closure of the smaller hull, as in §3. That hull is therefore compact, and the point separation and local coordinates of $Y$ restrict to $Y_U$. This gives the full theorem by the second method.

### An everywhere strictly plurisubharmonic exhaustion

There is a second way to finish the collar argument of §8. It yields an explicit strictly plurisubharmonic potential on the compact region where the collar estimate gives no sign. Write $x=\operatorname{Re}z$ and $y=\operatorname{Re}\mu$ in the oriented isothermal disk and its physical velocity coordinate. For any prescribed compact $K$ in the open bidisk, take
$$
 g=\exp\!\left(N(Ax+e^{By}-A-e^B)\right).
$$
On the full bidisk, $0<g\leq 1$. On $K$, sufficiently large positive constants $B,A,N$, chosen in that order, make $g$ strictly plurisubharmonic. Here is why these two real coordinates suffice. Set $X=(dx(v),dx(Jv))$ and $Y=(dy(v),dy(Jv))$. Positive projected area controls the horizontal part of $v$ by $|X|$. On a vertical tangent plane $J$ is multiplication by $i$, so $X=Y=0$ implies $v=0$. Compactness makes both bounds uniform on $K$. [Directional bounds](TransportOkaGrauert/PhysicalSteinDirections.lean) · [Coordinate Levi forms](TransportOkaGrauert/PhysicalLinearLevi.lean)

Put $u=Ax+e^{By}$ and $c=Be^{By}$. After division by the positive factor $Ng$, the Levi form of $g$ in direction $v$ is
$$
 A\,dd^c x(v,Jv)+c\,dd^c y(v,Jv)+Bc\,|Y|_2^2+N\,|AX+cY|_2^2.
$$
The proof bounds the first two terms using the horizontal and vertical components. Choosing $B$ controls the pure $Y$ term. Choosing $A\geq\max(1,Be^B)$ and then $N$ controls the remaining mixed term, using $A|X|\leq|AX+cY|+c|Y|$. The resulting lower bound is strictly positive for every $v\ne0$. A smooth regularized maximum combines $g$ with the collar exhaustion, preserving compactness of all sublevels. This argument proves the displayed strict Levi inequality even at zero velocity. [Quantitative estimate](TransportOkaGrauert/PhysicalSchurEstimate.lean) · [Patching theorem](TransportOkaGrauert/PhysicalSteinPatch.lean) · [Full-domain certificate](TransportOkaGrauert/PhysicalSteinStrict.lean)

Bohr and Paternain identify the isothermal CR equations with the intrinsic transport distribution. Their Lemma 4.1 proves integrability on the interior. Grauert’s theorem applies directly to the strictly plurisubharmonic exhaustion there. For an abstract compact oriented simple surface, the isothermal parametrization is smooth up to the boundary, and an ambient smooth extension of its conformal factor agrees with the metric on the closed disk. [Bohr and Paternain, Lemmas 4.1 and 4.9](https://www.numdam.org/item/10.5802/jep.231.pdf) · [Grauert, 1958](https://doi.org/10.2307/1970257) · [Paternain, Salo and Uhlmann, Theorems 3.4.15–16 and Remark 3.4.17](https://users.jyu.fi/~salomi/lecturenotes/GIP2D_driver.pdf)

## 10. A curvature check on the divisor construction

There is an independent way to compute the smooth coefficients $c$ and $k$ of §§1 and 4, including their values on the diagonal $p=x$. Here $J_g$ denotes rotation by $+\pi/2$ on the Riemannian surface. Write $x=\exp_p\xi$, $r=|\xi|$, $\gamma(t)=\exp_p(t\xi)$, and let $j(t)$ solve

$$j''(t)+r^2 K(\gamma(t))j(t)=0,\qquad j(0)=0,\qquad j'(0)=1.$$

No conjugate points gives $j(1)>0$ for $r>0$, and $j(1)=1$ for $r=0$. In geodesic polar coordinates centered at $p$, write the metric as $dr^2+S(r,\theta)^2d\theta^2$. For a fixed ray and $r>0$, $j(t)=S(rt,\theta)/r$. In particular $\partial_\theta=rj(1)J_g\partial_r$ at $x$ and $\nabla_{\partial_\theta}\partial_r=j'(1)J_g\partial_r$.

For $V=r\partial_r$, the transverse eigenvalue of $\nabla V$ is $j'(1)/j(1)$. In the radial parallel frame of §4, $\partial_r$ has angle $\theta$, so $\nabla_{\partial_\theta}\partial_r=(1+\omega(\partial_\theta))J_g\partial_r$. Hence the coefficients in the two identities are

$$c=\frac{j'(1)-j(1)}{r^2j(1)},\qquad k=\frac{j'(1)-1}{r^2j(1)}.$$

Integrating $(t j'-j)'=t j''$ and $j''=-r^2Kj$ gives formulas with regular denominators,

$$c=-\frac{\int_0^1 t K(\gamma(t))j(t)\,dt}{j(1)},\qquad
k=-\frac{\int_0^1 K(\gamma(t))j(t)\,dt}{j(1)}.$$

The coefficients are jointly smooth in $(p,\xi)$ by smooth dependence for the ordinary differential equation. At $\xi=0$ we have $j(t)=t$, so $c(p,p)=-K(p)/3$ and $k(p,p)=-K(p)/2$. These recover the smooth factors by a route independent of coordinate division, and test the signs even where the curvature is nonzero. [Jacobi fields and the distance Hessian, §3.8.2](https://users.jyu.fi/~salomi/lecturenotes/GIP2D_driver.pdf)

**Flat test.** In a parallel Euclidean frame with base coordinate $z$, we have $w=z-p$ and $c=\omega=0$. We may take $H_p=1$, so (4) becomes $F_p=(z-p)-\mu^2\overline{(z-p)}$. On the unit circle this is the equation of the unoriented line through $p$ and $z$. For $|\mu|<1$ the map $a\mapsto a-\mu^2\bar a$ has real determinant $1-|\mu|^4>0$, exactly as required. In the curved case the same computation at $x=p$, using $\nabla V(p)=I$, shows that the interior velocity disk over $p$ is a reduced principal divisor.

## 11. Prior work and verification

**The documented question.** Bohr asked in 2022 whether the interior is Stein for every simple surface. The 2023 transport Oka–Grauert paper, §1.2, describes the difficulty in curved metrics. Lemma 4.10 already uses the translated flat polynomial and its reciprocal. The scalar integrating factor for a complex one-form also predates the present construction. The contribution claimed in §§1–3 is to correct the geodesic-pencil polynomial for arbitrary curvature and every centre and to use its zeros on both boundary faces. Sections 6–9 deduce the same theorem from Jacobi fields without solving a transport equation for a holomorphic factor. [Bohr's question](https://www.math.uni-bonn.de/people/bohr/linz22_twistor.pdf) · [Bohr and Paternain](https://doi.org/10.5802/jep.231) · [Paternain, Salo and Uhlmann, Theorem 4.1](https://sites.math.washington.edu/~gunther/publications/Papers/attenuated_connection10.pdf)

**The closest curved models.** Bohr, Monard and Paternain construct global blow-down maps for constant-curvature simple metrics and their perturbations, and local maps for general metrics. Monard and Qi give a rotational family, including examples with conjugate points, in which the first coordinate is already a nonvanishing factor times the centered polynomial $z-\bar z\mu^2$. An embedding as an open domain of $\mathbb C^2$ alone leaves the domain's holomorphic convexity to be proved. The general canonical blow-down problem, with boundary conditions on the map, is a separate question. [Bohr, Monard and Paternain, Theorems 1.2–1.4 and Question 3.7](https://doi.org/10.3842/SIGMA.2026.045) · [Monard and Qi, Theorem 1](https://arxiv.org/html/2510.09518v1#S2.SS2)

**Significance.** The conclusion gives ordinary Stein theory on the full twistor interior of every simple surface, including Cartan's theorem B for coherent analytic sheaves. Section 4 also separates any two interior points by functions smooth on the closed bundle. Bohr, Monard and Paternain explicitly identified this separation problem beyond their perturbative regime in §1.3.1. Recovering a metric from measured boundary data, and obtaining an inversion formula or stability estimate, are different tasks. In two dimensions boundary distance rigidity for simple surfaces already has a proof. [Bohr, Monard and Paternain, §1.3.1](https://sigma-journal.com/2026/045/sigma26-045.pdf#page=8) · [Pestov and Uhlmann](https://doi.org/10.4007/annals.2005.161.1093)

**Verification.** Lean proves the three ordinary Stein conditions for every simple conformal disk and every open base subdomain. The coefficient may be smooth only on a neighborhood of the closed disk. The proof derives the invariant-mean theorem from scalar ray injectivity and a smooth integral kernel. An independent proof constructs a bounded-below, strictly plurisubharmonic exhaustion on the full disk. For an abstract surface Lean verifies the tangent-disk transfer with a supplied chart. Its existence and intrinsic transport compatibility use the classical geometric results. [Theorems and verification](STEIN-FORMALIZATION.md)

**Priority.** The literature search of 24 November 2026 found no earlier proof for all simple surfaces. Priority remains open to correction.

**Manuscript license.** Licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).

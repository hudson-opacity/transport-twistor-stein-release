# Prescribing Birkhoff jumping loci for transport first integrals

**AI contribution.** OpenAI Codex agents explored the jumping-locus constructions, drafted this note, and performed the internal mathematical and Lean checks described below.

On every compact oriented simple surface, each closed subset of the surface disjoint from its boundary occurs as the set of fibres where a smooth, geodesically invariant $\mathrm{SL}(2,\mathbb C)$-valued loop fails to have a canonical Birkhoff factorization. The partial indices are $\{1,-1\}$ on that set and $\{0,0\}$ elsewhere. In particular, the partial indices can vanish over the entire boundary while jumping at an interior point. This gives a negative answer to the sufficiency question immediately after Bohr and Paternain's Theorem 5.13. For the triangular loops below there is also an exact test using the full incoming data. [Bohr–Paternain, §5.3, p. 764](https://www.numdam.org/item/10.5802/jep.231.pdf#page=39)

In rank one the sole partial index is the winding number of a nonvanishing scalar loop. It is constant as the base point moves along a path. Rank two is therefore the first possible rank for this counterexample.

## A single loop

The triangular transition matrix below is the degree-one Atiyah–Ward ansatz from Yang–Mills twistor theory. Its factorization is classical. Here the geodesic transport equation determines which families of these loops occur over a simple surface. [Atiyah–Ward, *Instantons and algebraic geometry*](https://doi.org/10.1007/BF01626514) · [Taujanskas, explicit Laurent-series calculation, pp. 20–21](https://www.dpmms.cam.ac.uk/~gt306/mp1.pdf#page=20)

Write $\nu=e^{i\theta}$ for the positively oriented circle parameter. An inside factor and its inverse extend holomorphically to $|\nu|<1$, smoothly up to the circle. An exterior factor satisfies the same conditions in the variable $\nu^{-1}$ at and outside the circle. The canonical factorization is $W=GF$ with $G$ exterior, $G(\infty)=I$, and $F$ inside. This is the order and normalization used in §5.3 of the paper.

**Lemma.** For $h\in C^\infty(S^1,\mathbb C)$, the unordered pair of partial indices of
$$
 T_h(\nu)=
 \begin{pmatrix}\nu&h(\nu)\\0&\nu^{-1}\end{pmatrix}
$$
is $\{0,0\}$ if the circle average $c=h_0$ is nonzero and $\{1,-1\}$ if $c=0$.

Write $h=h_-+c+h_+$ for its strictly negative, constant, and strictly positive modes. Put $U(t)=I+tE_{12}$. Direct matrix multiplication gives
$$
 T_h=U(\nu h_-)\,T_c\,U(h_+/\nu).
$$
The left multiplier is exterior and the right multiplier is inside. Both have determinant one and inverse $U(-t)$. The coefficient of $\nu^{-1}$ in $h_-$ contributes a **constant** to the exterior multiplier. Such a multiplier preserves partial indices. If $T_c=G_cF_c$ is canonical, set $L=U(\nu h_-)G_c$, $R=F_cU(h_+/\nu)$, and $D=L(\infty)$. Then $T_h=(LD^{-1})(DR)$ has the required normalization. For a smooth family parametrized by the base, the half-series and their derivatives converge uniformly on their respective closed disks locally in the base. This follows by integration by parts in $\theta$ to arbitrary order after taking base derivatives. The two normalized factors therefore vary smoothly wherever the formulas for $G_c,F_c$ do.

For $c\ne0$ the canonical factors are
$$
 T_c=
 \begin{pmatrix}1&0\\ (c\nu)^{-1}&1\end{pmatrix}
 \begin{pmatrix}\nu&c\\-c^{-1}&0\end{pmatrix}.
$$
Both determinants are one. For $c=0$, $T_c=\operatorname{diag}(\nu,\nu^{-1})$ already displays the partial indices. One can also exclude a canonical factorization directly. If $T_0=GF$, the second column of $F=G^{-1}T_0$ is $\nu^{-1}$ times the second column of an exterior matrix. This column has only strictly negative modes, while $F$ has only nonnegative modes. It would vanish, contradicting invertibility. Uniqueness of the unordered partial indices is the usual Birkhoff factorization theorem. [Bohr–Paternain, §§2.1 and 5.3](https://www.numdam.org/item/10.5802/jep.231.pdf#page=39)

## The Euclidean disk and its incoming data

Take the closed unit disk $M\subset\mathbb C$ and use its parallel frame. The geodesic through $(z,\nu)$ is $t\mapsto(z+t\nu,\nu)$. For any smooth scalar first integral $h$, all entries of $W=T_h$ are first integrals. Write $w=W|_{\partial_+SM}$ for the incoming trace. Its scattering extension to the full boundary agrees with $W|_{\partial SM}$, including at tangencies, and hence is smooth. Its unique invariant extension $w^\sharp$ is $W$. The lemma gives the exact noncanonical locus
$$
 \left\{z\in M:\frac1{2\pi}\int_0^{2\pi} h(z,e^{i\theta})\,d\theta=0\right\}.
$$

For the explicit counterexample, $h(z,\nu)=z-\nu^2\bar z$ is invariant since $\nu-\nu^2\bar\nu=0$. Its average is $z$. The loop is canonical at every $z\ne0$, including the boundary, and equals $\operatorname{diag}(\nu,\nu^{-1})$ at the origin. The example uses only straight-line transport and the displayed elementary factorizations.

For $z\ne0$ the smooth normalized factors of this particular first integral are
$$
 G_z(\nu)=\begin{pmatrix}1&0\\(z\nu)^{-1}&1\end{pmatrix},\qquad
 F_z(\nu)=\begin{pmatrix}\nu&z-\nu^2\bar z\\-1/z&\nu\bar z/z\end{pmatrix}.
$$
They have determinant one, $G_z(\infty)=I$, and $G_zF_z=W_z$. Their entries and inverses are polynomial in their respective angular coordinates. The classical one-parameter jumping matrix $T_c$ also appears explicitly in Dunajski’s Appendix B.2. The transport step is choosing its off-diagonal representative to be constant along geodesics. A search of the subsequent transport literature did not locate a published resolution of this specific boundary test. [Dunajski, *Solitons, Instantons, and Twistors*, Appendix B.2](https://academic.oup.com/book/52956/chapter/421960798) · [Adukov, Mishuris and Rogosin, triangular partial indices, §3(b)](https://pmc.ncbi.nlm.nih.gov/articles/PMC7277130/)

There is a direct test for any $T_h$ in this family given its incoming upper-right entry $a=w_{12}$. For $|z|<1$ and $|\nu|=1$, put
$$
 \tau_-(z,\nu)=\operatorname{Re}(z\bar\nu)+
 \sqrt{\operatorname{Re}(z\bar\nu)^2+1-|z|^2}.
$$
This is the backward distance to the entry point $z-\tau_-(z,\nu)\nu$, obtained by solving $|z-t\nu|=1$ for $t\ge0$. At that point the velocity is still $\nu$. Thus the scalar backprojection
$$
 \mathcal B a(z)=\frac1{2\pi}\int_0^{2\pi}
 a\!\left(z-\tau_-(z,e^{i\theta})e^{i\theta},\,e^{i\theta}\right)d\theta
$$
is precisely $h_0(z)$. Its zeros give all noncanonical interior fibres. The same formula holds on $\partial M$ by continuity for these smooth compatible data. It uses the incoming entries themselves, so equal boundary partial indices can give different backprojections.

## Every simple surface

Let $M$ be a compact oriented simple Riemannian surface with smooth boundary, and $X$ its geodesic vector field. Choose a smooth global positively oriented orthonormal frame $e_1,e_2$, possible since $M$ is a disk. For $v=\cos\theta\,e_1+\sin\theta\,e_2$ set $\nu(x,v)=e^{i\theta}$. Define the real connection one-form $\omega$ by $\nabla e_1=\omega e_2$. Parallel transport of $v$ gives $X\theta=-\omega_x(v)$, interpreted locally in the angular coordinate. Consequently
$$
 C=\nu^{-1}X\nu=-i\omega_x(v)
$$
is a globally defined skew-Hermitian scalar connection attenuation. Theorem 1.3 of Bohr and Paternain gives $q$ satisfying $(X+C)q=0$ with $q$ and $q^{-1}$ smooth and fibrewise holomorphic. In particular both are inside factors. The function $b=\nu q$ is a nowhere-zero first integral on $SM$, since $X\nu=C\nu$. [Bohr–Paternain, Theorem 1.3, p. 730](https://www.numdam.org/item/10.5802/jep.231.pdf#page=5)

For any smooth scalar first integral $a$, define the determinant-one matrix first integral
$$
 W_a=\begin{pmatrix}b&a\\0&b^{-1}\end{pmatrix}.
$$
Right multiplication by the inside factor $\operatorname{diag}(q^{-1},q)$ gives $T_{qa}$ in the chosen angle coordinate. The lemma therefore identifies its noncanonical locus with the zero set of $(qa)_0$. If $a_{\rm in}$ is the incoming trace and $E_-(x,v)$ is the incoming unit vector of the geodesic through $(x,v)$, the same scalar is the weighted backprojection
$$
 (qa)_0(x)=\frac1{2\pi}\int_{S_xM}
 q(x,v)\,a_{\rm in}(E_-(x,v))\,d\theta .
$$
The metric, the chosen $q$, and the incoming data determine this integral for every interior $x$. When $M$ is the Euclidean disk in its parallel frame, $q=1$ is available and the preceding explicit formula results.

**Prescription.** Fix any $f\in C^\infty(M,\mathbb C)$. Apply Bohr–Paternain's Lemma 3.2 with rank one, attenuation $C$, mode $m=0$, prescribed zeroth coefficient $f$, and prescribed first coefficient zero. It produces $\phi\in C^\infty(SM,\mathbb C)$ satisfying
$$
 (X+C)\phi=0,\qquad \phi_0=f,\qquad \phi_1=0 .
$$
Set $a=\phi/q$. The two scalar transport equations give $Xa=0$, and $qa=\phi$. Hence the noncanonical locus of $W_a$ is exactly $f^{-1}(0)$. The incoming trace of $W_a$ has a smooth scattering extension since $W_a$ is a smooth first integral. If the null-homotopy condition on the full boundary loop map is imposed as in §5.1, it holds as well. The map takes values in $\mathrm{SL}(2,\mathbb C)$, which deformation retracts to $SU(2)\simeq S^3$, and every map from the boundary torus to $S^3$ is null-homotopic. [Bohr–Paternain, Lemma 3.2, p. 737](https://www.numdam.org/item/10.5802/jep.231.pdf#page=12)

For any closed $K\subset M$, one can choose $f$ smooth and nonnegative with $f^{-1}(0)=K$. Cover $M\setminus K$ by countably many open sets on each of which a smooth nonnegative bump $\chi_j$ is positive, with $\operatorname{supp}\chi_j\subset M\setminus K$. Choose $t_j>0$ so that $t_j\|\chi_j\|_{C^j(M)}\le2^{-j}$. The series $f=\sum_j t_j\chi_j$ converges in every $C^k$, vanishes on $K$, and is positive at every point of its complement. The cases $K=M,\varnothing$ also follow directly by taking $f=0,1$, respectively.

Taking $K\cap\partial M=\varnothing$ gives canonical boundary loops. The set where the partial-index pair is **discontinuous** is the relative boundary $\partial_M K$. If $K$ is nowhere dense, it is both the noncanonical locus and the discontinuity locus. If $K$ has interior, the pair is locally constant with value $\{1,-1\}$ there.

## Appendix. Recovering all indices with known geodesic incidence

Let $w$ be smooth incoming $\mathrm{GL}(n,\mathbb C)$ data whose invariant extension is smooth. Fix an interior point $x$ and an oriented orthonormal frame there. For the unit vector $v_\theta$ at angle $\theta$, form the loop $W_x(e^{i\theta})=w(E_-(x,v_\theta))$. Each of its Fourier coefficients is an integral of the given boundary entries,
$$
 \widehat W_x(k)=\frac1{2\pi}\int_0^{2\pi}w(E_-(x,v_\theta))e^{-ik\theta}\,d\theta .
$$
Write $H^2_+$ for the square-integrable $\mathbb C^n$-valued circle functions with nonnegative modes, and $P_+$ for orthogonal projection onto that space. For a bounded matrix symbol $L$, its Toeplitz operator is $\mathcal T_L u=P_+(Lu)$ on $H^2_+$. For each integer $m$, let
$$
 d_m(x)=\dim\ker \mathcal T_{\nu^{-m}W_x}.
$$
The block in row $p$ and column $r$ of this operator is $\widehat W_x(p-r+m)$ for $p,r\ge0$. These infinite matrices specify the criterion directly from the full incoming data and $E_-$.

To see what $d_m$ measures, take any Birkhoff factorization $W_x=G\operatorname{diag}(\nu^{a_1},\dots,\nu^{a_n})F$. The Toeplitz product identity $\mathcal T_{AB}=\mathcal T_A\mathcal T_B$ holds if $B$ is inside or if $A$ is exterior. In the first case multiplication by $B$ preserves $H^2_+$. In the second, multiplication by $A$ preserves the strictly negative modes, so the intermediate projection leaves the final projection unchanged. Applying these identities to $F,F^{-1},G,G^{-1}$ shows that $\mathcal T_F$ and $\mathcal T_G$ are invertible. They flank the diagonal Toeplitz operator with entries $\mathcal T_{\nu^{a_j-m}}$. The kernel of a scalar shift $\mathcal T_{\nu^s}$ has dimension $\max(-s,0)$. Thus the multiplicity of any index $k$ is
$$
 d_m(x)=\sum_{j=1}^n\max(m-a_j,0),\qquad
 \#\{j:a_j=k\}=d_{k+1}(x)-2d_k(x)+d_{k-1}(x).
$$
Indeed $d_{m+1}-d_m$ counts the $a_j\le m$. In particular, the fibre is canonical exactly when the second difference at $k=0$ equals $n$. Rotating the chosen frame rotates the loop parameter, which preserves the Hardy modes and these dimensions. [Ehrhardt, Wiener–Hopf factorization and Toeplitz nullities](https://arxiv.org/abs/math/0002027)

This is an exact, nonlocal test with known incidence at each queried interior point. A criterion expressed intrinsically using only the boundary scattering relation, without supplying $E_-(x,\cdot)$, is a different question.


## Formal verification

Lean verifies the flat counterexample with the original smooth angular factorization requirements. The proof reconstructs the unique invariant extension of the incoming data, verifies the full-boundary map is null-homotopic in the general linear group, gives smooth normalized factors at every nonzero point, and rules out even continuous holomorphic boundary factors at the origin. [Counterexample](../TransportOkaGrauert/BoundaryJump.lean) · [Incoming trace and uniqueness](../TransportOkaGrauert/JumpIncoming.lean) · [Null-homotopy](../TransportOkaGrauert/JumpHomotopy.lean)

The exact Haar-mean criterion is also checked for arbitrary smooth triangular loops, as is the polynomial construction with any prescribed finite exceptional set on the flat disk. Lean verifies the scalar gauge reduction and the transport differentiation used on curved surfaces. The existence of the two scalar solutions on every simple surface is invoked from the published theorems in the mathematical proof above. [Smooth mean criterion](../TransportOkaGrauert/SmoothTriangularLoop.lean) · [Finite prescribed sets](../TransportOkaGrauert/PolynomialJumps.lean) · [Curved calculation](../TransportOkaGrauert/CurvedJump.lean)

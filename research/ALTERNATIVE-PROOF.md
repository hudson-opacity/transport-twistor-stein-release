# Transport Oka–Grauert via bounded endpoint corrections

This note gives a proposed mathematical derivation of the general theorem from the linear transport and tomography results used by Bohr and Paternain. Its extra step is to control a two-parameter family of linear solutions at one fixed Sobolev order. The proof of that estimate is included below for review. The analytic inputs concerning surfaces have yet to be formalized in this project.

## Reduce the given attenuation once

Let $M$ be a compact, oriented, simple Riemannian surface with smooth boundary. Simplicity means strictly convex boundary, nontrapping, and absence of conjugate points. Write $X$ for the geodesic vector field on $SM$, $\Omega_k$ for angular mode $k$, and $\Pi$ for projection onto all nonnegative modes. Let $A:SM\to\operatorname{Mat}_n(\mathbb C)$ be smooth, of arbitrary finite positive rank, with $A_k=0$ for $k<-1$. Write $\mathcal G$ for the group of smooth invertible fields whose entries and inverse entries have only nonnegative modes. We seek $F\in\mathcal G$ such that $XF+AF=0$, with smoothness up to the boundary. [Bohr–Paternain (BP), §1.1, Theorem 1.3](https://www.numdam.org/item/10.5802/jep.231.pdf#page=5)

Paternain and Salo first construct an ordinary smooth transport frame $R$ by solving on a larger surface. They factor $R=HU$ with $H\in\mathcal G$ and $U$ unitary and obtain
$$
 B=H^{-1}XH+H^{-1}AH=-(XU)U^{-1}.
$$
The last expression makes $B$ skew-Hermitian. The first has no modes below $-1$, and skew-adjointness then excludes every mode above $1$. Thus $B$ is a skew-Hermitian connection one-form plus a skew-Hermitian Higgs field. A frame $G\in\mathcal G$ for $B$ gives the required frame $HG$ for $A$. The argument below uses the path $tB$, so a single loop factorization suffices even when $A$ has infinitely many Fourier modes. [Paternain–Salo, Lemma 3.1, Theorem 4.2 and Lemma 5.2](https://arxiv.org/pdf/2006.02257#page=10)

## Solve a linear endpoint equation

Give $V=\operatorname{Mat}_n(\mathbb C)$ its Hilbert–Schmidt inner product. For real $p=(s,t)$, define
$$
 C_p(Y)=tBY-sYB,\qquad D_p=X+C_p .
$$
Left and right multiplication by a skew-Hermitian matrix are skew-adjoint on $V$. Each $C_p$ is therefore a skew-Hermitian connection–Higgs pair on a trivial rank-$n^2$ bundle. Its coefficients are linear in both endpoints. The fixed source $f=-B$, regarded as $V$-valued, has modes in $\{-1,0,1\}$.

If $D_pU_p=-B$ and $\Pi U_p=U_p$, then
$$
 J_{t,s}=I+(t-s)U_p,\qquad XJ_{t,s}+tBJ_{t,s}-J_{t,s}sB=0 .
$$
Indeed $D_pI=(t-s)B$. We need a choice for which $\|U_p\|_{C^0}$ stays bounded near each $(a,a)$. Bare solvability is insufficient. For $s\ne t$, the solution $-I/(t-s)$ produces $J_{t,s}=0$. The left–right attenuation identity also occurs in the pseudolinearization of the ray transform. [Zhou, §6, equations (6.1)–(6.2)](https://arxiv.org/pdf/1610.02185#page=16)

## Continuity of the localized weighted normal

Fix a simple patch $M_j$, a real smooth cutoff $\chi$ compactly supported in its interior, and a closed ambient surface $N$ containing that patch. For a smooth square matrix weight $W$ on $SM_j$, let $I_W$ integrate $W(x,v)f(x)$ along each oriented geodesic. Use the fixed Santaló density on the incoming boundary. Define
$$
 K(W,V')=\chi I_W^*I_{V'}\chi,\qquad Q(W)=K(W,W),
$$
using restriction and zero extension at the cutoffs. For any nonnegative integer $q$, the weight variables with their $C^\infty$ topologies map jointly continuously to $\mathcal L(H^q(N),H^{q+1}(N))$ in operator norm, as follows.

1. For a smooth invertible weight, Zhou's interior theorem gives a normal operator of order $-1$. The compact interior cutoffs give the asserted bounded map on $N$. For arbitrary $W$, take $c>\sup\|W\|$. Both $cI+W$ and $cI-W$ are invertible, and $Q(W)=(Q(cI+W)+Q(cI-W))/2-Q(cI)$. Complex polarization then expresses every $K(W,V')$ as a linear combination of bounded diagonal normals. This proves boundedness at each fixed pair of weights. [Zhou, §5, Lemma 5.2](https://arxiv.org/pdf/1610.02185#page=16)
2. Fix $W$. If $V'_i\to V'$ smoothly and $K(W,V'_i)\to T$ in operator norm, test against smooth sections $f,h$ of the input and dual output bundles. Using the distribution pairing with the fixed smooth density gives
$$
 \langle K(W,V'_i)f,h\rangle
 =\langle I_{V'_i}(\chi f),I_W(\chi h)\rangle_{L^2(\partial_+ SM_j)} .
$$
Finite geodesic lengths and compactness give convergence on the right. Operator-norm convergence gives $\langle Tf,h\rangle$ on the left. Smooth $h$ separate distributions and smooth $f$ are dense in $H^q$. Hence $T=K(W,V')$. The same argument holds in the other variable. Since the smooth weight space is Fréchet and the operator target is Banach, the closed graph theorem gives separate continuity, taking real scalars for the conjugate-linear variable.
3. For any sequence $W_i\to W$, the continuous maps $V'\mapsto K(W_i,V')$ are pointwise bounded by the separate continuity just proved. The closed sets where all the operator norms $\|K(W_i,V')\|$ are at most $m$, for positive integers $m$, cover the Fréchet weight space. By Baire one has interior. Taking differences gives a uniform bound on a neighborhood of zero, hence equicontinuity by scaling. Thus $V'_i\to V'$ implies $K(W_i,V'_i)-K(W_i,V')\to0$, and separate continuity handles the other difference. Metrizability now gives joint continuity. A closed graph upgrade of this kind also appears in work on transport normals by Bohr, Monard and Paternain. [Bohr–Monard–Paternain, Lemmas 6.5–6.6](https://arxiv.org/pdf/2403.05985#page=25)

The argument fixes the metric and obtains continuity at the precise Sobolev order used below. Zhou's coefficient perturbation estimate for the connection–Higgs normal on functions and one-forms is at $L^2\to H^1$. The $H^2\to H^3$ result for the four two-mode blocks follows from the preceding derivation. [Zhou, Lemma 3.6](https://arxiv.org/pdf/1610.02185#page=11)

## Lift the two prescribed modes

We need BP's homogeneous solution $S_{-1,C_p}(g_{-1}+g_0)$, whose modes $-1,0$ coincide with its input. Fix $p_0=(a,a)$. We derive one constant $c$ on a neighborhood of $p_0$ such that
$$
 \|S_{-1,C_p} g\|_{H^2(SM)}\le c\|g\|_{H^3(SM)} .
$$

**Shift the modes before constructing the normal.** The simple surface is diffeomorphic to a disk. Fix a smooth oriented unit frame and let $e=e^{-i\theta}$ in its angle coordinate. Set $\widetilde C_p=C_p+e^{-1}(Xe)I_V$. Then $D_p(eu)=e(X+\widetilde C_p)u$. The extra term is purely imaginary and evaluates a one-form on the unit velocity, since $X\theta$ is, up to sign, the connection form of the chosen frame. Thus $\widetilde C_p$ remains a skew-Hermitian pair. Multiplication by $e^{-1}$ shifts modes $(-1,0)$ to $(0,1)$. The required operator is $S_{-1,C_p}g=eS_{0,\widetilde C_p}(e^{-1}g)$, where both fixed multipliers preserve each Sobolev order. [BP, proof of Lemma 3.2, shift for general $m$](https://www.numdam.org/item/10.5802/jep.231.pdf#page=14)

**Fix the patches, the coefficient extension and its support.** Use BP's closed metrized extension $N$, simple patches $M_j$, and real cutoffs $\psi_j$ compactly supported in their interiors. Here $M\Subset M_1^\circ$, $\psi_1=1$ on $M$, and $\sum_j\psi_j^2=1$. On $M_1$, extend the connection one-form and Higgs coefficients of each of the finitely many fixed pairs entering the affine family $\widetilde C_p$. Extend the tensor components in real frames and a real basis of skew-Hermitian matrices, then multiply by a fixed interior cutoff equal to one on $M$. Recombine using the original real coefficients $1,s,t$. This preserves tensor types and skew-adjointness and gives one compact interior support for the whole family. Use zero attenuations on the other patches as in BP. Choose all angular trivializations once. [BP, proof of Lemma 3.2, construction before (3.5)](https://www.numdam.org/item/10.5802/jep.231.pdf#page=13)

Write $I_j^{0,1}(p)$ for the extended attenuated transform restricted to modes $0,1$. Set
$$
 P_p=\sum_j\psi_j I_j^{0,1}(p)^* I_j^{0,1}(p)\psi_j .
$$
On the first patch let $R_p$ be the smooth parallel transport normalized to the identity on the incoming boundary. Its inverse gives the weight $W_p$ in the geodesic integral. The incoming vectors of geodesics meeting the compact coefficient support form a compact set disjoint from glancing. This follows from strict convexity, continuity of the exit time, and its zero value at glancing. Over a compact neighborhood of this set the entrance, flow, and exit coordinates are smooth. The integral equation for parallel transport has coefficients jointly smooth in $p$, incoming vector and time. Differentiation and induction at each finite order on compact parameter neighborhoods give smooth dependence in all those variables. Near glancing $R_p=I$ on the entire geodesic. Hence $W_p$ varies continuously in $C^\infty(SM_1)$. [BP, (3.5)–(3.6) and the parallel transport formula](https://www.numdam.org/item/10.5802/jep.231.pdf#page=13)

In each angular frame the transform of $f_0(x)+e^{i\theta}f_1(x)$ is $I_{W_p}f_0+I_{e^{i\theta}W_p}f_1$. Its localized normal is therefore a two-by-two block matrix of the operators $K$ above with the constants dictated by BP’s angular measure. For unnormalized $d\theta$ each pure mode has squared norm $2\pi$ times its base squared norm, so the coefficient-space blocks carry a factor $(2\pi)^{-1}$ against standard base measure. We keep BP’s adjoint in the definition of $P_p$ and in (3.4). Hence $P_p:H^2(N)\to H^3(N)$ is operator-norm continuous. At $p_0$, BP show $P_{p_0}$ is an injective, self-adjoint elliptic operator of order $-1$. This makes it an isomorphism on this Sobolev pair. Ellipticity gives closed range and smooth kernel and cokernel representatives. Self-adjointness identifies any distribution annihilating the range with a smooth element of the zero kernel. BP obtain injectivity from the skew-Hermitian attenuated ray transform on each simple patch, eliminating its potential kernel by the missing negative mode and the zero boundary value of the potential. [BP, Lemma 3.2 and (3.4)–(3.5)](https://www.numdam.org/item/10.5802/jep.231.pdf#page=12) [Paternain–Salo–Uhlmann, Theorem 1.3](https://arxiv.org/pdf/1108.1118#page=3)

Shrink the neighborhood until $\|P_{p_0}^{-1}(P_p-P_{p_0})\|_{H^2\to H^2}<1/2$. A Neumann series gives $\|P_p^{-1}\|_{H^3\to H^2}\le 2\|P_{p_0}^{-1}\|$. For smooth data the inverse takes smooth values by fixed-$p$ elliptic regularity. With a fixed Seeley extension $E$, BP's solution on $SM$ is
$$
 S_{0,\widetilde C_p}g
 =\left(I_1^{0,1}(p)\,\psi_1 P_p^{-1}Eg\right)^{\sharp_p}\big|_{SM}.
$$
The adjoint formula identifies its modes $0,1$ with $g$. The extension $E$ is bounded at $H^3$. The forward transform after multiplication by $\psi_1$ has support in a fixed compact subset $K$ of the incoming boundary away from glancing, because every contributing geodesic meets $\operatorname{supp}\psi_1$. In flow coordinates over a compact neighborhood of $K$, the transform pulls the base input to $SM_1$, multiplies by its weight and integrates over the geodesic. Normalize time by the smoothly varying positive length to obtain the fixed interval $[0,1]$. In normalized time $r$, the pullback of Liouville volume along $(b,r)\mapsto \varphi_{r\tau(b)}b$ has density $\tau(b)|\langle v,\nu\rangle|$ against boundary measure and $dr$. Both factors have a positive minimum on the chosen compact set of incoming labels. Thus the flow-coordinate diffeomorphism and its inverse have bounded Jacobians there, through the time endpoints. The time-length factors are smooth and bounded there. Pullback of a base section to the unit tangent bundle is bounded at $H^2$ in local trivializations by integration over the compact velocity circle. Cauchy–Schwarz in time and the product and chain rules through order two give the forward $H^2\to H^2$ estimate with constants controlled by uniform derivatives of $W_p$. For data supported in $K$, the lift is $h^{\sharp_p}=R_p\,\pi_{\rm in}^*h$. The same coordinates bound pullback at $H^2$, and multiplication by $R_p$ is uniformly bounded there. These statements give the asserted estimate for $S_{-1,C_p}$, with smooth output for smooth input. [BP, (3.4)–(3.6) and their estimates](https://www.numdam.org/item/10.5802/jep.231.pdf#page=13)

## Correct the unrestricted solution

Write $C_p=\Gamma_p+\Phi_p$ for its one-form and Higgs field, and $\mu_\pm=\eta_\pm+(\Gamma_p)_{\pm1}$. Here $X=\eta_-+\eta_+$, with $\eta_\pm$ shifting angular degree by $\pm1$. Two further parameter-dependent choices occur in BP's construction.

* **Unrestricted transport.** Solve $D_pu=f$ using a fixed larger surface, a fixed compactly supported extension of $f$, and a compactly supported extension of $C_p$ by one-forms and Higgs fields as above. Take zero data at the geodesic endpoint used in BP's Lemma 3.4 and restrict to $SM$. Geodesics meeting the support of either extended function have incoming vectors in a fixed compact set away from glancing. The integral solution is a variable-limit time integral of the source multiplied by parallel transport. In the normalized flow coordinates used above, that integral is bounded at order three. Cauchy–Schwarz treats the integral itself, differentiation in transverse coordinates passes under the integral sign, and differentiation with respect to the time limit produces the integrand. The transport multipliers have uniformly bounded derivatives through order three on a compact parameter neighborhood. The fixed smooth extension is bounded at order three. This yields $\|u\|_{H^3}\le c\|f\|_{H^3}$. Alternatively, BP's commutator induction through order three controls its constants by the fixed geometry and finitely many coefficient derivatives. [BP, Lemma 3.4 and (3.8)](https://www.numdam.org/item/10.5802/jep.231.pdf#page=15)
* **One-mode equations.** BP construct right inverses for $\mu_-:\Omega_0\to\Omega_{-1}$ and $\mu_+:\Omega_{-1}\to\Omega_0$ in global isothermal coordinates. Fixed scalar factors and conjugation by a smooth invertible disk gauge reduce each to the disk Cauchy integral or its complex conjugate. Their Lemma 6.2 explicitly supplies disk gauges smooth jointly in the point and the finite parameters $p$. On a relatively compact parameter neighborhood these matrices and their inverses have uniformly bounded derivatives through order three. Use a fixed compactly supported Seeley extension of disk data, apply the plane Cauchy operator, and restrict to the disk as in (3.7). This fixed $H^2\to H^3$ operator, composed with the smooth matrix multipliers, gives uniform $H^2\to H^3$ bounds for the two right inverses. [BP, Lemma 3.3 and (3.7)](https://www.numdam.org/item/10.5802/jep.231.pdf#page=14) [BP, Lemma 6.2, parameter clause](https://www.numdam.org/item/10.5802/jep.231.pdf#page=42)

Set $q_0=\mu_+u_{-1}$ and $q_{-1}=\Phi_pu_{-1}+\mu_+u_{-2}$. Use the one-mode right inverses to choose $g_0,g_{-1}$ satisfying $\mu_-g_0=q_{-1}$ and $\mu_+g_{-1}=-q_0$. Put $v=S_{-1,C_p}(g_{-1}+g_0)$. Comparing Fourier modes gives
$$
 D_p\Pi u=f-q_0-q_{-1},\qquad D_p\Pi v=q_{-1}+q_0.
$$
In the first identity the discarded modes of $u$ affect only the output degrees $0,-1$. In the second the output at degree $-1$ is $\mu_-v_0$, at degree $0$ it is $-\mu_+v_{-1}$, and the higher modes vanish since $D_pv=0$. Thus $U_p=\Pi(u+v)$ is smooth, has nonnegative modes and satisfies $D_pU_p=f$. The Fourier projections are fixed and bounded at every Sobolev order. Forming the two $q$'s uses one derivative, the one-mode inverses gain one, and the homogeneous lift loses one. The resulting bound is
$$
 \|U_p\|_{H^2(SM)}
 \le c\big(\|u\|_{H^2}+\|g_{-1}+g_0\|_{H^3}\big)
 \le c'\|f\|_{H^3(SM)}
$$
uniformly for $p$ near $p_0$. [BP, proof of Proposition 3.1](https://www.numdam.org/item/10.5802/jep.231.pdf#page=16) [BP, Lemma 6.1](https://www.numdam.org/item/10.5802/jep.231.pdf#page=41)

Since $\dim SM=3$, the $H^2$ norm controls the supremum norm. For example, extend across boundary charts, apply Fourier Cauchy–Schwarz with $(1+|\xi|^2)^{-1}\in L^2(\mathbb R^3)$, and sum a finite partition of unity. The Euclidean operator norm of a matrix is bounded by its Hilbert–Schmidt norm. Lean uses the maximum absolute row sum as its operator norm. For fixed rank $n$ that norm is bounded by $n\max_{i,j}|U_{ij}|$ and by $\sqrt n\,\|U\|_{\rm HS}$. Both comparisons are checked in Lean, so an entrywise or Hilbert–Schmidt Sobolev estimate supplies the formal bound. No uniformity over ranks is needed. Taking $f=-B$ gives the required $C^0$ bound $c_a$ near $(a,a)$.

## Compose near-identity gauges and descend to the twistor space

For each $a\in [0,1]$, take an open interval $V_a$ around $a$ small enough that $(s,t)$ belongs to the preceding neighborhood whenever $s,t\in V_a$, and $|t-s|c_a<1/2$. Nonnegative Fourier modes extend $(t-s)U_p$ holomorphically into each unit velocity disk. Rapid decay of the angular coefficients of a smooth field, including after any number of base derivatives, gives smoothness up to the closed disk. For fixed unit vectors $v,w$, apply the scalar maximum modulus principle to the disk function $v^*(t-s)U_pw$. Taking the supremum over both vectors gives the same norm bound throughout the disk. Thus $J_{t,s}$ is invertible throughout by the Neumann series. Finite-dimensional matrix inversion makes its inverse holomorphic in each open disk and smooth up to its boundary. Its boundary field consequently has only nonnegative modes. We have proved $J_{t,s}\in\mathcal G$. [BP, Proposition 4.4 and Remark 4.5 on disk extension](https://www.numdam.org/item/10.5802/jep.231.pdf#page=20) [Project chart version of near-identity inversion](../TransportOkaGrauert/NearIdentity.lean)

Take a finite subcover by the intervals $V_a$. A partition $0=t_0<\cdots<t_\ell=1$ of mesh below its Lebesgue number puts each consecutive pair in a common interval. Starting with $G_0=I$, form $G_{j+1}=J_{t_{j+1},t_j}G_j$. By the product rule the endpoint equation gives $XG_j+t_jBG_j=0$ inductively, and $\mathcal G$ is closed under multiplication. Then $HG_\ell$ is the desired frame for $A$. This finite product requires only local boundedness of the corrections, with no differentiation in the endpoints.

Finally, BP identify $\mathcal G$-orbits of admissible attenuations with smooth gauge classes of flat partial $(0,1)$-connections on the closed transport twistor space $Z$ whenever $M$ is a disk. The zero attenuation represents the product holomorphic structure. Every attenuation has now been gauged to zero. The base is a disk and $Z$ retracts to it, so each smooth complex vector bundle on $Z$ is topologically trivial and admits the smooth trivialization used in that correspondence. Thus the moduli space of the paper's boundary-regular holomorphic vector bundles has one class in each rank. [BP, Definition 4.11, Proposition 4.12 and Theorem 4.13](https://www.numdam.org/item/10.5802/jep.231.pdf#page=26)

## What remains to verify

The mathematical inference for independent review is the local uniformity of the selected two-mode lifts. Zhou supplies the interior normal's order for fixed invertible weights. Polarization and the distribution pairing give continuity in the required operator norm, and BP's formulas supply the remaining estimates with the supports and metric held fixed. Taking those cited results as inputs, this derivation leaves no identified additional mathematical hypothesis. External mathematical review of the parameter estimate is outstanding.

Lean verifies the nonlinear endpoint implication on the closed disk, the Fourier coefficient identities for the chart geodesic field, Banach-space stability of the patched operator under dense test-pairing hypotheses, continuous dependence of normalized transport in the uniform norm, and the Euclidean three-dimensional embedding for finite Fourier energy. Formalizing the surface tomography inputs, their realization as the specified Sobolev operators, and the geometric twistor correspondence remains necessary for a complete machine proof. The published nonlinear transport theorem and its equivalent bundle conclusion appear above as theorem statements and consequences. The derivation uses neither as an input.

## Machine-checked model cases for the matrix frame theorem

| Input | What Lean constructs | Entry point |
|---|---|---|
| Flat disk. Any smooth direction-only matrix attenuation of any finite rank, with no angular Fourier modes below −1 | Smooth integrating factors on the unit tangent bundle, with both inverse identities and the prescribed Fourier cutoff | [DiskSeries.smooth_directionOnlyIntegratingFactor](../TransportOkaGrauert/DiskSeries.lean) |
| Flat disk. Any strictly upper triangular matrix of any finite rank, with finite sums of monomials c zᵖ z̄ᑫ wᵏ, k ≥ −1, as its entries on the unit circle | A smooth invertible frame satisfying the transport equation and the horizontal and vertical twistor equations throughout the closed velocity disk | [UpperDisk.polynomial_integrating_factor](../TransportOkaGrauert/UpperDisk.lean) · [UpperTwistor.polynomial_twistor_frame](../TransportOkaGrauert/UpperTwistor.lean) |
| Flat disk. Any scalar attenuation with the same polynomial base and angular dependence | A scalar exponential integrating factor and its reciprocal, with global smooth extensions | [PolynomialDisk.scalar](../TransportOkaGrauert/PolynomialDisk.lean) |
| Any smooth conformal metric on the disk. A smooth closed scalar one-form on an open convex neighborhood | A rank-one frame constructed from a potential obtained by the Poincaré lemma, with smoothness, angular cutoff and the curved geodesic equation | [ClosedForm.closedForm_chart_frame](../TransportOkaGrauert/ClosedFormFrame.lean) |

The first row permits infinite Fourier series and unrestricted matrix entries. The second permits variation of noncommuting matrices along one geodesic. The third permits scalar diagonal attenuation with base dependence.

The common chart target gives explicit definitions of strict convexity, finite geodesic escape, the normal Jacobi equation, and a holomorphic frame. The universal statement is defined as a proposition. Lean proves that the flat metric satisfies its simplicity hypotheses and that both arbitrary-rank families above satisfy its precise frame conclusion. [Chart target](../TransportOkaGrauert/SimpleDiskTarget.lean) · [Euclidean simplicity](../TransportOkaGrauert/FlatSimple.lean) · [Flat instances](../TransportOkaGrauert/FlatTargetInstance.lean)

### Why the flat constructions work

Write the base point as z and the unit direction as w. Along a straight geodesic z + tw, the coordinate u = z − w² z̄ stays fixed, and the derivative of z̄ is w̄. A polynomial in the characteristic coordinates u, z̄ and w can therefore be integrated term by term with respect to z̄. Expanding z = u + w² z̄ puts ordinary base-coordinate polynomials into precisely this form.

For a strictly upper triangular attenuation, solve for one frame entry at a time. The entry in row i can depend on corrections from row k only when k > i. This gives a terminating recursion, retains the order of matrix multiplication and produces a frame of the form I + N. Its inverse is the finite sum of powers of −N through degree n−1. Rank three already exhibits the ordered integral of the (1,2) coefficient against the primitive of the (2,3) coefficient. [Ordered recursion](../TransportOkaGrauert/UpperRecursion.lean) · [Finite inverse](../TransportOkaGrauert/Nilpotent.lean) · [Rank-three formula](../TransportOkaGrauert/Triangular.lean)

For a direction-only attenuation A, multiplication by w shifts the allowed Fourier modes into the nonnegative range. Its disk extension B has boundary value wA. Along a fixed ray B(w) is constant, so the explicit matrix exponential exp(−z̄ B(w)) solves the transport equation. The proof reconstructs B from genuine Haar Fourier coefficients, obtains absolute summability from two integrations by parts, and recovers the original smooth boundary field. Negative modes of the two frames vanish by Cauchy–Goursat. [Fourier decay](../TransportOkaGrauert/FourierDecay.lean) · [Disk reconstruction](../TransportOkaGrauert/DiskSeries.lean) · [Boundary modes](../TransportOkaGrauert/BoundaryModes.lean)

## Lean components of the general matrix argument

| Step | Kernel-checked content | Concrete input still required |
|---|---|---|
| Normalize the attenuation | A factored ordinary frame gives the skew-Hermitian gauge identity. Skew-adjointness truncates modes at +1, and the mixed rank-squared field preserves the three modes. [Loop normalization](../TransportOkaGrauert/LoopNormalization.lean) · [Mixed field](../TransportOkaGrauert/SkewReduction.lean) | Construct the ordinary frame and its smooth loop-group factorization on the simple surface. |
| Estimate the patched normal | Polarization, weak pairings on dense tests, operator-norm continuity and local uniform bounds for a right inverse on a fixed Banach pair. Normalized transport exists and depends continuously on its coefficient along compact rays. Weighted ray integrals yield continuous test pairings. [Weights](../TransportOkaGrauert/WeightPolarization.lean) · [Transport ODE](../TransportOkaGrauert/WeightTransport.lean) · [Ray integrals](../TransportOkaGrauert/RayTests.lean) · [Patched inverse](../TransportOkaGrauert/PatchedInverse.lean) | Realize the geometric Sobolev spaces and their ray-transform pairings, prove interior order −1 and diagonal invertibility, and control the flow maps through order two. |
| Solve with nonnegative modes | Each angular coefficient is smooth in the base through the boundary. The matrix equation is equivalent to its neighboring Haar coefficient equations. Lean proves directly in the chart that the homogeneous correction cancels both defects from taking the nonnegative modes. The abstract estimate for the three supplied lifts loses one derivative. The Euclidean three-dimensional Fourier estimate controls pointwise evaluations. [Smooth coefficients](../TransportOkaGrauert/SmoothCoefficient.lean) · [Coefficient equations](../TransportOkaGrauert/ModeTransport.lean) · [Euclidean embedding](../TransportOkaGrauert/SobolevSup.lean) · [Mode correction](../TransportOkaGrauert/RightInverse.lean) | Realize and estimate the three operators on the actual surface and transfer the Euclidean Sobolev estimate through a bounded extension and chart localization. |
| Pass from local solutions to a frame | Genuine normalized Haar modes, holomorphic inversion on the closed velocity disk, the mixed transport product identity, and global continuation for arbitrary rank. [Disk inversion](../TransportOkaGrauert/NearIdentity.lean) · [Relative frames](../TransportOkaGrauert/ChartOrbits.lean) · [Endpoint theorem](../TransportOkaGrauert/NearDiagonal.lean) | The formal endpoint theorem takes the locally uniform single-source estimate as its hypothesis. |
| Pass to bundles | An abstract correspondence on classes carries the zero orbit to the product bundle. [Descent](../TransportOkaGrauert/Descent.lean) | Uniformization into the disk chart, the boundary-degenerate complex structure, and the geometric correspondence of Proposition 4.12. |

The other available continuation proof differentiates a smooth frame in the path parameter and uses a homogeneous ODE for the transport error. The finite-step argument above requires only a bound on the selected solutions. [Path derivative and Grönwall argument](../TransportOkaGrauert/PathContinuation.lean)

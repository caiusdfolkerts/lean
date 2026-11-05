# Ellipsoids are determined by their intrinsic volumes

## The mathematical targets

This note explains the Lean development accompanying *Ellipsoids are determined by their intrinsic volumes*. Its central objects are ordinary Euclidean ellipsoids and ordinary intrinsic volumes. The correspondence with those objects is part of the mathematical work: neither a semiaxis integral nor a coefficient transformation is substituted for geometric volume in the definitions.

An ellipsoid in dimension $n$ is represented by a centre $c$, an orthogonal frame $U$, and positive semiaxes $a_1,\ldots,a_n$:

$$
E=c+U\operatorname{diag}(a_1,\ldots,a_n)\overline B^n.
$$

The development also gives both directions of the equivalence between this representation and an arbitrary invertible affine image of the ball. Equal semiaxes are permitted throughout. Congruence means that an ambient Euclidean isometry carries one actual body onto the other.

**Reconstruction.** The formal statement corresponding to Theorem 1.1 quantifies over every dimension and every pair of full ellipsoids. Its hypothesis is equality of $V_1,\ldots,V_n$, and its conclusion is congruence. The zero-dimensional case is included; the analytic argument treats positive dimension.

**Uniform recovery and sharpness.** For $n\ge1$ and $0<a\le b$, the statement corresponding to Theorem 1.2 gives a constant $C=C(n,a,b)>0$ such that every pair with semiaxes in $[a,b]$ satisfies

$$
\min_{\pi\in S_n}\max_i |a_i-b_{\pi(i)}|
\le C\left(\max_{1\le k\le n}|V_k(E)-V_k(F)|\right)^{1/n}.
$$

The sharpness neighborhoods use this unordered-semiaxis distance. For every radius $r\in(a,b)$, exponent $\gamma>1/n$, neighborhood size $\delta>0$, and proposed constant $C>0$, there are two ellipsoids, each within distance $\delta$ of the radius-$r$ sphere, violating the estimate with exponent $\gamma$. When $n\ge2$, the second clause additionally requires their top intrinsic volumes to agree.

**The coefficient theorem.** Theorem 2.1 concerns an enlarged domain, not merely coefficient vectors arising from real-rooted polynomials. With positive endpoint coefficients fixed, all internal coefficients may be zero. Its conclusions include injectivity, positive principal minors of the actual Jacobian, smooth extension around the closed orthant, the strict coefficient bound, properness, and a smooth embedding as a manifold with corners.

## Ordinary intrinsic volumes enter through geometry

The native definitions use Lebesgue measure on `EuclideanSpace` and the Minkowski sum

$$
P_E(t)=\operatorname{vol}_n\bigl(E+t\overline B^n\bigr),\qquad t\ge0.
$$

The polynomial `steinerInterpolant` interpolates the values of this function at $0,1,\ldots,n$. Its coefficient of degree $n-k$, divided by the volume $\kappa_{n-k}$ of the corresponding unit ball, defines `intrinsicVolume E k`. In positive dimension, a separate theorem proves that this polynomial equals $P_E(t)$ for *every* nonnegative $t$. This connects the interpolated coefficients to the ordinary Steiner coefficients. The general ellipsoid statement is `FullEllipsoid.hasSteinerFormula`.

For an axis-aligned ellipsoid, write $A=\operatorname{diag}(a_i)$ and set

$$
h(x)=\|Ax\|,\qquad s(x)=\frac{A^2x}{h(x)}\quad(x\ne0).
$$

Here $h$ is its support function and $s(x)$ is its support point in direction $x$. The geometric proof uses the homogeneous normal-offset map

$$
N_t(x)=\|x\|s(x)+t x,\qquad N_t(0)=0.
$$

Its image of the closed unit ball is exactly the parallel body. Injectivity follows from support inequalities and equality in Cauchy--Schwarz. Surjectivity is established by maximizing a support ratio on the sphere and applying the vanishing derivative condition at the resulting extremum. Thus the desired image identity is proved from the sets themselves.

Away from zero, the derivative of $N_t$ is explicit. Its determinant is a degree-at-most-$n$ polynomial in $t$, and it is positive for $t\ge0$. Applying the finite-dimensional change-of-variables theorem on the punctured unit ball gives

$$
P_E(t)=\int_{\overline B^n}\det DN_t(x)\,\mathrm dx.
$$

The omitted point has measure zero in positive dimension. The determinant coefficients are integrable. After integration, the degree bound and uniqueness of interpolation identify the resulting polynomial with `steinerInterpolant`, proving the all-radius identity. Rigid-motion invariance transports the construction to arbitrary centres and orthogonal frames.

The subsequent bridge to the formula used in the paper passes through spherical integration, elementary symmetric functions, Gaussian integrals, and a Mellin integral. Polar coordinates provide their exact normalization. The result for an axis-aligned body is `intrinsicVolume_axisBody_eq_coefficientTransform`. For general ellipsoids it is `FullEllipsoid.volume_eq_coefficientTransform`. The top volume is separately identified as $\kappa_n\prod_i a_i$.

This route proves the needed geometric identity directly for ellipsoids. The formula of Gusakova, Spodarev, and Zaporozhets [GSZ] sets the target; the formal proof supplies its geometric and analytic dependencies explicitly, including the exact Mellin convergence ranges.

## The analytic reconstruction argument

Put $x_i=a_i^2$, and let $e_j$ be their elementary symmetric coefficients, with $e_0=1$. The analytic extension fixes arbitrary $e_0,e_n>0$ and allows $e_1,\ldots,e_{n-1}\ge0$. Define

$$
Q(t)=\sum_{j=0}^n e_jt^{2j},\qquad
Q_k(t)=\sum_{j<k}e_jt^{2j},\qquad
F_k(e)=\frac12\int_0^\infty
t^{-k}\frac{Q_kQ'-Q_k'Q}{Q^{3/2}}\,\mathrm dt,\qquad 1\le k<n.
$$

These are literal real integrals in `coefficientTransform`. Their integrability, smooth dependence on coefficients, and derivatives are proved before the resulting Jacobian is used. The estimate $Q(t)\ge e_0+e_nt^{2n}$ controls both ends of the integration interval and allows small negative perturbations around boundary points of the orthant.

The positivity mechanism is Lemma 3.1. For a nonzero positive $\sigma$-finite measure on $(0,\infty)$, let $a_r=\int t^r\,\mathrm d\mu(t)$. With distinct positive exponents $p_i$, its matrix is

$$
C_{ij}=\min(p_i,p_j)\,
a_{3\min(p_i,p_j)}a_{2\max(p_i,p_j)-\min(p_i,p_j)}.
$$

The formal theorem assumes precisely the finite moments in the manuscript; it does not require finite total mass. This matters in the Jacobian application: the measure $t^{-1}Q(t)^{-3/2}\,\mathrm dt$ has infinite mass near zero. Power tilts of the measure are ordered stochastically. Their cumulative probabilities define a Gram matrix $G$. With $d_i=p_i a_{3p_i}$ and $R_{ij}=\min(p_i,p_j)/\max(p_i,p_j)$, the identity is

$$
C=\operatorname{diag}(d)\,(G+G\circ R)\,\operatorname{diag}(d).
$$

The matrix $G$ is positive semidefinite with positive diagonal, whereas $R$ is positive definite. A strict Schur-product argument supplies the required positive definiteness of $C$.

For the coefficient Jacobian $J$, set $m_r=\int_0^\infty t^{r-1}Q(t)^{-3/2}\,\mathrm dt$ and $D=\operatorname{diag}(m_3,m_6,\ldots,m_{3(n-1)})$. Integration by parts identifies the actual derivative with the head--tail formula in Lemma 4.1. Its symmetric part decomposes as

$$
\operatorname{sym}(DJ)=\frac14\sum_{\ell=0}^n e_\ell C^{(\ell)}\succ0.
$$

Each nonzero block is an instance of the moment kernel. The $e_0$ term already gives strict positivity on the whole internal coordinate space. A nonsingular homotopy to the identity then gives every positive principal minor, without treating $J$ itself as a symmetric matrix.

The source proves the needed rectangle univalence theorem directly, in the diagonal-stability form established above. Stiemke's alternative supplies $v>0$ with $Jv>0$, so a short step in direction $-v$ decreases every output. A compact minimal-counterexample argument and induction over faces give global injectivity, including the boundary. This implements the role played by Gale--Nikaido [GN] in the paper. Finally, equality of top volume fixes $e_n$, injectivity fixes the remaining coefficients, and equality of polynomial root multisets gives congruence.

## Stability, multiplicities, and the sharp exponent

The strict inequality $F_k(e)>\sqrt{e_k}$ supplies a bounded coefficient box from bounded output data. Together with continuity, it gives properness on the closed orthant. The nonsingular derivative gives a smooth ambient inverse near each point, including every boundary face. The development also expresses the resulting embedding using Mathlib's standard `EuclideanQuadrant` and its manifold-with-corners model.

For quantitative recovery, the code retains the leading coefficient itself as the last output and uses

$$
\widehat G(e_1,\ldots,e_n)=\bigl(F_1(e),\ldots,F_{n-1}(e),e_n\bigr).
$$

This is `augmentedCoefficientMap`. Its derivative is invertible and the map is injective. On the compact coefficient family arising from semiaxes in $[a,b]$, its inverse satisfies

$$
\|e-f\|_\infty\le L\,\|\widehat G(e)-\widehat G(f)\|_\infty.
$$

Local inverse charts give locally Lipschitz inverses; compactness gives a uniform bound. The volume discrepancy controls this output discrepancy: the first coordinates use $V_k=\kappa_kF_k$, and the last uses $e_n=(V_n/\kappa_n)^2$ with the bounded semiaxis products. This implements the manuscript's normalized volume map without assuming equal top volumes or convexity of the image.

The loss of exponent occurs when coefficients are converted back to roots. For monic polynomials with bounded real roots, the formal estimate is a uniform matching bound of order $\Delta^{1/n}$, where $\Delta$ is their maximum coefficient discrepancy. Multiplicities are retained.

Here the source uses a different proof from the manuscript's Rouché argument. Interpolate the coefficients continuously between the two monic polynomials. A Cauchy root bound and an estimate of the initial polynomial at each moving root keep the roots near the initial root set. Continuity of the root multiset makes the number of roots on each side of a separated vertical line locally constant, hence constant along the homotopy. These count identities match the sorted real endpoint roots. The intermediate polynomials are allowed to have nonreal roots.

Applying this estimate to squared semiaxes and then using the Lipschitz bound for the square root on $[a^2,b^2]$ yields the exponent $1/n$ in Theorem 1.2. There is no lower bound on the separation between semiaxes.

For sharpness, take two monic, simple-real-rooted polynomials $f$ and $g=f-c$, with $c\ne0$ sufficiently small. If their roots are $u_i$ and $v_i$, use squared semiaxes $r^2+\varepsilon u_i$ and $r^2+\varepsilon v_i$. Their monic root polynomials differ only in the constant term, by $c\varepsilon^n$. The maximum coefficient discrepancy is therefore $|c|\varepsilon^n$. Smoothness gives volume error $O(\varepsilon^n)$, while the semiaxis matching distance is bounded below by a positive multiple of $\varepsilon$. For $n\ge2$, rescale both bodies to the volume of the radius-$r$ sphere. Their scale factors tend to one and differ by $O(\varepsilon^n)$, which is $o(\varepsilon)$. The linear separation survives, and homogeneity preserves the $O(\varepsilon^n)$ volume error. Every larger exponent therefore fails even with this fixed volume.

## References

[GN] D. Gale and H. Nikaido, The Jacobian matrix and global univalence of mappings, Math. Ann. 159 (1965), 81–93, Theorem 4 and Remark 4.3.

[GSZ] A. Gusakova, E. Spodarev, and D. Zaporozhets, Intrinsic volumes of ellipsoids, Zap. Nauchn. Sem. POMI 515 (2022), 121–140; arXiv:2206.14002, Theorem 1.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The smaller topic files in `reading/` show the development before assembly; they are provided for navigation and are not an alternative build. The compiler checks the corresponding assembled development in `source/`. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

# Volume polynomials and the Heine–Shephard problem

## The mathematical objects

The basic definition uses actual convex sets and actual Lebesgue volume. In Lean, `Body d` is the type of nonempty compact convex subsets of `Fin d` $\to\mathbb R$. Lower-dimensional sets are included. A coefficient vector `Coefficients n d` has one real entry for every multi-index of total degree $d$. The assertion `Realizes K c` means

$$
\sum_{|\alpha|=d}c_\alpha t^\alpha
=\operatorname{vol}_d\!\left(\sum_{i=1}^{n}t_iK_i\right)
\qquad(t_i\geq0).
$$

The locus `VolumeLocus n d` quantifies over all such tuples $K$. Thus polynomiality, nonnegativity of coefficients and the principal conclusions are not built into the realization relation.

The equivalence with homogeneous multivariate polynomials is proved, including uniqueness from evaluation on the nonnegative orthant. Mixed volume is then extracted with the paper's normalization:

$$
c_\alpha=\frac{d!}{\alpha!}
V(K_1[\alpha_1],\ldots,K_n[\alpha_n]).
$$

The supporting polynomiality argument first treats finite polytopes by facet and pyramid decompositions, and then passes to arbitrary compact convex sets by Hausdorff approximation. This also establishes coefficient nonnegativity, continuity and the operations on mixed volumes needed later.

The all-dimensional Alexandrov--Fenchel proof proceeds through common simple polytopes, their support-coordinate volume forms, and a finite matrix argument with a facetwise induction. A proved common refinement and Hausdorff continuity extend the inequality to arbitrary compact convex bodies, including degenerate ones. The inequality is a supporting theorem of the development, rather than an assumption on the realizations under consideration.

Coordinate spaces carry the usual product norm. Where an inner-product argument is needed, an explicit linear equivalence transports the body and the measure. In particular, planar fiber averaging does not assume an inner-product instance for a space carrying the sup norm. Every change of coordinates either preserves Lebesgue measure or retains its positive Jacobian factor until it is cancelled mathematically.

## The sharp semialgebraicity threshold

The main entry points are `Main.semialgebraicity_iff` and `Main.polytope_locus_not_semialgebraic`, both in `reading/volume_polynomials/main_semialgebraicity.lean`. All names in this note have the prefix `VolumePolynomials.` unless otherwise stated. The first theorem has exactly the hypotheses $n\geq1$ and $d\geq3$; the second has $n,d\geq3$. The polytope locus requires each body to be a finite convex hull with nonempty ambient interior, with no bound on its number of vertices.

The geometric reduction starts with the seven-term cubic

$$
\begin{align*}
P_{\alpha,s,z}(X)
={}&3\alpha X_1^2X_2+3\alpha X_1^2X_3
+3X_1X_2^2+3X_2^2X_3\\
&+3sX_1X_3^2+3X_2X_3^2+6zX_1X_2X_3,
\qquad \alpha>0,\quad0<s<1.
\end{align*}
$$

The degree--dimension theorem reads the affine dimensions of partial Minkowski sums from monomial support. For this cubic, each body is planar. If the three planes shared a line, the six repeated mixed coefficients would satisfy a cyclic product identity. Their prescribed values instead give the ratio $s$, so $s\ne1$ excludes that possibility. Compatible coordinates then put the bodies in the three coordinate planes.

`PlanarInteraction.proposition_3_1` is an exact equivalence with planar data $A,B,C,T$ satisfying

$$
\begin{array}{c|c|c}
&\text{coordinate widths}&\text{area}\\ \hline
A&(1,s)&\alpha T\\
B&(1,1)&T\\
C&(1,1)&T
\end{array}
\qquad T>0,\qquad 6V_3(A,B,C)=2Tz.
$$

The structure used for the lifted case allows $\operatorname{area}(A)\geq\alpha T$; the cubic equivalence explicitly adds the equality. Its converse uses the actual coordinate-plane bodies and a common dilation by $(3/T)^{1/3}$.

The planar interaction theorem constructs a body $Q$ of widths $(1,1)$ such that $6V_3(A,B,C)=2V_2(A,Q)$ for every $A$. It applies to arbitrary compact convex $B,C$ with the prescribed unit coordinate widths, including zero-area inputs. The logarithmic estimate comes from their corner slope measures. The analytic argument proves an exponential-kernel estimate for arbitrary finite signed measures satisfying the required exponential-moment hypothesis, then applies it to the determinant convolution of the $2\times2$ slope-measure matrix. The geometric upper estimate and polygonal lower witnesses give explicit constants in

$$
c\,s^3\log(1/s)\leq r(s)-b(s)
\leq C\,s^3\log(1/s),\qquad
r(s)=\frac{1+s+\sqrt{1+s^2}}2.
$$

Here $b(s)$ is the infimum of a fiber of the original coefficient locus. Closedness and nonemptiness prove that this infimum is attained. The semialgebraic obstruction is applied to that actual minimum, rather than to a separately defined geometric optimization problem.

For dimension $3+k$, the slice is

$$
X_1^kP_{c_k\alpha,s,z},\qquad c_k=\frac{2(k+1)}{k+2}.
$$

The forward proof constructs a fiber body from each original realization. Fubini gives the factor $t_1^k$; the common-line contradiction works with the integrated fiber area and transverse width. A Minkowski average is constructed by finite averaging and compactness, preserving the needed linear functionals. Continuity on the interior and the null boundary of a convex body justify integration. The sharp Berwald estimate then gives $\operatorname{area}(A)\geq\alpha T$. For $k=0$, the base measure is the zero-dimensional Lebesgue measure and the area identity is exact. Conversely, the simplex-cone construction has the required first two height moments and preserves the property of being a finite convex hull.

The negative result for three bodies extends to $n\geq3$ by a polynomial coefficient embedding and its exact preimage identity. The full-dimensional polytope clause uses a separate density theorem: the closure of that polytope locus is the whole convex-body locus. Semialgebraic closure is supplied by the real-algebraic dependency chain. For $n\leq2$, Appendix A is formalised with all zero patterns and the full separated-index quadratic inequalities; its ordinary coefficients are connected explicitly to the binomial-normalized sequence.

## Shape forcing and the analytic area function

`Main.shape_forcing` packages the whole of Theorem 1.2. Its witnesses are finite lists of rational polynomial equalities and strict inequalities. The implementation uses a concrete system of $39$ equalities and $8$ inequalities. The theorem concerns every coefficient vector satisfying this system and every realization of that vector.

After a proved affine normalization, extrusion identities turn the conditions into planar mixed-area equalities. Equality in the planar Minkowski inequality identifies the relevant projected bodies up to translation. Following these identifications around the three planes produces the return matrix

$$
M=\begin{pmatrix}0&1\\-1&2/3\end{pmatrix}.
$$

The resulting fixed equation identifies the specified body, up to an affine copy, with the literal infinite Minkowski sum

$$
K_\lambda=\sum_{j\geq0}\lambda^jM^j[-e_1/2,e_1/2],
\qquad0<\lambda<1.
$$

The bridge to this series is stated separately from the fixed equation: it describes all convergent choices of points from the summand segments. The canonical nine-body construction supplies the converse existence needed for the exact projection of the finite system onto the area graph.

Irrational rotation gives infinitely many actual exposed edges. Their directions and the semialgebraic boundary argument establish that the body is not semialgebraic; affine transfer then applies this conclusion to every realization. The area calculation is

$$
a(\lambda)=\frac1{(1-\lambda^2)\sin\theta}
\sum_{j\geq1}|\sin(j\theta)|\lambda^j,
\qquad \cos\theta=\frac13.
$$

The analytic endpoint retains the actual complex power series and its derivatives at zero. Rational Taylor coefficients, analyticity on the open unit disk and the absence of local continuous extensions at every point of the unit circle are separate conclusions. The latter is stronger than the required obstruction to analytic continuation. Transcendence is also expressed literally over `RatFunc` $\mathbb R$, using the injective rational-function algebra of right-hand germs at zero; an explicit polynomial nonrelation on $(0,1)$ accompanies it.

## Countable inequalities and rational reconstruction

`Main.countable_characterization` gives, for every finite number of bodies $n$ and every $d>0$, an effective sequence of rational homogeneous quadratic forms $Q_j$ such that

$$
c\in\mathcal V_{n,d}\quad\Longleftrightarrow\quad
(\forall\alpha,\ c_\alpha\geq0)\quad\text{and}\quad
(\forall j,\ Q_j(c)\geq0).
$$

The rational matrices are given by the executable definition `Main.volumeInequalityMatrix`; an evaluation identity connects them to the homogeneous polynomials. The formal statement also includes $n=0$.

The geometric input is an explicit affine normalization into a fixed box, followed by finite rational nets for tuples of convex bodies. Rational elimination, rational hull tests and certified volume approximation make the finite nets effective. Inner and outer cube counts bound each sampled volume; rational Lagrange interpolation then gives coefficient approximations with proved, vanishing errors in both directions. The net centers therefore need not be exact coefficient vectors of their associated polytopes. Homogeneous rational quadratic forms separate a nonrealizable normalized coefficient vector from these compact approximating sets. Scaling returns the criterion to the original cone, including the zero vector.

A computable coefficient vector is supplied through a rational name $a_h$ with $|c_\alpha-a_h(\alpha)|\leq1/(h+1)$ for every $h,\alpha$. A certificate checks either a negative coefficient or a strictly negative quadratic value using only finitely many rational approximations. The relevant endpoints are:

> `Main.nonrealizable_strict_inequality`\
> `Main.finite_rational_certificate`\
> `Main.rational_rejection_terminates`.

They provide strict separation, certificate soundness and completeness, and exhaustive enumeration, respectively.

`Main.rational_polytope_reconstruction` supplies actual finite rational vertex lists. Finite paths impose both coefficient accuracy and successive Hausdorff-distance bounds. Lexicographic prefix stabilization and summable tail bounds prove convergence of the entire output sequence to an actual realizing tuple. The ambient box is computed from the input name, and the construction includes the zero vector without deciding whether a real coefficient is zero. No effective convergence rate is asserted. For a nonrealizable named input, a finite stage rejects; successful finite stages alone are not presented as a realization certificate.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The smaller topic files in `reading/` show the development before assembly; they are provided for navigation and are not an alternative build. The compiler checks the corresponding assembled development in `source/`. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

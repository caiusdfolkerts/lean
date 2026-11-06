# The Wishart product inequality and spectral correlation

## The mathematical targets

The central result is a correlation inequality for actual Wishart measures. If

$$
X\sim W_p(\alpha,\Sigma),\qquad \alpha>p-1,\quad \Sigma\succ0,
$$

partition the coordinates into disjoint nonempty sets and put $\Delta_i=\det X_{I_i,I_i}$. For arbitrary real exponents $\nu_i\ge0$ and any selected block $j$, Theorem 1.1 states

$$
\mathbb E\prod_i\Delta_i^{\nu_i}
\;\ge\;
\mathbb E\Delta_j^{\nu_j}\,
\mathbb E\prod_{i\ne j}\Delta_i^{\nu_i}
\;\ge\;
\prod_i\mathbb E\Delta_i^{\nu_i}.
$$

All these moments are finite. Equality in the full product inequality holds exactly when the covariance blocks between distinct active factors vanish. An active factor has positive exponent; an exponent zero imposes no independence condition.

The endpoint is `WishartVerification.theorem_1_1` in [core05](source/wishart/verified/core05.lean). It uses the density-defined nonsingular Wishart measure and an arbitrary admissible real shape. A Gaussian Gram model by itself would cover only integer shapes. The separate theorem `theorem_1_1_of_hasLaw` transports the result to a random matrix with the specified distribution. The [literal principal statement](source/verification/statements_principal.lean) fixes the determinant integrals and the equality condition independently of inferred theorem-type aliases.

The remainder of the development establishes the paper’s overlapping-compression extensions, singular integer laws, inverse-Wishart and beta-II results, complex and quaternionic analogues, and the examples and closure assertions in the final section. Precise declaration names and source locations are collected in the [theorem correspondence](verification/theorem-scope.md).

## Regression at real shape

The Wishart measure is constructed on the finite-dimensional space of symmetric matrices. Its density is proportional to

$$
(\det X)^{(\alpha-p-1)/2}
\exp\!\left(-\tfrac12\operatorname{tr}(\Sigma^{-1}X)\right)
\mathbf 1_{X\succ0}.
$$

Normalization, measurable matrix operations, changes of variables, and marginal and congruence identities belong to the support development. They are used to prove the regression law; the regression formula is not an extra assumption on the measure.

After whitening a selected block of size $q$, write

$$
\Sigma=
\begin{pmatrix}I_q&K\\K^T&K^TK+C\end{pmatrix},\qquad C\succ0.
$$

The conditional matrix has the representation

$$
X=
\begin{pmatrix}0&0\\0&W\end{pmatrix}+Y^TY,
\qquad
Y=[S^{1/2},\;S^{1/2}K+G],
$$

where $S\sim W_q(\alpha,I)$, $W\sim W_{p-q}(\alpha-q,C)$, and the rows of $G$ are independent centered Gaussian vectors with covariance $C$, independently of $S$ and $W$. Admissibility of the residual shape follows from $\alpha>p-1$.

The formal proof identifies the pushforward of the product of these concrete measures with the original Wishart measure. The change of variables uses the Schur complement and the determinant and trace identities in the density. This makes the result available at every real admissible shape and gives a usable integration formula for the later comparisons. The main regression source is [core01](source/wishart/verified/core01.lean), supported by the vendored Wishart modules.

## Why a determinant product increases with a Gaussian mean

Fix a positive semidefinite covariance $C$ of rank $r\ge1$, a real shape $N>r$, and a vector $v$. Let $W$ have shape $N-1$ and covariance $C$ on its range, independently of $z\sim N(0,C)$. The varying matrix is

$$
V_t=W+(z+\sqrt t\,v)(z+\sqrt t\,v)^T.
$$

Lemma 3.1 assumes that $g$ is $C^2$ on an open neighborhood of the positive semidefinite cone, with polynomial bounds for $g$, $Dg$, and $D^2g$. Its radial identity is

$$
4tF''(t)+2NF'(t)=\mathbb E\,\mathcal L_{N,v}g(V_t),
\qquad F(t)=\mathbb E g(V_t).
$$

The operator has a first-order part $2N Dg[vv^T]$ and a second-order part obtained by averaging the second derivative along $v\xi^T+\xi v^T$, where $\xi\sim N(0,V)$. Its quadratic form $\Gamma(g,g)$ is nonnegative, and

$$
\mathcal L(e^h)/e^h=\mathcal Lh+\Gamma(h,h).
$$

The formal proof retains exactly this finite-order hypothesis. A cutoff extends the test to a global $C^2$ function with the same value, differential, and Hessian on the cone. Polynomial bounds are needed only on that support. Compactly supported Stein identities extend to this class, and differentiation under the integral uses only the first two derivatives. Writing $J(s)=\mathbb E g\{W+(z+sv)(z+sv)^T\}$, the proof shows that $J$ is even and twice differentiable, giving $F'(0+)=J''(0)/2$ and the same finite right limit for $F'(t)$. The integrating-factor argument assumes nonnegativity of the expected operator itself.

For real shape, scalar regression and covariance under rectangular congruence give the identity for arbitrary mean directions. A reduced covariance factor has exactly $\operatorname{rank} C$ columns, so the shape hypothesis is precisely $N>\operatorname{rank} C$. The residual law is an explicit pushforward of the standard Wishart density, independently of an ambient Gaussian with covariance $C$. For integer shape, covariance regularization extends the identity to every positive semidefinite covariance, including zero. The endpoints are [lemma_3_1_real](source/wishart/verified/lemma_3_1_real.lean) and [lemma_3_1_integer](source/wishart/verified/lemma_3_1_integer.lean). Their [literal statement checks](source/verification/statements_radial_c2.lean) spell out the local $C^2$ and polynomial hypotheses, ordinary derivatives, finite boundary derivative, probability mass, and integrability.

For determinant products, the logarithmic generator can be estimated using compressed inverse matrices. The positive quadratic term then converts a logarithmic estimate into an estimate for the product. A positive regularization makes the matrix derivatives legitimate; polynomial envelopes justify removing it. A single remaining determinant admits a stronger direct stochastic comparison under a Gaussian mean shift. This is the reason the final pair can avoid the rank requirement imposed on a general remaining product.

In regression coordinates, changing one selected eigenvalue changes the length of just one Gaussian mean row. The radial result therefore makes the conditional remaining product increasing in that eigenvalue. This is the analytic step that connects regression with spectral association.

## Ordered eigenvalues, association, and equality

The relevant ordered eigenvalue laws have a density of the form

$$
\prod_i w_i(\lambda_i)\prod_{i<j}(\lambda_j-\lambda_i)^b,
\qquad a<\lambda_1<\cdots<\lambda_q<b_0,
$$

with positive weights, positive repulsion exponent, and finite normalizing integral. The formal association argument proceeds by conditioning on the last coordinate. The conditional lower-coordinate law is another ordered law of the same kind. Its density ratio between two conditioning values is increasing, which orders its increasing expectations. The total covariance identity finishes the induction. Truncation gives nonnegative functions and extended expectations; the strict version keeps the strictness and moment hypotheses needed for equality.

For the whitened selected Wishart block, the eigenframe is independently Haar distributed. Averaging the remaining conditional factor over this frame preserves its coordinatewise monotonicity. Association now separates the selected factor from the product of the others. Iterating gives the full product bound.

If two active blocks are coupled through nonzero covariance, a Gaussian mean changes in a nonzero direction and the relevant stochastic comparison is strict. The strict ordered-eigenvalue result then makes the product inequality strict. Conversely, vanishing cross-covariance between active blocks gives independence. This proves the equality characterization rather than merely its sufficient direction.

Proportional shifts have the form $X_{I_i,I_i}+c_i\Sigma_{I_i,I_i}$, with $c_i\ge0$. Whitening turns these into scalar shifts. The same mechanism applies to the tilted eigenvalue laws and proves Proposition 4.1: the joint-to-product moment ratio is nondecreasing in every exponent, and the full product tilt dominates the selected-factor tilt on increasing selected spectral tests. These results are in [proportionate_shifts01](source/wishart/verified/proportionate_shifts01.lean).

## Overlap and the three real spectral classes

For a full-column-rank $p\times k_i$ matrix $B_i$, a compression is $B_i^TXB_i$. Different compressions may overlap. Its covariance is $C_i=B_i^T\Sigma B_i$, and the normalized compression is

$$
S_i=C_i^{-1/2}B_i^TXB_iC_i^{-1/2}.
$$

The three classes in Section 5 have different sufficient rank conditions. The complete endpoints retain that distinction.

| Class | Selected proper factor of rank $q$ | Full product after constant and full-rank factors are removed |
| --- | --- | --- |
| Increasing geometrically log-convex functions of shifted determinants | Final pair unrestricted; otherwise $\alpha\ge\min\{q+\max_{i\ne j}k_i,p+1\}$ | At most two remaining factors unrestricted; otherwise $\alpha\ge\min\{k_{(1)}+k_{(3)},p+1\}$ |
| Convex spectral gauges, followed by increasing geometrically log-convex functions | Final pair unrestricted; otherwise $\alpha\ge q+1$ | At most two remaining factors unrestricted; otherwise $\alpha\ge k_{(3)}+1$ |
| $\exp h_i(\log\lambda(S_i+c_iI))$, with finite convex symmetric coordinatewise increasing $h_i$ | $\alpha\ge\min\{q+\max_{i\ne j}k_i,p+1\}$ | At most one remaining factor unrestricted; otherwise $\alpha\ge\min\{k_{(1)}+k_{(2)},p+1\}$ |

The ranks are ordered decreasingly. Full-rank factors can be split by spectral association on the entire whitened matrix. Constants are removed using their actual almost-sure behavior. For disjoint principal blocks, the complete statements include the paper’s improved shape ranges and the empty-block clauses. In particular, the two-block log-spectral statement retains the sufficient condition $\alpha\ge p$; it is not silently replaced by the stronger determinant-specific final-pair result.

A convex spectral gauge is represented as a supremum of positive linear forms on the positive cone. Finite smooth approximations preserve the generator estimate. The logarithmic spectral class uses supporting planes, the variational characterization of products of leading eigenvalues, and finite frame and power-mean approximations. Monotone convergence supplies the general finite convex profile. Boundary values are defined by a positive scalar regularization tending to zero and are proved to have the required continuity and comparison properties.

The real rank restrictions have a concrete obstruction. For $X\sim W_2(\alpha,I)$, put $S=X_{11}$ and

$$
Q_\pm=(e_2\pm a e_1)^TX(e_2\pm a e_1).
$$

The overlap calculation gives

$$
\operatorname{Cov}(S,Q_+Q_-)
=4\alpha a^2\bigl[\alpha-2+(\alpha+2)a^2\bigr].
$$

It is negative for $1<\alpha<2$ and $0<a^2<(2-\alpha)/(\alpha+2)$. The rational choice $\alpha=3/2$, $a=1/4$ gives $-27/256$. The [overlap source](source/wishart/verified/overlap_obstruction.lean) obtains the moments from the actual Wishart law and its Bartlett representation. It also proves the displayed conditional expectation $\mathbb E[Q_+Q_-\mid S]=\alpha(\alpha+2)+2(\alpha-2)a^2S+a^4S^2$ on that realization, together with its Wishart pushforward identity. The assertion is more than an algebraic calculation under assumed moments.

Corollary 5.4 treats actual integer Gaussian Gram laws with positive definite covariance, including singular Gram matrices when there are fewer rows than columns. Almost surely constant factors, zero determinants, and the finite nonnegative extension of the outer functions at zero are handled explicitly. The finite moments of nonnegative determinant powers follow from polynomial Gaussian growth. The complete Section 5 interfaces are in [real_clauses01](source/wishart/verified/real_clauses01.lean).

## Inverse-Wishart and the exact moment threshold

The inverse law is fixed by

$$
Y\sim IW_p(\beta,\Omega)
\quad\Longleftrightarrow\quad
Y^{-1}\sim W_p(\beta,\Omega^{-1}),
\qquad \beta>p-1.
$$

Its block regression has a useful different shape: after conditioning, the entire matrix is an affine Loewner-increasing function of the selected block, with independent coefficients. Consequently arbitrary nonnegative measurable spectral factors with a common monotonicity direction satisfy the comparison, with the finite-moment assumptions stated in Theorem 6.1. There is no overlap rank restriction. Both increasing and decreasing factors are covered. The [positive-spectrum endpoint](source/wishart/verified/inverse_association01.lean) states the functions on their natural ordered positive domain.

For positive shifted determinant powers, the exact joint finite-moment condition is

$$
2\sum_{i:\,k_i>0}\nu_i<\beta-p+1.
$$

The positive-rank restriction in the sum is essential. Empty determinants are one, independently of their exponent. Sufficiency follows by comparing compressed determinants with powers of the ambient determinant after inversion and integrating against the Wishart density. Necessity isolates the smallest eigenvalue near zero while keeping the others in a compact interval away from zero and the eigenframe in an open set on which all active compressions see that direction. Thus overlaps do not change the threshold.

For an unshifted full-column-rank compression, the moment is expressed through the multivariate gamma ratio and the determinant of its compressed covariance. The all-rank endpoint includes the zero-dimensional gamma convention and its separate unrestricted moment domain. Nonpositive powers allow every nonnegative shift, including zero, and satisfy the comparison without the positive-tail restriction. These conclusions, including the counterexample to an uncorrected rank-zero threshold, are exposed in [real_tail01](source/wishart/verified/real_tail01.lean).

## Beta-II laws are constructed, not postulated

The matrix beta-II development proves that the printed determinant density is normalized and agrees with the independent congruence mixture

$$
X=Y^{1/2}ZY^{1/2},\qquad
Y\sim IW_p(\beta,\Omega),\quad
Z\sim W_p(\alpha,I).
$$

The equivalent conditional Wishart hierarchy is also identified. The real Wishart comparison acts inside the mixture and the inverse-Wishart comparison acts outside it. The endpoint uses an actual-law almost-sure constant condition when removing factors; it does not replace that condition by a convenient but stronger symbolic test.

The exact moment range passes through the mixture. The bound $X\preceq\|Z\|Y$, together with finite positive moments of $\|Z\|$, proves sufficiency. An event of positive probability on which $Z\succeq I$ proves necessity. The unshifted moment formula factors into a Wishart gamma ratio and an inverse-Wishart gamma ratio. As above, zero-column factors contribute one and no threshold exponent.

The concrete density, hierarchy, support, constant-factor removal, rank condition, and moment statements have separate [literal beta-II gates](source/verification/statements_beta_ii.lean) and [moment gates](source/verification/statements_beta_ii_moments.lean). The underlying construction is in [real_beta_ii01](source/wishart/verified/real_beta_ii01.lean) and [real_beta_ii02](source/wishart/verified/real_beta_ii02.lean).

## Complex and quaternionic fields

For $\mathbb F=\mathbb C$ or $\mathbb H$, let $b=\dim_{\mathbb R}\mathbb F$, so $b=2$ or $4$. The density in Section 7 is proportional to

$$
(\det X)^{\frac b2(\alpha-p+1)-1}
\exp\!\left(-\tfrac b2\operatorname{Re}\operatorname{tr}(\Sigma^{-1}X)\right),
\qquad X\succ0,\quad\alpha>p-1.
$$

Each real Gaussian component in the integer Gram model has variance $1/b$. The source proves the density normalizers, probability mass, covariance transformations, and Gram pushforwards for these conventions. Quaternionic positivity, full column rank, real eigenvalues, and the Moore determinant are connected to the concrete complex representation; the literal field gates fix those meanings.

The decisive analytic fact is that the compressed log determinant is subharmonic under one row update over either field. The real obstruction therefore disappears. Supporting-plane and leading-eigenvalue approximations extend this property to every finite convex symmetric coordinatewise increasing logarithmic profile. Regression and spectral association then give every selected split and the full product inequality for arbitrary overlapping compressions.

The theorem covers both all admissible real shapes of the normalized density and all positive integer Gaussian Gram shapes, including singular Gram matrices. As in the paper, the covariance is positive definite; singularity here concerns the random Gram matrix. Boundary values on the positive semidefinite cone are part of the definition and proof. Determinant powers have finite moments; the general profile comparison permits extended expectations. The final theorem is in [field_residual08](source/wishart/verified/field_residual08.lean), with concrete statement checks in [statements_field](source/verification/statements_field.lean).

## Examples and closure

The final section instantiates the spectral class with nonnegative-coefficient symmetric polynomials, elementary and Schur-positive expressions, positive trace powers, and powers of unitarily invariant norms. The comparison statements identify these matrix expressions with their log-spectral profiles, including singular boundary values. The norm argument passes through a symmetric absolute norm on singular values.

Products, nonnegative sums, and increasing geometrically log-convex outer composition preserve the appropriate profile class. The [closure module](source/wishart/verified/spectral_profile_closure.lean) proves the profile properties and boundary identities. A sum with every effective coefficient zero is handled separately, since its logarithm is not a finite profile.

The paper also claims finite moments for the uncomposed polynomial, trace-power, and invariant-norm-power examples. This requires a separate argument: a general convex logarithmic profile can grow too quickly for a finite expectation. [Spectral example moments](source/wishart/verified/spectral_example_moments.lean) supplies polynomial and norm envelopes, [field spectral moments](source/wishart/verified/field_spectral_moments.lean) obtains the needed eigenvalue moments from the actual density and Gram laws, and [field example finite moments](source/wishart/verified/field_example_finite_moments.lean) proves the individual and joint finite-moment conclusions. No integrability assumption is added to those endpoints.

## Manuscript corrections

The paper supplied with the recovered development had two points requiring correction for an exact correspondence.

**Anderson argument, page 14.** A section-volume root need not be concave across empty sections. The replacement argument compares opposite sections. If $A_r$ is the section obtained by translating the symmetric convex sublevel set by $-rv$ and intersecting a centered ellipsoidal density layer, then $A_{-r}=-A_r$. For $0\le s\le r$ and $r>0$, choosing $\theta=(1+s/r)/2$ gives

$$
\theta A_r+(1-\theta)A_{-r}\subseteq A_s.
$$

When $A_r$ has positive volume, Brunn–Minkowski and symmetry give $|A_s|\ge|A_r|$; when it has zero volume, the comparison is immediate. Integrating the density layers proves the required Gaussian monotonicity. The Lean proof uses its valid Anderson/Prékopa–Leindler infrastructure.

**Moment threshold, pages 18 and 20.** The exponent sum must exclude rank-zero compressions. The corrected formula is the positive-rank sum displayed above. The formalisation includes both the corrected all-rank theorem and a rank-zero counterexample to the uncorrected condition.

The corrected PDF retains all other pages exactly at the rendered-page level. The [original manuscript](verification/original-paper.pdf) is retained for comparison. [The correction script](verification/correct_manuscript.py) checks its hash before applying the changes, and [the correction record](verification/manuscript-corrections.json) records the original and final hashes, replacement text, and affected regions. These are disclosed changes to the manuscript, not extra hypotheses hidden in the formal statements.

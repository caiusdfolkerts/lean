# Universal cold spots of E8 and related lattices

For a lattice $L$ in Euclidean space, the Gaussian potential is

$$
\Theta_L(\alpha,x)=\sum_{v\in L}e^{-\alpha\lVert v-x\rVert^2},
\qquad \alpha>0.
$$

A cold spot minimises this potential. A deep hole maximises the distance to the nearest lattice point. The formalisation proves that these two sets coincide for every positive parameter for $E_6$, $E_8$, $E_7^*$, $BW_{16}$, and every $D_n^+$ with even $n\geq8$. It also proves the sharp values, the complete equality sets, the covering radii, the numbers of translation classes, and the extension to positive Gaussian mixtures. The analytic inequality of Theorem 3.1, the theta inequality of Proposition 3.2 and the Eisenstein identity of Proposition 8.1 are proved with their full quantifiers and equality cases.

All references to theorem numbers and equations below refer to the paper, *Universal cold spots of E8 and related lattices*. This note explains what the Lean statements mean, their proof dependencies, and the places where the formal proofs take a different route. The source `reading/paper_verification/lattice_paper_theorems.lean` collects the principal lattice statements; the correspondence table below locates the analytic and geometric results. The umbrella import `paper_verification` includes the complex-coordinate and root-normalisation bridges identifying the formal objects with the paper's lattices.

## The exact statements and their geometric meaning

The theorem `lattice_theorem_1_1` is one conjunction containing the five cases of Theorem 1.1. Its $D_n^+$ component has the literal form

$$
\forall n\in\mathbb N,\quad 8\leq n\ \Longrightarrow\
n\text{ even}\ \Longrightarrow\
\forall\alpha>0\ \forall x\in\mathbb R^n,\quad
\operatorname{Cold}_L(\alpha,x)\ \Longleftrightarrow\
\operatorname{Deep}_L(x).
$$

There is no divisibility-by-eight restriction and no restriction of $x$ to a finite candidate set. The $E_6$, $E_8$ and $BW_{16}$ cases quantify over all of $\mathbb R^6$, $\mathbb R^8$ and $\mathbb R^{16}$. The $E_7^*$ case uses the full seven-dimensional zero-sum subspace of $\mathbb R^8$. Gaussian convergence, lattice identifications and the geometric classification are proved dependencies; they do not survive as extra assumptions of this theorem.

The coordinate definition

$$
D_n^+=\{z\in\mathbb Z^n:\textstyle\sum_i z_i\text{ is even}\}
\ \cup\
\left(\{z\in\mathbb Z^n:\textstyle\sum_i z_i\text{ is even}\}
+\tfrac12\mathbf1\right)
$$

is translated directly into `dPlusSet`. For any coordinate set $L$, `setGaussian` is the infinite sum over the subtype of actual points of $L$. The reindexing maps used later are proved bijections, so coset formulae count each lattice point once. The geometric definitions are independent of the analytic ones:

$$
\operatorname{sqDist}(x,y)=\sum_i(x_i-y_i)^2,
\qquad
\operatorname{squaredDepth}(L,x)=\inf_{v\in L}
\operatorname{sqDist}(x,v).
$$

The predicate `IsColdSpot` globally minimises `setGaussian`; `IsDeepHole` globally maximises `squaredDepth`.

This distinction between coordinate functions and Euclidean space matters in Lean: the ordinary norm on a finite function type is a supremum norm. The code explicitly proves that `sqDist` is the square of the *Euclidean* distance after the standard $\ell^2$ conversion. The theorem `squaredDepth_eq_infDist_sq` then identifies the real infimum with squared metric distance to the lattice. Separate equivalences transport both global extremum predicates. These bridges are in `reading/paper_verification/lattice_metric_meaning.lean`; `reading/paper_verification/e7_metric_meaning.lean` proves the corresponding statements for the zero-sum subspace and proves that its dimension is seven.

The two table collectors establish the following values. A radius entry includes both a universal upper bound and a point attaining it. A class entry is the cardinality of the quotient of all real deep holes by the actual lattice translation relation.

| Lattice             | Squared covering radius | Deep-hole classes |
|:--------------------|:-----------------------:|:-----------------:|
| $E_6$               |          $4/3$          |        $2$        |
| $E_8$               |           $1$           |       $135$       |
| $E_7^*$             |          $7/8$          |       $36$        |
| $BW_{16}$           |           $3$           |       $120$       |
| $D_n^+$, even $n>8$ |          $n/8$          | $\binom{n}{n/2}$  |

These are `lattice_covering_radius_table` and `lattice_translation_class_table`. For even $n>8$ in the $D_n^+$ family, representatives retain an integer-parity bit as well as their half-coordinate support. After normalising the first coordinate to be integral, these data give a bijection with the $n/2$-element subsets of the coordinates. For $E_8$, the quotient is identified with the nonzero isotropic vectors in its binary quadratic quotient. Finite binary and ternary calculations enter the counts only after a proved bijection with the actual geometric translation quotient.

## The unrestricted analytic inequality

Theorem 3.1 is a statement about every probability measure $\mu$ on $[0,R]$, for every $R>0$. With $G_\mu(f)=\exp\int\log f\,d\mu$, it is

$$
\begin{align*}
G_\mu(\cosh p)^4+G_\mu(\cosh(R-p))^4
&-G_\mu(\sinh p)^4-G_\mu(\sinh(R-p))^4\\
&\geq 2\cosh R\,G_\mu(\cosh(2p-R)).
\end{align*}
$$

Equality holds precisely for a point mass or $\tfrac12(\delta_p+\delta_{R-p})$. The Lean endpoints `hyperbolic_geometric_mean_inequality_literal` and `hyperbolic_geometric_mean_equality_literal_iff` state the displayed inequality and this exact classification. They assume neither finite support nor integrability of the negative logarithm.

The last point requires an explicit construction. Lean's total real logarithm and total Bochner integral cannot by themselves represent the convention $\exp(-\infty)=0$. The formal geometric mean uses

$$
\log_n f=\log\max(e^{-n},f),\qquad
G_\mu(f)=\inf_n\exp\left(\int\log_n f\,d\mu\right).
$$

The regularised exponentials are proved decreasing and convergent. The theorem `geometricMean_eq_extended_integral` proves that this definition is exactly the extended logarithmic integral in the paper: it is zero when the logarithmic loss has infinite integral, and agrees with the usual exponential integral when that loss is finite. Thus an endpoint atom, or an unbounded negative logarithmic integral without such an atom, is handled by the statement itself.

The proof first minimises the hyperbolic objective over the compact space of probability measures on the compact interval. Lower semicontinuity is proved using the regularised moments. The first variation along mixtures supplies a potential whose minimum contains the support of a minimising measure. Zero sinh moments are handled before differentiating logarithms. A continuous exponential transform extends the almost-everywhere variation identity to the whole support, including the endpoint analysis. A strict convexity argument for the normalised curvature then rules out three distinct support points. The resulting two-atom measure is an actual convex combination of Dirac measures, obtained by a representation theorem rather than imposed as a hypothesis.

The scalar two-point argument covers every weight and both boundary atoms. Two proof substitutions make its analytic dependencies practical in Lean. First, `reading/paper_verification/hyperbolic_stieltjes.lean` derives the required resolvent formula from Mathlib's real integral representation of fractional powers. The rational substitution, polynomial cancellation and strict kernel inequality are proved explicitly; no complex cut contour theorem is assumed. Second, `reading/paper_verification/hyperbolic_compact_minimum.lean` replaces the corner asymptotics of the manuscript's Lemma 5.2 by a compact minimisation on $0\leq p\leq q\leq R\leq B$. The scale inequality forces an offending minimum to a boundary. An exact one-sided derivative calculation supplies an inward direction of strict decrease there. This also excludes the unwanted equality cases. The finite scale bound $B$ is chosen from a hypothetical counterexample, so the final result has no bounded-scale restriction.

`reading/paper_verification/hyperbolic_theorem.lean` assembles this chain. For the theta transfer, write $A_\alpha(t)=\sum_{m\in\mathbb Z}e^{-\alpha(m-t)^2}$, $a=A_\alpha(0)$ and $c=A_\alpha(1/2)$. Take $R>0$ with $\cosh R=a^2/c^2$. The quadratic theta identities and the pushforward to the hyperbolic parameter reduce the remaining estimate to

$$
F_{\mathrm{diag}}(t)=(ac)^3A_\alpha(2t)A_\alpha(2t-1/2)
\geq(ac)^4.
$$

Applied at $v=2t$, the product inequality (5) of the paper is strict except at $t=0,1/4,1/2$. An equality measure must therefore be supported on these three points, whose hyperbolic parameters are $R,R/2,0$. The hyperbolic equality classification then gives exactly the four measures in Proposition 3.2, equation (7): $\delta_0$, $\delta_{1/4}$, $\delta_{1/2}$ and $\tfrac12(\delta_0+\delta_{1/2})$.

## The full $D_n^+$ family and the special dimension eight

Theorem 3.3 gives the attained minimum

$$
\min_x\Theta_{D_n^+}(\alpha,x)
=\bigl(A_\alpha(0)A_\alpha(1/2)\bigr)^{n/2}.
$$

The code proves the exact parity decomposition of the lattice sum into products of ordinary and alternating one-dimensional Gaussian factors. Summability precedes every interchange and reindexing. The theta inequality is applied to the uniform empirical measure of the folded coordinates. The dimension argument is proved for every real exponent $k\geq1$ and then specialised to $k=n/8$; it therefore covers all even dimensions in the paper, including those not divisible by eight.

For even $n>8$, equality is exactly the half-grid locus with precisely $n/2$ nonintegral coordinates. For $E_8$ the locus is the union of $e_1+E_8$, the points with four integer and four nonintegral half-integer coordinates, and the vectors $m+\varepsilon/4$ with $m\in\mathbb Z^8$ of odd coordinate sum and $\varepsilon\in\{\pm1\}^8$ having an even number of negative signs. Both parity conditions of the printed quarter-grid description are retained. The endpoints in `reading/paper_verification/dn_theorems.lean` and `reading/paper_verification/e8_paper_theorems.lean` express these literal loci. At $n=8$, the dimension-lift exponent is one, so all four theta equality measures survive. For $n>8$, the strict equality conditions of the power inequality retain only the balanced endpoint measure. Recovering the signs of the alternating factors gives the two parity conditions in the quarter-grid family.

The geometric proof of Proposition 3.4 proceeds independently. Coordinate rounding constructs even-sum integer witnesses in both cosets; the parity-repair lower bound proves that their costs give the actual infimum. An algebraic envelope inequality gives the sharp radius and its equality set. Matching the two independently obtained loci proves the $D_n^+$ and $E_8$ parts of Theorem 1.1.

The one-dimensional extremum result used in this chain is also proved in full. The formal proof replaces the cited Jacobi product argument by overlapping estimates: Gaussian Poisson summation and first-harmonic dominance for $0<\alpha\leq4$, and paired exponential estimates for $\alpha\geq4$. Their union covers every positive parameter. Positivity and the exact zero set of the alternating factor follow from duplication identities and the proved strict extrema.

## Projection and diagonal gluing

### The general transfer statements

The endpoint `rational_orthogonal_lattice_projection_transfer` states Proposition 6.1 in an arbitrary finite-dimensional real inner-product space. Its inputs are a full lattice $L$, rational subspaces $H$ and $H^\perp$, and $t_0\in H^\perp$ where all fibre Gaussians agree for every $\alpha>0$. A set $C_L$ must be the exact minimum set for every $\alpha>0$ and meet the affine slice $H+t_0$. Rationality means that each lattice intersection spans its subspace. The proof constructs

$$
G=L/\bigl((L\cap H)+(L\cap H^\perp)\bigr),
\qquad M=\pi_H(L),
$$

proves $G$ finite, and derives the disjoint coset decomposition from its representatives. Orthonormal coordinate maps preserve the Gaussian sums, distances and extremum predicates; either summand may have dimension zero.

Convergence of every lattice-coset Gaussian follows from discreteness: an inverse-power series dominates its tail. Bijective reindexing then gives $\Theta_L(\alpha,x+t_0)=c(\alpha)\Theta_M(\alpha,x)$, with positivity of $c(\alpha)$ derived from the nonempty fibres. The general Laplace lemma identifies the limit of $-\alpha^{-1}\log\sum_i e^{-\alpha d_i}$ with $\inf_i d_i$ for a nonempty family of nonnegative energies, assuming convergence at one positive parameter. Equal fibre theta functions therefore have a common squared distance $\delta$, giving $d(x+t_0,L)^2=d(x,M)^2+\delta$. The conclusions identify the exact universal minimum set $C_M=\{x\in H:x+t_0\in C_L\}$ and give $\min\Theta_M(\alpha,\cdot)=\min\Theta_L(\alpha,\cdot)/c(\alpha)$. They also prove $C_M=\operatorname{Deep}(M)$ whenever $C_L=\operatorname{Deep}(L)$.

For Proposition 7.1, `lattice_diagonal_gluing` uses the actual finite quotient $M/L$. The glued set is independently defined as pairs in $M$ whose difference lies in $L$, and is identified with the displayed diagonal coset union. Coset coverage, translation of the Gaussian argument, and product factorisation are derived for convergent infinite sums. The paper's named minima $\kappa,\sigma$ are encoded as attained least values of the actual Gaussian ranges; positivity of $\kappa$ follows from an attaining point. The finite-profile defect identity then yields

$$
\Theta_{\Gamma(L,M)}(\alpha,(x,y))\geq
2\kappa\sigma-[M:L]\kappa^2.
$$

Equality holds exactly when both arguments minimise the $M$-sum and, for every coset, at least one shifted argument minimises the $L$-sum. The statement covers every Euclidean dimension and every finite index, including index one.

### Projection to the dual of $E_7$

The formal ambient space is the seven-dimensional hyperplane

$$
H=\{x\in\mathbb R^8:\textstyle\sum_i x_i=0\}.
$$

The root lattice is defined as $E_8\cap H$, and its dual is defined independently by integral Euclidean pairings. The code proves that this dual equals the orthogonal projection of $E_8$ to $H$. For the root lattice $E_7$, it also supplies an integral simple-root basis with the $E_7$ Cartan matrix and proves minimum squared norm two. Thus both the lattice and its normalisation agree with Section 6.

The transfer uses two exact identities, valid for every $x\in H$:

$$
\Theta_{E_8}\bigl(\alpha,x+\tfrac18\mathbf1\bigr)
=A_{2\alpha}(1/4)\Theta_{E_7^*}(\alpha,x),
\qquad
d\bigl(x+\tfrac18\mathbf1,E_8\bigr)^2
=d(x,E_7^*)^2+\tfrac18.
$$

These are `e8_slice_gaussian_factorization` and `e8_slice_depth_factorization`. The first comes from a proved bijection between $E_8$ and its projected points with their integer fibre coordinates; all series are proved summable. The second follows directly from the nearest fibre distance. The projected point $e_1-\tfrac18\mathbf1$ attains squared depth $7/8$.

Theorems `coldSpot_E7_dual_iff_deepHole` and `e7Dual_gaussian_minimum` therefore give the full $E_7^*$ part of Theorem 1.1 and Theorem 6.2, including the exact minimum $A_\alpha(0)^4A_\alpha(1/2)^4/A_{2\alpha}(1/4)$. Their only analytic premise is $\alpha>0$. The separate theorem `isE7DeepHole_iff_paper` proves the literal representative description in equation (26). With $x_0=e_1-\tfrac18\mathbf1$ and $y_S=\tfrac12\mathbf1_S-\tfrac14\mathbf1$, the classes are $x_0+E_7^*$ and $x_0+y_S+E_7^*$ for $|S|=4$, with precisely complementary subsets identified. An explicit bijection with the quotient of all deep holes by lattice translations gives $1+\binom84/2=36$ classes.

### Diagonal gluing and Barnes--Wall

For Section 7, the code defines $\mathrm{RM}(1,3)$ and $\mathrm{RM}(1,4)$ as evaluations of affine binary functions. It proves the similarity $M\cong E_8/\sqrt2$, constructs all 16 cosets of $M/E_8$, and identifies their diagonal union with

$$
\Gamma=D_{16}+\tfrac12\mathrm{RM}(1,4).
$$

The standard lattice is the actual scaled set $BW_{16}=\sqrt2\Gamma$; the code proves its minimal squared norm is four.

The Gaussian of $\Gamma$ is proved equal to the inner product of its two 16-entry E8 theta profiles. The elementary identity behind Proposition 7.1 separates the difference from the claimed lower bound into nonnegative terms. Its equality theorem forces both marginal minima and, in each coset, at least one minimal profile entry.

The geometric proof independently establishes the same equality condition for squared depth $3/2$. Every deepest point has eligible marginal blocks, and the full E8 hole classification forces their coset depths to take only the values $1/2$ and $1$. Scaling gives `coldSpot_bw16_iff_deepHole` and the exact squared covering radius three. Evaluating the complementary quarter-coordinate witness gives the literal minimum in equation (28). Writing $B_\alpha(t)=\sum_{m\in\mathbb Z}(-1)^m e^{-\alpha(m-t)^2}$, its value for the standard normalisation is

$$
16\bigl(A_{2\alpha}(1/4)^{16}-B_{2\alpha}(1/4)^{16}\bigr).
$$

The 15 nontrivial binary characters are connected to actual E8 root halves, then to all eligible real points. The theorem `bw16_coldSpot_iff_root_union` proves the complete root-indexed union printed in Section 7.5. In the unscaled lattice $\Gamma$ this is

$$
\bigcup_{r\in R(E_8)}
\{(r/2+s,r/2+t):s,t\in M,\ \chi_r(t-s)=-1\},
\qquad \chi_r(g)=(-1)^{2\langle r,g\rangle}.
$$

Its coordinates are multiplied by $\sqrt2$ for $BW_{16}$. The character exponent is proved integral, so no rounding operation changes the character. A bijection from 120 character--phase pairs to the quotient of all actual deep holes proves the class count. The finite binary lemmas are kernel-checked exact identities; the analytic and geometric results quantify over every real ambient point.

## The cubic identity and $E_6$

The $E_6$ verification uses Eisenstein coordinates throughout its analytic part. A pair $(u,v)\in\mathbb R^2$ denotes $u+v\omega$, where $\omega=(-1+i\sqrt3)/2$, and its squared Euclidean norm is $Q(u,v)=u^2-uv+v^2$. Integral pairs are the actual lattice $E=\mathbb Z[\omega]$. The equivalence with complex coordinates, the norm identity, and the equality of the indexed Gaussian series with the sum over $E$ are all proved. Thus the subsequent theta identities apply to the ordinary Gaussian, not to a function specified by desired properties.

Write $c=(1-\omega)/3$, $\theta=1+2\omega$, $F(z)=\Theta_E(\alpha,z)$, $a=F(0)$, and $b=F(c)$. The proof of Proposition 8.1 is slightly different from the manuscript's. The normalised three-point Eisenstein transform sends $E^3$ bijectively to three common cosets, subject to one residue condition modulo $\theta$, and preserves the sum of the three squared norms. An affine rotation about $c$ cyclically permutes the three residue classes without changing their Gaussian weights. Each class therefore contributes exactly $b/3$. Reindexing the absolutely convergent triple sum gives the positive identity

$$
F(z)F(z+c)F(z-c)=\frac b3\bigl(aF(\theta z+c)
+aF(\theta z-c)+bF(\theta z)\bigr).
$$

This establishes the same identity directly on the physical lattice, without introducing a two-dimensional Poisson-summation dependency.

For $P(z)=F(z)F(z+c)F(z-c)$, the verified three-term arithmetic--geometric mean inequality gives $(ab^2)^2P(\theta z)\le P(z)^3$. Periodicity and continuity give an actual positive minimum of $P$; applying the inequality there proves $P\ge ab^2$. Equality forces $F(\theta z)=a$, and the independently proved strict maximum theorem for $F$ gives $z\in E+\mathbb Zc$. All statements quantify over every $\alpha>0$ and every complex point.

The lattice $L_6=E^3+\mathbb Z(c,c,c)$ has a literal, injective three-coset parametrization. Applying the scalar product bound to its Gaussian sum shows that equality occurs exactly when the three coordinate phases are distinct. This gives the permutations of $(0,c,-c)$, modulo $L_6$, and the minimum $3ab^2$. The geometric proof is independent of the analytic equality predicate: explicit nearest representatives in all three residue classes prove the scalar depth bound and its equality case. Their three-coordinate combination gives squared covering radius $2/3$ and the same complete hole set. This avoids the manuscript's limiting argument as well.

Finally, an explicit bijection identifies these coordinates with $\mathbb R^6$, and scaling by $\sqrt2$ gives the root normalisation. Six displayed generators are proved to have the $E_6$ Cartan Gram matrix and to generate the entire lattice over $\mathbb Z$. The final lattice has minimum squared norm $2$, squared covering radius $4/3$, and exactly two deep-hole classes in its actual translation quotient. In particular, `coldSpot_E6_iff_deepHole` proves the full $E_6$ case of Theorem 1.1, and `e6_gaussian_minimum` records its value at parameter $\alpha$ as $3\Theta_E(2\alpha,0)\Theta_E(2\alpha,c)^2$.

## Affine symmetries and the E8 Weyl orbit

The orbit statements quantify over arbitrary actual deep holes, rather than over a chosen finite list. For even $n>8$, `dn_deep_holes_single_affine_orbit` constructs an affine isometry preserving $D_n^+$ and sending either hole to the other. A half-grid point is a half-support vector plus an integer vector. Coordinate permutations align the supports. An even-sum integer displacement is already a lattice translation. For an odd-sum displacement, changing the signs of one supported and one unsupported coordinate corrects its parity. This changes exactly two signs and preserves the lattice. The resulting affine map preserves both lattice membership and the Euclidean distance between every pair of ambient points.

For $E_7^*$, `e7_deep_holes_single_affine_orbit` uses the complete hole classification in the seven-dimensional zero-sum hyperplane. Reflection in twice a four-subset shift carries the distinguished representative to a signed shift; a root-lattice translation handles the sign. Integral duality proves that the reflection preserves the actual projected dual lattice. Composition then connects every pair of holes. The predicate `IsE7AffineSymmetry` records preservation of lattice membership and squared Euclidean distance; its `euclidean_distance` theorem identifies this with the metric of `EuclideanSpace`, not the default supremum metric on coordinate functions.

The $E_8$ statement is stronger. The predicate `E8AffineWeyl` is generated by reflections in actual lattice vectors of squared norm two and translations by the actual $E_8$ root lattice, together with identity, composition and inversion. Thus `e8_deep_holes_single_affine_weyl_orbit` constructs a witness in the affine Weyl group itself. It does not merely produce an unspecified lattice isometry.

Reflection in the all-positive half-root connects the integer representative to a quarter-coordinate representative. A balanced half-root with four positive and four negative coordinates connects this to the balanced half-grid family. Coordinate transpositions are reflections in roots of the form $e_a-e_b$. A change of two coordinate signs is the composition of reflections in $e_a-e_b$ and $e_a+e_b$. Induction decomposes the required permutations and even sign changes into these generators. Together with lattice translations, these maps reach all three families in the complete $E_8$ classification. The theorem `E8AffineWeyl.euclidean_distance` proves literal Euclidean distance preservation for every generated transformation.

These extensions are in `source/coordinate_orbits.lean`, `source/e7_orbits.lean` and `source/e8_orbits.lean`. The aggregate `source/release_all.lean` imports them alongside the original development. The original base modules remain unchanged.

## Positive mixtures, scope and proof dependencies

Corollary 1.2 follows by integrating the common Gaussian comparison against an arbitrary nonzero positive measure on $(0,\infty)$. The formal development first uses nonnegative extended-valued integrals, so Tonelli's interchange does not require a hidden sigma-finiteness assumption on the mixing measure. It proves the strict comparison off the common minimum set, and then the equivalence between finiteness of the extended energy and the paper's convergent real lattice sum. The endpoint `lattice_corollary_1_2` states the real convergent version for all five families. `lattice_corollary_1_2_extended` proves the stronger version in which finiteness is required at only one point and the energy may be infinite elsewhere.

The project follows the mathematical dependency chain needed for the principal conclusions. The general projection and gluing propositions are treated separately from their lattice applications, so their exact scope can be read without reconstructing the $E_7^*$ or Barnes--Wall arguments. The orbit statements are proved separately from the analytic comparison: their proofs use the complete geometric classifications, and none is an additional assumption of a principal result.

The four references in the manuscript are accounted for explicitly. The stable-cold-spot result of Bachoc, Moustrou, Vallentin and Zimmermann (reference \[1\] there) supplies the background question. Brouwer's Barnes--Wall model (\[2\], Section 7) is matched by the proved code and scaling identities. Chapman's cubic-theta work \[3\] provides context for an identity proved directly here. The Jacobi-product consequence cited from DLMF \[4, Section 20.5\] is established by the complete extremum proof described above. The foundational boundary consists of proved results in the pinned Lean and Mathlib environment: real and complex analysis, Gaussian Fourier summation, measure theory, compactness of probability measures, finite algebra and elementary Euclidean geometry. The source import graph and the declaration-level dependency report make this boundary inspectable.

## A reader's correspondence table

Unless indicated otherwise, the names below lie in `PaperVerification.ColdSpots`. The analytic names in the second row lie in `PaperVerification.Hyperbolic`.

| Manuscript result | Lean declarations |
|:---|:---|
| Theorem 1.1 | `lattice_theorem_1_1` |
| Theorem 3.1 | `hyperbolic_geometric_mean_inequality_literal`; `hyperbolic_geometric_mean_equality_literal_iff` |
| Proposition 3.2 | `theta_geometric_mean_inequality_literal`; `theta_geometric_mean_equality_literal_iff` |
| Theorem 3.3 | `dPlusGaussian_minimum`; `dPlusGaussian_eq_min_iff_paperHalfGrid`; `gaussian_E8_minimum_iff_paper_families` |
| Proposition 3.4 | `dPlus_squared_covering_radius`; `isDeepHole_dPlus_iff_paperHalfGrid`; `isDeepHole_E8_iff_paper` |
| Proposition 6.1 | `rational_orthogonal_lattice_projection_transfer` |
| Proposition 7.1 | `lattice_diagonal_gluing` |
| Theorem 6.2 and (26) | `e7Dual_gaussian_minimum`; `e7_covering_radius`; `isE7DeepHole_iff_paper` |
| Section 7, (28) and full root union | `bw16_gaussian_minimum_literal`; `bw16_deepHole_iff_root_union`; `bw16_gaussian_equality_iff_root_union` |
| Proposition 8.1 | `eisenstein_cubic_identity`; `eisenstein_product_minimum`; `eisenstein_product_equality_iff` |
| Section 8.3 and (32) | `e6_gaussian_minimum`; `e6_cold_spot_description`; `e6_deep_hole_description` |
| Introduction tables | `lattice_covering_radius_table`; `lattice_translation_class_table` |
| Corollary 1.2 | `lattice_corollary_1_2`; `lattice_corollary_1_2_extended` |

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The smaller topic files in `reading/` show the development before assembly; they are provided for navigation and are not an alternative build. The compiler checks the corresponding assembled development in `source/`. The default build also compiles `source/verification.lean`, which checks the entire combined development, including private helper definitions. Generated diagnostic files are kept in `.lake/reports/`.

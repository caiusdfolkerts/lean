# Formalisation

This guide explains how the algebraic, geometric, and rigidity arguments in *Singular-vector spans beyond boundary format* are represented in Lean. The central comparison relates multiplication in a Segre ring to the span of the original singular rank-one tensors. The proof retains the ordinary quotient rings, tensor products, schemes, and generic quantifiers throughout.

## 1. The original objects and the generic quantifiers

### The Segre ring and its Artinian reduction

The parameters $n_i$ are projective dimensions; the vector space in factor $i$ is $K^{n_i+1}$. Theorem 1.1 assumes $n_i\geq1$; the all-format tensor theorem also includes $n_i=0$. For $k\geq1$ put $d=1+\sum_i n_i$. The formal ring is
$$
R(\mathbf n)=\bigoplus_{q\geq0}\bigotimes_{i=1}^k\operatorname{Sym}^q(K^{n_i+1}).
$$
It is built from symmetric powers, finite tensor products, and an external direct sum. A canonical algebra equivalence identifies it with the balanced multihomogeneous polynomial algebra. This comparison preserves the full algebra and every homogeneous piece.

A matrix $A\in K^{\operatorname{Cell}(\mathbf n)\times d}$ specifies the coefficients of the linear parameters, where $\operatorname{Cell}(\mathbf n)=\prod_i\{0,\ldots,n_i\}$.

`SymmetricReduction` is the literal ideal quotient $R/(\theta_1,\ldots,\theta_d)$. `symmetricActualPiece` takes the image of $R_q$ in that quotient. For $\ell$ in its first piece, `symmetricFirstLefschetz` is multiplication $x\mapsto\ell x$. The coordinate and quotient equivalences intertwine this map with the matrices used in the proof. These three definitions lie in the namespace `SymmetricRealization`.

### Tensors, singular tuples, and the critical space

`ActualTensorSpan.Tensor` is Mathlib’s finite tensor product. Its contractions use the coordinate bilinear pairing $\langle x,y\rangle=\sum_a x_a y_a$. `IsSingularTuple` requires a nonzero vector in every factor and, for each factor, a scalar making its contraction proportional to that vector. The scalar may be zero. These conditions include isotropic vectors and retain their meaning in characteristic two.

`singularSpan` is the ordinary submodule span of the corresponding pure tensors. The critical space is independently defined by all ambient linear critical equations. The projective endpoint uses Mathlib’s projectivization and the span of the original singular points. Proofs connect these objects to their coefficient arrays, preserving contractions and the entire generator sets. Thus an equality of spans in the endpoint is an equality of the original subspaces, not a definition by a dimension formula.

### What “general” means in the statements

A generic tensor assertion supplies a nonzero polynomial $p$ in all tensor coefficients, a tensor $T$ with $p(T)\ne0$, and the conclusion for every tensor where $p$ is nonzero. This is a nonempty principal Zariski open in the whole coefficient space. The proofs in `PaperVerification.PolynomialGenericity` identify this certificate with the ordinary nonempty-open formulation and prove density using Mathlib’s prime-spectrum topology. Intersections of the required rank and geometric loci are constructed within the proof.

Theorem 1.1 retains the order of its two generic quantifiers. First it gives a nonzero polynomial $g$ in all parameter coefficients. Every reduction with $g(A)\ne0$ is finite-dimensional and Artinian. For each such reduction, a basis of its entire degree-one piece and a nonzero polynomial in those basis coordinates specify the general forms $\ell$. An additional theorem exhibits an actual pair $(A,\ell)$. Neither generic assertion relies on an empty parameter space. Regularity, finite reducedness, and the cohomology comparisons needed later are established inside the proof chain.

## 2. The first Lefschetz map: algebra and rigidity

The endpoint `SymmetricPrincipal.theorem_1_1_symmetric_rank` states
$$
\operatorname{rank}(\ell:A_1\longrightarrow A_2)
   =\min\{\dim_K A_1,\dim_K A_2\}
$$
and gives the exact dimension of its kernel. The dimensions are those of the actual quotient pieces. Their finite-dimensionality is a proved conclusion of the parameter certificate.

| Number of factors | Exceptional projective dimensions | Kernel dimension |
|:---|:---|:---|
| Two, both dimensions at least two | $(2,2),\ (2,3),\ (2,4)$ | $3,\ 3,\ 2$ |
| At least three | $(1,1,1),\ (1,1,2),\ (1,1,3)$ | $3,\ 3,\ 1$ |


Permutations give the same values. Every other tuple in these ranges has zero kernel. The separate two-factor line case has $A_2=0$; with one factor, the complete reduction is algebra-isomorphic to $K$.

### Integral two-factor multiplication

For two factors the rank-sum parameters are $L_s=\sum_{i+j=s}x_{ij}$. The construction proves the required quotient bases in degrees one and two, together with straightening and the parameter comparisons. The integral shelling construction proves freeness and independence as well as spanning. Its relations have no denominators, so the basis remains valid after reduction to any characteristic.

In $A_{3,3}$, multiplication by $x_{21}$ is invertible. In the paper’s source and target orders its image coefficient vector is
$$
(-a,d,e,-b-3d,g,h,c-3e-2g,-f-3h,-i).
$$
The coefficients are recovered successively in the order $a,d,e,b,g,h,c,f,i$. In $A_{2,5}$ a second integral multiplication calculation has determinant one. The column-extension argument propagates injectivity from these two starting points; the smaller quotients give surjectivity and the three exceptional two-factor dimensions. These are identities and unbounded inductions in Lean, not checks of a finite list of formats.

### Products of chains and the remaining formats

The staircase degeneration has chain monomials as a basis and specializes to the order-complex Stanley–Reisner ring. Its multiplication kernel is identified with the infinitesimal-motion kernel of the actual rigidity matrix, after eliminating the square coefficients. The Koszul relations account for trivial motions. The rigidity matrix is defined directly by coordinate differences in every characteristic; the argument never divides by two.

The rigidity development proves coning, joins, gluing, vertex attachment, and one-extension in the required characteristics. Boolean cores and the two three-chain starting boxes yield Proposition 5.1; coordinate increments handle arbitrary positive chain lengths. The rigidity predicate includes affine spanning, the convention needed for the join and gluing arguments. Stress-freeness of the three exceptional boxes gives surjectivity there. Nonvanishing minors then transfer maximal rank through the staircase family and to the general parameter locus. The intrinsic symmetric-power endpoint uses the proved algebra equivalences described above.

## 3. Actual schemes and genericity

Lemma 2.2 concerns the original singular scheme, including its scheme structure. The development therefore starts with its literal equations. Choose a pivot coordinate in each factor, normalize that coordinate to one, and write the remaining coordinates as $z_{i,a}$. If $c_{i,a}(T,z)$ is the coordinate contraction of the original tensor, the normalized equations are
$$
g_{i,a}(T,z)=c_{i,a}(T,z)-z_{i,a}c_{i,p_i}(T,z),
 \qquad a\ne p_i.
$$
There are $q=\sum_i n_i$ variables and $q$ equations. The relevant algebra is
$$
B_T=K[z_{i,a}]/(g_{i,a}(T,z)).
$$
Finiteness and reducedness always refer to this quotient. In particular, passing to a radical ideal is not used to manufacture reducedness.

### A generic calculation in the original coefficients

The argument first makes all $D=\prod_i(n_i+1)$ tensor entries algebraically independent and works over an algebraic closure of their rational function field. At a normalized critical point $x$, let $a$ be the number of isotropic factors and put $E=K(x)$. Each isotropic factor supplies a monic quadratic dependence among its coordinates. Consequently $\operatorname{trdeg}_K E\leq q-a$; this uses integrality and remains valid when the quadratic is inseparable in characteristic two.

The critical conditions are linear in the tensor entries. Their rank is $q$ at a nonisotropic tuple and $q-a+1$ when $a>0$. The source computes this rank from the intersections of the corresponding tensor subspaces. If $a>0$, the transcendence-degree tower would give
$$
D\leq(q-a)+(D-q+a-1)=D-1.
$$
Thus a generic critical point has no isotropic factor. The same argument then shows that its $q$ normalized coordinates are algebraically independent over the original field.

For reducedness, the proof solves designated tensor coefficients as rational functions of the point coordinates and the remaining coefficients, with a denominator nonzero at the origin. At the pure pivot tensor the critical equations have linear part $-z$, so their fiber Jacobian is $-I_q$. Algebraic independence makes this determinant nonzero at every generic critical point. This differentiates the original equations while holding $T$ fixed, and never divides by two.

The Nullstellensatz gives a unit-ideal identity for the equations and their Jacobian determinant. Descent and clearing denominators produce a nonzero polynomial in all original tensor entries. Its nonvanishing makes the quotient étale of relative dimension zero, hence finite and reduced. The chart theorem is `GenericChartCertificate.exists_finite_reduced_certificate`. Permuting pivots and multiplying certificates gives one open for all charts.

### The actual embedded scheme

The embedded singular ideal is independently defined as the sum of the Segre-image ideal and the ambient critical-linear ideal. Complete chart ideal comparisons give a scheme isomorphism with the intrinsic zero scheme. Nilpotents are retained throughout. The global endpoint is `EmbeddedSchemePrincipal.lemma_2_2`.

For $m\geq1+\sum_i n_i$, a multiplication minor also makes the slice ideal the unit ideal on every chart. Explicit quotient-algebra isomorphisms eliminate the final coordinates wherever a slice is invertible. `EmbeddedSchemePrincipal.lemma_2_2_graph` places basepoint-freeness, finiteness, and reducedness on one nonempty full-coefficient open.

## 4. Projective cohomology and the Koszul gap

Proposition 2.1 is the bridge from multiplication in the Segre ring to the actual singular rank-one tensors. Write $X=\prod_i\mathbf P^{n_i}$ and let $f_1,\ldots,f_m\in R_1$ be the tensor slices. Define
$$
\mu_T:R_1\otimes K^m\longrightarrow R_2,
 \qquad (\ell_j)_j\longmapsto\sum_j f_j\ell_j,
 \qquad \Gamma_T=\operatorname{im}\mu_T^*.
$$
The graph of the last contraction has span $\Gamma_T$. Its remaining critical equations form a regular section of
$$
E=\bigoplus_i\pi_i^*Q_i\otimes
       \mathcal O_X(2,\ldots,2,1,2,\ldots,2),
 \qquad L=\mathcal O_X(2,\ldots,2).
$$
The position of the $1$ is $i$. On the graph, the ambient Segre hyperplane bundle pulls back to $L$: its coordinates are products of a base Segre coordinate and a slice $f_j$. At each zero, finiteness of the original chart quotient makes its equations a system of parameters in a regular local ring, hence a regular sequence. Away from the zero scheme a unit coefficient gives a contracting homotopy. Together these prove local Koszul exactness, including when the zero scheme is empty; no extra regularity hypothesis is needed.

### Why the higher terms contribute no extra equations

For $r\geq2$, the actual term $\bigwedge^r E^*\otimes L$ decomposes into external products
$$
\mathop{\boxtimes}_i
 \Omega_{\mathbf P^{n_i}}^{r_i}(2r_i-2r+2),
 \qquad \sum_i r_i=r.
$$
The decomposition retains every degree tuple and uses canonical wedge maps with their restriction and pullback formulas. The notation $\Omega^p$ here denotes the exterior power of the actual coordinate Euler kernel. The proof compares that kernel directly with the critical bundle; it needs no unproved identification with a separate Kähler-differential construction.

The characteristic-independent projective calculation proves the precise vanishing ranges needed here. For positive twists, higher cohomology vanishes, and $H^0$ vanishes when the twist is at most the exterior degree. For nonpositive twists, $H^q$ vanishes for $q<r_i$; for negative twists it vanishes for $q<n_i$. Thus the displayed positive-twist terms could contribute degree-zero cohomology only if $r_i>2r-2$, impossible for $r\geq2$. The other cases contribute degree at least $r_i$, including dimension-zero factors. The product comparison yields
$$
H^q(X,\bigwedge^r E^*\otimes L)=0
 \qquad(r\geq2,\ q<r).
$$
For $\mathcal O(t)$, normalized monomials give the coordinate Čech calculation. The coordinate Euler map has explicit reciprocal-coordinate local splittings; its exterior kernel sheaves are identified with genuine Koszul cycles. Short exact sequences then give the required differential-form vanishings, including the negative twists, without assuming a general Bott or Serre-duality theorem. The product comparison uses a double Čech resolution on actual affine rectangles and its tensor comparison. It therefore concerns ordinary sheaf cohomology on the product scheme.

A short exact sequence argument now suffices. If $B_r$ is the image of the $r$th Koszul differential, the sequences $0\to B_{r+1}\to\bigwedge^rE^*\otimes L\to B_r\to0$ give $H^q(B_r)=0$ for $q<r$ by descending induction. In particular, $H^0(B_2)=H^1(B_2)=0$, so
$$
H^0(X,I_Z\otimes L)\simeq H^0(X,E^*\otimes L).
$$
The global sections on the right are precisely the small-factor critical equations after applying $\mu_T$. Local coordinate formulas establish this identification for the entire map.

## 5. The span formula and every tensor format

Reducedness identifies pointwise vanishing with membership in the original chart ideals. The global comparison therefore gives
$$
\operatorname{span}(Z_T)^\perp=\ker\mu_T+C_T,
 \qquad \operatorname{span}(Z_T)=\Gamma_T\cap H_T,
$$
where $C_T$ is the space of small-factor critical relations. The injectivity of the actual global equation map gives $\dim\mu_T(C_T)=\sum_i\binom{n_i+1}{2}$. Rank–nullity then yields $\dim\operatorname{span}(Z_T)=\operatorname{rank}\mu_T-\sum_i\binom{n_i+1}{2}$, as in Proposition 2.1. No separate independence hypothesis on the critical rows is needed. The trace functional on $R_2$ sends $\prod_i x_{i,p_i}x_{i,q_i}$ to $\prod_i\delta_{p_iq_i}$; its pullback under $\mu_T$ is exactly $T$. Since $T\in H_T$, it follows that $T\in\operatorname{span}(Z_T)$ even when this span is defective.

`GraphGeometry.proposition_2_1` states the chart version; `EmbeddedSchemePrincipal.proposition_2_1` states the result for the actual embedded scheme. Its dimension companions give the additive identity in natural numbers and the printed subtraction in integers under the same hypotheses; no truncation of a negative difference is possible.

For Theorem 1.3, the balanced range uses the full-product terms $\boxtimes_i\Omega^{r_i}(1+2r_i-r)$. Except when one $r_i=r$, every nonzero factor contributes cohomology in degree at least $r_i$. In that remaining case, $r\leq n_i$ and the other factors have negative twists: their total degree is at least $\sum_{j\ne i}n_j\geq n_i\geq r$ by the triangle inequality. This proves the same gap, including dimension-zero factors. Every remaining format admits the graph argument; reindexing transports all contractions and singular generators. `PrincipalTensor.theorem_1_3` concludes membership in the ordinary span inside Mathlib’s tensor product; `PrincipalTensor.theorem_1_3_finite_linear_combination` gives the equivalent finite sum. Proved tensor equivalences handle factors of vector dimension one. The one-factor case is included; a supplementary all-arities endpoint also covers the scalar empty tensor product.

### First excess and the exact defect

At $m=\sum_i n_i+2$, choose $\sum_i n_i+1$ slice parameters and let $\ell$ be the remaining slice in their Artinian quotient $A$. Resolving first by the parameter sequence identifies the relevant Koszul homology with $\ker(\ell:A_1\to A_2)$. Thus Theorem 1.1 supplies the exact defect in Corollary 1.2, including every nonexceptional format. The projective-line family has defect $b$ and the matrix family has defect zero; the latter is handled without assuming independence of its oversized slice array.

The endpoints in `OriginalProjectivePrincipal` use the projective span of the actual nonzero singular pure tensors. Containment in the critical space is proved first. Refining the generic open makes the original tensor nonzero; its span membership then makes both projective spaces nonempty. Their codimension is therefore the same as that of their affine cones. Factor-reindexing covers every permutation, including the factor used for the slice presentation.

| Exceptional tensor formats in Corollary 1.2 | Projective defect |
|:--------------------------------------------|:-----------------:|
| $(3,3,6)$ and $(3,4,7)$                 |       $3$       |
| $(3,5,8)$                                 |       $2$       |
| $(2,2,2,5)$ and $(2,2,3,6)$             |       $3$       |
| $(2,2,4,7)$                               |       $1$       |


The formal index has $\sum_i n_i+2$ elements, so it is exactly the last vector-space dimension at first excess. `FullFactor` adjoins this factor to the original family. The quantified permutation reorders every factor, including this last one.

## 6. Arbitrary excess and explicit thresholds

Section 6 writes the last vector-space dimension as $m=\sum_i n_i+e+1$, with $e\geq1$. The same geometric comparison identifies the span defect with degree-two Koszul homology of the slice space. In the staircase specialization, this is the failure of infinitesimal rigidity in dimension $\sum_i n_i+e$. A rigid comparability graph therefore supplies full generic span. The constructions have enough vertices for the slices to be independent, and nonzero minors transfer the attained rank to the original Segre ring.

For Theorem 6.1, ordered blocks partition a Boolean lattice into interval cores. Their joins are rigid; adjacent block swaps have explicitly counted overlaps large enough for gluing. Coverage and connectivity then give the whole Boolean graph. Coordinate-length induction extends the result to every positive tuple. The two resulting ranges are
$$
k\geq4e,
 \qquad\text{or}\qquad
 b\geq4,\quad k\geq3b,\quad e\leq2^b-3b+1.
$$
The second uses complete tripartite joins. In characteristic two the proof also forces the diagonal of the motion matrix to vanish, using the invertibility of an entrywise-squared anchor matrix. Thus skew symmetry is not silently treated as alternation. The logarithmic consequence is $k\geq3\lceil\log_2(4e)\rceil$ for $e\geq3$. The corresponding endpoints are `OriginalProjectivePrincipal.theorem_6_1_first`, `theorem_6_1_second`, and `theorem_6_1_logarithmic` in that namespace.

For Theorem 6.3, fix $k\geq3$ and $e\geq2$, set $c_0=2$ for $k=3$ and $c_0=1$ otherwise, and choose $L\geq c_0$. With $N=2L+c_0(e-2)$, the exact criterion is
$$
(L+1)^{\lfloor k/2\rfloor}+(L+1)^{\lceil k/2\rceil}
       \geq kN+e.
$$
Consecutive diagonal boxes form a rigid core. The left side is a lower bound for the number of core neighbors of every outside vertex, so each can be attached. Chain-length induction handles all $n_i\geq N$. `OriginalProjectivePrincipal.theorem_6_3` retains this complete criterion; the following declarations retain the printed square-root, root, uniform, and excess-two consequences.

For three smaller factors, the explicit consequence is $n_i\geq2e+2\lceil\sqrt{7e}\rceil$. For fixed $k\geq4$, put $q=\lceil k/2\rceil$; the threshold is
$$
n_i\geq e+2\left\lceil((k+1)e)^{1/q}\right\rceil+4k-2.
$$
The separate uniform bound is $n_i\geq3e^2$, and at excess two the smaller bound $n_i\geq6$ suffices. For example, $k=3$, $e=2$, $L=3$ gives $N=6$ and the exact inequality $4+16=3\cdot6+2$. Every bound quantifies over all eligible integers.

The arithmetic is separated from its geometric application. The namespace `AsymptoticBounds` treats the literal ceilings and unbounded inequalities. `AsymptoticGrowth.three_factor_growth` and `AsymptoticGrowth.many_factor_growth` express the two growth estimates as actual `Asymptotics.IsBigO` statements. These supporting calculations feed the kernel-checked tensor and projective endpoints.

## Reading the source

`source/verification/complete.lean` imports the mathematical development. The numbered stage modules follow its dependency order; larger stages have subdirectories named for their mathematical components. They are parts of one project, not alternative versions. Declaration namespaces retain the common prefix `PaperVerification.Segre`, so the names in this guide can be searched directly in the source.

The algebraic construction and rank arguments begin in `source/segre/stage001.lean` through `stage014.lean`. The cohomology infrastructure is collected under `stage015/`; the projective-space calculations are under `stage025/`. The bundle, exterior-power, and Koszul comparisons are under `stage027/`, followed by the critical-equation and graph calculations under `stage028/`. The actual tensor conclusions are under `stage030/`, the embedded schemes and projective conclusions under `stage031/`, and the asymptotic bounds and final rigidity statements under `stage032/`. The adjacent stage files assemble those components.

`source/verification/complete.lean` imports the full development and checks the principal theorem types, the definitions of the underlying mathematical objects, and their authored dependencies. It also checks all project declarations for unapproved axioms. These checks run as part of the normal build; their generated report is ignored by Git.

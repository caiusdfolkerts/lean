# Quadratic generation for smooth polytopes with long edges

This note explains the mathematical scope and organisation of the Lean 4 project accompanying *Quadratic generation for smooth polytopes with long edges* [paper]. Its purpose is to make the formal statements, their correspondence with the paper, and the route for checking the proofs easy to inspect. The public entry point is `source/toric_quadratic.lean`.

## The principal statements

The formalisation retains every dimension, the paper's edge bounds, all lattice points, and the original quantifiers. The first theorem works over an arbitrary field. The two mixed statements are provided both as statements about polytopes and in the paper's language of ample divisors on smooth projective split toric varieties.

### Normality and quadratic generation

Let $M\cong\mathbb Z^n$, let $P\subset M_{\mathbb R}$ be a smooth lattice polytope of dimension $n\geq1$, and suppose that every edge has lattice length at least $n$. Theorem 1.1 has two conclusions. First, for every integer $r\geq1$, every lattice point of $rP$ is a sum of $r$ lattice points of $P$. Second, for every field $k$,

$$
\varphi_P:k[X_a:a\in P\cap M]\longrightarrow k[M][t],
\qquad X_a\longmapsto\chi^a t,
$$



$$
\ker\varphi_P=
\bigl(X_aX_b-X_cX_d:
a,b,c,d\in P\cap M,\ a+b=c+d\bigr).
$$

The public declaration is `ToricQuadratic.normal_and_quadratic`; its underlying endpoint is `PaperVerification.ToricGeometry.toric_theorem_1_1`. The integer-decomposition conclusion quantifies over every positive dilation. The ideal equality is an equality inside Mathlib's actual multivariate polynomial ring.

Two public corollaries make the coordinate and coefficient conventions explicit. `ToricQuadratic.normal_and_quadratic_in_lattice` states the conclusion in an arbitrary lattice with a chosen integral basis, using its actual realification and character algebra. `ToricQuadratic.normal_and_quadratic_over_ring` proves the same kernel equality over every commutative coefficient ring, together with IDP. These statements are proved from the geometric and algebraic development; they do not add hypotheses to Theorem 1.1.

### Prescribed parity

Suppose that $P$ and $Q$ are smooth $n$-dimensional lattice polytopes with the same normal fan and every edge of both polytopes has length at least $n$. For every

$$
m\in\operatorname{int}(P+Q)\cap M,\qquad \alpha\in M/2M,
$$

Theorem 1.2 supplies $a\in P\cap M$ and $b\in Q\cap M$ with $a+b=m$ and $[a]=\alpha$.

This is `ToricQuadratic.prescribed_parity`. The quotient in this statement is the actual quotient of the lattice by twice the lattice. An earlier part of the proof uses arbitrary integral representatives; `theorem1_2_iff_quotient_classes` proves the equivalence of the two formulations.

### Adjoint multiplication

At the edge bound $n+1$, Theorem 1.3 proves the set equality

$$
(P\cap M)+(\operatorname{int}Q\cap M)=\operatorname{int}(P+Q)\cap M.
$$

The public declaration is `ToricQuadratic.adjoint_decomposition`. Both inclusions are included. The statement places no extra hypothesis on the dimension, positivity, or nonemptiness of the adjoint polytope.

The original geometric formulation is also present. For ample integral Cartier divisors $A,B$ of degree at least $n+1$ on every invariant curve, the formalisation proves the surjectivity of

$$
H^0(X,\mathcal O_X(A))\otimes_k
H^0(X,\mathcal O_X(B)\otimes\omega_X)
\longrightarrow
H^0(X,\mathcal O_X(A)\otimes\mathcal O_X(B)\otimes\omega_X).
$$

Here $\omega_X=\bigwedge^n\Omega^1_{X/k}$ is constructed from the intrinsic sheaf of Kähler differentials. The map is the ordinary multiplication of global sections into the tensor sheaf. The exported declaration `ToricQuadratic.toric_paper_theorem_1_3` gives this surjectivity together with the lattice-point equality. The corresponding divisor version of prescribed parity is `ToricQuadratic.toric_paper_theorem_1_2`.

## What the definitions mean

### Lattices, polytopes, edges, and faces

The coordinate types `Lattice` and `Ambient`, with parameter $n$, are respectively $\mathbb Z^n$ and $\mathbb R^n$. An object of type `LatticePolytope` consists of a finite nonempty set of integral generators together with the assertion that its ordinary real convex hull is full-dimensional. Redundant generators are allowed. Its carrier is exactly that convex hull.

An edge is a nondegenerate segment which is an actual extreme subset of the convex polytope. The code proves that its endpoints are vertices and hence belong to the integral generating set. For integral endpoints $v,w$, lattice length is

$$
\gcd\bigl(|w_1-v_1|,\ldots,|w_n-v_n|\bigr).
$$

The predicate `Smooth` says that, at every vertex, all the incident edges are positive integral multiples of the vectors in an integral basis. It therefore asserts exactly the paper's primitive-edge-basis condition.

The file `reading/toric_quadratic/toric_lattice_coordinates.lean` justifies the arbitrary-lattice form of Theorem 1.1. Its constructions start with an integral basis of an abstract lattice and extend it to its realification $\mathbb R\otimes_{\mathbb Z}M$. They prove equivalence of the smoothness and edge hypotheses, invariance of lattice length, preservation of IDP in every degree, and transport of the toric kernel by the literal renaming of its polynomial variables.

Proper faces are handled in their own saturated affine lattices. The integral affine charts used in the induction are constructed from subsets of smooth bases. Their image and integral-preimage theorems prove that the chart includes precisely the lattice points in the face's affine span. Relative interior, sums, and parity all transport through these charts. This is the bridge needed when the proof passes from dimension $n$ to a face of smaller dimension.

### The ring map and the exchange relation

The variables of `paperToricMap` are indexed by all the actual lattice points of $P$. Its source is Mathlib's `MvPolynomial`; its target `Polynomial (AddMonoidAlgebra k M)` represents $k[M][t]$. The proved formula `paperToricMap_X` identifies the image of a variable with $\chi^a t$. The quadratic ideal is an ordinary `Ideal.span` of the displayed equal-sum quadratic binomials.

A decomposition is a multiset of lattice points. Its cardinality is the degree and its sum is the target point. A `QuadraticMove` replaces exactly two entries by two entries with the same sum, while keeping the remaining multiset fixed. Connectivity is the reflexive transitive closure of this relation. The algebraic bridge proves that connectivity of every fiber implies equality of the actual kernel and quadratic ideal. It first works in a multiset semigroup algebra and then proves its equivalence with Mathlib's polynomial ring.

### The intrinsic toric variety

The scheme-theoretic statements begin with an integral scheme $X$, a smooth proper structure morphism $X\to\operatorname{Spec}k$, an action of the actual split group scheme $\mathbb G_m^n$, and an equivariant dense open immersion of that torus into $X$. A `SplitToricEmbedding` contains precisely the immersion, density, and equivariance data. The proved equivalence `torusCharacterAddEquiv` identifies the coordinate lattice with the actual group of scheme characters of the torus: every character is proved to be a monomial.

Ample Cartier divisors are described by actual invertible fractional sheaves and the usual criterion that nonvanishing opens of sections of positive tensor powers give an affine cover (Stacks Project, tag 01PS). The fan and the polytope of global-section characters are derived from these inputs. The intrinsic section polytope is the convex hull of the actual integral character exponents of the normalised section module. Integral translations arising from choices of torus frame are exhibited and transported through the mixed statements.

An `InvariantIntegralCurve` is an actual closed integral one-dimensional subscheme, with an action making its inclusion equivariant. The code classifies every such curve as $\mathbb P^1_k$. It then proves existence and uniqueness of the ordinary integer degree of the restricted line bundle. The resulting degree is independent of the auxiliary ample divisor and of the chosen isomorphism with $\mathbb P^1$. Thus the endpoint's degree inequalities range over all invariant curves and have their usual mathematical meaning.

## The proof from boxes to quadratic equations

### The exchange argument in Section 2

Proposition 2.1 is formalised independently of toric geometry. Its hypotheses are IDP and the two stated conditions in the saturated affine lattice of each face: prescribed parity in $\operatorname{relint}(2F)$, and an interior summand for a proper face. Its conclusions are connectivity in every degree and quadratic generation over every commutative coefficient ring.

The central operation creates a repeated summand in any triple. If two entries span the same smallest face as the triple, parity replaces them by a pair one of whose entries has the parity of the third. Taking their integral midpoint creates the repeat. Otherwise, the proper-face interior-summand condition first puts one entry in the relative interior of the smaller face, reducing to the preceding case.

For the induction, write two transformed decompositions as

$$
z=2b+\sum_{i=1}^{r-2}u_i
=2d+\sum_{i=1}^{r-2}v_i.
$$

The integral point

$$
q=z-b-d=\frac12\left(\sum_i u_i+\sum_i v_i\right)
$$

lies in $(r-2)P$. IDP decomposes it into $r-2$ lattice points. Holding $b$ fixed and then $d$ fixed reduces both comparisons to degree $r-1$. The Lean proof uses this argument for every $r\geq3$, including the degree-three midpoint bridge.

Finally, distinct characters are linearly independent in the target semigroup algebra, so the kernel is generated by differences of monomials in common fibers. A path of quadratic exchanges expresses each difference as a sum of monomial multiples of quadratic binomials. This last step is an ideal-theoretic proof, not a count of tested fibers.

### The covering argument in Section 4

Lemma 4.1 is `PaperVerification.Toric.lattice_basis_polytope_covering`. It allows unrelated bases in the different boxes and all points, including boundary points, of the convex hull of their incidence vectors.

The proof separates the analytic and geometric ingredients. A finite exponential balancing theorem is proved by minimising a coercive function on the span of the centred configuration. Cauchy--Binet then converts this balance into weights for an inverse Gram matrix. In the resulting positive-definite norm, a nearest lattice point $z$ to $x$ satisfies the inequalities obtained by comparison with $z+v_j$ and $z-v_j$:

$$
|v_j^{\mathsf T}Q(x-z)|\leq
\tfrac12v_j^{\mathsf T}Qv_j .
$$

The balanced frame identity expresses $x-z$ as a point of the desired zonotope. A compactness argument includes zero weights on the boundary of the base polytope.

Equation (7) of the paper is implemented by a separate theorem about paired boxes in two convex sets. A convex combination of their matched centre sums gives a translated covering zonotope inside the intersection $P\cap(m-Q)$. Unit boxes give a lattice decomposition; side-two boxes give a point in every prescribed class modulo $2M$.

For Corollary 4.3, long incident edges first give unit corner boxes. Their centres have at least half a unit of slack against every primitive integral facet normal. The shifted supporting halfspaces therefore supply the matched centres for an interior target. A boundary target passes to an actual proper face, and induction supplies IDP for every positive dilation.

The declaration `LatticePolytope.lemma4_2_unit_corner_boxes` gives the full unit-box multiplication lemma: common normal fan and unit corner boxes imply a lattice decomposition of every target in $P+Q$, including its boundary. Basis independence and inheritance by saturated faces precede the dimension induction.

### The geometric induction in Sections 3, 5--7

The geometric proof uses finite smooth complete fans of actual lattice cones. Nefness is feasibility of supporting linear functionals. Here a *combinatorially contractible* relation satisfies the explicit cone-replacement condition of Casagrande [casagrande]; *extremality* means facehood in the cone of balanced ray coefficients dual to nef supports. The relation criteria and the identification of these contractible degrees with actual edge lengths are proved.

Extremality implies cone replacement, which gives fiber/base fan coordinates, quotient fans, and disjointness of the selected fan loci. The star-subdivision argument proves pushdown and the minimum-coefficient lift with its exact degree formula. Uniqueness for a given positive collection identifies the lift. No equivalence with scheme-level contractions or the geometric Mori cone is formalised. The principal proofs use the proved fan consequences directly and require neither identification.

Both mixed theorems use strong induction on the actual dimension. The proof constructs all obstructing combinatorially contractible relations. A relation with empty negative support is treated by homogeneous simplex allocation and induction on its smaller base. Otherwise, the target falls into one of three exhaustive cases: near an old facet, near a selected locus, or in the region covered by matched box centres. The first two cases use exact saturated slices and lower-dimensional induction; the third uses the covering lemma.

The boundary cases matter. The dimension-zero assertion is proved in the singleton lattice. At an endpoint where the globally displaced support is merely nef, the code proves the needed strict support of the lower-dimensional restriction. The inner-slice identity for the adjoint theorem checks every old facet: the selected normal heights, the adjacent quotient inequalities, and the nonincident-facet reserve. No extra ampleness assumption is introduced for the second adjoint factor.

## A map from the paper to the code

Names below are relative to `PaperVerification.ToricGeometry`, except for the covering and simplex-allocation rows, whose prefix is `PaperVerification.Toric`. Names beginning with `ToricQuadratic` are fully qualified. The descriptive topic files in `reading/` correspond to the assembled compilation units in `source/`.

| Paper | Lean declaration or family |
| --- | --- |
| Proposition 2.1 | `ToricQuadratic.proposition2_1_finite_lattice_hull`; `LatticePolytope.proposition2_1` |
| Lemma 3.1 (fan form) | `ToricQuadratic.real_corner_boxes_iff_contractible_degrees`; `ToricQuadratic.real_corner_boxes_iff_extremal_degrees` |
| Lemma 3.2 (fan form) | `ToricQuadratic.RealSlices.displacedSupport_wallDegreesAtLeast`; `ToricQuadratic.RealSlices.displacedSupport_convexity`; `SmoothCompleteFan.displaced_supportFace_eq_slice` |
| Lemma 4.1 | `lattice_basis_polytope_covering` |
| Lemma 4.2 | `LatticePolytope.lemma4_2_unit_corner_boxes` |
| Corollary 4.3 | `LatticePolytope.integerDecomposition_of_smooth_long_edges` |
| Lemma 4.4 | `simplex_parity_topological` |
| Lemma 5.1 (fan form) | `SmoothCompleteFan.selected_positive_card_bound`, `SmoothCompleteFan.selected_two_positive_full_bound`, and `SmoothCompleteFan.selected_positive_count_full_cone` |
| Proposition 5.2 (fan form) | `ToricQuadratic.RealSupport.proposition_5_2` |
| Equation (13) | `SmoothCompleteFan.canonical_slice_eq_of_edges` |
| Theorem 1.2 | `toric_theorem_1_2_polytope`; `toric_theorem_1_2_quotient_classes` |
| Theorem 1.3 | `toric_theorem_1_3_polytope`; `toric_theorem_1_3_polytope_sets` |
| Theorem 1.1 | `toric_theorem_1_1` |

The auxiliary correspondence is componentwise; contractibility and extremality in the fan rows have the cone meanings specified above. Lemma 3.2's exact fiber-degree formula is `SmoothCompleteFan.PrimitiveRelation.degree_displaced_focus`; the primitive-facet height estimate is `nonincident_facet_displacement_reserve`. The table identifies the components of each multi-part lemma. The two `RealSlices` declarations include arbitrary real original support, arbitrary real displacement heights, every invariant wall, and the zero and equality cases of the displacement budget. The fan form of Proposition 5.2 also allows arbitrary real original support.

The first declaration in the Proposition 2.1 row permits an arbitrary finite lattice convex hull in $\mathbb R^n$, including a lower-dimensional one. The corner-box equivalences in the Lemma 3.1 row use real support values and a nonnegative real box size. The two public wrappers derive purity and an integral strict-support witness from the given complete fan and ample real support. The equivalences identify literal containment of all box points with the stated degree inequalities, for either all combinatorially contractible relations or just the support-dual extremal relations.

For the original divisor formulations, the final file is `reading/toric_quadratic/toric_paper_theorems.lean`. The namespace is `PaperVerification.ToricSchemes.SplitToricEmbedding`. The declarations `toric_paper_theorem_1_2` and `toric_paper_theorem_1_3` use ordinary degrees on actual invariant curves. The preceding modules prove the intrinsic fan classification, the section-polytope dictionary, the canonical differential-sheaf calculation, and transport of section multiplication through the genuine scheme and sheaf isomorphisms.

## Real supports and boundary cases

The main theorems concern integral divisors, but the convex-geometric auxiliaries also use real coefficients. Two modules, supported by a short fan-foundations module, make this generality explicit. They begin with the existing smooth complete fan and its actual Cartier points. Across each adjacent pair of maximal cones, the difference of the Cartier points is the wall degree times the primitive dual lattice direction. Thus the predicate `RealSupport.WallDegreesAtLeast` tests every ordinary invariant degree, including the nonextremal ones. Its equivalence with the existing integral wall-degree predicate is proved.

For Lemma 3.2, write $H=\sum_jh_j\leq e$, with all $h_j\geq0$. When $e>0$, the support

$$
B=C_h-\left(1-\frac{H}{e}\right)C
$$

is nef: the extremal relation criterion reduces this assertion to the original degree bound and the inequality that the total selected positive contribution is at most $H$. Every wall degree of $B$ is therefore nonnegative. Linearity gives

$$
\deg_\eta(C_h)\ \geq\
\left(1-\frac{H}{e}\right)\deg_\eta(C)
\ \geq\ e-H
$$

for every invariant wall $\eta$. If $e=0$, nonnegativity and the budget force all selected heights to vanish, so $C_h=C$. This also explains why the proof includes a nef endpoint when $H=e$, without requiring an ample adjoint polytope.

For the fan form of Proposition 5.2, let $a$ be real ample support with every wall degree at least $n$. Choose a maximal cone $\sigma$ containing no negative focus of a cone-replacement relation $R$ with $\deg_a(R)<2r(R)$, and fix $D\subseteq\sigma$. The proof selects all combinatorially contractible primitive relations for which the support $a-2\mathbf1_D$ has negative degree. For an activated relation, let $\delta>0$ be the deficit and let $m\geq1$ be its least negative coefficient. Set

$$
\tau=\frac{\delta}{m}.
$$

Then $m\tau=\delta$ and $0<\tau\leq\delta$. The original degree bound gives exactly the budgets used in the nefness argument:

$$
\tau_i\leq2|D\cap U_i|-2|D\cap\{y_{i,1},\ldots,y_{i,q_i}\}|-n,
\qquad \tau_i\leq2r_i-n.
$$

The cases with zero, one, or two positive exceptional rays prove that the constructed support is nef. At the original cone its Cartier point is the chosen corner of the box for $a$, and its polytope lies in the original polytope. Varying $D$ gives every corner, and convexity gives the entire side-two box. The public endpoint constructs the activated family, the corrections, and the nef support internally; none is supplied as an additional hypothesis.

The public statements require no extra projectivity witness. `FanBasics` derives purity from completeness and constructs integral strict support by rational approximation in the finite open system of Cartier-point inequalities, followed by clearing denominators. This internal witness leaves the original real support and degrees unchanged. The simplex allocation in Lemma 4.4 and the shifts in Sections 6--7 retain their integer parameter domains.

## References

[paper] C. Folkerts, Quadratic generation for smooth polytopes with long edges, nineteen-page manuscript, 2026.

[casagrande] C. Casagrande, Contractible classes in toric varieties, Mathematische Zeitschrift 243 (2003), 99–126. arXiv:math/0111332.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The smaller topic files in `reading/` show the development before assembly; they are provided for navigation and are not an alternative build. The compiler checks the corresponding assembled development in `source/`. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

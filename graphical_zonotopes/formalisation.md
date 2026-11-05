# Sharp bounds for indecomposable summands of graphical zonotopes

The development contains the seventeen principal main-text theorems, the general planar corollaries, and the extensions described below. The scope boundaries distinguish these results from the optional claims that are not included.

## What the formal objects mean

All polytopes are actual subsets of finite-dimensional real coordinate spaces. A finite polytope is the convex hull of a finite set of points; a lattice polytope has a finite such presentation by integer-coordinate points. The graphical zonotope is the Minkowski sum of the segments $[e_u,e_v]$ over the graph's edges. A weak summand comes with a genuine identity

$$
Q+R=\lambda Z_G,\qquad \lambda\in\mathbb R_{>0}.
$$

The development proves that its compact convex complement convention is equivalent to an actual nonempty finite polytopal complement whenever $Q$ is a finite polytope. No integral or rational restriction is imposed on $\lambda$.

Dimension means affine dimension. The Lean expression is `Module.finrank ℝ (vectorSpan ℝ Q)`: Mathlib's `vectorSpan` spans all differences of pairs of points of $Q$, and `direction_affineSpan` identifies it with the direction space of the affine span. Thus dimension is translation invariant. "Full dimensional" means dimension $|V|-1$, as in the affine hyperplane of the zonotope. The direction graph also has a literal geometric meaning: each of its edges requires a nondegenerate exposed segment of the polytope parallel to $e_u-e_v$. The geometric direction-count bridge counts the actual one-dimensional real direction spaces, rather than an assigned set of allowed roots.

The intermediate indecomposability predicate quantifies over compact convex decompositions. The public ordinary-polytopal predicate quantifies over finite polytopes and concludes that each summand is a nonnegative homothetic copy, with arbitrary translation. The proved equivalences `minkowskiIndecomposable_iff_polytopal` and `weakSummand_indecomposable_iff_polytopal` justify this choice. Their hard direction reconstructs arbitrary compact summands from their lower support functions before proving that they are finite polytopes; it does not assume that the pieces already belong to the supermodular model.

### The generalized-permutahedron convention

For a normalised supermodular set function $z$, the lower base polytope is

$$
B(z)=\left\{x:\sum_{v\in V}x_v=z(V),\quad
\sum_{v\in S}x_v\ge z(S)\text{ for every }S\subseteq V\right\}.
$$

Normalisation here is only $z(\varnothing)=0$. Singleton values remain arbitrary and encode translations. They are set to zero only when taking the cone modulo translations.

`IsGeneralizedPermutahedron Q` means that $Q=B(z)$ for such a function. The theorem `generalizedPermutahedron_iff_weak_complete` proves, for every actual finite polytope $Q$, its equivalence with being a weak Minkowski summand of the complete-graph zonotope. This is the deformation convention for generalized permutahedra used by the paper's reference \[2\], Padrol, Pilaud and Poullot, *Deformed graphical zonotopes*, pp. 1--3, and is compatible with the lower-support description in the paper's Lemma 2.1. The note does not assert a separately formalised converse from arbitrary polytopes with root-parallel edges, or a separate normal-fan equivalence.

## The principal statements

All Lean declaration names below belong to the `GraphicalZonotopes` namespace. Write

$$
b_s=\binom{s}{2}2^{s-2}-(2^s-s-1)+1,\qquad
L_s=(s-2)2^{s-1}+2s-2-\binom{s}{2},
$$

and $U_2=1$, $U_s=b_s-b_{s-1}+1$ for $s\ge3$. The natural-number implementation of $b_s$ is proved equal to the printed integer formula; truncated subtraction is not an implicit change of meaning. The book $K_s*I_k$ has $s$ mutually adjacent hubs and $k$ independent outer vertices, each adjacent to every hub. The maximum dimension below is always the maximum among actual indecomposable weak summands.

### Theorem 3.1 (paper p. 8)

Every $n\ge4$: the displayed path-cube polytope is lattice, indecomposable and of dimension $n-1$, with its literal complement in $2Z_{P_n^3}$. Its actual graph is $P_n^3$, planar and $K_5$-free, with $3n-6$ edges and maximum degree $\min(n-1,6)$. The displayed formula is identified with the formal witness.

**Lean:** `Path.principal_path_theorem`

### Theorem 4.1 (paper p. 11)

Every full-dimensional indecomposable generalized permutahedron on $n\ge4$ coordinates has at least $3n-6$ actual directions and maximum actual degree at least $\min(n-1,6)$. Equality in the direction bound forces a 3-tree. Both bounds are attained for every $n$. There is no clique-number hypothesis.

**Lean:** `sharp_direction_bounds`; `direction_bounds_polytopal`

### Theorem 5.4 (paper p. 18)

Arbitrary finite separator data, full private zero/minimizer kernels, positive branch scales and the actual closure equation. The assembled function is supermodular and graphical; its complete tight-kernel dimension equals the quotient response-relation dimension. Extremality, the positive relation line and the branch-capacity bound follow with their printed hypotheses.

**Lean:** `Separator.positive_response_gluing_finite`

### Theorem 6.1 (paper p. 22)

Every 3-tree on at least four vertices: existence of a full-dimensional indecomposable weak summand is equivalent to at most three tetrahedra on each triangle, and to the printed component criterion. A lattice witness has tetrahedron coefficients one, triangle coefficients in $\{0,-1,-2\}$, actual graph $G$, and a complement in $(n-3)Z_G$.

**Lean:** `threeTree_classification_polytopal`

### Theorem 7.1 (paper p. 33)

All $s\ge2,k\ge1$: maximum dimension $\min(s+k-1,s+b_s-1)$, hence full dimension exactly when $k\le b_s$. A maximum-dimensional lattice witness is a summand of $(s-1)\min(k,b_s)Z_G$.

**Lean:** `clique_book_classification`

### Theorem 7.2 (paper p. 33)

Every clique separator of size $s\ge2$: an extreme graphical ray has at most $b_s$ components with nonzero private coefficient block. Zero blocks are not counted. No auxiliary order is imposed on the finite vertex set.

**Lean:** `Separator.clique_separator_capacity_finite`

### Theorem 7.5 (paper p. 36)

Every $1\le k\le\binom{s}{2}$, $s\ge2$: a full-dimensional lattice indecomposable book summand, with the stated actual dilation and a lattice complement. The single-outer-vertex simplex case is included.

**Lean:** `BooleanModule.small_count_lattice_books_literal`

### Theorem 7.10 (paper p. 41)

Every $s\ge5$ and every integer $L_s\le k\le b_s$: a full-dimensional lattice indecomposable summand of $(s-1)kZ_G$, with a lattice complement. All intermediate branch counts are covered.

**Lean:** `BooleanModule.book_upper_interval`

### Theorem 7.12 (paper p. 46)

Every $s\ge2$: the minimum number of actual directions in the saturated book is $\binom{s}{2}+sU_s$, with lattice equality. Each hub has at least $U_s$ active outer neighbours; the equality witness has exactly that many at each hub. For $s\ge3$ the actual hub graph is complete.

**Lean:** `SaturatedDirections.paper_theorem_7_12_geometric`

### Theorem 8.1 (paper p. 51)

All $k\ge1$: maximum dimension $\min(k+3,9)$ for $K_{1,1,2,k}$. At $k=6$, a nine-dimensional lattice summand of $4Z_G$ has 25 actual directions, and the host has no supporting spanning 3-tree.

**Lean:** `DiamondBook.paper_theorem_8_1_polytopal`

### Theorem 8.2 (paper p. 54)

Every $n\ge10$: a $K_5$-free graph with $3n-5$ edges, treewidth exactly four, and a full-dimensional lattice indecomposable summand of $(n-6)Z_G$ whose actual graph is $G$. Every proper edge-subgraph fails to support full dimension.

**Lean:** `SparseFamily.paper_theorem_8_2_polytopal`

### Theorem 8.4 (paper p. 57)

Every $p\ge1$: set $B_p=2^p+p$, $D_p=2^p+2p+1$, $M_p=(p-1)2^p+2$. The graph $K_{1,1,p,B_p}$ has a $D_p$-dimensional lattice indecomposable summand of $M_pZ_G$; for all $b\ge B_p$, the maximum dimension of $K_{1,1,p,b}$ is $D_p$.

**Lean:** `TwoHub.exponential_family`

### Theorem 8.7 (paper p. 63)

All $p,b\ge1$, with $a=\min(p,b)$: maximum dimension $\min(p+b+1,2^a+2a+1)$, lattice attainment and the exact full-dimension criterion. Both parameter orders and every intermediate case occur.

**Lean:** `TwoHub.two_singleton_classification`

### Theorem 8.9 (paper p. 64)

For four positive part sizes, put $N=\sum n_i$, $L=N-\max n_i$. A spanning admissible 3-tree exists exactly when $3\max n_i\le2N-3$. Separately, the maximum dimension among summands whose **actual support on their active vertices is a 3-tree** is $\min(N-1,3L-4)$, with lattice attainment. Those active vertices may be a proper subset of the ambient vertices.

**Lean:** `four_partite_spanning_threeTrees`; `four_partite_threeTree_dimension_attained`

### Theorem 9.1 (paper p. 66)

Every 3-tree on $n\ge6$, every full-dimensional lattice indecomposable summand, arbitrary real translations and every real $\lambda>0$: $\lambda\ge\max_e\left\lceil\frac12\sum_{C\supseteq e,\,|C|=4}|y_C|\right\rceil\ge2$, with nonzero integral tetrahedral coefficients. The path family attains two for every $n$.

**Lean:** `threeTree_lattice_dilation_sharp`; `threeTree_translated_lattice_lower_bound`

### Theorem 9.5 (paper p. 68)

For $K_5$-free $G$ on $n\ge4$, a full-dimensional lattice indecomposable summand of unscaled $Z_G$ forces $G$ to be complete four-partite with each part of size one or two; its actual graph is all of $G$, and $n\le8$, sharply. The translated-lattice endpoint is included.

**Lean:** `unit_lattice_classification_sharp`

### Theorem 9.8 (paper p. 71)

Every $r\ge4$: the zonotope of the complete $r$-partite graph with two vertices per part is a sum of two full-dimensional lattice indecomposable polytopes, with Boolean slacks and full actual graphs. For even $r$, both are centrally symmetric up to translation; for odd $r$, one is a translate of the negative of the other.

**Lean:** `DoubledParts.principal_boolean_phase_theorem`

The broader active-coordinate classification from Introduction §1.3 is also present as `unit_lattice_active_classification_finite`: dimension at least three is enough, without ambient full dimension. It identifies the nonisolated actual support as four parts of size one or two and bounds the number of active coordinates by eight.

## How the dependency chain closes

The base-polytope layer proves the finite greedy-vertex description, lower-support reconstruction and Minkowski addition. Elemental supermodularity inequalities become an explicit finite cone; Möbius coordinates describe graphical support. The exposed-edge calculations identify positive elemental slacks with actual root directions. The tight-kernel criterion then connects one-dimensional cone faces with ordinary geometric indecomposability. This common layer is proved once and used by every family.

The direction bounds pass through triangle-connected tetrahedral collections and their growth and degree inequalities. The unrestricted theorem separately handles larger cliques; it does not use a $K_5$-free hypothesis silently. Equality identifies the inductive 3-tree structure. The admissible 3-tree construction uses compatible boundary states and coefficient rigidity. Its graph predicate is the ordinary inductive construction from a tetrahedron by adding a fresh vertex adjacent to the vertices of an existing triangle.

Separator gluing keeps the whole private coefficient space, including coordinates assigned zero by a witness. Both internal zero rows and differences between minimising rows enter its kernel. If $A$ is the boundary-row matrix and $m_i$ the branch responses, the exact relation space is

$$
\ker\left(\mathbb R^r\longrightarrow\mathbb R^m/\operatorname{im}A,
\quad c\longmapsto\sum_i c_i[m_i]\right).
$$

Under the theorem's private-kernel hypotheses, its dimension equals the complete tight-kernel dimension of the assembled function. The additional ordinary-face bridge identifies this space with the span of the actual least convex face. It uses Mathlib's ordinary convexity and extremality definitions, and chooses any auxiliary vertex order internally. Thus the face statement is not replaced by a merely sufficient extremality test.  The Boolean response circuits, interval constructions and coordinate embeddings then give the entire book classification. Full coordinate decision trees and their cell/depth identities produce the two-hub families, with no bounded search substituted for the parameter induction.

For unit lattice dilation, integrality makes the elemental slacks Boolean. Local coefficient restrictions force thinness and square closure, and Cartesian completion gives the four-part structure. The Boolean phase construction proves the complementary indecomposable summands in every required dimension. The separate forest oscillation argument proves the real dilation lower bounds, while Appendix B constructs the endpoint-corrected path-join equality witnesses for every path length.

The planar corollaries use genuine plane topology. `HasPlaneDrawing` requires injective vertex placement and continuous simple edge arcs, meeting only at shared endpoints. The $K_5$ obstruction is closed by `Graph.IsArcK5.elim`, through a proved polygonal redrawing and Jordan/crosscut separation; it is not an input assumption. The $K_{3,3}$ obstruction bounds tetrahedra on a triangle. Together they identify connected tetrahedral components and prove Corollaries 6.4--6.5 for all geometrically planar graphs. The supporting Schönflies sources and their compatibility port are included in the development.

For Theorem 8.2, `HasTreewidthAtMost` is an ordinary tree decomposition with bags, vertex and edge coverage, and connected occurrence of each vertex. The conclusion is literally width at most four and not at most three. The latter follows from an induced six-vertex $K_2*C_4$ core of minimum degree four, using the proved low-degree consequence of a width-three decomposition. Thus "treewidth four" is not merely an upper bound or a different combinatorial surrogate.

## Additional statements and prescribed supports

The source includes the mathematical separator consequences in §5, the planar and partial-3-tree classifications and dimension spectra in §6, the Boolean module lemmas in §7, and the complete decision-tree statement of Lemma 8.6. Corollaries 9.10--9.12 include all sixteen four-part size patterns, complementary indecomposable lattice summands in every dimension at least three, and the least positive real dilation among $K_5$-free graphical zonotopes: one for orders four through eight and two for every order at least nine. Appendix B.1 is included for every $m\ge2$; the Lean parameter is $m-2$, so there is no omitted initial or infinite tail case.

**Corollary 7.11.** Its public source is `reading/extensions/book_spectrum.lean`, with endpoints `prescribed_coordinate_criterion`, `lattice_dimension_spectrum` and `positive_dimension_spectrum`. The statements retain all corner cases. If a prescribed coordinate set $U$ has at least two elements, let $h$ count its hubs and $t$ its outer vertices. A weak indecomposable summand of dimension $|U|-1$, constant in every coordinate outside $U$, exists exactly when

$$
t=0,\qquad\text{or}\qquad h=t=1,\qquad\text{or}\qquad
h\ge2\text{ and }1\le t\le b_h.
$$

"Constant" allows an arbitrary real value for each outside coordinate, so arbitrary translations remain permitted. It does not require every allowed internal edge to be active. The proof establishes the restriction equivalence from actual edge geometry and lower-support reconstruction, then applies the book classification; no-hub, one-hub, and two- or three-coordinate cases are treated explicitly. The spectrum assertion is every positive integer through $\min(s+k-1,s+b_s-1)$, with lattice attainment throughout.

## Proof choices and scope

Some formal proofs reorganise the paper's arguments. Theorem 8.2 uses the same graphs with a different recursively constructed polytope, retaining every existential conclusion; it therefore bypasses the specific boundary certificate in Lemma 8.3. In Boolean membership coordinates, an extension at a boundary triangle $a,b,t$ adds $wb(a+t-at)$ to the set function, where $w$ is the new vertex, and then exchanges the hub names. The proof preserves extremality and all old actual directions, creates the three required new directions, and increases the maximum slack by at most one. The ten-vertex seed has bound four, giving the asserted bound $n-6$ after every extension. For Theorem 9.8, on the vertex set $\{1,\ldots,r\}\times\{0,1\}$, the formal witness uses the integral lower-support function

$$
z(S)=\left\lfloor
\frac{|E(G_r[S])|+|\{i:(i,0)\in S\}|}{2}
\right\rfloor.
$$

The proof establishes the full existential theorem and both symmetry conclusions with this formula. Equality with the paper's displayed Walsh coefficients is not a claim of the formalisation. Theorem 3.1 and Appendix B do identify their particular displayed formulas with the formal witnesses.

The direct Boolean proof of Theorem 9.5 supplies the local restrictions it needs without exporting the whole classification taxonomy of Lemma 9.6 as a separate literal theorem. The algorithmic running-time claims in §§6.7--6.8 and Remark 6.3, and the balanced-tree refinement of Remark 8.8, are separate refinements; the mathematical classification and spectrum statements they accompany are included.

Appendix A is a downstream application and supplies no premise of a principal proof. Proposition A.2 is included in full: the literal determinant has the printed Newton polytope, homogeneity, degree, stability and absolute irreducibility. Here $m=n-2$ is the matrix size, and the polynomial has $m+2$ variables; the paper's path family has $n\ge4$, hence $m\ge2$. The polynomial is defined by the determinant of the displayed tridiagonal matrix. Its recurrence is then proved from that definition. For every size $m$, it is homogeneous of degree $m$, has that total degree, and is nonzero when all complex variables have positive imaginary part. For every field and every $m>0$, it remains irreducible over every field extension, in particular an algebraic closure. The zero-size determinant is the unit polynomial and is correctly excluded from irreducibility. The endpoints are `PathDeterminant.proposition_A_2_stability` and `PathDeterminant.proposition_A_2_absoluteIrreducible`.

The combined endpoint `PathDeterminant.proposition_A_2` contains all five assertions.

**The Newton identity** has a direct positive-continuant proof. With zero-based variables, define

$$
D_0=E_0=1,\qquad
E_{k+1}=t_{k+2}D_k+t_kE_k,\qquad
D_{k+1}=E_{k+1}+t_{k+1}D_k.
$$

A trailing Laplace expansion identifies $D_m$ with the literal matrix determinant. Both components have nonnegative coefficients and are nonzero. For any real coordinate weights, addition therefore takes the minimum of support weights, while multiplication adds them. The resulting minimum-plus recurrence has the same triple and quadruple formula as the minimum of the linear functional on $B(z_{m+2})$. The latter formula is proved using actual Minkowski addition and cancellation of attained minima of base polytopes. Separation of closed convex sets then gives equality of the actual Newton polytope with $Q_{m+2}$. Every weight is allowed, including negative and tied weights. This argument does not require the graphic representation in Proposition A.1. The exact identity is proved by `PathDeterminant.polynomial_newtonPolytope`.

The separate Corollary A.3 extension defines the Newton polytope as the convex hull of the actual nonzero monomial exponents. Minimum subset weights and maximum total weight first prove the needed product geometry when the product has a supermodular base polytope. The two factors inherit integral lower supports. Their coordinate minima vanish separately; extremality and a unit elemental slack then force one factor's Newton polytope to be the origin, so that factor is a nonzero constant. Scalar extension preserves support, giving absolute irreducibility over every field. This proof makes no assumption that the field embeds in the reals: only the natural-number exponent vectors are placed in real space. Its public endpoint is `NewtonGeometry.corollary_A_3_absoluteIrreducible`.

Proposition A.1's all-field rank formula, graphic representation and spanning-tree projection remain separate from these arguments and are not claimed as verified. The present review found no counterexample to a principal theorem and no justified mathematical correction to the supplied PDF.

### References for conventions

The supplied paper, especially Lemma 2.1 and §§3--9, fixes the statements being compared. The weak-summand convention for generalized permutahedra is explicit in Padrol, Pilaud and Poullot, *Deformed graphical zonotopes*, pp. 1--3. The geometric planarity dependency is the vendored source of Álvaro Begué's `schoenflies-lean`, revision `05a43d29cde026618777db3d4e4316204ccca237`; its license, upstream hashes and compatibility changes are included in the reproducible project.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The smaller topic files in `reading/` show the development before assembly; they are provided for navigation and are not an alternative build. The compiler checks the corresponding assembled development in `source/`. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

# Compatibility and realization of coordinate projection areas

## The mathematical objects and the principal statements

For a nonempty compact convex set $K\subseteq\mathbb R^d$, let

$$
A(K)_{ij}=\operatorname{Area}\{(x_i,x_j):x\in K\},\qquad
\mathcal R_d=\{A(K):K\subseteq\mathbb R^d\text{ is nonempty, compact, and convex}\}.
$$

The diagonal entries are zero: the diagonal projection is contained in a line, which has planar Lebesgue measure zero. Lower-dimensional convex sets are included. In particular, the zero array is the area array of a point. Closure means ordinary Euclidean closure in the finite-dimensional space of arrays, equivalently entrywise convergence.

The escape cone $\mathcal E_d$ consists of nonnegative symmetric hollow arrays $q$ for which there is a vector $w\in\mathbb R^d_{\geq0}\setminus\{0\}$ satisfying

$$
w_kq_{ij}\leq w_jq_{ik}+w_iq_{jk}
\qquad(i,j,k\text{ distinct}).
\tag{1}
$$

Zero entries and zero weight coordinates are permitted. The nonzero condition on $w$ is essential and is part of the Lean definition.

The project uses Mathlib's `ConvexBody` type, whose fields are a carrier set and proofs of convexity, compactness, and nonemptiness. The type name does not impose nonempty interior. Projection area is `volume.real` of the image under the literal coordinate map. It is not a primitive function characterized by assumed inequalities.

There are two coordinate models in the code. Finite function spaces `Fin d` $\to\mathbb R$ make coordinate deletion and finite matrices convenient; `EuclideanSpace` $\mathbb R$ `(Fin d)` supplies the Euclidean diameter used in the paper. An explicit continuous linear equivalence preserves every coordinate value and every projected area. The `PaperInterfaces` chapter of `source/main.lean` proves these identifications. Thus a change of ambient norm is not used to change the meaning of the diameter claim.

Names in the second column are unqualified; their namespaces are given beneath the table.

| Paper | Lean declaration and content |
|:--------------|:---------------------------------------------------|
| Paper | Lean declaration and content (continued) |
| Theorem 1.1 | `positive_rank_three_obstruction`: every positive hollow symmetric matrix of rank three in dimension at least five is outside $\operatorname{cl}\mathcal R_d$, and every four-label principal array is realized. |
| Proposition 2.3 | `boundary_compatibility_of_local_positivity`: two actual boundary quartets have the same restricted partition on their common triple; positivity is required only on those quartets. |
| Corollary 2.4 | `boundary_quartets_bound_sharp` and `boundary_quartets_unique_extension`: at most three boundary quartets occur on five labels; the bound is attained, and two or more determine a unique partition into blocks of sizes two and three. |
| Proposition 3.2 | `exists_prescribed_width_polytope_exact_prisms`: every escape witness gives a symmetric polytope with the prescribed widths and exact prism realizations of $q+L^{-2}A(B)$ for every $L>0$. |
| Theorems 1.2, 3.3 | `escapeCone_eq_divergingDiameterLimits` and `closure_realizationLocus_eq_union_escapeCone`: the exact escape characterization and $\operatorname{cl}\mathcal R_d=\mathcal R_d\cup\mathcal E_d$. |
| Theorem 3.3, approximation | `mem_escapeCone_iff_exists_full_dimensional_symmetric_sequence`: the same limit can be obtained from full-dimensional centrally symmetric polytopes with diverging diameter. |
| Theorem 4.1 | `strict_weighted_realization_with_vertex_bound`: strict positive weighted triangle data have centrally symmetric polytope realizations with at most $d(d-1)+2$ vertices and diameter exceeding any prescribed real number. |
| Corollary 5.2 | `weighted_triangles_obstruction`: no positive hollow symmetric matrix of rank at most three on at least five labels admits nonzero nonnegative weights satisfying all weighted triangle inequalities. |
| Corollary 5.3 | `exists_open_nonrealizable_strict_quartets`: a nonempty relatively open set of positive arrays lies outside the closure, while every four-label matrix has signature $(1,3)$. |
| Proposition 6.1 | `local_spectral_zero_reduction`: the full zero-row reduction from the local four-label spectral condition, for any choice of class representatives and without a global rank bound. |
| Theorem 6.2 | `rank_at_most_three_classification`: for every nonnegative hollow symmetric matrix of rank at most three, exact and limiting realization are equivalent and occur precisely when the quotient has at most four classes. |

The escape, closure, obstruction, open-set, and boundary compatibility results are in `ProjectionAreaPaper`; the prism construction is in `ProjectionAreaEscape`; the strict construction is in `ProjectionAreaStrict`; the rank classification is in `ProjectionAreaPaper.NonnegativeHollowMatrix`. The boundary corollary is in `ProjectionAreaMixedGeometry`, and the general zero-row reduction is in `ProjectionAreaSpectralZero`. The weighted-metric obstruction is in `ProjectionAreaRankThree.PositiveHollowMatrix`. The strict construction assumes $d>0$, including the one-dimensional segment case. The escape and quotient statements also cover dimension zero. The two `selected_boundary_quartets_` declarations in `ProjectionAreaPaper` state the boundary bound and unique extension for any five distinct selected labels in an arbitrary ambient dimension. Corollary 2.5 is the exact nonrealizability declaration `ProjectionAreaPaper.positive_rank_le_three_not_realizable`.

## Mixed-volume foundations

The supporting volume-polynomial theory is included as Lean source. Its mixed volumes are defined from coefficients of actual volume polynomials, with the conventional factorial normalization. The relevant theorems include existence of those polynomials, symmetry and multilinearity of mixed volume, monotonicity, covariance under linear maps, continuity on compact convex bodies, and the Alexandrov--Fenchel inequality. These are proof dependencies, not hypotheses added to the projection-area theorems.

The two basis modules contain the compactness and volume continuity machinery and the planar extrusion theory. The module `source/volume_polynomials/projection_area_foundation.lean` collects the additional proof chapters needed for Alexandrov--Fenchel and monotonicity.

Coordinate-segment extrusion is proved directly, with its normalization made explicit. If $E_i=[0,e_i]$ and $\pi_i$ deletes coordinate $i$, then

$$
(m+1)V(E_i,K_1,\ldots,K_m)
=V(\pi_iK_1,\ldots,\pi_iK_m).
$$

The proof compares the relevant volume-polynomial coefficients after integrating interval fibers. Two applications in dimension four give

$$
12V(E_i,E_j,K,K)=\operatorname{Area}(\pi_{ij}K),
\tag{2}
$$

where $\pi_{ij}$ deletes $i,j$. Equation (2) identifies the complementary area matrix with a genuine mixed-volume pairing. It is particularly useful for checking that no retained-coordinate and deleted-coordinate conventions have been interchanged.

The four-dimensional sufficiency result is also reconstructed from its geometric proof. The included construction is not restricted to positive or generic data. It includes boundary polytopes, their planar tilings and areas, positive diagonal changes of coordinates, and every zero pattern. Its final input is a nonnegative symmetric hollow four-by-four matrix with nonpositive determinant. The output is one compact convex nonempty set with all sixteen entries of the prescribed area matrix.

### Where Alexandrov--Fenchel enters, and how it is proved

The foundation proves Alexandrov--Fenchel for arbitrary compact convex bodies and additive Haar measure in a finite-dimensional real normed space of dimension at least two. The endpoint has no simplicity, interior, or smoothness hypothesis. The proof is an induction on dimension, with the planar case obtained from Brunn--Minkowski. The pinned supporting library proves Brunn--Minkowski through Prékopa--Leindler and finite-product tensorization, starting from an independently proved one-dimensional Brunn--Minkowski inequality. Thus this chain is acyclic.

The order of the intermediate results matters. Polynomiality and nonnegativity of the volume coefficients are established first, by decomposing finite convex hulls into pyramids over their actual exposed facets and then passing to limits. First variation expresses mixed volume as a sum of support heights multiplied by nonnegative facet mixed volumes. It therefore proves monotonicity independently of Alexandrov--Fenchel.

For a finite tuple of polytopes, a generic perturbation of support heights constructs a common simple refinement. Adding a small multiple of this reference polytope puts the tuple into one open cone of support heights. The mixed-volume pairing on that cone extends to a symmetric bilinear form $Q(x,y)=x^{\mathsf T}My$. Increasing one support height while fixing another enlarges the corresponding facet, so the earlier monotonicity theorem gives $M_{ij}\geq0$ for $i\ne j$.

The graph of positive off-diagonal entries is connected. This is proved first for a diagonal background using Brunn--Minkowski, and then for the general background using positivity and multilinearity. Thus connectivity does not assume the inequality being proved. For a positive reference height $h$, put $m_i=(Mh)_i/h_i>0$. The induction hypothesis on the lower-dimensional facet spaces gives

$$
x^{\mathsf T}Mx\leq\sum_i\frac{((Mx)_i)^2}{m_i}.
$$

After conjugating by $D_m^{-1/2}$, the reference vector is a positive eigenvector of eigenvalue one. A finite maximum principle gives that every eigenvalue is at most one and that this eigenspace has dimension one. The displayed inequality gives $\lambda\leq\lambda^2$. Hence there is only one positive eigenvalue, and the spectral theorem yields the required reverse Cauchy--Schwarz inequality, including its null case. Continuity, thickening, and finite-hull density remove all the intermediate polyhedral assumptions.

This establishes the mathematical input used in the boundary proof below. The full Shenfeld--van Handel equality classification is not an additional axiom or an unproved dependency: the project proves the specific rigidity needed here by a separate argument.

## Escape: why the weights are necessary

The proof of the necessary direction of Theorem 3.3 begins with arbitrary bodies $K_m$ whose areas converge and whose diameters tend to infinity. It does not assume that the bodies are polytopes or centrally symmetric.

For each body, choose a coordinate of maximal width and a chord joining points where that coordinate is minimal and maximal. Translate the chord midpoint to the origin. A parallelogram contained in each relevant planar projection bounds every transverse coordinate by a fixed multiple of the corresponding area divided by the selected coordinate width. That width also tends to infinity. A reciprocal longitudinal/transverse rescaling therefore places the normalized bodies in one fixed compact box. The normalized chord directions have maximum coordinate norm one.

Compactness gives a subsequence of both the bodies and their directions. The limiting direction is nonzero because its maximum coordinate norm remains one. Projected-area continuity is applied also to the varying linear projection maps, so the limit of the actual areas has the required fiber-area representation. This step includes degenerate limiting bodies; an interior assumption is not introduced to obtain continuity.

The weighted triangle inequality comes from a planar area seminorm. For a compact convex set $C$ and two linear functionals $f,t$, put

$$
F_{C,t}(f)=\operatorname{Area}\{(f(x),t(x)):x\in C\}.
$$

On a fixed $t$-fiber, every image under a linear functional is a compact interval. The width of the image under $f+g$ is at most the sum of the two widths. Integrating fibers proves

$$
F_{C,t}(f+g)\leq F_{C,t}(f)+F_{C,t}(g),\qquad
F_{C,t}(sf)=|s|F_{C,t}(f).
$$

These are proved for ordinary planar measure. Taking absolute values of the limiting direction coordinates supplies the nonnegative, nonzero weight vector in (1).

Finally, arbitrary convergent sequences of area arrays are divided by their diameter behavior. A bounded-diameter subsequence can be translated into one fixed ball; compactness and area continuity then give an exact realizer of the limit. Otherwise a subsequence has diameter tending to infinity and supplies escape weights. This proves the inclusion $\operatorname{cl}\mathcal R_d\subseteq\mathcal R_d\cup\mathcal E_d$ without assuming that the realization locus itself is closed.

The closedness assertion in Theorem 3.3 is `ProjectionAreaPaper.escapeCone_isClosed`. Normalize each weight vector so that its coordinates sum to one. The resulting simplex is compact. A convergent subsequence of witnesses retains nonnegativity, sum one, and all the weighted inequalities in the limit. Thus its limit is still a nonzero witness. This argument permits zero weight coordinates.

## Escape constructions and strict exact realizations

For the reverse inclusion, the code constructs actual centrally symmetric finite convex hulls. The width identities are proved for all zero-weight patterns. Given any witness $w$ in (1), Proposition 3.2 supplies a centrally symmetric polytope $B$ containing the origin with $W_B(w_i e_j-w_j e_i)=q_{ij}$. Coordinates with zero weight are kept explicitly; they are not discarded by division. The `EscapePrisms` chapter of `source/projection_escape.lean` also establishes equation (4) in §3 of the paper:

$$
K_L=[-Lw/2,Lw/2]+L^{-1}B,\qquad
A(K_L)_{ij}=q_{ij}+L^{-2}A(B)_{ij}\quad(L>0).
$$

This follows from the actual planar segment-extrusion formula, including zero projected directions and degenerate planar sets. The two segment endpoints lie in $K_L$, giving the Euclidean bound $\operatorname{diam}(K_L)\geq L\lVert w\rVert$.

The main escape characterization has a separate proof by approximation through strictly positive data. The approximation lemmas produce positive weights and strict weighted triangle inequalities converging to the given data. Applying the exact strict construction at increasing diameter thresholds gives escaping polytopes. Adding a sufficiently small centrally symmetric finite hull with interior makes each approximant full-dimensional. The added amount is chosen separately for each index using area continuity, while diameter does not decrease. Consequently convergence, symmetry, finite generation, full dimension, and divergence of diameter hold along the same sequence.

Here is the exact strict construction from Theorem 4.1. When $w_i>0$, set $d_{ij}=q_{ij}/(w_iw_j)$ and $d_{ii}=0$. These entries satisfy the strict triangle inequalities. For each unordered pair $r=(i,j)$, define

$$
f^r_k=\frac{d_{ki}-d_{kj}}2,\qquad b^r_k=\frac{w_k f^r_k}2.
$$

The designated difference is $f^r_j-f^r_i=d_{ij}$, whereas every other pair $(k,\ell)$ satisfies $|f^r_\ell-f^r_k|<d_{k\ell}$. The Lean proof also handles pairs sharing one endpoint; the strict inequality is not inferred from a disjointness assumption.

For sufficiently large $T$, take

$$
P_T=\operatorname{conv}\bigl(\{Tw,-Tw\}\cup
\{b^r/T,-b^r/T:r=(i,j),\ i<j\}\bigr).
$$

In each coordinate plane the designated four points form a diamond. Writing every other transverse point in the corresponding planar basis gives coefficients $\alpha,\beta$ with $|\beta|<1$. One finite threshold ensures $|\alpha|/T^2+|\beta|\leq1$ for all pairs simultaneously. Thus the entire projection is exactly the designated diamond, not merely contained in a region of the correct area. Its area is $q_{ij}$.

There are at most $2+2\binom d2=d(d-1)+2$ generating points, and hence at most that many vertices. The Lean statement includes both finiteness of the extreme-point set and the bound on its cardinality; the bridge is the theorem that every extreme point of a convex hull belongs to its generating set. The two axis points give $\operatorname{diam}(P_T)\geq2Tw_i$ for any chosen coordinate $i$. Positivity of $w_i$ then yields the full "arbitrarily large diameter" quantifier.

The introductory strict sentence in Theorem 1.2 does not separately assume positive areas. Its counterpart is `strict_nonnegative_weighted_realization_with_vertex_bound`. If a nonnegative array has a zero off-diagonal entry, strict weighted triangles rule out a third label. The entire array is then zero, and a long centrally symmetric segment supplies the missing low-dimensional case. This keeps the introductory statement faithful even where its triangle conditions are vacuous. The arbitrary-diameter conclusions explicitly assume $d>0$; in the introductory theorem this already follows from the nonzero witness in (1). In dimension zero every body is a point, so such a conclusion would be false; the general escape and closure theorems still cover that dimension, with an empty escape cone and the singleton zero realization locus.

## The boundary obstruction: an elementary equality argument

The paper obtains compatibility of boundary quartets through equality theory for mixed volumes. The formalization uses a different argument that proves the needed geometric consequence directly. It requires the ordinary Alexandrov--Fenchel inequality and monotonicity, together with elementary fiber-product and planar-area arguments. It does not assume the Shenfeld--van Handel equality characterization.

### Balanced kernels and exact fiber products

A positive rank-at-most-three four-by-four area matrix has determinant zero. Its three opposite square-root products satisfy a boundary equality. Positive diagonal normalization gives a complementary matrix with a kernel vector having exactly two positive and two negative coordinates. All coordinates of this kernel vector are nonzero. The normalization proof covers all three choices of the largest opposite product.

Let $c$ be such a kernel, and split its coordinate segments into positive and negative boxes $P,Q$. Equation (2) makes their self-pairings and mutual pairing equal to the same positive number. Apply Alexandrov--Fenchel after replacing $P$ by $P+sT$, for arbitrary comparison body $T$ and $s>0$. The first-order coefficient gives one inequality between the pairings with $T$; exchanging $P,Q$ gives the opposite one. Thus

$$
\sum_i c_i V(E_i,T,K,K)=0\qquad\text{for every actual convex body }T.
\tag{3}
$$

This universal pairing identity replaces the use of Lemma 2.2 below. The general mixed-area measures in that lemma are not constructed in this project.

Fix an omitted coordinate with positive coefficient, and write $L=\pi_iK$. Enlarge $L$ to the intersection $D$ of the two cylinders determined by the projections that delete the two negative coordinates. This is a compact convex fiber product with $L\subseteq D$. Its two defining projections are unchanged. Subtracting (3) for embedded copies of $D$ and $L$ makes the two negative terms vanish. Every remaining term is nonnegative by monotonicity. The selected positive term must therefore vanish, giving

$$
V(D,L,L)=\operatorname{Vol}(L).
$$

The projection $L$ has interior. To prove this rather than assume it, suppose that it has a nontrivial affine relation. Lift that relation to the four original coordinates, with coefficient zero in the omitted coordinate. The fiber-area seminorm gives inequalities between the absolute values of its coefficients. The normalized boundary matrix forces those absolute values to agree up to positive diagonal factors. One zero coefficient therefore forces all coefficients to be zero, a contradiction.

Put $a=\operatorname{Vol}(L)>0$, $b=V(L,D,D)$, and $c=\operatorname{Vol}(D)$. Two applications of Alexandrov--Fenchel give $ab\leq a^2$ and $ac\leq b^2$, hence $c\leq a$. Containment gives the reverse inequality. Since a proper enlargement of a compact convex set with interior has strictly larger volume, $D=L$. The boundary kernel has therefore forced an exact equality of bodies with a fiber product.

### Overlapping fiber products force a prism

Two incompatible partitions induce two different fiber-product descriptions of their common three-coordinate projection. After relabeling, one description says that the middle-coordinate fiber depends only on the first base coordinate; the other says that it depends only on the second. The planar base has positive area and hence nonempty interior.

On the interior of this base, a small rectangle allows any fixed fiber to propagate by two coordinate moves. For a fixed height, the set of base points carrying that height is relatively open and relatively closed. Connectedness makes it the whole interior whenever it is nonempty. Convex approximation and closedness then include boundary fibers. The common projection is an actual coordinate prism.

The prism gives two rectangular coordinate shadows. One further fiber-product equality in the first quartet gives a third. Relabeling these shadows as $01,12,23$, and normalizing the four coordinate ranges to $[0,1]$, gives

$$
q_{01}=q_{12}=q_{23}=1,
\qquad A=q_{02},\quad B=q_{03},\quad C=q_{13},\qquad 0<A,B,C\leq1.
$$

The remaining contradiction is a planar area calculation.

### The planar calculation

For a compact convex set in the unit square, let its fibers at horizontal coordinates $0$ and $1$ be $[l_0,u_0]$ and $[l_1,u_1]$, and assume its vertical range is $[0,1]$. Define the signed overlap

$$
h=\min(u_0,u_1)-\max(l_0,l_1).
$$

It may be negative. The trapezoid between the edge intervals, together with triangles to a top and a bottom point, lies inside the set. Their interiors are disjoint, and their exact triangle areas give

$$
\operatorname{Area}\geq\frac{1+h}{2}.
$$

The formal proof constructs the four triangles as affine images of a unit pyramid. Their intersections lie in three affine lines of measure zero, so their areas add even in degenerate endpoint cases.

If a three-dimensional convex set has a full unit-square shadow, all four pairs of the corresponding vertical edge fibers of its other two shadows intersect. The sum of their signed overlaps is nonnegative. The sum of the other two shadow areas is therefore at least one. Applied to the rectangular path above, this yields $A+B\geq1$ and $C+B\geq1$.

Set $p=AC$. Then $(1-B)^2\leq p\leq1$, and the hollow determinant is

$$
\det Q=p^2-2p(1+B)+(1-B)^2
\leq p^2-p-2pB\leq-2pB<0.
$$

This contradicts the boundary determinant zero. Incompatible partitions cannot occur. Finally, a finite combinatorial proof using kernel reduction shows that five labels cannot support five pairwise compatible balanced quartet partitions. The computation enumerates finite partitions, not numerical samples of convex bodies or area arrays.

### Compatibility and the sharp five-label count

The compatibility theorem is stated independently, with no rank hypothesis on the full area matrix. A boundary equality on each of the two selected quartets supplies its own balanced kernel and its own local rank bound. The endpoint `boundary_compatibility_of_local_positivity` therefore proves Proposition 2.3 in its full form: positivity is required only on the two specified quartets, with arbitrary injective selections of five labels from a larger coordinate space. The area between their nonshared labels, and all areas involving outside labels, are unrestricted. The predicate expressing this condition is proved equivalent to positivity of each actual four-coordinate projection.

For Corollary 2.4, each boundary quartet determines one of its three balanced cuts; positivity makes this cut unique. The code forms a partial choice of cuts, leaving nonboundary quartets unassigned. Two compatible quartets omitting $m,n$, with common-triple partition $\{a,b\}\mid\{r\}$, force the global partition $\{a,b\}\mid\{r,m,n\}$. Small finite checks on pairs and triples of cuts show that every additional compatible quartet extends this same partition and omits a member of its three-element block. The full cardinality and uniqueness statements then follow symbolically for arbitrary partial choices. No additional boundary quartet is assumed to exist.

The bound is attained by an actual twelve-point convex hull. In complementary coordinate subspaces of $\mathbb R^5$, take the square $[-1,1]^2\times\{0\}^3$ and the cube $\{0\}^2\times[-\tfrac12,\tfrac12]^3$, and take their convex hull. The area in coordinates $01$ is $4$; each area on two of coordinates $2,3,4$ is $1$; and every mixed projection is the diamond with axis half-lengths $1$ and $\tfrac12$, also of area $1$. Exactly the three quartets retaining both labels $0,1$ are boundary quartets. The `SharpBoundaryExample` chapter of `source/main.lean` computes the projected convex hulls and their Lebesgue areas, rather than merely postulating this area matrix.

## Excluding escape and treating every zero pattern

The escape obstruction has an independent algebraic proof. Positive weights turn (1) into ordinary triangle inequalities for $q_{ij}/(w_iw_j)$ and preserve matrix rank. If a witness has a zero coordinate, positivity permits that coordinate to be replaced by a sufficiently small positive number. The finite minimum used in this argument is proved positive; zero weights are not simply excluded.

Every positive four-point metric with zero hollow determinant has the opposite-edge equalities of a rectangle. The Lean proof obtains these from a four-point cut decomposition and an explicit sum of nonnegative products for the determinant. Applying the rectangle relations on overlapping four-point subsets contradicts positivity on five labels. Thus a positive metric matrix on at least five labels has rank at least four. The resulting Corollary 5.2 is `ProjectionAreaRankThree.PositiveHollowMatrix.weighted_triangles_obstruction`. This theorem includes the zero-weight cases. Combining it with the geometric obstruction and the compactness/escape alternative gives exclusion from the entire closure.

For Corollary 5.3, the formalization uses the explicit rank-at-most-three array $q_{ij}=(i-j)^2$ on distinct integer labels. Adding $\varepsilon>0$ to every off-diagonal entry makes its quadratic form strictly negative on the sum-zero hyperplane. Invertibility and the spectral decomposition then give exactly one positive and three negative eigenvalues on every quartet. Since the unperturbed array is outside the closure of the realization locus, sufficiently small perturbations remain outside it. The strict quadratic inequality is open, as is positivity, giving the claimed nonempty open set in the space of hollow symmetric arrays.

For the nonnegative rank-at-most-three case, a zero entry $q_{ij}=0$ forces every cross minor of rows $i,j$ to vanish: the relevant four-label determinant is

$$
(q_{ik}q_{j\ell}-q_{i\ell}q_{jk})^2=0.
$$

The separate statement of Proposition 6.1 derives this same identity from the weaker local spectral hypothesis: the determinant on four distinct labels is nonpositive, so the displayed square vanishes. Repeated-label cases follow directly from hollowness and symmetry. This argument therefore also covers ambient dimensions below four, where the four-distinct-label condition is vacuous. On nonzero rows this is equivalent to positive proportionality. The code constructs the quotient by this actual equivalence relation, chooses one original coordinate from each class, and proves

$$
Q=RQ^*R^{\mathsf T},\qquad \operatorname{rank}Q^*=\operatorname{rank}Q.
$$

The matrix $R$ is also the explicit coordinate-replication map for bodies. Selecting representatives and replicating coordinates prove both directions of exact realization. The induced fixed continuous maps on area arrays prove both directions for closure membership as well. No zero-pattern condition is imposed on the approximating arrays. The general proposition allows every representative section of the quotient map; a canonical section is supplied to show that such choices exist. The replication factor is proved to equal one at each chosen representative, matching the paper's normalization.

A quotient with at most four labels is realized by the full four-dimensional construction, padding by zero coordinates when needed. A quotient with at least five labels is positive and is excluded from the closure by the preceding argument. This proves the complete criterion, including arbitrary numbers of zero rows and repeated proportional rows.

## Literal auxiliary statements and the displayed example

The module `source/additional_results.lean` makes several conclusions explicit that are not needed as separate statements in the principal proof chain. Each is proved from the preceding development, with its own statement.

##### Full dimension in Lemma 2.1.

The theorem `ProjectionAreaFullInterior.positive_boundary_interior_of_equality` proves that every actual realization of a positive boundary quartet has nonempty interior in $\mathbb R^4$. The intermediate endpoint `positive_boundary_interior` uses the equivalent rank bound. To see the proof, suppose the body has a nontrivial affine relation. The coefficient inequalities used above force every coefficient to be nonzero. Translating and multiplying each coordinate by its coefficient puts the body in $x_0+x_1+x_2+x_3=0$, preserving positivity and the rank bound. It is then the graph of its three-coordinate projection $L$, which has interior.

Define the genuine mixed-volume brightness functional by

$$
N_L(v)=3V_3([0,v],L,L).
$$

Coordinate extrusion and covariance under six explicit linear maps of determinant $\pm1$ identify all six graph projection areas with values of $N_L$. Monotonicity and a proved Minkowski inclusion of sums of segments give Hlawka's inequality. Alexandrov--Fenchel and strict volume monotonicity give $N_L(v)>0$ for $v\ne0$ when $L$ has interior. The boundary equalities then contradict Hlawka's inequality for three explicit independent directions. This supplies the literal four-dimensional conclusion; the principal compatibility proof above already needed only the separate three-coordinate interior result.

##### The seminorm in Lemma 3.1.

The theorem `ProjectionAreaPaper.escaping_limit_seminorm` has exactly the sequence hypotheses of the paper, with ordinary Euclidean diameter. It produces an actual Mathlib `Seminorm`, a Euclidean unit vector $v$, and the identities $q_{ij}=N(v_i e_j-v_j e_i)$ for every pair. The construction proves the stronger assertion for every $q\in\mathcal E_d$. Take the finite symmetric vertex family of the prescribed-width polytope $B$ and put

$$
N_w(x)=\max_{b\text{ in the vertex family}}2|\langle x,b\rangle|.
$$

This is the pullback of an ordinary finite sup norm, so the bundled seminorm laws come from established norm and linear-map lemmas. The proved vertex bounds and their attained values give $N_w(w_i e_j-w_j e_i)=q_{ij}$. With $r=\|w\|>0$, set $v=w/r$ and $N(x)=N_w(rx)$. This gives the required unit normalization without discarding any zero weight. The chosen $v$ is even nonnegative; the statement does not require it to be a particular subsequential chord direction from the original bodies.

##### Density after Theorem 4.1.

Let $\mathcal S_d$ be the set of positive hollow symmetric arrays admitting nonzero positive weights and all strict weighted triangles. This set is defined by the inequalities, independently of realization. The code proves

$$
\mathcal S_d\subseteq\mathcal R_d,
\qquad \operatorname{cl}\mathcal S_d=\mathcal E_d,
\qquad \operatorname{cl}(\mathcal R_d\cap\mathcal S_d)=\mathcal E_d.
$$

The first assertion is exact strict realization; the second combines the proved strict approximation with closedness of the escape cone. The nonzero-weight condition also makes these identities valid in dimension zero, where both $\mathcal S_0$ and $\mathcal E_0$ are empty.

##### The circle in Lemma 5.1.

The theorem `ProjectionAreaCircleMetric.rank_three_circle_realization` starts with a positive hollow symmetric rank-three matrix satisfying the ordinary triangle inequalities. It uses squared distances in `EuclideanSpace` $\mathbb R$ `(Fin 2)`. It gives at most four distinct points, a positive-radius circle containing them, and a nondegenerate rectangle in the four-label case. The previously proved metric rank bound reduces the number of labels to three or four; this is an exhaustive reduction, not a restriction of the theorem. For three labels, write $a=q_{01}$, $b=q_{02}$, $c=q_{12}$, and set

$$
s=\sqrt a,\qquad z=(a+b-c)/2,\qquad
x=z/s,\qquad t=\sqrt{b-x^2}.
$$

The metric inequalities give $t>0$. The actual points $(0,0),(s,0),(x,t)$ have the required squared distances and circumcenter $(s/2,(x^2+t^2-sx)/(2t))$. For four labels, the rectangle equalities supply three possible labelings of four explicit rectangle corners. The argument does not use the circle assertion to prove the rank bound from which it starts.

##### The introductory hexagon matrix.

The matrix on page 2 is defined entry by entry. A factorization through $\mathbb R^3$ proves rank at most three, and its first three-label determinant is six, proving exact rank three. The points $(b_i/2,\sqrt3\,c_i/2)$, for the displayed vectors $b,c$ in the paper, are proved distinct, to have norm one, and to have exactly those squared distances. The endpoint `ProjectionAreaExamples.hexagon_obstruction` then applies the general theorem: this particular array is outside $\operatorname{cl}\mathcal R_5$, while every four-label restriction has an exact realization. The further endpoint `hexagon_signature` gives exactly one positive, two negative, and two zero eigenvalues. Its proof uses the displayed quadratic-form factorization: it is nonpositive on the sum-zero hyperplane, so there is at most one positive eigenvalue. Zero trace and rank three then give the exact three counts. No numerical rank or eigenvalue calculation is used. These squared distances fail the metric inequalities: $q_{02}=3>q_{01}+q_{12}=2$, so the example does not satisfy Lemma 5.1's hypotheses.

##### The zero-dimensional convention.

The arbitrary-diameter statement is made for $d\geq1$. The separate theorem `ProjectionAreaZeroDimension.strict_empty_data_counterexample` checks the limiting convention explicitly: the unique empty array and empty weight vector satisfy the literal positive-entry and strict-triangle conditions vacuously, but every convex body in $\mathbb R^0$ has diameter zero. This is a verified counterexample to extending that particular conclusion to dimension zero, rather than a purported proof of such an extension.

##### What the check establishes.

##### Reading and editing.

Start with `source/main.lean` for the rank results, compatibility, and zero-row reduction; `source/projection_escape.lean` for escape and closure; and `source/projection_core.lean` for strict realizations. `source/additional_results.lean` contains the example and the additional statements. `source/full_dependency_audit.lean` inspects all nine mathematical modules.

##### Computation and trust.

Finite cut arguments use kernel reduction to prove universal combinatorial lemmas for arbitrary real arrays. Reporting commands introduce no propositions. The basis modules clear two elaborator caches between chapters, preserving kernel declarations and proof terms. The ordinary kernel checker remains enabled throughout.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

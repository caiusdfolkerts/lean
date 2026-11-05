# Normal–projective equivalence and the exact cube bound

## Scope and the mathematical statements

The development concerns three assertions of the manuscript. For a fixed simple $d$-polytope, Theorem 1 identifies normal--projective equivalence with membership in the same connected component of the labelled realization space modulo affine transformations. Corollary 2 says that every simple convex three-polytope is normal--projectively unique. Theorem 3 gives the exact largest distance from a combinatorial $d$-cube to the standard cube:

$$
k_d=2d-3\qquad(d\ge2).
$$

Its upper bound uses $d-1$ projective and $d-2$ normal moves. Its lower bound holds throughout the family

$$
P_{d,\varepsilon}=
\{x\in\mathbb R^d:x_i\ge0,\ x_i+\varepsilon x_{i+1}\le1\quad(1\le i\le d)\},
\qquad 0<\varepsilon<1,
$$

with cyclic indices, and forces at least those numbers of the two move types separately. The local construction in Lemma 4 supplies the bound of $2d$ moves in a neighborhood of any simple realization.

The formal cube development often writes $d=n+1$ with $n\ge1$. This is an indexing convention for a nonempty cyclic index type, covering every integer $d\ge2$. The cyclic parameter remains an arbitrary real number in $(0,1)$; no finite enumeration or selected value of $\varepsilon$ is used.

The principal declarations are listed below. The namespace prefix `NormalProjective` is omitted in this table only.

| Manuscript | Lean declaration |
|:---|:---|
| Theorem 1 | `CanonicalModel.Realization.pnRelated_iff_same_component` |
| Lemma 4, local bound | `normalized_matrix_local_word`; `CanonicalModel.Realization.local_word_neighbourhood` |
| Corollary 2 | `simple_three_pn_unique`; `simple_three_presentations_pn`; `simple_three_faceOrderIso_pn` |
| Theorem 3, upper bound | `CubeUpper.every_cube_exact_word` |
| Theorem 3, lower bound | `CubeTargetLabels.cyclic_to_geometric_cube_lower_bound` |
| Theorem 3, exact maximum | `CubeTargetLabels.geometric_largest_PN_distance` |

## Realizations and moves are geometric objects

A presentation is a finite labelled system of inequalities in the actual coordinate space $\mathbb R^d$,

$$
P=\{x:\langle n_i,x\rangle\le h_i\quad(i\in F)\}.
$$

The carrier is compact and has nonempty interior. Each $n_i$ has Euclidean length one. For each label $i$, a strict facet witness makes exactly the $i$th inequality tight. This excludes redundant inequalities and duplicate facets. The faces are the actual exposed faces of the carrier, ordered by inclusion. A realization of a reference presentation includes an order isomorphism of those face lattices preserving the specified facet labels.

The finite-halfspace theory proves that the displayed equality faces are exactly all nonempty maximal proper exposed faces. It also proves that the carrier is the convex hull of its finitely many actual vertices. At an extreme point, active normals span the dual space: otherwise a nonzero annihilating direction would give a short segment through the point inside the carrier. A basis can therefore be extracted from the active normals. Different vertices have different active labelled sets, which proves their finiteness. Compact convexity then recovers the carrier from its extreme points.

The converse representation is supplied by `FiniteHullModel.finite_hull_has_facet_model_all_dimensions`. Its input is an arbitrary finite vertex list whose convex hull has nonempty interior, and its conclusion gives a canonical complete facet presentation with literally the same carrier. Repeated or nonextreme input generators are allowed. In positive dimension, translate an interior point to zero, take the polar, and use its actual extreme points as facet labels for the original hull. At a polar vertex, an average of independent active primal normals is a strict witness for the corresponding facet. Dimension zero is handled separately by the presentation with no inequalities. Thus the choice of facet coordinates does not restrict the class of polytopes. This representation theorem identifies carriers and facet labels; the realization-space topology used here is the facet-coordinate topology.

The topology on presentations is induced by their unit-normal and support coordinates, as in the manuscript's facet-coordinate argument for Theorem 1. Normalization from nonzero raw inequalities is explicit and continuous: divide each normal and its support by the same positive Euclidean length. This preserves the carrier and every labelled facet. Affine equivalence is witnessed by an actual invertible affine map, with the required carrier and facet images; the affine quotient carries the quotient topology.

A normal move means equality of the corresponding outward unit normals. A projective move is an invertible homogeneous matrix whose denominator is nonzero at every point of the source carrier, and whose images of the carrier and all labelled facets are exactly the specified target sets. The inductive relation `CanonicalModel.Realization.PNWord` has only three constructors: an empty word, a projective step, and a normal step. It records the two counts separately. In particular, affine changes are projective moves when a distance is being counted; there is no uncounted affine-move constructor.

## The component theorem and local control

The stability argument concerns the entire face lattice. First, nearby bounded halfspace systems have a common carrier bound. For each possible set of tight labels, feasibility inside that common compact ball is a closed condition on the coefficients. Consequently, a tight system that is infeasible at the original presentation remains infeasible nearby, including when its coefficient matrix is singular.

At each simple vertex, its $d$ active rows are independent. The corresponding inverse-matrix formula varies continuously, and all nonactive inequalities remain strict in a sufficiently small neighborhood. Combining these facts gives a bijection of all old and new vertices preserving every incidence. A separate face theorem upgrades the vertex incidence bijection to an order isomorphism of the actual exposed-face lattices. This excludes both the loss of an old face and the appearance of an untracked new vertex.

The elementary projectivity is

$$
T_u(x)=\frac{x}{1+u(x)}.
$$

For inequalities $f_i(x)\le h_i$, its transformed rows are $f_i+h_i u$, with the same supports. The formal proof establishes the full image identity in both directions. Positivity of the source denominator and boundedness exclude a point in the transformed halfspace system with an invalid inverse denominator: such a point would produce a nonzero feasible recession direction in the original bounded region.

After centering and choosing a generic linear frame, all entries in one selected normal coordinate are nonzero. The controller changes one column at a time using support changes and these rank-one projective updates. A final update corrects the remaining common term. Positive row rescalings return the raw system to the required normalized presentation. All intermediate systems depend continuously on the target coefficients, so one neighborhood keeps every step within the stable labelled realization space. A uniform carrier bound makes every projective denominator positive. Conjugating back through the fixed affine chart preserves both move counts and removes the generic-coordinate assumption from the result.

Thus each PN class is open. Conversely, a normal step admits a support interpolation within the same labelled type. An admissible projective step, after separating its affine factor, admits the path $T_{tu}$, $0\le t\le1$. The affine factor is identified in the affine quotient. These constructions put every PN word inside one connected component of that quotient. The open partition by PN classes then proves the reverse inclusion. No unproved assertion about connectedness of realization spaces is used in Theorem 1.

## The three-dimensional corollary

The new geometric chain establishes the connectedness needed in dimension three through actual convex caps. The cap structure stores a geometric triangulation of the standard triangle with at least one interior vertex, positive heights at its interior vertices, zero heights at its three corners, and affine upper supporting planes. A plane is tight at exactly the three vertices of its face and strictly above every other vertex. These are pointwise geometric conditions; connectedness, stresses, and PN equivalence are not fields of the structure.

### From a simple polytope to a cap

Normalize the primal inequalities to $n_i\cdot x\le1$ and choose a root vertex $r$. For $t>0$, use the following affine primal image and its polar vertices:

$$
P_t=\frac{P-(1-t)r}{t},\qquad
w_i(t)=\frac{t n_i}{1-(1-t)n_i\cdot r}.
$$

The three normals active at $r$ remain fixed, and all other $w_i(t)$ tend to zero as $t\downarrow0$. One fixed affine map sends the three root normals to the base triangle and zero to a point at positive height above its barycentre. For small positive $t$, all remaining vertices therefore have positive height and strictly interior horizontal projections.

The supporting facets of this actual polar yield the roof planes. Their vertical coefficients are proved positive. The development derives projection injectivity, exact intersections of projected triangles, and coverage of the base triangle; none is an additional input assumption. Corresponding root labels give caps with the same labelled triangles and corner embedding. The return from polarity is an explicit admissible projectivity together with affine coordinate changes.

### Harmonic drawings and the planar count

For positive edge weights and fixed triangular boundary values, the Dirichlet matrix is invertible. The proof is a finite maximum principle: an extremum at an interior vertex propagates across every positive edge, and connectedness carries it to the boundary. This proves existence, uniqueness, and continuous dependence without assuming a graph embedding theorem.

The geometric part proves the required triangular-boundary case of the convex-combination embedding argument used by Floater and Tutte. The source is a genuine geometric triangulation. The strict maximum principle puts every nonboundary image vertex inside the outer triangle. Planar separation proves that adjacent image triangles lie on opposite sides of their common edge; starting at a boundary face, connectedness of the face graph then gives nondegeneracy of every face. The supporting planar separation results have Lean proofs in the retained TauCeti dependency.

Global nonoverlap uses horizontal lines avoiding the finitely many image vertex heights. Such a line cuts each triangle it meets in an interval. At a nonboundary right endpoint there is a unique next triangle, whose interval continues strictly farther right. Finiteness forces the walk to end at the outer boundary. The terminal triangle is unique, and the predecessor at every stage is unique. Hence distinct cut intervals have disjoint interiors. Choosing a generic horizontal line through any proposed open overlap proves disjointness of all image-face interiors.

An interior vertex's image star contains a neighborhood of its image. To prove this, take a small punctured ball avoiding the opposite edges of all incident triangles. Opposite-side adjacency makes the image star open there; its finite closed-triangle cover makes it closed. Connectedness of the punctured planar ball supplies the whole neighborhood. This construction uses neither vertex injectivity nor global nonoverlap. Combining it with the already proved nonoverlap gives exact vertex--face incidence and then injectivity. A separate edge argument gives exact intersections of closed image triangles, including their boundaries. Finally, their union is relatively open and closed in the outer triangle's connected interior; taking its closure supplies the outer boundary as well.

The resulting declaration `Planar.TriangularDisk.harmonicTriangularDisk` therefore constructs an actual triangular disk with precisely the original labelled faces and corners. Each of its geometric fields has been derived from the harmonic equations and the source triangulation.

An elementary count avoids a new homology development. Choose $\ell(z)=\operatorname{Re}z+a\operatorname{Im}z$, with $0<a<1$, avoiding the finitely many slopes that identify two vertex heights. Every triangle has one middle-height vertex. At an interior vertex, the two level rays each enter exactly one incident triangle. At the boundary, only the middle corner has an inward level ray. A finite closed-cover argument supplies existence, and exact simplex intersections supply uniqueness. If $I$ is the number of interior vertices and $F$ the number of triangles, this gives

$$
F=2I+1.
$$

Counting edge--face incidences gives $3F=2E+3$, where $E$ is the number of interior edges, and hence $E=3I$. The face count is the declaration `Planar.TriangularDisk.elementary_face_count`.

### A proved Maxwell lifting map

There are three finite real vector spaces: interior heights $H\cong\mathbb R^I$, interior edge weights $W\cong\mathbb R^E$, and interior equilibrium forces $F_0\cong\mathbb R^{2I}$. Affine interpolation on each triangle defines a linear map $A:H\to W$: the jump of the two adjacent face gradients is a scalar multiple of the quarter-turn of their common edge. The equilibrium map is

$$
(B\omega)_v=\sum_{u\sim v}\omega_{vu}(p_u-p_v).
$$

Oriented face contributions cancel at each interior vertex, proving $BA=0$. If $Ah=0$, all adjacent face gradients agree, so the height is a single affine function; its three zero boundary values make it zero. Thus $A$ is injective.

The dual obstruction to surjectivity of $B$ is an infinitesimal motion preserving all edge lengths and vanishing on the boundary. If two vertices of a nondegenerate triangle have zero velocity, its two remaining edge constraints force the third velocity to have zero dot product with two independent directions. That velocity is zero. Starting at a boundary edge, this argument propagates across shared edges through the connected face graph. The motion is therefore zero, so $B$ is surjective. Together with $E=3I$, these results prove

$$
\operatorname{im}A=\ker B.
$$

This is the lifting theorem used by the proof; it is derived from the concrete maps and the dimension count, rather than supplied as an axiom. The sign convention has a concrete geometric check. Orient an interior edge $ab$ so that the third vertex $v$ of its left face lies on the positive side. If $L$ is the affine plane of the right face, then

$$
L(p_v)-h_v=(Ah)_{ab}\det(p_b-p_a,p_v-p_a).
$$

Thus positive stress gives a strictly concave local fold, and the strict supporting inequality of any existing cap gives positive extracted stress.

Global support follows by a finite descent argument. For a vertex outside a triangle, one edge separates the vertex from that triangle's third vertex. The neighboring face across that edge has a strictly smaller plane value at the chosen vertex. Consequently, a face minimizing that value must contain the vertex, where the value is its prescribed height. Strict descent also excludes equality at every nonincident face. Finally, a face containing an interior vertex misses at least one boundary corner. Its plane has nonnegative values at all three corners and a positive value at a missing corner. The strictly positive barycentric coordinates of the interior vertex then give a positive height there. These arguments supply all the global strict-cap inequalities.

Extract positive equilibrium weights from the endpoint caps and interpolate them linearly. The Dirichlet solution supplies the horizontal coordinates at every parameter, and the embedding theorem supplies their actual triangulation. A canonical height solution is

$$
h_t=(A_t^{\mathsf T}A_t)^{-1}A_t^{\mathsf T}\omega_t.
$$

Injectivity of $A_t$ proves that its Gram matrix is invertible. The coefficient formulas, nondegeneracy of all triangles, and locally constant incidence orientations prove continuity. Uniqueness recovers the exact endpoint heights. Polarizing these caps about a proved interior center gives a path of simple polytopes of the prescribed labelled type. Theorem 1 then gives the unrestricted PN relation in Corollary 2.

The final interface also accepts two presentations with different facet label types and an arbitrary isomorphism of their actual exposed-face orders. The proved characterization of facets as the nonempty maximal proper faces recovers the label bijection. Relabelling along this bijection leaves the target carrier literally unchanged and transports a PN word while preserving its projective and normal counts. Thus the geometric corollary does not require the user to supply prealigned facet labels.

The cap-path statement proved here is continuity. The stronger assertion in the manuscript's auxiliary Lemma 5 that all cap vertex coordinates are rational functions with no poles is outside this verification. The proved continuous path supplies the full conclusion of Corollary 2.

## The sharp cube bound

The upper-bound argument develops the polar-diagonal construction of Adiprasito, Kalmanovich, and Nevo [akn]. It works on the actual polar crosspolytope. Choose a point on each opposite-vertex diagonal so that the first site is a strictly positive convex average of the others. A projective move and a normal move merge one more diagonal into the common intersection. After $d-2$ such pairs, all diagonals meet at one interior point. A final projectivity recenters there. Opposite polar vertices then lie on opposite rays of a basis, so the primal is a parallelotope. Its affine map to the standard cube is absorbed into the final projectivity, and the initial translation into the first. The case $d=2$ is treated with its single projective move.

The lower-bound argument tracks a labelled vertex through an arbitrary word. In a rooted affine frame, write the inequalities as $x_i\ge0,\ Ax\le\mathbf1$. A normal move multiplies $A$ by a positive diagonal matrix. A projective move changes it by a rank-one update after an actual change of rooted frame. After $r$ projective moves,

$$
A_{\mathrm{final}}=D A_{\mathrm{initial}}+R,
\qquad D>0\text{ diagonal},\quad\operatorname{rank}R\le r.
$$

For the cyclic family, $A=I+\varepsilon S$. Subtracting any diagonal matrix leaves a $(d-1)\times(d-1)$ minor with determinant $\varepsilon^{d-1}$. It follows that at least $d-1$ projective moves are necessary. Consecutive blocks of either type can be compressed, so an alternating word still requires at least $d-2$ normal moves. The verified lower bound is stated for arbitrary target labellings of the geometric standard cube. It is therefore a bound on the intended geometric distance, not just on a particular labelling of the target presentation.

For the source, `CubeUpper.every_cube_exact_word_of_faceOrderIso` exposes the corresponding interface for an arbitrary facet-label type and an actual face-order isomorphism to the cube. It constructs the facet alignment, applies the upper-bound word, and transports every intermediate presentation back to the original labels. The source carrier is exactly the input carrier, the target is the standard cube, and the counts remain $n$ and $n-1$ in dimension $n+1$. The declarations `CubeUpper.cube_dimension_parameter_iff` and `CubeUpper.cube_move_counts_reindex` prove that the parameter range is exactly $d\ge2$ and that the corresponding counts are $d-1$, $d-2$, and $2d-3$.

## References

[paper] C. Folkerts, Normal–projective equivalence and the exact cube bound, supplied manuscript, version 9.

[akn] K. Adiprasito, D. Kalmanovich, and E. Nevo, On the realization space of the cube, J. Eur. Math. Soc. 26 (2024), 261–273. doi:10.4171/JEMS/1361.

[floater] M. S. Floater, One-to-one piecewise linear mappings over triangulations, Math. Comp. 72 (2003), 685–696. doi:10.1090/S0025-5718-02-01466-7.

[tutte] W. T. Tutte, How to draw a graph, Proc. London Math. Soc. (3) 13 (1963), 743–767. doi:10.1112/plms/s3-13.1.743.

[ziegler] G. M. Ziegler, Lectures on Polytopes, Graduate Texts in Mathematics 152, Springer, 1995.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

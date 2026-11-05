# A counterexample to Smilansky’s conjecture

## The mathematical statement

The Lean project accompanying this note verifies Theorem 1, Proposition 5, and the general summand criterion of Lemma 2 in *A Counterexample to Smilansky’s Conjecture* (the original source package used the title *An indecomposable cubical four-polytope*), together with Lemma 3(i)–(ii). The main witness is the ordinary convex hull of 144 rational points in real four-dimensional Euclidean space. The formalization supplies a second proof of the theorem, organized around exact certificates for that final polytope. The paper obtains its witness by joining six copies of a 32-vertex block. The formal proof can check the resulting coordinates directly, so its correctness does not depend on the implementation of that construction.

**The main statement.** There is a full-dimensional rational convex polytope $K\subset\mathbb R^4$ with

$$
f(K)=(144,404,390,130)
$$

whose facets are combinatorial three-cubes. Every parallel redrawing of its edge graph has the form

$$
h_v=\alpha p_v+b
$$

for one $\alpha\in\mathbb R$ and one $b\in\mathbb R^4$. Moreover, if $A,B\subset\mathbb R^4$ are convex and $K=A+B$, then there are $r\in[0,1]$ and $b\in\mathbb R^4$ such that

$$
A=rK+b,\qquad B=(1-r)K-b.
$$

The summand statement includes arbitrary convex sets. In particular, it does not assume in advance that $A$ and $B$ have finitely many extreme points. Their nonemptiness, boundedness, and eventual polytopal form follow from the hypotheses and conclusion. A parallel redrawing is an assignment with $h_v-h_u=\lambda_{uv}(p_v-p_u)$ on every edge $uv$. The scalars $\lambda_{uv}$ may be any real numbers, including negative numbers and zero.

The principal Lean declaration is `CubicalIndecomposability.theorem_one`, in `source/verification_bundle.lean` (the topic-level version is `reading/cubical_indecomposability/main.lean`). Its hypotheses contain no incidence, rank, rigidity, or convexity certificate supplied by the reader. The explicit witness and every certificate used to establish its properties are proved inside the project.

A fixed finite witness proves the full theorem here because the theorem is existential. The formalization goes beyond checking a finite graph or a matrix over a finite field: it identifies all geometric faces of an actual real convex hull, quantifies over every real parallel redrawing, and quantifies over every convex Minkowski decomposition. These are the infinite mathematical assertions needed for Theorem 1.

## The underlying convex geometry

The ambient space is Mathlib’s `EuclideanSpace ℝ (Fin 4)`. A convex polytope consists of a finite, nonempty vertex set together with a proof that those vertices are exactly the extreme points of its convex hull. The underlying set is defined by `convexHull`; it is not defined by the proposed incidence table.

A nonempty face is an exposed face in the ordinary sense. Thus it is the set of maximizers of a continuous linear functional on the polytope. Its dimension is the real dimension of its affine direction space, represented by Mathlib’s `vectorSpan` and `Module.finrank`. The face numbers count these actual geometric faces. The empty face can be adjoined as a least element, and the project explicitly extends the cube isomorphisms to the resulting complete face lattices.

The coordinate data use primitive homogeneous integer vectors

$$
q_v=(q_{v,0},q_{v,1},q_{v,2},q_{v,3},q_{v,4}),
       \qquad q_{v,4}>0,
$$

and set

$$
p_v=\frac{1}{q_{v,4}}
                   (q_{v,0},q_{v,1},q_{v,2},q_{v,3}).
$$

There are 130 integral supporting forms. After choosing a common sign convention, their slacks $s_f$ satisfy

$$
s_f(p_v)\geq0,\qquad
 s_f(p_v)=0\ \Longleftrightarrow\ v\text{ is incident with }f.
$$

Every one of the $130\cdot144=18\,720$ evaluations is checked by Lean’s kernel. Positive denominators reduce the checks to exact integer arithmetic.

These evaluations also prove that the listed points are genuine extreme vertices. For two distinct labels $v,w$, one of the supporting forms vanishes at $p_v$ and is strictly positive at $p_w$. Summing the forms that vanish at $p_v$ gives a functional with a strict minimum at $p_v$ among the listed points. The same strict exposed point property holds in their convex hull. This proves both the vertex assertion and injectivity of the labeling; neither is taken as an assumption.

The same idea realizes all the proposed lower-dimensional faces. For a nonempty intersection of selected facet vertex sets, sum their nonnegative slacks. Its zero set in $K$ is exactly the desired exposed face. A convex combination has zero slack precisely when every vertex receiving positive weight has zero slack. Consequently, the zero set is the convex hull of exactly the listed vertex labels.

## Why the face list is complete

The certificate lists 1,069 nonempty faces, including $K$ itself: 144 vertices, 404 edges, 390 two-faces, 130 facets, and one whole polytope. At this point the supporting forms prove that every listed object is a face. Two further arguments establish their dimensions and prove that no geometric face has been omitted.

For the dimensions, each listed face occurs at the appropriate position in a flag of five strictly nested exposed faces,

$$
F_0\subsetneq F_1\subsetneq F_2\subsetneq F_3
                   \subsetneq F_4=K.
$$

Strictness follows from the corresponding strict containments of vertex sets. The dimension of a nonempty exposed face increases strictly under proper containment, while every subset of the ambient space has affine dimension at most four. There is therefore no room for a gap: the five dimensions are exactly $0,1,2,3,4$. This simultaneously proves that $K$ is full-dimensional and that every assigned face dimension is correct. The argument avoids large determinant calculations for individual faces.

Completeness uses two general theorems about actual convex polytopes of dimension at least two. Their facet adjacency graph is connected, and each ridge belongs to exactly two facets. Both theorems are supplied with proofs in the project’s geometric dependencies. They are not hypotheses of the final theorem.

Suppose a nonempty family of genuine facets contains, for each ridge of each member, a second distinct facet through that ridge. The ridge theorem says that these are the only two incident facets. The family is therefore closed under every step in the actual facet adjacency graph. Connectedness forces it to contain every facet.

Apply this criterion recursively inside each listed face. The finite data check all 3,510 intervals in which the listed dimensions differ by two, supplying both intermediate faces. Induction on dimension first shows that the listed ridges inside a listed facet are exhaustive, then uses the preceding adjacency argument to show that the listed facets are exhaustive. Every proper face lies in a facet, so the induction also accounts for every lower-dimensional face. In dimensions zero and one, every proper nonempty face is an already verified extreme vertex.

This distinction is essential: an incidence table with the desired counts would not by itself establish the theorem. The induction proves that the table is in bijection with all nonempty exposed faces of the real convex hull. Counting the entries now gives the actual $f$-vector.

To verify that a facet is a combinatorial cube, label its eight vertices by $\{0,1\}^3$. A nonempty coordinate face is specified by a word in

$$
\{0,1,*\}^3.
$$

There are 27 such words; an asterisk leaves that coordinate free. The certificate identifies each word with the corresponding actual face of the facet and checks inclusions in both directions. This gives an order isomorphism with the nonempty face poset of the standard three-cube. Adjoining the empty face gives an isomorphism of the complete 28-element face lattices. Thus the proof establishes the usual combinatorial meaning of “cube”, without requiring the geometric facet to be an affine parallelepiped.

## The rigidity certificate

For a listed edge $uv$, let $d_{uv}\in\mathbb Z^4$ be a primitive integer vector parallel to $p_v-p_u$, and choose a coordinate $k$ with $d_{uv,k}\ne0$. Parallelism implies the three linear equations

$$
d_{uv,k}(h_{v,i}-h_{u,i})-
 d_{uv,i}(h_{v,k}-h_{u,k})=0
                    \qquad(i\ne k).
$$

The integer directions are checked against the homogeneous coordinates. The geometric part of the proof establishes that each of the 404 listed edges is an actual one-dimensional exposed face of $K$. The converse enumeration is also proved: every actual edge has one of the listed endpoint pairs, with either orientation. Every geometric parallel redrawing therefore satisfies these equations.

The proof solves the equations through 60 small elimination steps. The largest step involves 25 unknown coordinates. The steps follow the geometry behind the paper’s propagation arguments: a vertex with two known neighbors, an affinely independent four-cycle with known values, or a four-cycle constrained by two skew spokes. Their algebraic certificates allow Lean to check the linear consequence directly, without importing a separate numerical rank computation.

The eight vertices with labels

$$
1,3,5,7,9,11,13,15
$$

form the shared unit cube. Its redrawing is described by four translation coordinates and three coordinate scales. In the source, the seven initial scalar coordinates are

$$
h_{1,0},\ h_{1,1},\ h_{1,2},\ h_{1,3},\
 h_{3,0},\ h_{5,1},\ h_{9,2}.
$$

There are 576 scalar vertex coordinates in total. The generated Lean proofs express the other 569 coordinates as exact linear combinations of these seven. Each identity is proved from original edge equations and previously established identities. The coefficients were found by a small rational-arithmetic script, but the script’s output is not accepted on trust: `linear_combination` constructs an ordinary proof term for every identity.

Put

$$
s_x=h_{3,0}-h_{1,0},\qquad
 s_y=h_{5,1}-h_{1,1},\qquad
 s_z=h_{9,2}-h_{1,2}.
$$

Two remaining edge equations reduce, after removing common factors, to

$$
\begin{align*}
 115s_x-918s_y+803s_z&=0,\\
 -803s_x-115s_y+918s_z&=0.
\end{align*}
$$

They come from the edges labeled 50 and 243 in the explicit edge list. Both vanish on the uniform scaling line. Writing $u=s_y-s_x$ and $v=s_z-s_x$ leaves

$$
-918u+803v=0,\qquad -115u+918v=0.
$$

The determinant has absolute value $918^2-803\cdot115=750379$, so $u=v=0$. Substitution into the 569 coordinate formulas gives, for every vertex,

$$
h_v=h_1+(h_{3,0}-h_{1,0})p_v.
$$

This is the entire rigidity assertion. It applies to arbitrary real assignments, and not only to rational or numerically sampled ones. The explicit vertex-indexed formula appears in `parallel_vertex_assignment_formula`. The theorem `parallel_vertex_assignment_iff` states the exact equivalence between parallelism on the actual edges and this homothetic form. The ambient-map formulation is `parallel_redrawings_homothetic`.

## The quotient deformation space

The project also formalizes the precise notation of Section 2 of the paper. For a polytope $P\subset\mathbb R^d$, let $\mathcal R(P)$ be the linear subspace of assignments to its actual extreme vertices satisfying the parallelism equations on all actual edges. Constant assignments form a $d$-dimensional translation subspace $\mathcal T(P)$. Define

$$
\mathcal D(P)=\mathcal R(P)/\mathcal T(P),\qquad
       D(P)=\dim_{\mathbb R}\mathcal D(P).
$$

These are actual Mathlib submodules and quotient modules. In Lean their names are `redrawingSpace`, `translationSpace`, `DeformationSpace`, and `deformationDimension`, in the namespace `Papers.Polytopes`.

For a polytope with two distinct vertices, the identity assignment has a nonzero class in $\mathcal D(P)$. The project proves that $D(P)=1$ is equivalent to every redrawing being a homothety plus a translation. Equality of quotient classes is unpacked as a difference belonging to the translation subspace, so this equivalence retains all quantifiers and both implications. Applied to the explicit witness, it gives

$$
D(K)=1,\qquad \dim\mathcal R(K)=5.
$$

The declarations are `deformation_dimension` and `redrawing_dimension`.

The two elementary rules of Lemma 3 are also proved in their full generality. An affinely independent four-cycle in any real module has only homothetic redrawings modulo translations (`lemma_three_one`). In every ambient dimension, a redrawing vanishing at two distinct actual neighbors vanishes at their common vertex (`redrawing_zero_of_two_neighbors`, in `Papers.Polytopes`).

For an actual face $J$ of $P$, every vertex of $J$ is a vertex of $P$, and every edge of $J$ is an edge of $P$. Restricting vertex assignments therefore gives a linear map $\mathcal R(P)\to\mathcal R(J)$. It sends translations to translations and induces

$$
\rho_J:\mathcal D(P)\longrightarrow\mathcal D(J).
$$

The definition `FaceDetermines` means exactly that $\rho_J$ is injective. A general lemma proves that it suffices for a redrawing vanishing on $J$ to vanish everywhere: subtract the constant value on $J$ from a representative of a class in the kernel. This is the paper’s stated equivalence, used explicitly in the block verification.

## From redrawings to Minkowski summands

The final bridge proves Lemma 2 with its literal hypothesis $D(P)=1$, in every ambient dimension and for arbitrary convex summands. The quotient-space equivalence reduces it to the following general redrawing-to-summand argument. Suppose $K=A+B$. For every vertex $p_v$, choose $a_v\in A$ and $b_v\in B$ with $p_v=a_v+b_v$. An exposing functional for an edge forces the two cross-sums $a_u+b_v$ and $a_v+b_u$ onto the same edge. Consequently,

$$
a_v-a_u=\lambda_{uv}(p_v-p_u)
$$

for a real scalar $\lambda_{uv}$. The verified rigidity theorem gives $a_v=rp_v+b$ for all vertices.

The scalar belongs to $[0,1]$. One can see this using an exposing functional at a vertex and a second, distinct vertex: both cross-sums belong to $K$, so their functional values cannot exceed the maximum on $K$. Applied to the homothetic formula, the two inequalities give $r\geq0$ and $1-r\geq0$.

It remains to prove that the selected components generate the whole summands. Convexity immediately gives $\operatorname{conv}\{a_v\}\subseteq A$. For the reverse inclusion, let $\ell$ be any linear functional and choose a vertex $p_v$ maximizing $\ell$ on $K$. For every $a\in A$, the point $a+b_v$ lies in $K$, hence

$$
\ell(a)\leq\ell(p_v)-\ell(b_v)=\ell(a_v).
$$

Separation from the finite convex hull $\operatorname{conv}\{a_v\}$ now shows that $A\subseteq\operatorname{conv}\{a_v\}$. Therefore

$$
A=\operatorname{conv}\{a_v\}=rK+b.
$$

The same argument gives $B=(1-r)K-b$. No assertion that an arbitrary summand is already polytopal is needed; that fact is a consequence of the proof. The general theorem is `lemma_two`; its specialization to the explicit witness is `minkowski_summands`. The one-point case is handled directly in the general argument, so no unstated nondegeneracy assumption is introduced.

## The auxiliary block: Proposition 5

Proposition 5 is verified independently and in full. Its witness is the paper’s 32-vertex block after the normalization of Section 4.4. The formal proof starts from the resulting rational coordinates and checks them directly. In this affine chart the two interface facets are already affinely equivalent, and the disjoint facet is already a parallelepiped. These stronger properties provide the two required projective conclusions using the identity projectivity.

The geometry follows the same complete argument as for $K$: strict exposing forms identify exactly 32 extreme vertices; support intersections realize 209 nonempty faces; strict flags determine their dimensions; and ridge adjacency proves completeness. This gives

$$
f(P)=(32,80,72,24).
$$

Actual face-poset isomorphisms establish that all 24 facets are cubes. The three distinguished facets and their common face have vertex sets

$$
\begin{align*}
 F&:\quad\{24,25,26,27,28,29,30,31\},\\
 H&:\quad\{8,10,12,14,24,26,28,30\},\\
 G&:\quad\{1,3,5,7,9,11,13,15\},\\
 Q&:\quad\{24,26,28,30\}.
\end{align*}
$$

The formalization proves $F\cap H=Q$, $\dim Q=2$, and that $Q$ has exactly four extreme vertices. It also proves $G\cap(F\cup H)=\varnothing$ for the entire geometric sets. Disjoint vertex lists alone are not used as a substitute: if two actual faces intersect, their intersection is a nonempty face and hence contains a vertex of the original polytope.

The deformation claims use exact real linear identities from the 80 actual edge directions. They express all 128 scalar vertex values in terms of seven values on $G$. A second set of identities recovers those seven values from seven evaluations on $H$. Thus a redrawing vanishing on either $G$ or $H$ vanishes everywhere. The quotient-space criterion from the preceding section proves that both facets determine $P$.

For $F$, all restricted values are expressed using the six scalar values

$$
h_{24,0},h_{24,1},h_{24,2},h_{24,3},h_{25,0},h_{28,1}.
$$

Subtract the translation $h_{24}$. Only the two differences

$$
h_{25,0}-h_{24,0},\qquad h_{28,1}-h_{24,1}
$$

remain. The resulting map from the image of $\rho_F$ to $\mathbb R^2$ is proved injective; finite-dimensional linear algebra gives $\dim\operatorname{im}\rho_F\leq2$. This proves the rank of the actual quotient restriction map, rather than merely a rank estimate for a matrix suggested by the facet labels.

The interface map has a short exact description. Put

$$
d=(-11,11,-15,51),\qquad c=\frac{18851}{313170},
$$

$$
\ell(x)=-\frac{x_0}{165}-\frac{4468x_2}{156585}
                         -\frac{77459x_3}{7985835},\qquad
 \phi(x)=x+(\ell(x)+c)d.
$$

Lean verifies $\ell(d)=0$, so $\phi^{-1}(x)=x-(\ell(x)+c)d$. Exact rational calculations show that $\phi$ fixes the four vertices of $Q$ and maps

$$
25\mapsto8,\quad27\mapsto10,\quad
                      29\mapsto12,\quad31\mapsto14.
$$

An affine map preserves convex hulls, giving $\phi(F)=H$. Agreement with the identity on the vertices of $Q$ extends to their affine span, proving pointwise fixation of the whole quadrilateral. Finally, $G$ is the unit cube in the hyperplane $x_3=0$. The affine embedding from $[-1,1]^3$ is

$$
(y_0,y_1,y_2)\longmapsto
                  \left(\frac{y_0+1}{2},\frac{y_1+1}{2},
                        \frac{y_2+1}{2},0\right).
$$

Its injectivity and equality of its image with the entire facet are proved. In the projective definitions an invertible homogeneous linear map represents a projectivity, and positivity refers to its actual last-coordinate denominator. The identity witnesses therefore have precisely the usual projective meaning.

The complete statement is `Block.proposition_five`. Its hypotheses contain none of the support, incidence, rank, or reconstruction certificates used in its proof.

## Source organisation

The compiled proof consists of four modules under `source/`. The convex geometry and redrawing criterion are in `foundation_bundle.lean`; `incidence_bundle.lean` checks the exact face data; `verification_bundle.lean` establishes the witness and its rigidity; and `block_verification_bundle.lean` proves the auxiliary block statements. The public import is `cubical_indecomposability`.

The smaller files under `reading/` expose the original topic divisions. They are a reading aid, not a second verification target. The default build compiles the assembled proof and `source/verification/complete.lean`. That check inspects all four bundles, rejects project axioms and unsafe or partial declarations, recomputes the principal dependency graph, and replays every local definition, theorem and opaque body through Lean's kernel under a fresh name. Structural declarations remain covered by the source compiler. Generated reports stay under `.lake/reports/`.

# Formalisation

The formalisation proves the principal results of *Small nonrational four-polytopes* for actual finite convex polytopes. The principal interface is `source/papers/small_nonrational.lean`. Its proofs assemble the geometric, algebraic and finite-classification arguments explained below.

Theorem 1 supplies a seventeen-vertex four-polytope whose realization fields are exactly the real subfields containing √5. Theorem 2 establishes rational realizability for every four-polytope with at most ten vertices. Theorem 3 treats simple-vertex deletion in arbitrary dimension. Together these give an attained minimum vertex count N satisfying 11 ≤ N ≤ 17. The density assertions retain their stronger, typewise quantifiers; they are distinguished throughout from rational existence.

## Geometric meaning and quantifier order

A `ConvexPolytope` $d$ contains a nonempty finite subset of $\mathbb R^d$ and a proof that its listed points are exactly the extreme points of their convex hull. Its dimension is the dimension of its affine hull. Faces are actual nonempty exposed faces, with inclusion as their order. Consequently the objects in the main theorems carry no certificate asserting rationality or membership in a finite catalogue.

Combinatorial equivalence is an order isomorphism of these face posets. The theorem `combinatoriallyEquivalent_iff_complete_face_iso` proves its equivalence with the complete face-lattice formulation by adjoining the empty face. Vertex labels transport along the induced bijection on zero-dimensional faces. This transport is used whenever a statement is to hold for an arbitrary realization of the same combinatorial type.

For a real subfield $K$, `RealizableOver` $P$ $K$ means that there is a combinatorially equivalent polytope whose actual vertex coordinates lie in $K$. The rational version has the same geometric content. Field membership is therefore a property of an ordinary realization, not a syntactic property of a coordinate table or a presumed description of its facets.

The density definition has two universal quantifiers. For every realization $Q$ combinatorially equivalent to $P$, and for every $\varepsilon>0$, it supplies a rational realization $R$ and a face-order isomorphism matching each vertex of $Q$ to a vertex of $R$ within $\varepsilon$. The names `RationallyApproximable` and `RationallyDense` distinguish the local assertion at a specified realization from the assertion for its whole type. The proofs control the individual labelled vertices, so they do not obtain density merely by changing labels or projective coordinates.

This distinction matters especially in Proposition 8(iii). Its hypothesis is that *some* equivalent realization $Q$ admits the row bound. Its conclusion is approximation at *every* equivalent realization, including ones where the ranks of polygon-relation spaces change. The formal statement retains this order of quantification. The section on Proposition 8 below explains why a local rationalisation argument alone would not discharge it.

The finite interfaces also record equalities of complete face families. `RealizesBoundary` identifies every facet and every polygonal face of an actual labelled polytope with the finite boundary. An `Encoding` identifies the vertex, edge and polygon families of every facet. A list of some supporting faces is sufficient in the seventeen-vertex obstruction, where only those faces are used; a complete boundary equality is required in the exhaustive classification and reconstruction arguments.

These definitions are connected to Euclidean topology, matrix rank, determinants, affine spans and convex hulls by proved lemmas. The machine readable dependency graph follows those lemmas through the project to the pinned Lean and Mathlib environment. The definition review checks the connection to the paper independently of compilation.

## The seventeen-vertex witness and its field obstruction

Theorem 1 has two distinct proof obligations. One must construct the polytope and verify its relevant faces; one must then show that every realization of the same face lattice forces the quadratic field. Both are proved in `Consolidated.Seventeen`.

The witness uses seventeen exact homogeneous points with coordinates in $\mathbb Z[\phi]$, where $\phi=(1+\sqrt5)/2$. A positive affine chart gives ordinary real vertices. Exact supporting forms separate the labels and prove that all seventeen listed points are distinct extreme points. Four independent affine directions prove full dimension. The selected plane faces and facet faces used by the obstruction are proved to have their asserted dimensions and zero sets.

This is a fixed exact witness for the paper’s existential theorem. The formalisation does not require a claim about every value of the small parameter in the paper’s construction. The fixed witness proves the same seventeen-vertex theorem, with the same quantification over all real subfields. Its coordinates already belong to every subfield containing $\sqrt5$, which gives one direction of the field equivalence.

For the other direction, start with an arbitrary realization over $K$ of the ordinary face lattice. Its face-order isomorphism transports the selected faces and vertices. Geometric dimension becomes homogeneous linear rank over $K$, and a vertex outside a supporting face is proved to remain outside its homogeneous span. These facts justify all intersections and changes of projective frame in the incidence reconstruction.

The reconstruction supplies the configuration in Lemma 5. In homogeneous coordinates, the nine required four-point dependencies are
$$
1238,\quad1245,\quad1267,\quad1346,\quad1578,\quad
2347,\quad2356,\quad3458,\quad4678.
$$
Every three of the seven original labels are independent, the initial four form a frame, and the separately reconstructed point has the required distinction from point 2. The field-generic theorem `Papers.Nonrational.projective_golden_root` derives
$$
\tau^2+\tau-1=0.
$$
For a real subfield, such a root belongs to $K$ exactly when $\sqrt5$ does; indeed $(2\tau+1)^2=5$. The proof handles either root and does not assume that the reconstructed configuration chooses the positive one.

The exported `seventeen_vertex_field_theorem` therefore concerns every realization of the face lattice. The separate theorem `sqrt_five_notMem_rationalSubfield` proves the irrationality step from the primality of five. This gives an actual nonrational four-polytope, rather than merely a displayed realization with irrational coordinates.

The reconstruction uses only the supporting faces needed for the obstruction. No unproved assertion that a supplied list is the entire facet list enters the argument. Each face that is used has its own checked geometric witness and rank proof.

## Simple-vertex deletion, fields and density

Theorem 3 quantifies over every natural dimension $d$, every full $d$-polytope $P$, and every simple vertex $v$, assuming $|\operatorname{vert}P|>d+1$. Simplicity means degree $d$ in the actual edge graph. The deleted polytope is literally
$$
P'=\operatorname{conv}\bigl(\operatorname{vert}P\setminus\{v\}\bigr).
$$
The proof constructs the nonemptiness needed to define it and verifies that all remaining listed points are still extreme vertices.

At a simple vertex the edge directions form a basis. In its coordinates, all other vertices lie in the nonnegative orthant. The neighbours lie on the coordinate-sum-one hyperplane, while all other vertices have coordinate sum strictly greater than one. The vertex-count hypothesis provides such an additional point, proving that deletion preserves full dimension. The corner cut exposes the simplex on the neighbours and gives a complete description of the remaining faces.

That face description proves the combinatorial assertion. Any face-order isomorphism from $P$ to another realization $Q$ induces an isomorphism between their deletions at corresponding vertices. The formal conclusion quantifies over this arbitrary isomorphism; the deleted type does not depend on a chosen geometric model.

Restoration must then work over the original real subfield and near a specified realization. Supporting forms for the exposed simplex facet and its neighbouring facets encode the required zero and strict positive values of the restored point. A positive projective chart makes the construction available for every realization of the deleted type. The linear solves and changes of chart preserve the subfield $K$. Thus
$$
\operatorname{Fields}(P)=\operatorname{Fields}(P'),
$$
where each side is the full set of real subfields admitting a realization. There is no rationality or generic-position assumption on the starting polytope.

For density, the prescribed zero parameters remain exactly zero and the positive parameters vary continuously. Nonzero minors and strict supporting inequalities persist in a small neighbourhood. Rational approximation of the core and of the free parameters then gives a rational restoration near the specified original vertices. The converse restores a realization, approximates it, deletes, and returns through rational approximations of the chart. The result is the two-way statement
$$
P\text{ is rationally dense}
             \quad\Longleftrightarrow\quad
             P'\text{ is rationally dense}.
$$

The geometric, field and topological parts are assembled in `Consolidated.DeletionGeometry`, `Consolidated.DeletionFields`, and `Consolidated.DeletionDensity`. The endpoint `Papers.Polytopes.paper_simple_vertex_deletion` contains all four conclusions. Corollary 4 follows by deleting a simple vertex from an eleven-vertex four-polytope, applying Theorem 2 to the resulting ten-vertex polytope, and using equality of realization fields.

## Small configurations and the exceptional rank-four matroid

Lemma 11 applies to every spanning real $8\times4$ matrix, allowing zero rows, repeated rows and disconnected represented matroids. It asserts rational approximation with the signs of all ordered maximal minors preserved exactly when the basis family is not isomorphic to the golden family. That exceptional family has no rational representation.

The paper writes points as columns of $[I_4\mid D(\tau)]$; the formalisation uses their transposed rows. The block is exactly
$$
D(\tau)=\begin{pmatrix}
 1&1&0&1\\ 1&0&1&1\\ 0&1&\tau&\tau+1\\1&1&\tau&0
 \end{pmatrix},\qquad \tau^2+\tau-1=0.
$$
The theorem `lemma11_nonbases` proves that its dependent four-subsets are exactly the nine sets displayed in Section 3, for both roots. Separate supporting lemmas prove independence of every triple and spanning by every five labels. Thus the exception is identified by the actual matrix, not just by an internal catalogue number.

The finite classification covers 832 isomorphism classes of loopless rank-four matroids on eight elements. The paper initially restricts to 731 connected classes; retaining the disconnected classes in the formal catalogue avoids a separate component argument. Exhaustiveness follows from checked basis-family constraints and proof certificates for the excluded assignments. It is not assumed from a published enumeration. All 831 nonexceptional classes are discharged by rational-density proofs or proved obstructions to real realization. The chart arguments eliminate all equations in 776 classes, reduce to one residual equation in 20, and derive contradictory normalized equations in the remaining 35.

A chart proof preserves the required vanishing minors by rational parametrisation or variable elimination. Every denominator is proved nonzero on the chart, and exceptional chart points are handled separately. The finitely many nonzero determinants keep their signs in a sufficiently small open neighbourhood. A formal equivalence connects this exact incidence density with the chirotope statement. Zero rows are restored by rational row scaling after replacing them temporarily by repeated nonzero rows; the final theorem has no nonzero-row restriction.

Lemma 10 supplies the lower-rank result on at most eight labels. Its proof classifies the small incidence cores and derives coordinate contradictions for the Fano and MacLane obstructions, then rationally reinserts the remaining points. Intrinsic coordinates retain the ranks of every labelled subset, including configurations of rank below the ambient dimension. No projective Euler or Melchior theorem is imported as an assumption.

Lemma 12 handles the multiaffine step even at singular original zeros. For a rational polynomial $p(x_1,\ldots,x_n,z)$, each $x_i$ has degree at most one, while $z$ has unrestricted degree. At a zero where $p(\,\cdot\,,z)$ is a nonzero polynomial, regular zeros are dense in that fibre; one then solves rationally along a coordinate with nonzero slope. The parameter and all other coordinates may vary rationally in the approximation. Neither smoothness at the original point nor irreducibility is added to the statement.

## Proposition 8 and the global eight-row argument

The closed density module `Papers.DensityTheorems` proves Proposition 8(i) for at most nine vertices and Proposition 8(ii) when there are at most nine nonsimplicial facets or at most nine nonsimple vertices. The latter assertion places no bound on the total number of vertices or facets. Deletion and polar-core restoration transfer density from the small cores to the entire type.

For part (iii), write $W_R$ for the affine relation space of a polygonal face $R$, extended by zero on the other labels. The actual selected-row count is proved to agree with the paper’s equation (4):
$$
\begin{aligned}
 h_F&=\dim\sum_{R\subset F}W_R, & g&=\sum_R(|R|-3),\\
 E&=\sum_F(|F|-4), & c&=g+E-\sum_Fh_F.
\end{aligned}
$$
The theorem `proposition8iii_admitting_rows` assumes the bound $c\le8$ at one realization and proves density near every realization of the type. Appendix A.4 of the accompanying paper gives the complete geometric argument for this transfer.

The rank $h_F$ is combinatorially invariant on facets with at most seven vertices. A change requires at least four nonsimplicial polygons. Since $E\le2c\le16$, a remaining type with at least ten nonsimplicial facets has at most two facets on eight or more vertices. At the realization to be approximated, omit supplementary relation rows only for those facets whose polygon-relation ranks have fallen. The retained matrix still has at most eight rows. Columns outside each omitted facet occupy at most four row positions; if there are two such groups, their possible supports intersect in at most one position.

The relative approximation lemma takes $U\subseteq K\subseteq\mathbb R^p$, $p\le4$. Rational subspaces approaching $K$ preserve all coordinate-intersection dimensions; inside them one can approximate $U$ while preserving its own coordinate-intersection dimensions. After the direct dimension cases, only a plane inside a three-dimensional hyperplane in $\mathbb R^4$ remains. Diagonal rescaling fixes the hyperplane rationally. The closed conditions on the plane are then containments of specified rational lines, or equality with a rational plane. All remaining rank conditions are open. This proves the required rational approximation and allows two column groups to agree on their common coordinate axis.

The ordinary rank-four theorem supplies the rational ambient kernel. In the golden case, the nonzero-entry count and a positive supporting form force repetition of a four-support. At most eight distinct required four-supports remain, so one of the nine exceptional incidences can be omitted. The explicit omitted-incidence charts then supply the needed perturbation, with the outside-column ranks retained.

Finally, the supporting forms of the omitted facets are lifted through constant-rank kernels along with the homogeneous vertex coordinates. All other facets retain full relation bases. The exact zero incidences, nonzero minors and strict supporting inequalities preserve the complete face lattice. `Papers.GlobalEightRelationRowsClosed` discharges the rank-four input with the proved Lemma 11 and exports the global conclusion.

## Why the finite reduction covers actual polytopes

The finite part begins only after the analytic reductions. Actual incidence identities and inequalities bound the remaining facet profiles. A residual ten-vertex polytope has no simple vertex, at least ten nonsimplicial facets, and a selected relation-row count at least nine. Every such polytope is assigned to one of the exhaustive families used by the final coverage theorem.

Three completeness arguments are required. The local classification must cover every actual three-dimensional facet. The candidate universe must contain every permitted placement of that facet on the ambient labels. The boundary search must cover every complete actual boundary in that universe. Each is a proved theorem, and each is used by the next one.

A finite facet cell records its vertices, edges and polygonal ridges. Ten-bit masks encode finite subsets through a proved decoding equivalence. The actual encoding retains the full boundary of a quadrilateral or larger polygon, not just its vertex set. Local template coverage quantifies over all injections of the local vertices. Rooted coverage accounts for the distinguished facet and the permitted ambient renamings. When a family fixes an ambient graph, the actual encoding proves the full induced-edge and nonedge restrictions used in constructing its candidate universe.

The large families are divided into rooted small-facet cases, profiles with facets on six vertices, three families with a facet on seven vertices, and graph-restricted cases. The first profile dispatch covers all 478 rows of its catalogue: 477 rooted rows and the remaining graph row. The dispatch for seven-vertex facets uses 69 pure rows, 34 mixed rows, and eight rows with two facets on six vertices. In the last branch, the proved surplus bound eliminates all but canonical seven-vertex template 13. Every other such template contributes local surplus at least $5/2$, while the total surplus is at most $2$. The theorem `TwoSixNarrowing.case_template_eq_thirteen` proves this implication for the actual realization. All eight square-pyramid counts remain in the finite dispatch. This reduction retains every residual polytope.

A growth state is a selected subfamily of cells. At an open ridge exactly one selected facet is incident. Every complete target extending the state must supply a second incident facet. The checker verifies that every candidate for this second facet is either excluded for a proved local reason or represented by a child state. Exclusions use incompatibility, an already closed ridge, or an exhausted exact facet quota. Child states may be renamed and may subsume smaller certified states; all such maps have proved boundary semantics and decrease the induction index.

Induction on this checked finite graph proves coverage of every complete actual boundary. It does not infer completeness from a search program having terminated. Graph-route normalization is likewise proved for all actual labelings, and the finite graph catalogue and route selection are exhaustive. The construction programs and packed integers supply proposed certificates; the Lean theorems supply their mathematical meaning and check every condition needed by the induction.

A proved quota-monotonicity lemma reuses larger-quota forests for some six-facet profiles. Each row retains its original exact quota. Every leaf is checked anew: it either violates that quota or equals an original certified leaf, as an entire ordered leaf before cell decoding. This shares checked search subtrees without changing the geometric cases.

The formal proof uses these exhaustive growth and graph arguments directly. Completeness of a published simplicial-sphere catalogue is not a premise of the finite reduction.

The final theorem, `CompletedResidualCoverage.complete`, splits the proved geometric partition and combines these classifications into `TenVertexResidualTargetCoverage`. Its hypotheses retain the actual row count needed for the surplus argument. This closes Theorem 2 and Proposition 9 without a coverage premise supplied by the user.

## Terminal configurations, projection and exceptions

The terminal theorem resolves all 4,726 boundary records: 4,664 by projection certificates, twelve by exact rational witnesses, and fifty by impossibility proofs. These are records, not distinct types. Checked equalities and permutations link each entry to the actual labelled boundary.

A projection certificate records an incidence deletion order and a height reconstruction order. The incidence rules of Lemma 6 are justified by actual facial geometry. A point or plane is reinserted through a rational kernel chart with the required constant rank. Linear independence is proved from the facial witnesses; it is not a field of the certificate which asserts an unverified fact about real coordinates.

The height stage records complete facet relation coverage and certified nonzero pivots. A pivot must be absent from the possible support of every later row. If the pivot lies in a selected frame, the certificate includes the replacement-frame condition that proves its coefficient is nonzero. Thus the triangular system can be solved continuously and rationally. Strict supporting inequalities survive, and the final affine chart returns to a realization near the original vertices with precisely the original face lattice.

These results have unrestricted numbers of points and height rows. The whole-type version transports the complete facet and polygon families along any face-order isomorphism. Its theorem `ReconstructionCertificate.rationallyDense` is the general density result. `PaperCertifiedRelabelling` additionally retains the paper’s explicit bound of four vertices for polygons avoiding the chosen centre, so the conclusion of Proposition 9 is its precise projection criterion.

The exceptional branch is also geometric. Exact rational witnesses for the twelve Appendix B types come with supporting-form and rank proofs and an ordinary isomorphism of the full face order. The formal proof uses its own exact coordinate representatives; equality of the complete face type establishes the correspondence with the paper. The symmetric Cayley case supplies rational existence in the same way. Obstruction certificates have their own coordinate or determinant arguments. In particular, a Grassmann–Plücker contradiction is accompanied by a proof that every actual realization supplies the signs to which it applies.

The twelve witnesses are A73 (B.1), A14 (B.2), D0 and D4 (B.3), 85 (B.4), the four-prism and crossed two-prism types 0 and 2 (B.5), 52 and 53 (B.6), 679 (B.7), and 452 (B.8). Their existence proofs suffice for the terminal assembly; the additional local parametrisations in those sections are outside this verified scope.

Three further typewise density results are included in `AppendixProjectionDensity`: the three-prism boundary of B.5 and types 444 and 446 of B.8. Exact boundary identifications connect them to projection terminals 1981, 4331 and 4333, respectively. Each theorem applies to every actual realization of its complete boundary and concludes density throughout that combinatorial type. These density statements do not supply separate existence witnesses.

The argument for type A40 derives an incompatible system from its strict supporting forms, and therefore excludes that boundary as unrealizable. Types 31 and 32 are likewise excluded by proved Gale-space obstructions. For A14 and type 452 the formal proof uses exact rational witnesses with complete facet certificates.

Complete coverage and these terminal alternatives prove Proposition 9. Their rational realizations, together with the analytic small-core cases, prove Theorem 2. Deletion gives Corollary 4; the nonrational witness and Theorem 2 give the vertex bounds.

## Source organisation and verification

`source/papers/` contains the geometric definitions, the principal statements and the final assembly. `source/consolidated/` develops the relation matrices, rational charts, projection and reconstruction arguments. `source/cubical/` supplies the polytope foundations; the seventeen-vertex construction is assembled in `source/consolidated/seventeen.lean`. The remaining named directories retain the corresponding mathematical developments. `source/geometry/` holds the global coverage and transport interfaces; `source/finite/` groups the generated classification checks by family and splits large families into numbered parts.

Filenames use lowercase and underscores. Mathematical namespaces and Lean import identities retain their original names. The build maps these files into an internal module tree under `.lake/`, so every proof is compiled from exactly the source bytes checked in the supplied release. The source index in `verification/` records this correspondence and the expected hashes. No historical build artifacts are imported.

The default build runs the pinned Lean compiler with kernel checking enabled. It checks all 24,679 source modules, the principal and supporting endpoints, and the transitive axiom dependencies of the public and private declarations. A further pass checks every original proof occurrence, including compatible repeated theorem names, and its references into the pinned libraries. The permitted logical axioms are `propext`, `Classical.choice` and `Quot.sound`.

The generated finite data are proposed certificates. Their soundness theorems connect them to arbitrary actual polytopes, and Lean checks the proof terms establishing the required conditions. The literal elaborators and decision helpers construct ordinary kernel-checked terms; no unchecked Boolean answer is used as a mathematical premise. Compiler-generated runtime implementations are kept separate from the safe declarations’ logical dependencies.

Source compilation establishes the formal conclusions. The mathematical correspondence also requires the definitions and quantifiers to express the paper’s claims. Here that correspondence includes genuine extreme vertices, complete face lattices, every real subfield, and approximation near every realization where density is asserted. The central classification is unconditional: a catalogue-completeness premise is not supplied by the reader.

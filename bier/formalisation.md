# Explicit nonpolytopal Bier spheres

A Bier sphere is built from a simplicial complex and its Alexander dual by taking their deleted join. This project constructs explicit Bier spheres that cannot be the boundaries of convex polytopes. Its central obstruction compares an upper bound on the sign rank forced by a hypothetical convex realization with a spectral lower bound for the chosen sign matrix.

## The proof strategy

The argument has four main branches:

**Convex obstruction.** Exposed supporting faces give strict inequalities. An actual simplex facet and an outside vertex give coordinates. The two kinds of Bier facets force opposite coordinate signs. Principal inverse algebra identifies the signs with Schur complements. The padded inverse span theorem then bounds the rank of the actual realizing matrix.

**Spectral lower bound.** Actual matrix-rank factorization and sign-preserving perturbation reduce to general position. A positive Cauchy--Binet determinant expansion attains a minimum on the zero-sum logarithmic-weight hyperplane. Differentiating at the minimum gives equal leverage scores, hence a symmetric idempotent projection with the required diagonal. Cauchy--Schwarz gives the full spectral inequality. This proves the positioning result; it is not an imported assumption.

**Explicit constructions.** Exact finite-field arithmetic proves the twelve-by-twelve Paley matrix identities. Walsh orthogonality is proved for every finite coordinate set. Kronecker products and exact order-preserving enumerations produce the paper's 147456-by-145162 sign matrix. The all-sign-pattern construction is proved for arbitrary finite row types.

**Geometry of the variants.** The Bier sphere theorem is proved using the actual coned realization and a geometric link theorem. The isolated-label change is proved to be exactly a stellar facet subdivision. Convex coordinate inequalities prove that deleting its new vertex reverses that subdivision and reconstructs the entire original face family. The self-dual construction has an exact vertex-link isomorphism, and actual convex vertex figures transfer polytopality to that link.

The proof of Lemma 4 uses a diagonal-commutator argument with a complementary zero-pattern case instead of explicitly decomposing a support graph. The spectral proof uses determinant minimization instead of copying Forster's positioning argument line for line. Both alternatives prove the full stated results with the same mathematical hypotheses.

## Mathematical objects and scope

The development covers the principal example, all three variants, and the final general all-sign-pattern assertion of the eight-page paper.

### Ground sets, complexes, spheres, and convex realization

`Bier.Complex` is an ordinary downward-closed family of finite subsets, including the empty face. Its ground set is not assumed to coincide with its actual vertices. `Complex.vertices` consists precisely of the labels whose singleton is a face. `Complex.dimension` is the maximum face cardinality minus one, as an integer. These choices preserve the paper's distinction between a ghost label and an actual vertex.

`Complex.dual` uses complement in the entire labelled ground set. `Complex.bier` is exactly the deleted join: the unprimed subset is a face, the complement of the primed subset is a nonface, and the two subsets are disjoint. The properness assumption is the actual exclusion of the full ground set. The empty face condition supplies the paper's nonempty-complex convention.

`Complex.IsSphere n` means that the standard geometric realization is a genuine piecewise-linear sphere of dimension n. It is not defined by a circuit condition, a face count, rigidity, or membership in a generated combinatorial class. The imported `IsPLSphere` notion is a piecewise-affine homeomorphism to the standard simplex boundary. `Complex.bier_isSphere` proves the sphere theorem for every proper complex on at least two labels, including arbitrary ghost labels. Its proof constructs a linear image of the actual coned standard realization, proves injectivity and a neighborhood condition, and invokes the checked geometric link theorem.

`Bier.Polytopal K` quantifies over actual finite-dimensional real convex polytopes. `PolytopeRealization` includes a bijection from the actual vertices of K to the extreme vertices of a simplicial convex polytope, and an equivalence of the full face families with the boundary face family. It contains no assumed supporting-sign, Schur-complement, sign-rank, dimension, or nonpolytopality conclusion. Supporting functionals, affine independence, dimensions, and the vertex-figure realization of links are proved from this geometric definition. Restriction to a simplicial realizing polytope matches the standard meaning of a polytopal simplicial sphere: a face-lattice realization of such a sphere necessarily has simplex facets.

### Principal encoding and its exact enumeration

`signComplex k S hS H` has exactly the three face types in equation (1): core subsets of size at most k; one-anchor subsets with core size at most k−1; and the specified k-core-plus-anchor subsets for positive matrix entries. It forbids two anchors. Its downward-closure proof uses the actual size-k hypothesis. `signComplex_selected` requires and uses injectivity of the row subsets, so another row cannot silently change a prescribed negative membership into a positive one. `ghost` adjoins precisely one absent singleton.

The Paley character is defined on the actual field `ZMod 11`: zero has value zero, nonzero squares have value +1, and nonsquares have value −1. The twelve labels are infinity first and then the eleven field elements. In `paleyInt`, the finite label i+1 is represented by the natural index i+1; the character argument uses the difference of two such indices, so the common +1 cancels and this is exactly χ(j−i) in the paper. The diagonal and infinity row/column are stated explicitly. Orthogonality and sign entries are kernel-decided over the exact finite integer matrix, then transported to the real matrix. This is a complete exact finite proof of the explicitly fixed 12-by-12 matrix, not an experimental check standing in for an unbounded theorem.

`walsh` is the product of the binary character factors, hence exactly (−1) to the binary dot product. Its orthogonality is proved for every finite coordinate set. `explicitHadamard` is the indicated Kronecker product of two Paley factors and the ten-coordinate Walsh factor. Its index cardinality is exactly 147456.

`ExplicitLabel` is ordered lexicographically by the first Paley label, second Paley label, and binary integer value. The binary integer is `Nat.ofDigits 2` on the finite coordinate list; injectivity is proved from bounded digits. `explicitEnumeration` is an order isomorphism, not an arbitrary finite equivalence. `principalSigns` retains exactly the first 145162 columns. The row subsets are ordered by their increasing lists and enumerated by an order isomorphism, giving exactly the first 147456 nine-subsets of a twenty-element set. A shift from Fin 20 labels 0,...,19 to the paper's labels 1,...,20 preserves this order and the full face construction.

`principalInput_dimension`, `principalSphere_vertex_count`, `principalSphere_dimension`, and `principalSphere_isSphere` give respectively 9, 290365, 145181, and genuine PL sphere dimension 145181. Vertex counts count singleton faces and therefore exclude exactly the unprimed ghost; they do not count all ground labels indiscriminately.

### Geometric obstruction and padded inverse bound

The geometry normalizes actual vertex positions relative to an actual simplex facet and the outside vertex. The supporting-functional arguments retain strict inequalities at every vertex outside a face. `ghost_schur_signs` proves the two opposite extension/nonextension signs and invertibility of each genuine selected principal matrix. With X denoting the coordinate columns rather than the paper's N=−X, the desired sign matrix is −schurValue X; this convention must be retained in the final core restriction bridge.

`paddedPrincipalInverse` is the actual inverse of the principal matrix on S, extended by zero. The inverse is only used with an explicit unit-determinant hypothesis when an inverse identity is needed. The diagonal equalities and trace \|S\| are proved. `paddedPrincipalInverse_span_finrank` proves the full $m^2-m+1$ bound for arbitrary real G and every selected invertible principal submatrix. Its proof is an alternative complete argument using diagonal commutator constraints; it does not assume a dimension bound on the span. The fixed-cardinality feature theorem uses $k>0$ exactly to replace the constant term by trace/k. The arbitrary-cardinality theorem adds one real coordinate and gives $m^2-m+2$. Empty row/column sets and empty selected subsets do not create an unproved exception.

### Forster dependency: complete independent proof

`IsSignMatrix H` means every entry is literally +1 or −1. `SignRealizes H M` means $H_{rc}M_{rc}>0$ at every entry. `signRank H` is the minimum actual Mathlib real matrix rank over all strict realizations; existence and attainment are proved for sign matrices.

`Forster.signRank_spectral` proves the literal bound

$$
\sqrt{\lvert R\rvert\,\lvert C\rvert}\leq\operatorname{signRank}(H)\,\lVert H\rVert_{\mathrm{op}}.
$$

where spectralNorm is explicitly the continuous linear operator norm between standard Euclidean spaces. The proof covers every finite row and column type and every realizing matrix. No genericity, isotropy, or full-rank hypothesis remains in the final statement. `hadamard_columnRestriction_signRank` takes a genuine real `Matrix.IsHadamard` matrix and any embedding of its column index type, and proves $\lvert C\rvert\leq\operatorname{signRank}(H)^2$. Thus the principal contradiction requires no floating-point square-root estimate.

The full supporting chain is proved: actual matrix-rank factorization; sign-preserving perturbation to nonzero maximal minors; Cauchy--Binet; a coercive positive exponential determinant sum on the zero-sum hyperplane; attainment of its minimum; an explicit rank-one determinant derivative giving equal leverage scores; a symmetric idempotent projection with diagonal k/n; and the finite-sum Cauchy--Schwarz spectral estimate. The determinant-minimization proof replaces the original paper's radial-isotropy proof but proves the required positioning rather than assuming it. The literal operator-norm conversion uses the adjoint, not the entrywise matrix norm.

Cauchy--Binet source provenance: `CatalanSun/CauchyBinet.lean`, Chokmah LLC, commit 2d1890b21e946d5d61f364497b37a9fbb8790709, CC BY 4.0. The proof is included with local compatibility modifications. Attribution and the full license are retained in the source header and `licenses/vendor/catalan_sun_license`. Compatibility modifications are recorded in that header. No external certificate or unverified assertion is imported.

### Variants: complete geometric verification

The all-column-pattern matrix has one all-positive row and all possible sign patterns in the remaining rows. `allColumnSigns_rows_independent` proves actual row independence of every realizing real matrix. `allColumnSigns_signRank` gives the exact full row count. The dimension-three construction uses 74 distinct triples of a nine-element core and $2^{73}$ anchors; its checked actual vertex count is $2^{74}+19$ and its sphere dimension is $2^{73}+8$. The general parameterized construction retains $k<m$ and the required number of k-subsets in the final application.

`isolatedExtension` adds only the ghost singleton. `isolated_bier_stellar` is an equivalence for the complete face family with stellar subdivision of the all-primed facet, not merely a count of facets. `StellarFacetData.inverseRealization` proves the geometric reversal. From an actual realization of the subdivided complex it constructs the actual convex hull of all extreme vertices except the new vertex. The corner supporting functionals give genuine dual coordinates and prove nonnegativity and reconstruction on the whole polytope. Every other vertex outside the corner has coordinate sum strictly greater than one, by extremality. The retained neighbor simplex is exposed; every proper face of the deleted hull is proved to be either a surviving original exposed face or a simplex face of that base. Both directions of the full face correspondence and affine independence are proved before constructing the original `PolytopeRealization`. The intermediate outside-vertex assumption is discharged explicitly by any positive original vertex in the isolated construction. It is not a target assumption in the concrete final theorem.

`allLabelsSphere_nonpolytopal` and `all_labels_example` establish the entire variant: actual nonpolytopality, all labels present in the input and in both copies of the sphere, input dimension 9, sphere dimension 145181, genuine PL sphericity, and exactly 290366 actual vertices.

`selfDualSuspension` is exactly $2^E\cup(\{a\}*K)\cup(\{b\}*K^*)$, with no face containing both new labels. Its self-duality and exact full face correspondence of the distinguished vertex link with the ghost Bier sphere are proved. Exchange of primed/unprimed labels preserves faces and sends every face to a disjoint face. `PolytopeRealization.link_polytopal` constructs the actual convex vertex figure and its full boundary correspondence; `selfDualSuspension_nonpolytopal` applies this geometry to the proved link identity, with the necessary dimension hypothesis discharged from an actual edge. `self_dual_example` establishes literal self-duality, genuine PL sphere dimension 145182, actual face dimension 145182, exactly 290368 vertices, the simplicial involution with disjoint face images, and actual nonpolytopality.

### Principal correspondence

| Paper result | Checked Lean counterpart |
|------------------------------------|------------------------------------|
| Bier sphere theorem used in Section 1 | `Complex.bier_isSphere` for every proper complex, including ghosts |
| Theorem 2 fixed positive cardinality | `ghost_signRank_bound_fixedCard` |
| Theorem 2 arbitrary cardinalities | `ghost_signRank_bound_arbitrary` |
| Lemma 3 | `ghost_schur_signs` and the normalized core restriction bridge |
| Lemma 4 | `paddedPrincipalInverse_span_finrank`, with actual inverse/diagonal/trace identities |
| Forster bound \[2\] | `Forster.signRank_spectral`, no remaining genericity hypotheses |
| Theorem 1 principal example | `principal_example` |
| Section 4.1 no ghost | `all_labels_example` |
| Section 4.2 self-dual/symmetric | `self_dual_example` |
| Section 4.3 dimension-three input | `three_dimensional_example` |
| Final general all-sign construction | `general_allSign_construction_unrestricted`, with only the displayed binomial inequality |

The explicit principal construction uses exact finite field and binary formulas and the stated lexicographic order. None of the final nonpolytopality theorems assumes sign rank, supporting inequalities, vertex-figure realizability, inverse-stacking realizability, or sphericity as an unproved hypothesis.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

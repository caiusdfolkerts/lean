# The cubical lower bound theorem

## The inequalities and the proof strategy

Let $P$ be a cubical convex polytope of dimension $d$, and let $f_i$ denote its number of $i$-dimensional faces. The principal lower bound, for $d\geq3$, is

$$
f_1\geq\frac{d+1}{2}f_0-2^{d-1}.
$$

The graph has a bipartition into black and white vertices. Write $\Delta=\bigl|\lvert B\rvert-\lvert W\rvert\bigr|$ for the difference between their sizes. In dimensions $d\geq4$, the stronger bound is

$$
(d+1)f_0+(d-1)\Delta\leq 2f_1+2^d.
$$

The formalisation derives the bipartition from cubical geometry. It also proves the strengthened inequality for finite cubical PL $(d-1)$-spheres, including the existence of a colouring.

The main argument studies a linear system on the original graph. There is a vector $u_b\in\mathbb R^d$ for each black vertex and a scalar $s_w\in\mathbb R$ for each white vertex. A placement $p_w\in\mathbb R^d$ of the white vertices gives one equation per edge:

$$
\langle p_w,u_b\rangle+s_w=0.
$$

Local propagation proves that, for a generic placement, a solution is determined by its restriction to any facet. The facet solution space has dimension $2^{d-1}$. Comparing this upper bound with the number of unknowns minus the number of equations gives

$$
f_1\geq d\lvert B\rvert+\lvert W\rvert-2^{d-1}.
$$

Interchanging the two colour classes produces the absolute-value correction. The formal proof preserves a single placement throughout the propagation argument: it does not choose independent parameters for different facets.

Corollary 5 gives the higher-dimensional face bounds. For $1\leq i\leq d-2$, the integer form is

$$
\left[\binom di+\binom{d-1}{i-1}\right]f_0
\leq 2^i f_i+2^d\binom{d-1}{i-1}.
$$

For facets it is

$$
(d-1)f_0\leq2^{d-2}f_{d-1}+(d-2)2^{d-1}.
$$

For $d\geq4$, the strengthened proper-face inequality adds $(d-1)\binom{d-1}{i-1}\Delta$ on the left. The strengthened facet inequality is

$$
2(d-1)f_0+(d-1)(d-2)\Delta
\leq2^{d-1}f_{d-1}+(d-2)2^d.
$$

Both these integer forms and the real-valued formulas printed in the paper have explicit Lean statements. The lemma `nat_dist_cast_real` identifies natural-number distance with the real absolute difference. The conversions respect every dimension and index range, including the natural-number subtractions in the exponents.

## Geometric objects and genericity

`ConvexPolytope n` consists of a finite nonempty set of points in Euclidean space whose elements are exactly the extreme points of their convex hull. `P.dim` is the dimension of the affine direction space. The ambient dimension may be larger than `P.dim`.

Faces are nonempty exposed geometric faces. The whole polytope is included and the empty face is excluded. `faceNumber P i` counts faces of affine dimension $i$; `faceNumber_zero` identifies the vertex count. `IsCubical P` says that each facet's nonempty face poset is order-isomorphic to that of the standard cube of dimension `P.dim−1`. The standard cube is constructed as the convex hull of sign vectors, and its face classification is proved using exposing linear functionals.

`solutionSpace` is the kernel of the displayed edge operator. Facet restriction restricts the actual variables and equations. In the local propagation lemma, the vanishing of a white scalar is deduced from the neighboring black vector and an edge equation; it is not an extra hypothesis.

Genericity is expressed by a nonzero multivariate polynomial in all white-vertex parameter coordinates. Every placement outside its zero set has the required properties simultaneously for all vertices and facets. The supporting lemma in `source/cubical/generic_rank.lean` supplies a nonvanishing evaluation of a nonzero real polynomial.

## The PL-sphere extension

The native input is `Cubical.PL.CubeComplex`. Its cells are nonempty finite vertex sets, and every singleton vertex is a cell. Boolean cube charts identify all coordinate subfaces with the contained cells. Nonempty intersections are common faces. This is the common-face condition in Corollary 4.

The canonical realization is the realization of the order complex of nonempty cells. `K.IsSphere m` asserts a piecewise-affine homeomorphism, with piecewise-affine inverse, from the standard $m$-sphere to that realization. Purity, facet connectivity, simple connectedness, graph bipartition, and the PL type of vertex links are derived from this input.

The crucial local argument returns to the graph on the original neighbors of a cubical vertex. First, the abstract singleton link and the geometric singleton link have equivalent realizations. The geometric link of a finite PL sphere is again a PL sphere. Cell-to-neighbor-simplex maps then give inverse maps preserving all faces, and these induce piecewise-affine homeomorphisms. The abstract barycentric subdivision is PL-homeomorphic to the original neighbor complex. The simplicial-circuit rigidity theorem consequently applies to the original neighbor graph.

Thus the proof does not infer rigidity of an original graph merely from rigidity of a subdivision. No convex realization of the sphere or its links is assumed. The result uses this canonical abstract cubical model; a separately defined representation by embedded geometric polytopes would require its own comparison theorem.

## Stacked cubical sharpness

`FacetStacking P Q` specifies a facet of an actual convex polytope $P$ and an order isomorphism from the face poset of $Q$ to the cube-prism gluing poset. The gluing retains old proper faces except the attachment facet, adds a copy of each nonempty face of that facet, adds side prisms over its proper nonempty faces, and includes the new whole-polytope face. Its order is the product incidence with the lower boundary attached.

`IsStackedCubical` is the finite inductive closure of cubes under this operation. Rank preservation, cubicality of the new facets, the face increments, and preservation of all equality formulas are proved. Standard cubes are explicitly constructed in every positive dimension and attain the bounds.

The sharpness statements apply to every realized finite stacking sequence, with no bound on its length. A separate theorem constructing a new convex realization at every chosen facet, or prescribing every stacking length, is outside their scope.

## Main statements and their scope

### Principal convex statements

All names below are in `LeanEval.Geometry.PlatonicClassification`.

| Manuscript | Formal declaration | Quantifiers and conclusion checked |
|------------------------|------------------------|------------------------|
| Theorem 1, first inequality | `IsCubical.edge_bound`, `cubical_lower_bound` | Every ambient dimension `n`, every genuine convex `P : ConvexPolytope n`, every affine dimension `P.dim ≥ 3`; exactly `(d+1)f₀/2 − 2^(d−1) ≤ f₁`. |
| Theorem 1, stronger inequality | `IsCubical.strengthened_edge_bound` | Every `d ≥ 4` and every proper Boolean coloring; exactly the additional `(d−1)\|B−W\|/2`. |
| Existence of the bipartition | `IsCubical.bipartite` | Derived from actual cubical convex geometry. The stronger theorem's coloring parameter is not an unproved existence assumption. |
| Lemma 2 | `IsCubical.generic_local_propagation` | One nonzero polynomial in all white-vertex parameter coordinates; every nonvanishing evaluation gives the implication for every white vertex, every incident facet, and every solution of the original system. |
| Proposition 3 | `IsCubical.generic_facet_determination` | One common nonzero polynomial gives injectivity of actual facet restriction for every facet and exact facet-system dimension `2^(d−1)`. |
| Corollary 5, proper faces | `IsCubical.face_lower_bound` | Every `d ≥ 3` and every `1 ≤ i ≤ d−2`; both binomial coefficients, denominator `2^i`, and constant `2^(d−i) choose(d−1,i−1)` match. |
| Corollary 5, facets | `IsCubical.facet_lower_bound` | Every `d ≥ 3`; exactly `(d−1)f₀/2^(d−2) − 2(d−2) ≤ f_(d−1)`. |
| Final paragraph, proper faces | `IsCubical.strengthened_face_lower_bound` | Every `d ≥ 4`, same full index range; correction `(d−1) choose(d−1,i−1) \|B−W\| / 2^i`. |
| Final paragraph, facets | `IsCubical.strengthened_facet_lower_bound` | Every `d ≥ 4`; correction `(d−1)(d−2)\|B−W\| / 2^(d−1)`. |
| Cube/stacked sharpness | `IsStackedCubical.edge_equality_real`, `IsStackedCubical.face_equality_real`, `IsStackedCubical.facet_equality_real` | Exact equalities in the displayed real-valued formulas, for every finite realized stacking sequence and the same full dimension/index ranges. |

The integral variants are not used as substitutes for the displayed formulas: the conversions to the real-valued statements are proved in Lean. All natural subtractions in exponents and coefficients occur in ranges where their ordinary integer interpretations are justified. The paper's vertex number is `P.vertices.card`; `faceNumber_zero` proves its equality with `faceNumber P 0`.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

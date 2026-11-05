# Stress–flex orthogonality

## The statement and the geometric data

The paper begins with a finite cell decomposition of a closed oriented surface, with simple graph G = (V, E). Its vertices are realised at distinct points of ℝ³. The vertices of each face lie in an affine plane and include three noncollinear points. The realisation need not be embedded. A cone point lies outside every face plane, and an edge joins it to every original vertex.

An equilibrium stress assigns a scalar to every edge. An infinitesimal motion assigns a velocity to every vertex and makes the first derivative of every squared edge length vanish. When the cone vertex has velocity zero, Theorem 1 asserts for the sphere that

```math
\sum_v c_v u_v=0,
```

where cᵥ is the cone-edge stress. The same theorem asserts the existence of a nine-vertex embedded polyhedral torus for which this sum is nonzero.

For formulas, put the cone point at the origin and write pᵥ for the relative position of v. Orient each original edge arbitrarily, with tail s(e) and head t(e). Set

```math
A_{ve}=\mathbf 1_{v=t(e)}-\mathbf 1_{v=s(e)},\qquad
 F_v(w)=\sum_e A_{ve}w_e(p_{t(e)}-p_{s(e)}).
```

The stress equations are cᵥpᵥ + Fᵥ(w) = 0, and the motion equations are

```math
p_v\cdot u_v=0,\qquad
 (p_{t(e)}-p_{s(e)})\cdot(u_{t(e)}-u_{s(e)})=0.
```

Summing the stress equations and using ∑ᵥ Aᵥₑ = 0 gives ∑ᵥ cᵥpᵥ = 0, exactly the apex equilibrium equation. The formalisation includes this summation lemma, identifying the outer-vertex equations with the full coned stress.

For a general cone point O, put pᵥ = Pᵥ − O. A face equation N_f · P = d_f, with d_f − N_f · O ≠ 0, becomes n_f · pᵥ = 1, where

```math
n_f=(d_f-N_f\cdot O)^{-1}N_f.
```

Translation preserves original-edge differences. These identities give the direct passage between the normalised representation and the arbitrary-apex statement.

The abstract CW space is separate from the vertex-position map into ℝ³. The checked spherical theorem imposes no injectivity on a geometric surface map and no nonintersection requirement on realised edges or faces.

## Continuous stress transport in every finite dimension

Lemma 2 is independent of dimension. Suppose a stress continues continuously when the apex moves from 0 to a nearby point x, keeping all original vertices fixed. Pair the equilibrium equation at v with the original velocity uᵥ, then sum over v.

The original-edge terms cancel by virtual work: edge e contributes

```math
w_e(x)(p_{t(e)}-p_{s(e)})\cdot(u_{t(e)}-u_{s(e)})=0.
```

The cone equations for the original motion remove pᵥ · uᵥ. Hence

```math
x\cdot\sum_v c_v(x)u_v=0.
```

Let f(x) = ∑ᵥ cᵥ(x)uᵥ. For a fixed vector z, take x = tz with nonzero real t tending to 0. Division by t gives z · f(tz) = 0 eventually. Continuity gives z · f(0) = 0. Choosing z = f(0) proves f(0) = 0. This punctured-neighbourhood argument is the one used in the checked Lean proof.

The checked Lean declaration `StressFlex.continuation_orthogonality` treats arbitrary finite vertex and coordinate types. It uses actual supported symmetric stress matrices and the usual infinitesimal edge equations. Its incidence version is designed for the construction below. Neither definition contains the desired orthogonality conclusion.

The sign convention deserves an explicit check. The paper uses Mᵢⱼ = ωᵢⱼ off the diagonal and cᵢ = −(M1)ᵢ. Its Lemma 2 concludes (M₀1)ᵀU = 0. The checked matrix theorem has exactly that conclusion; the physical cone-weighted sum is its negative, which also vanishes.

## Where the sphere enters

The topology must not be replaced by an assumption that face potentials exist. The reconstruction uses an actual CW structure on a topological space X, together with a homeomorphism X ≃ S². Vertices, edges and faces are its genuine cellular indexing types in dimensions zero, one and two.

Let Bₑf be the coefficient of edge e in the actual cellular boundary of face f. The required facts are

```math
AB=0,\qquad \ker A=\operatorname{im}B.
```

The first is the chain-complex identity. The second follows from H₁(S²; ℝ) = 0, transported through cellular–singular homology comparison.

The checked dependency chain uses TauCeti's cellular comparison, incidence and singular-sphere homology modules. A basis equivalence converts each finite cellular chain group into ordinary functions on its cells. The differential becomes the corresponding incidence sum. Exactness in the category of real modules then supplies an actual preimage of each cycle.

The endpoint formula is also connected to geometry. TauCeti computes the boundary of a one-cell from the two endpoints of its attaching map. Our orientation names the endpoint with positive cellular coefficient the head. Equality between Aᵥₑ and the actual degree-zero cellular incidence is therefore a theorem, not an assumed matrix identity.

A separate bridge connects Bₑf ≠ 0 to face geometry. TauCeti's local-degree support result says that the coefficient vanishes if the face attaching map misses a point of the open edge. Its contrapositive places every point of the open edge in the face frontier. Taking closures places the entire closed edge in the closed face. Here one uses that closed cells are closed and that the closure of an open cell is its closed cell. Both edge endpoints consequently satisfy the face-plane equation.

This version does not require a coherent choice of face generators. Arbitrary cellular orientations suffice, because their actual boundary coefficients are retained.

## Whole-edge face coverage from the actual sphere

The incidence calculation for a nonzero boundary coefficient does not by itself handle every edge. A bridge may have zero coefficient in every face boundary, because its two traversals cancel. Assuming in advance that such an edge lies in one closed face would leave a gap between a general CW cellulation and the geometric hypotheses used by the stress formulas. The following argument derives that containment from the topology of the sphere.

The dimension bound is also derived. Compactness of the sphere and the CW compact-support theorem place the whole space in a finite skeleton, giving a bound above which its cell types are empty. A cell of maximal dimension is ambient-open. If its dimension differed from two, its characteristic chart would make local degree-two homology vanish, contradicting the sphere's nonzero local fundamental class. Descending from the finite-dimensional bound therefore excludes every cell above dimension two. The final theorem does not assume this conclusion separately.

Next the union of the open faces is dense. If an open cell of dimension zero or one had nonempty ambient interior, its characteristic map would give an ambient Euclidean chart of that dimension. Local homology in degree two would then vanish there. On a two-sphere, however, the global fundamental class maps to a nonzero local degree-two class at every point. Thus vertices and open edges have empty ambient interior. Their closed cells also have empty interior, since an edge adds only its two endpoints. A finite union of these closed sets still has empty interior. The CW cover therefore proves density of the open faces. Since the union of the finitely many closed faces is closed, it is the whole space; in particular, every vertex lies in a closed face.

Now fix an edge e whose entire incidence row vanishes. Let K contain all vertices and all other edges, with no faces. This is a genuine closed CW subcomplex. In the relative cellular complex of (X,K), the only one-cell is e and every face remains. The zero-row hypothesis says that each individual face basis vector is a relative two-cycle. Cellular comparison lifts it to a class h_f in H₂(X,K).

The map from these relative classes to cellular two-chains is injective. Consequently the relative fundamental class equals the finite sum of z_f h_f, where z_f are its actual cellular coefficients. At any interior point of e, the local fundamental class is nonzero. At least one of the classes h_f must therefore have a nonzero local coefficient there.

That coefficient is locally constant on the open complement of K. This follows directly from neighbourhood detection in relative homology: after subtracting the appropriate multiple of the fundamental class, a class vanishing at one point vanishes over a smaller neighbourhood. The genuine open-cell parametrisation of e has connected domain, so the selected coefficient is nonzero along the entire open edge.

Finally, the local coefficient of h_f vanishes in every other open face, by the exact relative basis-coordinate calculation. Density of the open faces and local constancy force it to vanish outside the closure of f. Hence the whole open edge lies in that closure. Taking closures gives containment of the closed edge. This treats the zero-incidence case without requiring injective face attaching maps or a separate theorem about vertex links.

The final geometric input structure therefore records only the paper's distinct vertex positions, planar noncollinear face vertices and simple loopless graph. Vertex and whole-edge face coverage are supplied by the proved CW-sphere argument, rather than being hypotheses of the principal theorems.

## Turning a stress into a cellular cycle

Associate to each edge the vector

```math
\beta_e=w_e(p_{s(e)}\times p_{t(e)}).
```

Cross the equilibrium equation at v with pᵥ. The cone term vanishes. The endpoint incidence sign converts each remaining term into Aᵥₑβₑ, giving

```math
\sum_e A_{ve}\beta_e=0.
```

Apply cellular exactness to each coordinate. There is a vector-valued two-chain a_f ∈ ℝ³ with

```math
\beta_e=\sum_f B_{ef}a_f.                 \tag{1}
```

This is the potential representation needed for transport. It replaces the paper's coherently oriented expression a_G − a_F by the actual cellular boundary formula. No dual CW structure or global choice of face orientation is required for the orthogonality proof.

Equation (1) is derived from the topological sphere. It is not a field of a structure called a sphere, an extra premise on the original stress, or an axiom.

## Explicit rational continuation

For a face with normalised plane n_f · p = 1, put

```math
a_f(x)=a_f+\frac{a_f\cdot x}{1-n_f\cdot x}n_f.
```

A direct calculation gives

```math
a_f(x)\cdot(p-x)=a_f\cdot p
```

at every vertex of that face, whenever the denominator is nonzero.

Define βₑ(x) = ∑_f Bₑf a_f(x). The support-to-geometry bridge shows that every nonzero summand preserves its affine value at both endpoints of e. Therefore βₑ(x) is perpendicular to both shifted endpoint vectors. Let

```math
q_e(x)=(p_{s(e)}-x)\times(p_{t(e)}-x),\qquad
 w_e(x)=\frac{\beta_e(x)\cdot q_e(x)}{q_e(x)\cdot q_e(x)}.
```

Initially the two endpoint vectors are independent: they are distinct points in a common affine plane that misses the origin. Continuity preserves this independence near 0. A cross-product identity then proves

```math
w_e(x)q_e(x)=\beta_e(x).
```

The identity AB = 0 still holds after the face vectors move. Hence the new cycle is closed, and the new original-edge force satisfies

```math
(p_v-x)\times F_v(w(x))=0.
```

It is parallel to pᵥ − x. The cone coefficient

```math
c_v(x)=-\frac{F_v(w(x))\cdot(p_v-x)}
                  {(p_v-x)\cdot(p_v-x)}
```

therefore completes the equilibrium equations.

Every denominator is nonzero at 0. Finiteness yields one common neighbourhood for all faces, edges and vertices. The formulas are continuous there, and at x = 0 they recover the original coefficients. Lemma 2 then proves spherical orthogonality.

This proves the spherical part of Theorem 1 through continuous stress transport. Proposition 3 is established separately: its quotient isomorphism and dimension formula require the additional lifting argument below. Real analyticity follows from the same explicit rational formulas and Mathlib's analytic closure rules.

## The full stress and lifting correspondence

Proposition 3 includes more than the continuation required for orthogonality. Write L(S) for the vector space of real vertex values whose restriction to each face comes from an affine function on that face. If S is a sphere and the apex x misses every face plane, the proposition asserts the natural linear isomorphism

```math
\operatorname{Stress}(S,x)\;\cong\;
L(S)\big/\{(b\cdot(P_v-x))_v:b\in\mathbb R^3\}.
```

It also asserts that the stress space has dimension dim L(S) − 3 and that every stress admits a real-analytic continuation when x moves sufficiently little.

In the normalisation above, three noncollinear vertices of a face give three linearly independent position vectors, because the face plane misses the origin. Thus a lifting determines a unique vector λ_f with λ_f · pᵥ equal to its prescribed height at every vertex of face f. To see existence, write its affine function as b · p + d and take λ_f = b + d n_f. Independence gives uniqueness.

The kernel argument uses actual second homology. A surface cellulation has no cells above dimension two. Consequently the group of cellular two-cycles is H₂(S²; ℝ), which is one-dimensional. Let z be the cellular fundamental cycle determined by the orientation. Its coefficient z_f is nonzero for every face. This last fact has a geometric proof: the map from global second homology to local homology at an interior point of the face is an isomorphism, and in cellular coordinates it reads precisely that face coefficient. The formalisation establishes it through the local-homology machinery.

For a lifting, form the vector-valued face chain with coefficients z_f λ_f. At an endpoint v of an edge e, its boundary has scalar product

```math
\left(\sum_f B_{ef}z_f\lambda_f\right)\cdot p_v
   = a_v\sum_f B_{ef}z_f
   = 0.
```

The same cross-product reconstruction as before therefore supplies an edge stress and then a cone stress. This construction is linear in the lifting. If its stress vanishes, each coordinate of the face chain lies in the one-dimensional kernel of B. Hence there is one vector b with z_f λ_f = z_f b for every f. Since z_f ≠ 0, all the face vectors equal b. The kernel is exactly the displayed space of global linear heights.

Surjectivity requires the face potentials to define one height at each vertex. There is a local-homology proof that avoids imposing an additional condition on vertex links. Fix a vertex v and let Kᵥ be the graph subcomplex consisting of every other vertex and every edge whose endpoints both differ from v. This subcomplex is closed and misses v. A closed one-cell consists of its open edge and its two attaching endpoints, so its inclusion in Kᵥ is an actual geometric condition.

For a stress potential a, the scalar face chain with coefficients a_f · pᵥ has boundary supported in Kᵥ. Indeed its boundary coefficient on an incident edge is βₑ · pᵥ, which is zero. The relative CW structure of the pair (X, Kᵥ) keeps precisely the cells outside Kᵥ, with their original characteristic maps. The absolute-to-relative chain map keeps those basis vectors and kills the basis vectors inside Kᵥ. Thus the scalar chain defines a class h in H₂(X, Kᵥ).

The global fundamental class gives a nonzero generator gᵥ of local second homology at v. Choose the scalar aᵥ for which h restricts to aᵥgᵥ. The difference h − aᵥg therefore vanishes locally at v. TauCeti's neighbourhood detection theorem for relative homology says that it already vanishes over some smaller neighbourhood U of v, disjoint from Kᵥ.

Every face whose closure contains v has an interior point in U. At that point, the cellular coefficient formula reads the two local classes as a_f · pᵥ and z_f times the same cell generator. Consequently

```math
a_f\cdot p_v=a_vz_f.
```

Since z_f is nonzero, the divided face vectors λ_f = a_f/z_f give the common height aᵥ at every vertex of f. They therefore define an element of the genuine lifting space L(S), and reconstruct the original stress. The checked proof includes the actual graph subcomplex, the absolute-to-relative basis calculation and this local coefficient comparison. In particular, it proves the normalisation by z_f; it does not assume a coherent orientation convention in which every z_f equals one.

The proved surjectivity and exact kernel give the quotient correspondence by the linear first isomorphism theorem. The global linear-height subspace has dimension three because one face contains three independent position vectors. The quotient dimension formula gives both dim Stress = dim L(S) − 3 and the additive equality dim Stress + 3 = dim L(S). For the fixed oriented cellular model, the quotient map is the explicit linear stress construction above; its inverse is well defined because the kernel and surjectivity are proved.

The rational formulas are well-defined whenever the moved apex avoids the face planes. For the asserted continuation, a sufficiently small open neighbourhood is enough. If the apex moves to x and 1 − n_f · x is nonzero, the shifted face has normal n_f/(1 − n_f · x) and level one. Distinct endpoints on that face remain linearly independent relative to the apex, so the edge and vertex denominators are nonzero there as well. The analytic closure rules for finite sums, products and reciprocals therefore apply to the full edge-and-cone coefficient family. The analytic continuation assertion on an open neighbourhood, including equilibrium and the exact initial stress, is now checked as `StressFlex.Spherical.analytic_stress_extension_at_apex`. The quotient and dimension assertions are checked independently by the preceding argument.

## The explicit torus

Take

```math
\xi_1=(1,0),\quad \xi_2=(0,1),\quad \xi_3=(-1,-1),
```

and

```math
A_k=(2\xi_k,-1),\quad B_k=(4\xi_k,0),\quad C_k=(2\xi_k,1).
```

For each cyclic index k, the three strips have corner cycles

```math
(A_k,B_k,B_{k+1},A_{k+1}),\qquad
(B_k,C_k,C_{k+1},B_{k+1}),\qquad
(C_k,A_k,A_{k+1},C_{k+1}).
```

These are the nine quadrilateral faces. The outer graph is the Cartesian product of two three-cycles, and the apex is O = 0.

The embedded surface needs a topological proof, beyond arithmetic on its graph. Let D be the triangle with vertices ξₖ, and let T be the radius–height triangle with vertices (2, −1), (4, 0), (2, 1). The map

```math
(\xi,(r,z))\longmapsto(r\xi,z)
```

on ∂D × ∂T has r ≥ 2. The gauge of D recovers r from the horizontal coordinates, proving injectivity. Explicit positive homogeneous gauges identify both polygonal boundaries with circles. Compactness of the domain and the Hausdorff property of ℝ³ give a closed embedding and a homeomorphism from S¹ × S¹ onto the image.

Each product of triangle edges maps to a planar quadrilateral. Its image is exactly the convex hull of its four corners. The bilinear formula gives one inclusion as a convex combination. For the converse, positivity of radius makes the image convex: the horizontal parameter for a weighted combination is

```math
\frac{a r_s s+b r_t t}{a r_s+b r_t}.
```

The denominator is positive, and the quotient belongs to [0, 1]. This proves the claimed planar polygon geometry.

Let u_Aₖ = (Jξₖ, 0), with all other velocities zero. The four vertices O, A₁, B₁, C₁ have affine-dependence coefficients (−1, 1, −1, 1). Extend them by zero, and set σᵢⱼ = −λᵢλⱼ off the diagonal. The affine dependence and the sum-zero condition imply equilibrium. Direct edge calculations give the infinitesimal-motion equations. Finally,

```math
\sum_i\sigma_{0i}u_i=(0,1,0)\ne0.
```

The checked declaration `StressFlex.Torus.stress_flex_counterexample` combines all these properties in one theorem. Its hypotheses do not assume that the coordinate picture is a torus: the two gauge circles, injective parametrisation, homeomorphism onto the geometric surface, convex-hull description of every face, straight edges, patch intersections, exact graph relation, supported stress and motion are all proved. The sum is taken over exactly the nine outer vertices and is exactly (0, 1, 0).

The cited strong conjecture uses infinitesimal flexes of the bar framework: its equations are imposed on graph edges, without additional diagonal constraints inside a quadrilateral. Connelly, Gortler, Theran and Winter explicitly allow closed surfaces with flat faces in their Conjecture 5.2. Its full-affine-span hypothesis is met by A₁, A₂, A₃ and C₁. The source includes explicit affine coordinates expressing every point of ℝ³ using those four vertices, with weights summing to one.


The paper's final, unnumbered period calculation is verified as well. The three lower faces form a genuine cycle in the dual graph: `lower_faces_intersection` proves that the preceding and current lower quadrilaterals meet in exactly the nondegenerate segment AₖBₖ. The only stressed edge on this cycle is A₁B₁, and `lower_cycle_period` proves

```math
\sum_{k=1}^{3}\sigma_{A_kB_k}(A_k\times B_k)=(0,-4,0).
```

For any assignment of vectors to all nine faces, the sum of the successive potential differences around this three-face cycle telescopes to zero. The displayed nonzero period therefore contradicts even these three prescribed differences. The theorem `no_global_face_potentials` rules out a global assignment respecting the oriented common-edge equations. This identifies the precise potential step that fails on the torus. The additional source is `source/torus_period.lean`.


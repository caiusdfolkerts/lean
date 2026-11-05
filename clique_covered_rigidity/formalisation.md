# Six-connected K4-covered graphs are rigid in three dimensions

## The assertions and their mathematical meaning

The main assertion is Theorem 1.1 of the paper: every finite, six-vertex-connected, $K_4$-covered simple graph is generically rigid in $\mathbb R^3$. The source statement quantifies over an arbitrary finite vertex type. Six-connectivity means that there are more than six vertices and deleting any set of fewer than six vertices leaves a connected induced graph. Coverage means that each actual edge belongs to an actual four-vertex clique.

For a placement $p:V\to\mathbb R^3$, the rigidity operator has one coordinate per ordered vertex pair, with zero rows for nonedges. Its two rows for an undirected edge agree. On a velocity assignment $u$, that edge row is

$$
(p_v-p_w)\mathbin{\cdot}(u_v-u_w).
$$

The generic rank $r(G)$ is the maximum attained rank of this operator over real placements. The definition does not assume a combinatorial rank formula. Generic rigidity means equality with the generic rank of the complete graph on the same vertices. The supporting development identifies the complete graph's motions at general-position placements with Euclidean twists and proves its rank to be $3|V|-6$ when $|V|\geq3$. These are the usual infinitesimal-rigidity semantics. The source also proves equivalence with actual local distance rigidity. The length map uses the Euclidean squared distance $\sum_{i=1}^{3}(p_{v,i}-p_{w,i})^2$. For a generically rigid graph, at every generic placement, sufficiently nearby placements preserving these values on graph edges must preserve them on every vertex pair. `FinalSemantics` exposes this conclusion for the main theorem and both corollaries. At generic general-position placements it also identifies the main theorem's actual motion kernel with the range of the global translation-and-rotation operator.

An entrywise comparison with the rational polynomial bar matrix proves that algebraically independent real coordinates attain the maximum rank for every graph. Thus `FinalAlgebraic` also states all three graph conclusions at ordinary algebraically generic coordinates, with actual local distance rigidity as the conclusion. It gives the exact matrix rank $3|V|-6$ in Theorem 1.1. The algebraic-independence hypothesis concerns all coordinates $p_{v,i}$ over $\mathbb Q$.

Corollary 1.2 has two endpoints. In its first form, $G$ is six-connected and each edge lies in an arbitrary generically rigid subgraph of order at least four. That subgraph may omit edges of the corresponding induced graph. In its second form, an arbitrarily indexed family of vertex sets, each of order at least four, consists of rigid clusters *in the ambient graph*; completing those clusters produces a six-connected spanning graph. Ambient rigidity can be transmitted through vertices outside a cluster. It is not replaced by rigidity of the induced subgraph.

The other principal assertion comprises all three clauses of Theorem 5.1. Let $J$ be a finite loopless multigraph of pin occurrences on a nonempty finite body set. For a partition $\mathcal P$ of the bodies, set

$$
D_J(\mathcal P)=6(|\mathcal P|-1)
-\sum_{A<B\in\mathcal P}\ell(m_J(A,B)),\qquad
\ell(a)=\begin{cases}0&a=0,\\3&a=1,\\5&a=2,\\6&a\geq3.\end{cases}
$$

The generic relative-motion dimension is $\max_{\mathcal P}D_J(\mathcal P)$. If no distinct bodies have identical twists in every compatible motion, the singleton partition is optimal. If the pin graph is also simple, all three coordinate rows of every pin constraint are independent. Parallel pins retain separate occurrence labels throughout the proof.

| Paper result | Principal Lean endpoint, in `Papers.Rigidity` |
|:------------------|:-|
| Theorem 1.1 | `sixConnected_k4Covered_rigid` |
| Corollary 1.2, edge cover | `sixConnected_rigidSubgraphCovered_rigid` |
| Corollary 1.2, completion | `rigidCluster_completion_sixConnected_rigid` |
| Theorem 5.1, all clauses | `PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins` |
| Theorem 5.1, maximum rank | `PairPinGraph.defect_at_maximal_rank_pins` |
| Sharpness of six-connectivity | `fiveConnected_k4Covered_flexible_exists` |

The maximum-rank formulation is useful in the main proof. Here genericity means simultaneous maximum rank for the finite family of relevant matrices. The proof that their rank loci are open and dense supplies a single real placement regular for every required graph and selected pin framework. The pin-row independence needed later is derived from Theorem 5.1.

## The dependency structure

The development starts from the actual rigidity matrix, its motion kernel, and its equilibrium-stress kernel. It constructs rigidity closure, complete frameworks, gluing, coning and the planar rigidity facts needed from Jackson--Jordán--Villányi \[2\]. The planar development incorporates the proofs adapted from Chen's *CombinatorialRigidity*, with its source commit and attribution retained. The pair-pin development incorporates the supporting algebra and sparse-graph proofs from Zheng's project \[3\].

The table names the proof sections and the compiled source files containing them. Section labels retain the names used in the assembly comments.

| Paper | Source route | Mathematical role |
|:-----------|:----------------------------|:-|
| §2 | `SupportedBound`, `RankContributionBound` — `source/consolidated/rigidity_combined03.lean` | Supported-code expectation and stress birth. |
| §3 | `MinimalCounterexample`, `OneFlexibility`, `SoftPinCenters` — `source/consolidated/rigidity_combined03.lean`, `source/consolidated/rigidity_combined06.lean`, `source/consolidated/rigidity_main_recovery01.lean` | Minimal counterexample, one flex, actual virtual axes. |
| §4 | `ConfigurationLocalForms`, `HypervertexDeletion` — `source/consolidated/rigidity_combined06.lean`, `source/consolidated/rigidity_main_recovery01.lean` | Actual local Euclidean motions and the deletion loss $\delta\geq7$. |
| §5 | `PairPinDefect`, `PairPinOptimal`, `PairPinMaximalRank` — `source/consolidated/rigidity_combined02.lean` | Exact generic quotient dimension and row independence. |
| §6 | `BodyLoadQuotient`, `ScalarObservers`, `ExceptionalScalarModes` — `source/consolidated/rigidity_combined04.lean`, `source/consolidated/rigidity_combined07.lean`, `source/consolidated/rigidity_main_recovery01.lean` | Copied stresses, compatible loads, scalar information and exceptional modes. |
| §7 | `TwoBodyContribution`, `HypervertexContribution`, `GlobalBudget` — `source/consolidated/rigidity_main_recovery01.lean` | Local contributions and the final rank contradiction. |
| §1 | `FinalTheorems`, `Closure` — `source/consolidated/rigidity_combined03.lean`, `source/consolidated/rigidity_main_recovery01.lean` | Unconditional graph theorem and both corollaries. |

Lemma 2.1 is developed by finite averaging. Place the coordinates and one extra marker in a uniformly random permutation, and let $A$ be the coordinates before the marker. Over any field $K$, for every $s\geq1$, a code of dimension $r$ whose nonzero vectors have support of size at least $s$ satisfies

$$
\mathbf E\dim(W\cap K^A)\leq \Phi_s(r)
:=\frac{r(r+1)}{2(r+s)}.
$$

Shortening at an active coordinate supplies the recursion, and the support bound gives the necessary lower bound on the number of active coordinates. Thus the main argument needs no exponential-clock machinery. The separate `PriorityOrders` and `PriorityExpectation` modules identify this finite mean with the literal Bochner expectation under independent uniform real priorities. The probability space is a product of Lebesgue measures restricted to $[0,1]$, with one factor for every coordinate and for the marker. The supported space is defined by the actual strict inequalities $x_i<x_{\mathrm{marker}}$.

The proof derives almost-sure distinctness from the nullity of singleton sections of the product measure. A finite sum over measurable order chambers proves integrability of the dimension. For each injective priority vector, summing that dimension over all coordinate relabellings traverses every finite order once. The product law is invariant under these relabellings, so integration gives the equality of the two means. The same argument works for any common atomless real probability law. The graph proof itself uses finite orders throughout.

The equality examples are developed for every $r\geq0$ and $s\geq1$ over every infinite field. Evaluate polynomials of degree below $r$ at $r+s-1$ distinct points. The polynomial root bound gives minimum support $s$, and injectivity of evaluation gives dimension $r$. Shortening preserves equality in the Singleton bound, so the same finite recursion gives equality in $\Phi_s(r)$. The finite-order endpoint is `SupportedCode.exists_code_attaining_bound`; the probability bridge also gives equality under independent uniform real priorities.

For any fixed stress subspace, new stresses at a vertex inject into its star image with support among the earlier neighbours. At a general-position vertex, every nonzero balanced star has at least four nonzero coordinates. This gives Corollary 2.2 for arbitrary stress subspaces, a generality needed after the scalar constraints and selected local modes have been removed.

## The pair-pin theorem

A body twist is $(\omega,t)\in\mathbb R^3\times\mathbb R^3$, with velocity $t+\omega\times p$ at a pin $p$. The proved triangle motion equivalence gives the same description for a noncollinear rigid triangle. The compatibility operator records the velocity difference at each occurrence. Its kernel is the genuine space of compatible assignments. Constant assignments give its six-dimensional common-motion subspace, and relative motions form the actual quotient by that subspace. The dimension in Theorem 5.1 is therefore a dimension of a constructed vector space.

The lower bound for every partition comes from block-constant twist assignments. One pin imposes at most three constraints, two at most five, and every larger bundle at most six. The partition maximum is first taken in $\mathbb Z$. The one-block partition proves that it is nonnegative before the natural-valued rank formula is used. All partitions are represented; unused block labels contribute nothing.

For the upper bound, quotient the bodies that have equal twists in every generic compatible motion. An explicit linear equivalence preserves the grounded motion kernel. A sparse-skeleton theorem selects enough crossing support edges to account for the remaining defect. On such an edge the actual compatibility equation implies the null-difference equation

$$
(\omega_i-\omega_j)\mathbin{\cdot}(t_i-t_j)=0.
$$

Zheng's sparse height argument supplies the required codimension of these null equations. Its proof is included: the combinatorial flag construction, field extensions, stress kernels, prime ideals, localisation and dimension estimates are mathematical dependencies, not assumed conclusions. The height calculation is proved directly over $\mathbb Q$, the coefficient field of the symbolic pin matrix, using componentwise Witt shears and verified field and height lemmas.

The incidence calculation keeps pin coordinates separate from twist coordinates. In a nonzero angular chart, two coordinates of each active pin can be eliminated. The resulting height estimate pays two dimensions per active pin and one per selected sparse null equation. The generic grounded matrix converts this height bound into the opposite rank bound. Polynomial minors then identify rational-function-field rank with the maximum attained real rank.

Finally, an optimal block-constant kernel has the same dimension as the whole kernel, so their inclusion is onto. Every optimal block consists of merged bodies. Under the no-merger hypothesis each block must be a singleton. In the simple case the singleton capacity sum is $3|E|$; rank-nullity and duality yield literal linear independence indexed by $E\times\{0,1,2\}$.

## Local motions, hypervertices and virtual axes

Failure of Theorem 1.1 yields a counterexample of least order and, subject to that, greatest edge count. These choices are derived from failure of the unrestricted theorem. They are not hypotheses of the principal endpoint. Its maximal rigid cliques of order at least four are the bodies. Write $\delta(v)=r(G)-r(G-v)$ for the generic rank lost on deleting $v$. Closure, planar rigidity and vertex elimination give the structural statements of §3. The deletion estimate is rederived from the actual common-pin operator: a loss of at most four forces the whole closed neighbourhood to be an ambient rigid cluster. Edge maximality then completes that neighbourhood to a clique, contradicting the proved nonsimpliciality. Hence $\delta(v)\geq5$, supplying the application of Jackson--Jordán--Villányi \[2, Lemma 8.23\] directly. Gluing gives distinct-body intersections of size at most two. The rank-contribution argument then gives one remaining flexibility dimension.

The differential step in §4 begins with the actual squared-edge-length map. On a constant-rank neighbourhood, a local fibre parametrisation realises every infinitesimal motion as a derivative of an actual length-preserving motion. Surviving body triangles determine their Euclidean motions uniquely. The source constructs their matrix frames, differentiates them and derives the Maurer--Cartan identities from matrix multiplication and inverse identities. It does not postulate integrability of arbitrary twist-valued forms.

A projective chart is used only to transport the relevant linear motion spaces and make a centre finite. The transformed placement then has its own actual Euclidean length fibre; no projective image is asserted to preserve Euclidean edge lengths.

The rank-four argument is reduced to explicit linear algebra. On a four-dimensional tangent slice, the three pin equations have a Cramer kernel vector whose coordinates are polynomials in the pin. The span of these actual vectors, even after restricting to a nonzero-minor chart, equals their coefficient span. A second body form compatible with the same pins gives pointwise eigenvector relations. A polynomial argument forces one common scalar on this span. The span has dimension at least three, so the difference of the two body forms after rescaling has rank at most one. Its three-dimensional case gives a finite or infinite centre space; its four-dimensional case gives proportional forms.

The scalar is realised locally by a ratio of explicit cofactor coordinates, so its differentiability is proved. Its derivative is retained when differentiating the proportionality relation. For proportional immersed forms on a space of dimension at least four, the Maurer--Cartan identities would otherwise produce a scalar-bracket identity on a four-dimensional subspace of the Euclidean Lie algebra; the source proves that identity impossible. Further differential lemmas handle the rank-one discrepancy and changes of rank. These steps are developed in `CofactorBodyForms`, `ProportionalDifferential` and `RankFourDifferential`.

Deleting a hypervertex leaves several incident body motions. The cases of deletion loss five and six force rank-three or rank-four relative twist configurations. Their centre-space classifications, together with the derived differential identities, force two distinct bodies to have equal twists in every compatible motion when the removed pin is restored at a suitable generic position. This contradicts their maximality. Consequently the actual generic deletion rank satisfies $\delta(v)\geq7$.

In the finite rank-three case, differentiating the actual centre equation forces its derivative to vanish. Differentiating the remaining moving difference-line relation then gives the contradiction pointwise. This supplies the conclusion of Lemma 4.5 without a separate flow-invariance argument or an integrability assumption on a chosen tangent distribution.

After deleting a soft point pin, the actual relative twist image of its two bodies is three-dimensional and has a projective centre. Write that centre as $q=(a,c)$, allowing $c=0$. Its twist equations are

$$
ct+\omega\times a=0,\qquad a\cdot t=0,
$$

and its physical force-axis direction at $v$ is

$$
d_v=c\,p_v-a\ne0.
$$

Virtual work shows that every compatible body force at $v$ lies in $\mathbb Rd_v$. This homogeneous formula includes centres at infinity. If another actual vertex of either incident body lay on the axis, all graph motions would also make that vertex follow the other body's twist. Ambient closure would enlarge that body, contradicting maximality. This exclusion is the geometric input to the later scalar and wrench rank arguments.

## Supported loads and the scalar code

The copied-edge space gives each body its own copy of every edge. Summing copies gives ordinary graph edge coefficients; restricting to compatible copies gives graph stresses. The aggregation kernel is the actual duplicate-edge space, and the local clique stress spaces form an actual direct sum. Force and moment balance identify graph stresses modulo local clique stresses with compatible body loads modulo duplicate loads. The same construction is made on every vertex prefix $T$, which matters when dimensions are averaged over insertion orders. For the intersection in Proposition 6.2(4), all the existing prefix load spaces are mapped injectively into the common coordinate space of body--vertex forces. In that ambient space the source proves the literal identity $D(V)\cap C(T)=D(T)$. If duplicate loads vanish at an omitted vertex, Lemma 6.1 forces every copied coefficient incident with that vertex to vanish. The duplicate representation is consequently supported on $T$. The endpoint is `BodyLoads.duplicate_loads_prefix_identity`.

A hinge requires particular care when its partner is absent from $T$. The prefix load space $C(T)$ is unchanged by moving an omitted vertex, because the forces and moments involve only points of $T$. Move the partner within an open set of generic, general-position placements. The unchanged force at the retained hinge must be parallel to every resulting partner direction, and hence must vanish. This real open-set argument supplies the omitted-partner step without assuming that a chosen basis or virtual centre descends to a smaller coefficient field.

Finite induction now subtracts genuine duplicate-edge modes until every two-body hinge load is zero. Previously normalised hinges stay zero: after each step, the loads are supported outside every cleared vertex. If a new hinge has an already cleared partner, the preceding vanishing lemma applies to this smaller support set. Point-pin loads remain unchanged. Normalisation therefore preserves the actual scalar values at all soft point pins.

The soft-force coefficient functionals span a subspace $U$ of the dual of the ordinary stress space $S(G)$. Define its literal annihilator

$$
K=\{\sigma\in S(G):\varphi(\sigma)=0\text{ for every }\varphi\in U\}.
$$

Rank-nullity gives $\dim S(G)=\dim U+\dim K$. Tetrahedral edge equations connect soft scalars into components. Hypervertices and larger bodies observe specified linear information from those components.

To prove that every component is observed, retain all original bodies and only the selected actual point pins. The resulting pair-pin graph is simple. Original graph motions separate every pair of its distinct bodies, so Theorem 5.1 makes its compatibility rows independent at the simultaneously chosen maximum-rank placement. A balanced load supported on those pins would annihilate the entire output of a surjective operator, and must vanish. Applying this to a putatively unobserved component gives the contradiction.

The resulting covering inequality is

$$
2\dim U\leq\sum_h a_h+\sum_C r_C+z,
$$

where $a_h$ is the actual scalar information readable from the star at $h$, $r_C$ is the actual scalar image rank at a large body, and $z$ counts components with exactly one observer. Such a sole observer is a hypervertex. Each exceptional component supplies a concrete supported stress mode. Its coefficient is read from actual edge coordinates, and its prefix support includes every vertex required by that mode.

## The final dimension account

For a fixed stress subspace $W$, let $\kappa_W(v)$ be its mean supported dimension increase when $v$ enters a uniform vertex order. Supported dimensions telescope in each order. Applying this to $K$ gives the exact identity corresponding to equation (6):

$$
r(G)=\sum_v\left(\frac{d(v)}2-\kappa_K(v)\right)-\dim U.
$$

All quantities here refer to the original graph. In particular, no numerical budget is passed as an additional hypothesis of the main theorem.

At a two-body vertex, normalised prefix loads have zero force at that vertex. Every such balanced local star extends to a local clique stress with the same prefix support. This identifies its stress birth with the sum of the two clique births and gives Lemma 7.1 exactly:

$$
\frac{d(v)}2-\kappa_K(v)
=\left(3-\frac6{|C_1|}\right)
+\left(3-\frac6{|C_2|}\right)
-\frac12\mathbf1_{\text{hinge}}.
$$

Selected five-vertex bodies supply their actual one-dimensional clique stress modes. Biorthogonal coefficient functionals split off precisely the modes available in each prefix. A nonzero such coefficient requires all five vertices of the core to be present. Each vertex is last among those five with probability $1/5$, proved by finite permutation symmetry. Thus equation (7) follows from an exact prefix dimension identity.

At a hypervertex, imposing the scalar equations removes exactly $a_h$ star dimensions; removing the selected core modes removes exactly $g_h$ more. Apply the supported-star bound to the residual space and simplify to obtain equation (8):

$$
\frac{d(h)}2-\kappa_K(h)-3
\geq\frac{a_h}{2}+\frac{3g_h}{10}+\frac{\delta(h)-6}{2}.
$$

The proof uses actual star restrictions and dual annihilators. Readability and mode independence are established from explicit edge coefficients.

For the body account, set $q(m)=3/2-6/m$. The allocation to a body of order $m$ is $q(m)$ at a point pin, $q(m)-1/2$ at a hinge whose other body is a tetrahedron, and $q(m)-1/4$ when both hinge bodies have order at least five. A tetrahedron receives zero in the mixed case. Negative entries, including $q(5)-1/2=-1/5$, are retained. In a selected five-vertex body, the partner of a mixed hinge port is a hypervertex. Otherwise the two hinge endpoints have only five external neighbours, giving a forbidden separator. In particular, a selected five-vertex body with no hypervertices has no such negative ports.

With no hypervertices, the scalar image lies in the kernel of synthesis by the actual wrench columns $(d_v,p_v\times d_v)$. Their rank is at least

$$
\min(p,2)+\mathbf1_{p\geq4},
$$

where $p$ is the number of soft ports. The force-and-moment proof covers parallel axes as well as finite pencils. With a sole hypervertex, taking moments about it gives a nonzero constraint at every soft port, so $r_C+1\leq p$ when $p>0$.

These inequalities pay $r_C/2$ from the body's actual allocations and the selected-core contributions. The remaining shortfalls occur only for selected $K_5$ bodies with one hypervertex, no soft ports, and three or four specified mixed hinge ports. Their charges are respectively $1/4$ and $1/2$. The exceptional-mode and neighbourhood-star estimates give, at each hypervertex,

$$
12+2z_h+b_{3,h}+2b_{4,h}\leq2\delta(h).
$$

Literal finite double counts identify all occurrences of $z_h$, selected core incidences and the two charged-body counts. Combining the body account, this inequality and the observer bound pays the entire scalar rank $\dim U$ from the excess over three per vertex. The exact ledger therefore forces $r(G)\geq3|V|$, contradicting $r(G)\leq3|V|-6$.

`FinalTheorems` chooses the required placement, constructs its actual soft scalar system and applies this contradiction. The closure lemmas then derive both forms of Corollary 1.2.

## A witness for the sharp threshold

The sharpness assertion in the introduction is witnessed by the $t=7$ instance of Jackson--Jordán--Villányi \[2, Example 7.5\]. Arrange seven $K_5$ cells cyclically in each of five rows. Every cell has two left ports, two right ports and a hub. Join its right pair completely to the next cell's left pair; the five hubs in each column form another $K_5$. The graph has $175$ vertices. Every edge lies in a cell $K_5$, a hub $K_5$, or a four-port bridge $K_4$, so every edge is $K_4$-covered.

For every real placement, restriction to the $35$ cell cliques, $7$ hub cliques and $140$ bridge bars gives

$$
r(G)\leq35\cdot9+7\cdot9+140=518.
$$

The complete graph has generic rank $3\cdot175-6=519$. Thus the witness is flexible, by a uniform rank bound rather than a sampled matrix.

After any deletion of at most four vertices, one of the five rows is intact. From each surviving vertex, five prescribed routes lead to the hubs in its own and four neighbouring cells. Outside their common starting vertex, these routes have disjoint supports. At least one route survives. Its terminal hub connects through its column's hub clique to the intact row, whose cells remain connected. This proves five-connectivity for every permitted deletion set. Finite computation is used only for disjointness of the fixed route templates and their small modular identities.

## Sources and source provenance

Caius Folkerts. *Six-connected $K_4$-covered graphs are rigid in three dimensions*. Manuscript, 2 November 2026.

Bill Jackson, Tibor Jordán and Soma Villányi. *Rank Contributions of Vertices in Rigidity Matroids of Clique Covered Graphs*. arXiv:2607.26266v1, 2026.

Dongzhe (Denzel) Zheng. *Stress Degeneracy of Direction Complexes of $(2,2)$-Sparse Graphs and Three-Dimensional Body--Pin Rigidity*. August 2026, DOI 10.13140/RG.2.2.17830.28485. Lean formalisation: source repository, commit

`e457fde9100c9b7226bd4d81af6860f210a531ab`. Adapted source files retain their Apache-2.0 notices.

Bryan Gin-ge Chen. *CombinatorialRigidity*, source repository, commit

`021c2284bc387efee3c3b20a18eb5f769638b578`. Adapted source files retain their Apache-2.0 notices.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.

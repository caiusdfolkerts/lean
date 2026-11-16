# Lean

This repo is home to the Lean formalisations for all my mathematics research. Over the last few months I've written 29 papers in convex geometry, commutative algebra and representation theory using AI. These include a resolution to the [Heine–Shephard problem](volume_polynomials/), and proofs of [Jockusch's 1993 cubical lower bound conjecture](cubical_lower_bound/), the [Hivert–Thiéry conjecture](deformed_coinvariants/) and the [Hanlon–Hicks–Lazarev conjecture](toric_power_maps/).

Descriptions of the papers and their corresponding formalisations, are listed in the table below. For each formalisation, I've also included an index that links all verified statements to their corresponding Lean4 declarations.

I've also made it easy to inspect theorem axioms via the default builds (there are no sorrys or admits in this repo!)

If you find any improvements, please contact me at [caiusdfolkerts@gmail.com](mailto:caiusdfolkerts@gmail.com).

You'll need to install Elan and Git to run the verification.

| Project | Result |
| --- | --- |
| [`alternating_forms`](alternating_forms/) | We determine the Hilbert series of a complex exterior algebra modulo two general quadrics in every dimension. |
| [`barycentric_invariance`](barycentric_invariance/) | Barycentric subdivision preserves the face ring of a finite simplicial poset as a module over its universal parameters. |
| [`bier`](bier/) | We construct the first explicit nonpolytopal Bier spheres. |
| [`cold_spots`](cold_spots/) | The deep holes of E₈ and several related lattices minimise every Gaussian lattice sum. |
| [`conditional_decomposability`](conditional_decomposability/) | A conditionally Minkowski decomposable $d$-polytope needs at least $4d-4$ vertices for every $d\ge3$. |
| [`cubical_lower_bound`](cubical_lower_bound/) | We prove Jockusch’s conjecture that stacked cubical polytopes minimize every face number for their dimension and vertex count. |
| [`deformed_coinvariants`](deformed_coinvariants/) | We prove the Hivert–Thiéry conjecture on deformed coinvariant algebras. |
| [`ellipsoid_intrinsic_volumes`](ellipsoid_intrinsic_volumes/) | The intrinsic volumes of an ellipsoid determine its semiaxes in every dimension. |
| [`two_fermion_coinvariants`](two_fermion_coinvariants/) | Two-coloured lattice paths index monomial bases for the two-fermion coinvariant rings of types A and B. |
| [`homological_shifts`](homological_shifts/) | We give a partition formula for the rank of every homological shift ideal of a polymatroidal ideal. |
| [`clique_covered_rigidity`](clique_covered_rigidity/) | Every six-connected graph whose edges lie in copies of $K_4$ is generically rigid in 3 dimensions. |
| [`mixed_volume_realization`](mixed_volume_realization/) | Mixed volume realisability is undecidable in dimension three; even for rational input data and a fixed input size of 44. |
| [`normal_projective`](normal_projective/) | A combinatorial $d$-cube can be brought to the standard cube in $2d-3$ normal or projective moves for $d\ge2$. |
| [`polymatroidal_ideals`](polymatroidal_ideals/) | A monomial ideal is polymatroidal if and only if every monomial localization has a linear resolution. |
| [`projection_areas`](projection_areas/) | Four-coordinate inequalities characterize coordinate projection areas in dimension four and no longer suffice in every higher dimension. |
| [`toric_quadratic_generation`](toric_quadratic_generation/) | For smooth lattice $d$-polytopes, normality and quadratic generation of the toric ideal both follow when every edge has lattice length at least $d$. |
| [`rank_three_projection_volumes`](rank_three_projection_volumes/) | We negatively answer a question of Huh: for $n \ge 5$, every positive hollow rank-three matrix lies outside the closure of the codimension-two coordinate projection-volume locus. |
| [`higher_specht_bases`](higher_specht_bases/) | We construct higher Specht bases for every Springer and Δ-Springer ring in characteristic zero. |
| [`three_sunlet_models`](three_sunlet_models/) | In every characteristic, the three-sunlet model of a finite abelian group of order $m\ge5$ has dimension $5m-4$. |
| [`symmetric_rank_conditions`](symmetric_rank_conditions/) | The minors defining symmetric northwest rank conditions form a Gröbner basis for the folded antidiagonal order over every field.|
| [`volume_polynomials`](volume_polynomials/) | We resolve the Heine–Shephard problem and prove the volume-polynomial locus is nonsemialgebraic for $n\ge3$ bodies in dimension $d\ge3$. |
| [`graphical_zonotopes`](graphical_zonotopes/) | An indecomposable generalized permutahedron of dimension $n-1\ge3$ has at least $3n-6$ edge directions. |
| [`sublattice_resolutions`](sublattice_resolutions/) | If $I$ has a sublattice initial ideal $J$, equality of the Betti numbers of $I$ and $J$ forces equality for $I^k$ and $J^k$ for every $k\ge1$. |
| [`cubical_indecomposability`](cubical_indecomposability/) | We disprove a conjecture of Smilansky by constructing a Minkowski indecomposable four-polytope whose facets are all combinatorial cubes. |
| [`unimodular`](unimodular/) | Integral facet equations and a single degree condition characterize the complete fans on a uniformly unimodular ray configuration. |
| [`singular_vector_spans`](singular_vector_spans/) | We classify all singular-vector span defects for generic tensors one step beyond boundary format. |
| [`small_nonrational`](small_nonrational/) | The minimum number of vertices of a four-polytope with no rational realization lies between 11 and 17. |
| [`wishart`](wishart/) | We prove the Wishart analogue of the Gaussian product inequality conjectured by Genest, Ouimet and Richards for arbitrarily many disjoint principal minors. |
| [`toric_power_maps`](toric_power_maps/) | We prove the Hanlon–Hicks–Lazarev conjecture on Frobenius generation for line bundles on smooth complex toric varieties. |

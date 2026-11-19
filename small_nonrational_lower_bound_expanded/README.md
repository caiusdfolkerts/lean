# Rational realizations of small four-polytopes

Every full-dimensional real four-polytope with at most ten vertices has a rational realization of its face lattice. The same holds for an eleven-vertex four-polytope with a simple vertex. Together with a seventeen-vertex construction whose field of realization must contain the square root of five, the rationality theorem places the attained minimum size of a nonrational four-polytope between eleven and seventeen vertices.

The statements in `Challenge.lean` use nonempty convex hulls of finite sets of extreme points, their exposed faces ordered by inclusion, and coordinates in the rationals. They correspond to Theorem 2, Corollary 4 and the numerical conclusion of the introduction of the corrected manuscript in `paper.pdf`. The paper proves the lower bound by combining geometric reductions, matrix density theorems and a complete finite treatment of residual types. The corrected exclusions of A40 and crossed two-prism type 1 belong to this last step.

The Lean proof descends from Caius Folkerts' original development. The source index at its pinned commit records the original path and SHA-256 for each named proof module. The package places the modules at their canonical Lean paths. Repeated certificate proofs use named Lean commands with integral parameters. Each command elaborates the original mathematical obligations. Binary numerical data consist of little-endian natural numbers in LZ4 blocks. The graph records index their cells in a shared catalogue and derive the ridge, vertex and edge incidence matrices from the cells. Their values are ordinary Lean constructor applications that enter the same finite checks. The fixed proof templates and all decoders appear as Lean source. [Original proof development and source index](https://github.com/caiusdfolkerts/research/tree/a39e089d37e218063266ecf9b612552741b1ddab/small_nonrational)

For 2,748 graph records the proof uses structural facet certificates. These replace growth-tree replay with a quota-clique exclusion or a checked contradiction using the facet constraints. The remaining records retain their original verification routes.

The rooted-forest and six-base proof families combine sibling modules with matching imports. Their individual declarations retain their names and proof bodies.

Each refutation uses one copy of the initial clauses for the geometric hypotheses and the contradiction proof. The comparison configuration checks the allowed axioms for the three selected results.

The code is licensed under Apache-2.0 and includes polytope foundations by Daniele Cappello. Caius Folkerts retains copyright in the corrected manuscript.

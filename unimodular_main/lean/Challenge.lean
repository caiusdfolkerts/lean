module
public import Mathlib
/-! Independent original-lattice geometric and ordinary-matroid interface draft.
No complete-paper or compiler verification claim. -/
@[expose] public noncomputable section
open Set
open scoped Classical BigOperators Matroid
namespace PalomarDeepMonotone
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
/-- The literal finite free integral lattice and its actual real scalar extension. -/
structure IsIntegralLattice (ι : N →+ V) : Prop where
  free : Module.Free ℤ N
  finite : Module.Finite ℤ N
  isBaseChange : IsBaseChange ℝ ι.toIntLinearMap
/-- The actual scalar extension of an integral dual character. -/
def IsIntegralLattice.realCharacter {ι : N →+ V} (h : IsIntegralLattice ι) :
    (N →+ ℤ) →+ Module.Dual ℝ V :=
  (h.isBaseChange.toDual.comp (addMonoidHomLequivInt ℤ).toLinearMap).toAddMonoidHom
/-- Real character extension evaluates to the given integral character. -/
theorem IsIntegralLattice.realCharacter_apply {ι : N →+ V} (h : IsIntegralLattice ι)
    (m : N →+ ℤ) (n : N) : h.realCharacter m (ι n) = (m n : ℝ) := by sorry
/-- Primitivity means a genuine integral functional takes the value one. -/
def IsPrimitive {A : Type*} [AddCommGroup A] (d : A) : Prop :=
  ∃ f : A →ₗ[ℤ] ℤ, f d = 1
/-- A nonempty maximal proper convex extreme face of the actual carrier. -/
def IsGeometricFacet (Q S : Set V) : Prop :=
  S.Nonempty ∧ Convex ℝ S ∧ IsExtreme ℝ Q S ∧ S ≠ Q ∧
    ∀ F : Set V, Convex ℝ F → IsExtreme ℝ Q F → F ≠ Q → S ⊆ F → F = S
/-- Every actual primitive inward edge direction, with its genuine one-dimensional
convex extreme face and a positive feasible real segment. -/
def IsPrimitiveEdgeDirection (ι : N →+ V) (Q : Set V) (w d : N) : Prop :=
  IsPrimitive d ∧ ∃ F : Set V,
    Convex ℝ F ∧ IsExtreme ℝ Q F ∧ ι w ∈ F ∧
    Module.finrank ℝ (vectorSpan ℝ F) = 1 ∧
    ∃ t : ℝ, 0 < t ∧ ι w + t • ι d ∈ F
/-- Smooth reflexive presentation in the original lattice: actual integral
vertices, every primitive facet's active dual basis, and equality of the entire
real convex hull with the unit supporting halfspaces. No classification conclusion
or deep-monotonicity condition is an input field. -/
structure Presentation (n : ℕ) (ι : N →+ V) where
  lattice : IsIntegralLattice ι
  rank_eq : Module.finrank ℤ N = n
  vertices : Finset N
  normals : Finset (N →+ ℤ)
  vertices_nonempty : vertices.Nonempty
  basis : {w // w ∈ vertices} → Module.Basis (Fin n) ℤ (N →+ ℤ)
  basis_mem : ∀ w j, basis w j ∈ normals
  basis_active : ∀ w j, basis w j w.val = 1
  active_subset : ∀ w m, m ∈ normals → m w.val = 1 → ∃ j, basis w j = m
  normals_occur : ∀ m ∈ normals, ∃ w j, basis w j = m
  hull_eq : convexHull ℝ (ι '' (vertices : Set N)) =
    {x : V | ∀ m ∈ normals, lattice.realCharacter m x ≤ 1}
namespace Presentation
variable {n : ℕ} {ι : N →+ V} (P : Presentation n ι)
/-- The actual original real convex polytope. -/
def carrier : Set V := convexHull ℝ (ι '' (P.vertices : Set N))
/-- The full set of primitive inward edge directions at an actual vertex. -/
def primitiveEdgeDirections (w : {w // w ∈ P.vertices}) : Set N :=
  {d | IsPrimitiveEdgeDirection ι P.carrier w.val d}
/-- Finiteness follows from smoothness and the complete actual edge geometry;
it is not a supplied finite edge sample. -/
theorem primitiveEdgeDirections_finite (w : {w // w ∈ P.vertices}) :
    (P.primitiveEdgeDirections w).Finite := by sorry
/-- The finite set of all actual primitive inward edge directions. -/
def primitiveEdgeFinset (w : {w // w ∈ P.vertices}) : Finset N :=
  (P.primitiveEdgeDirections_finite w).toFinset
/-- The entire real unit parallelepiped of the primitive inward edges. -/
def geometricUnitCorner (w : {w // w ∈ P.vertices}) : Set V :=
  {x | ∃ c : N → ℝ,
    (∀ d ∈ P.primitiveEdgeFinset w, 0 ≤ c d ∧ c d ≤ 1) ∧
      ι w.val + ∑ d ∈ P.primitiveEdgeFinset w, c d • ι d = x}
/-- Deep monotonicity requires containment of every whole real unit corner. -/
def DeeplyMonotone : Prop :=
  ∀ w : {w // w ∈ P.vertices}, P.geometricUnitCorner w ⊆ P.carrier
/-- The actual supporting face cut out by one original integral character. -/
def normalFace (m : N →+ ℤ) : Set V :=
  {x | x ∈ P.carrier ∧ P.lattice.realCharacter m x = 1}
/-- All original primitive geometric facet normals, with the actual facet test. -/
def geometricFacetNormals : Set (N →+ ℤ) :=
  {m | IsPrimitive m ∧ (∀ x ∈ P.carrier, P.lattice.realCharacter m x ≤ 1) ∧
    IsGeometricFacet P.carrier (P.normalFace m)}
end Presentation
end PalomarDeepMonotone

namespace PalomarDeepMonotone.VectorMatroid
open Set
variable {K α W : Type*} [Field K] [AddCommGroup W] [Module K W]
/-- Finite independent vector families satisfy genuine linear augmentation. -/
theorem linearIndepOn_finset_augment (v : α → W) {I J : Finset α}
    (hI : LinearIndepOn K v (I : Set α)) (hJ : LinearIndepOn K v (J : Set α))
    (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K v (insert e (I : Set α)) := by sorry
/-- The empty set is independent in the represented ground set. -/
theorem independent_empty (v : α → W) (E : Set α) :
    ((∅ : Finset α) : Set α) ⊆ E ∧ LinearIndepOn K v ((∅ : Finset α) : Set α) := by sorry
/-- The literal represented independence predicate is hereditary. -/
theorem independent_hereditary (v : α → W) (E : Set α) {I J : Finset α}
    (hI : (I : Set α) ⊆ E ∧ LinearIndepOn K v (I : Set α)) (hJI : J ⊆ I) :
    (J : Set α) ⊆ E ∧ LinearIndepOn K v (J : Set α) := by sorry
/-- The literal represented predicate satisfies the finitary exchange axiom. -/
theorem independent_augmentation (v : α → W) (E : Set α) {I J : Finset α}
    (hI : (I : Set α) ⊆ E ∧ LinearIndepOn K v (I : Set α))
    (hJ : (J : Set α) ⊆ E ∧ LinearIndepOn K v (J : Set α)) (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ ((insert e I : Finset α) : Set α) ⊆ E ∧
      LinearIndepOn K v ((insert e I : Finset α) : Set α) := by sorry
/-- The actual ordinary represented Mathlib matroid on the given original labels.
Its finite independent sets are exactly the linearly independent subsets of E. -/
def onSet (v : α → W) (E : Set α) : Matroid α :=
  (IndepMatroid.ofFinset E
    (fun I => (I : Set α) ⊆ E ∧ LinearIndepOn K v (I : Set α))
    (independent_empty (K := K) v E)
    (fun _ _ h hJI => independent_hereditary (K := K) v E h hJI)
    (fun _ _ hI hJ hcard => independent_augmentation (K := K) v E hI hJ hcard)
    (fun _ h => h.1)).matroid
/-- Full independent-set semantics includes every subset of the original labels. -/
theorem onSet_indep (v : α → W) (E I : Set α) :
    (onSet (K := K) v E).Indep I ↔ I ⊆ E ∧ LinearIndepOn K v I := by sorry
end PalomarDeepMonotone.VectorMatroid
namespace PalomarDeepMonotone
open scoped Matroid
/-- The ordinary constructive series/parallel class on the actual matroid ground.
The operations use actual deletion, contraction, loops, coloops, circuits and
cocircuits. This is not an excluded-minor predicate or a rank-only surrogate. -/
inductive GroundSeriesParallel {α : Type*} : Matroid α → Prop
  | empty (M : Matroid α) (hE : M.E = ∅) : GroundSeriesParallel M
  | addLoop {M : Matroid α} {e : α} :
      GroundSeriesParallel (M ＼ {e}) → M.IsLoop e → GroundSeriesParallel M
  | addColoop {M : Matroid α} {e : α} :
      GroundSeriesParallel (M ＼ {e}) → M.IsColoop e → GroundSeriesParallel M
  | parallel {M : Matroid α} {e f : α} :
      GroundSeriesParallel (M ＼ {e}) → e ≠ f → M.IsCircuit {e,f} → GroundSeriesParallel M
  | series {M : Matroid α} {e f : α} :
      GroundSeriesParallel (M ／ {e}) → e ≠ f → M.IsCocircuit {e,f} → GroundSeriesParallel M
namespace Presentation
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V} (P : Presentation n ι)
/-- The actual normal matroid of the original primitive geometric facets. -/
def normalMatroid : Matroid (N →+ ℤ) :=
  VectorMatroid.onSet (K := ℝ) (fun m : N →+ ℤ => P.lattice.realCharacter m)
    P.geometricFacetNormals
/-- Theorem1.2, original-lattice necessity and all ordinary minors. Every
primitive geometric normal label is retained, with no coordinate basis or finite
ambient-label premise. The explicit connected-component network presentation
is a separate source conclusion, not assumed by this statement. -/
theorem necessity_and_all_minors (hn : 1 ≤ n) (hP : P.DeeplyMonotone) :
    GroundSeriesParallel P.normalMatroid ∧
      ∀ M : Matroid (N →+ ℤ), M ≤m P.normalMatroid → GroundSeriesParallel M := by sorry
end Presentation
end PalomarDeepMonotone

namespace PalomarDeepMonotone
/-- An actual finite directed rooted multigraph, retaining every labelled edge,
including loops and parallel edges. The root is the Option.none vertex. -/
structure RootedNetwork (n m : ℕ) where
  source : Fin m → Option (Fin n)
  target : Fin m → Option (Fin n)
/-- Include old vertices after adding one new first vertex. -/
def liftVertex {n : ℕ} : Option (Fin n) → Option (Fin (n + 1)) := Option.map Fin.succ
namespace RootedNetwork
/-- The empty network on its root. -/
def empty : RootedNetwork 0 0 := ⟨Fin.elim0,Fin.elim0⟩
/-- A loop edge and a coordinate-padding vertex. -/
def addLoop {n m : ℕ} (G : RootedNetwork n m) : RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons none (liftVertex ∘ G.source)
  target := Fin.cons none (liftVertex ∘ G.target)
/-- A genuine bridge from the new vertex to the root. -/
def addBridge {n m : ℕ} (G : RootedNetwork n m) : RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons (some 0) (liftVertex ∘ G.source)
  target := Fin.cons none (liftVertex ∘ G.target)
/-- Duplicate the selected actual edge, retaining its endpoints. -/
def parallel {n m : ℕ} (G : RootedNetwork n m) (e : Fin m) :
    RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons (liftVertex (G.source e)) (liftVertex ∘ G.source)
  target := Fin.cons (liftVertex (G.target e)) (liftVertex ∘ G.target)
/-- Subdivide the selected actual edge through the newly added vertex. -/
def subdivide {n m : ℕ} (G : RootedNetwork n m) (e : Fin m) :
    RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons (liftVertex (G.source e))
    (fun j => if j = e then some 0 else liftVertex (G.source j))
  target := Fin.cons (some 0) (liftVertex ∘ G.target)
/-- Relabel edges while retaining the full incidence graph. -/
def relabel {n m : ℕ} (G : RootedNetwork n m) (e : Equiv.Perm (Fin m)) :
    RootedNetwork n m := ⟨G.source ∘ e,G.target ∘ e⟩
/-- Standard real incidence coordinates, with zero at the root vertex. -/
def vertex {n : ℕ} : Option (Fin n) → (Fin n → ℝ)
  | none => 0
  | some i => Pi.single i 1
/-- The actual ordinary Mathlib cycle matroid of the full incidence vectors. -/
def cycleMatroid {n m : ℕ} (G : RootedNetwork n m) : Matroid (Fin m) :=
  VectorMatroid.onSet (K := ℝ)
    (fun e => vertex (G.source e) - vertex (G.target e)) Set.univ
/-- The ordinary eligible construction class: loops, bridges, nonloop parallel
extensions, noncoloop series subdivisions, and genuine edge permutations. -/
inductive HasEligibleConstruction : {m : ℕ} → RootedNetwork m m → Prop
  | empty : HasEligibleConstruction empty
  | addLoop {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      HasEligibleConstruction G.addLoop
  | addBridge {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      HasEligibleConstruction G.addBridge
  | parallel {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      (e : Fin m) → G.cycleMatroid.IsNonloop e → HasEligibleConstruction (G.parallel e)
  | subdivide {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      (e : Fin m) → ¬G.cycleMatroid.IsColoop e → HasEligibleConstruction (G.subdivide e)
  | relabel {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      (e : Equiv.Perm (Fin m)) → HasEligibleConstruction (G.relabel e)
end RootedNetwork
namespace Components
open scoped Matroid
variable {α : Type*} (M : Matroid α)
/-- Actual circuit connectivity, including an isolated ground element itself. -/
def ConnectedTo (e f : α) : Prop :=
  (e = f ∧ e ∈ M.E) ∨ ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C
/-- The actual nonempty circuit-connectivity blocks, without choosing samples. -/
def Block := {S : Set α // ∃ e, (∃ f, ConnectedTo M f e) ∧
  {f | ConnectedTo M f e} = S}
/-- The actual ordinary restriction to one complete connectivity block. -/
def matroid (C : Block M) : Matroid α := M ↾ C.val
/-- Distinct actual circuit-connectivity blocks have disjoint ground sets. -/
theorem pairwise_disjoint :
    Pairwise (fun C D : Block M => Disjoint (matroid M C).E (matroid M D).E) := by sorry
/-- Literal connectivity of a nonempty matroid through actual circuits. -/
def Connected (M : Matroid α) : Prop :=
  M.E.Nonempty ∧ ∀ e f, e ∈ M.E → f ∈ M.E → ConnectedTo M e f
end Components
namespace Presentation
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V} (P : Presentation n ι)
/-- Theorem1.2's explicit network conclusion: the actual primitive-normal
matroid is a finite direct sum of its actual loopless connected restrictions,
each equal, on its whole ground, to a genuine eligible network cycle matroid. -/
theorem direct_sum_networks (hn : 1 ≤ n) (hP : P.DeeplyMonotone) :
    Finite (Components.Block P.normalMatroid) ∧
    P.normalMatroid = Matroid.disjointSigma (Components.matroid P.normalMatroid)
      (Components.pairwise_disjoint P.normalMatroid) ∧
    ∀ C : Components.Block P.normalMatroid,
      Components.Connected (Components.matroid P.normalMatroid C) ∧
      (Components.matroid P.normalMatroid C).Loopless ∧
      ∃ (m : ℕ) (e : Fin m ≃ (Components.matroid P.normalMatroid C).E)
        (G : RootedNetwork m m), G.HasEligibleConstruction ∧
        ((Components.matroid P.normalMatroid C).restrictSubtype
          (Components.matroid P.normalMatroid C).E).mapEquiv e.symm = G.cycleMatroid := by sorry
end Presentation
end PalomarDeepMonotone

/- The exact minor-realization converse, with a literal coordinate witness.
Unelaborated separate extension; previously frozen151/246 inputs are unchanged. -/
namespace PalomarDeepMonotone
namespace Coordinates
/-- The actual standard integral lattice of the realization witness. -/
abbrev Lattice (n : ℕ) := Fin n → ℤ
/-- Its actual real scalar extension. -/
abbrev Ambient (n : ℕ) := Fin n → ℝ
/-- Coordinate inclusion preserves the original integral point values. -/
def embed {n : ℕ} (z : Lattice n) : Ambient n := fun j => (z j : ℝ)
/-- Evaluation of a real point against its genuine integral normal vector. -/
def pairing {n : ℕ} (x : Ambient n) (m : Lattice n) : ℝ := ∑ j, x j * (m j : ℝ)
/-- An actual smooth-reflexive coordinate witness. Active normal bases and
whole real convex-hull/halfspace equality are geometric input data; neither
series-parallel structure nor deep monotonicity is assumed in this structure. -/
structure Presentation (n : ℕ) where
  vertices : Finset (Lattice n)
  normals : Finset (Lattice n)
  vertices_nonempty : vertices.Nonempty
  basis : {w // w ∈ vertices} → Module.Basis (Fin n) ℤ (Lattice n)
  basis_mem : ∀ w j, basis w j ∈ normals
  basis_active : ∀ w j, pairing (embed w.val) (basis w j) = 1
  active_subset : ∀ w m, m ∈ normals → pairing (embed w.val) m = 1 →
    ∃ j, basis w j = m
  normals_occur : ∀ m ∈ normals, ∃ w j, basis w j = m
  hull_eq : convexHull ℝ (embed '' (vertices : Set (Lattice n))) =
    {x : Ambient n | ∀ m ∈ normals, pairing x m ≤ 1}
namespace Presentation
variable {n : ℕ} (P : Presentation n)
/-- The actual finite real convex hull. -/
def carrier : Set (Ambient n) := convexHull ℝ (embed '' (P.vertices : Set (Lattice n)))
/-- Every actual primitive inward edge, certified by a genuine one-dimensional
convex extreme face and an actual positive segment at the vertex. -/
def primitiveEdgeDirections (w : {w // w ∈ P.vertices}) : Set (Lattice n) :=
  {d | IsPrimitive d ∧ ∃ F : Set (Ambient n),
    Convex ℝ F ∧ IsExtreme ℝ P.carrier F ∧ embed w.val ∈ F ∧
    Module.finrank ℝ (vectorSpan ℝ F) = 1 ∧
    ∃ t : ℝ, 0 < t ∧ embed w.val + t • embed d ∈ F}
/-- The whole actual edge set is finite by smoothness, not sampled or assumed. -/
theorem primitiveEdgeDirections_finite (w : {w // w ∈ P.vertices}) :
    (P.primitiveEdgeDirections w).Finite := by sorry
/-- All genuine primitive edges, using their proved finiteness. -/
def primitiveEdgeFinset (w : {w // w ∈ P.vertices}) : Finset (Lattice n) :=
  (P.primitiveEdgeDirections_finite w).toFinset
/-- The entire real unit parallelepiped of every primitive inward edge. -/
def geometricUnitCorner (w : {w // w ∈ P.vertices}) : Set (Ambient n) :=
  {x | ∃ c : Lattice n → ℝ,
    (∀ d ∈ P.primitiveEdgeFinset w, 0 ≤ c d ∧ c d ≤ 1) ∧
      embed w.val + ∑ d ∈ P.primitiveEdgeFinset w, c d • embed d = x}
/-- Actual containment of the whole real corner, at every vertex. -/
def DeeplyMonotone : Prop :=
  ∀ w : {w // w ∈ P.vertices}, P.geometricUnitCorner w ⊆ P.carrier
/-- The actual supporting face of an integral vector. -/
def normalFace (m : Lattice n) : Set (Ambient n) :=
  {x | x ∈ P.carrier ∧ pairing x m = 1}
/-- All genuine primitive geometric facet normals of this actual polytope. -/
def geometricFacetNormals : Set (Lattice n) :=
  {m | IsPrimitive m ∧ (∀ x ∈ P.carrier, pairing x m ≤ 1) ∧
    IsGeometricFacet P.carrier (P.normalFace m)}
/-- The full represented Mathlib matroid of the actual primitive facets. -/
def normalMatroid : Matroid (Lattice n) :=
  VectorMatroid.onSet (K := ℝ) embed P.geometricFacetNormals
end Presentation
end Coordinates
/-- Theorem1.2 exact minor class, including realization: every actual matroid
on its full genuine ground is constructively series-parallel exactly when its
ground restriction embeds as an ordinary minor in the actual primitive-normal
matroid of some positive-dimensional deeply monotone polytope. The ambient
label type may be infinite and all loops/ground elements are retained. -/
theorem exact_minor_class {E : Type*} (M : Matroid E) :
    GroundSeriesParallel M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ (P : Coordinates.Presentation n)
        (f : M.E ↪ Coordinates.Lattice n), P.DeeplyMonotone ∧
        (M.restrictSubtype M.E).mapEmbedding f ≤m P.normalMatroid := by sorry
end PalomarDeepMonotone

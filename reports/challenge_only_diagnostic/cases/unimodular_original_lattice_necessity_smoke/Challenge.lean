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
    ((∅ : Finset α) : Set α) ⊆ E ∧ LinearIndepOn K v (∅ : Set α) := by sorry
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
    (independent_empty v E)
    (fun _ _ h hJI => independent_hereditary v E h hJI)
    (fun _ _ hI hJ hcard => independent_augmentation v E hI hJ hcard)
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

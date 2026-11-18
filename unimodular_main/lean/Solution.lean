module
public import Mathlib
public import Unimodular.SeriesParallelClassification
public import Continuation.Geometry.OriginalPolytopeMatroid
public import Continuation.Geometry.OriginalPolytopeNetworks
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
    (m : N →+ ℤ) (n : N) : h.realCharacter m (ι n) = (m n : ℝ) := by
  simpa [IsIntegralLattice.realCharacter] using h.isBaseChange.toDual_comp_apply m.toIntLinearMap n
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
end Presentation
end PalomarDeepMonotone
namespace PalomarDeepMonotone.Bridge
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V}
/-- The same actual scalar-extension lattice, in the retained source vocabulary. -/
def sourceLattice (h : IsIntegralLattice ι) : TauCeti.Toric.IsIntegralLattice ι :=
  ⟨h.free,h.finite,h.isBaseChange⟩
/-- Uniqueness of scalar extension identifies the actual integral pairings;
no unfolding of an unexposed canonical character definition is needed. -/
theorem character_agrees (h : IsIntegralLattice ι) :
    h.realCharacter = (sourceLattice h).realCharacter := by
  apply AddMonoidHom.ext
  intro m
  exact (sourceLattice h).eq_realCharacter (fun z => h.realCharacter_apply m z)
/-- All geometric presentation fields are retained literally. -/
def sourcePresentation (P : Presentation n ι) : Unimodular.OriginalSmoothReflexivePresentation n ι where
  lattice := sourceLattice P.lattice
  rank_eq := P.rank_eq
  vertices := P.vertices
  normals := P.normals
  vertices_nonempty := P.vertices_nonempty
  basis := P.basis
  basis_mem := P.basis_mem
  basis_active := P.basis_active
  active_subset := P.active_subset
  normals_occur := P.normals_occur
  hull_eq := by
    rw [P.hull_eq]
    rw [← character_agrees]

theorem carrier_agrees (P : Presentation n ι) :
    P.carrier = (sourcePresentation P).carrier := by rfl

theorem edges_agree (P : Presentation n ι) (w : {w // w ∈ P.vertices}) :
    P.primitiveEdgeDirections w = (sourcePresentation P).primitiveEdgeDirections w := by
  ext d
  simp only [Presentation.primitiveEdgeDirections,
    Unimodular.OriginalSmoothReflexivePresentation.primitiveEdgeDirections,
    IsPrimitiveEdgeDirection, Unimodular.OriginalPolytopeTransport.IsPrimitiveEdgeDirection,
    IsPrimitive, TauCeti.isPrimitive_def, Set.mem_setOf_eq, carrier_agrees]

end PalomarDeepMonotone.Bridge
namespace PalomarDeepMonotone.Presentation
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V} (P : Presentation n ι)
/-- Finiteness follows from smoothness and the complete actual edge geometry;
it is not a supplied finite edge sample. -/
theorem primitiveEdgeDirections_finite (w : {w // w ∈ P.vertices}) :
    (P.primitiveEdgeDirections w).Finite := by
  rw [Bridge.edges_agree]
  exact (Bridge.sourcePresentation P).primitiveEdgeDirections_finite w
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

namespace PalomarDeepMonotone.Bridge
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V}
theorem edge_finsets_agree (P : Presentation n ι) (w : {w // w ∈ P.vertices}) :
    P.primitiveEdgeFinset w = (sourcePresentation P).primitiveEdgeFinset w := by
  apply Finset.coe_injective
  simp only [Presentation.primitiveEdgeFinset,
    Unimodular.OriginalSmoothReflexivePresentation.primitiveEdgeFinset,
    Set.Finite.coe_toFinset]
  exact edges_agree P w

theorem corners_agree (P : Presentation n ι) (w : {w // w ∈ P.vertices}) :
    P.geometricUnitCorner w = (sourcePresentation P).geometricUnitCorner w := by
  unfold Presentation.geometricUnitCorner
    Unimodular.OriginalSmoothReflexivePresentation.geometricUnitCorner
  rw [edge_finsets_agree]

theorem deeplyMonotone_agrees (P : Presentation n ι) :
    P.DeeplyMonotone ↔ (sourcePresentation P).DeeplyMonotone := by
  simp only [Presentation.DeeplyMonotone,
    Unimodular.OriginalSmoothReflexivePresentation.DeeplyMonotone,
    corners_agree, carrier_agrees]
  rfl

theorem facet_normals_agree (P : Presentation n ι) :
    P.geometricFacetNormals = (sourcePresentation P).geometricFacetNormals := by
  ext m
  simp only [Presentation.geometricFacetNormals,
    Unimodular.OriginalSmoothReflexivePresentation.geometricFacetNormals,
    Unimodular.OriginalSmoothReflexivePresentation.IsFacet,
    Presentation.normalFace, Unimodular.OriginalSmoothReflexivePresentation.normalFace,
    IsGeometricFacet, Unimodular.OriginalPolytopeTransport.IsGeometricFacet,
    IsPrimitive, TauCeti.isPrimitive_def, Set.mem_setOf_eq, carrier_agrees, character_agrees]
end PalomarDeepMonotone.Bridge

namespace PalomarDeepMonotone.VectorMatroid
open Set
variable {K α W : Type*} [Field K] [AddCommGroup W] [Module K W]
/-- Finite independent vector families satisfy genuine linear augmentation. -/
theorem linearIndepOn_finset_augment (v : α → W) {I J : Finset α}
    (hI : LinearIndepOn K v (I : Set α)) (hJ : LinearIndepOn K v (J : Set α))
    (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K v (insert e (I : Set α)) := by
  exact Unimodular.VectorMatroid.linearIndepOn_finset_augment v hI hJ hcard
/-- The empty set is independent in the represented ground set. -/
theorem independent_empty (v : α → W) (E : Set α) :
    ((∅ : Finset α) : Set α) ⊆ E ∧ LinearIndepOn K v ((∅ : Finset α) : Set α) := by
  simp
/-- The literal represented independence predicate is hereditary. -/
theorem independent_hereditary (v : α → W) (E : Set α) {I J : Finset α}
    (hI : (I : Set α) ⊆ E ∧ LinearIndepOn K v (I : Set α)) (hJI : J ⊆ I) :
    (J : Set α) ⊆ E ∧ LinearIndepOn K v (J : Set α) := by
  exact ⟨(Finset.coe_subset.2 hJI).trans hI.1, hI.2.mono (Finset.coe_subset.2 hJI)⟩
/-- The literal represented predicate satisfies the finitary exchange axiom. -/
theorem independent_augmentation (v : α → W) (E : Set α) {I J : Finset α}
    (hI : (I : Set α) ⊆ E ∧ LinearIndepOn K v (I : Set α))
    (hJ : (J : Set α) ⊆ E ∧ LinearIndepOn K v (J : Set α)) (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ ((insert e I : Finset α) : Set α) ⊆ E ∧
      LinearIndepOn K v ((insert e I : Finset α) : Set α) := by
  obtain ⟨e,heJ,heI,hli⟩ := linearIndepOn_finset_augment v hI.2 hJ.2 hcard
  refine ⟨e,heJ,heI,?_,?_⟩
  · simpa only [Finset.coe_insert] using (Set.insert_subset (hJ.1 heJ) hI.1)
  · simpa only [Finset.coe_insert] using hli
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
    (onSet (K := K) v E).Indep I ↔ I ⊆ E ∧ LinearIndepOn K v I := by
  change (∀ J : Finset α, (J : Set α) ⊆ I →
    (J : Set α) ⊆ E ∧ LinearIndepOn K v (J : Set α)) ↔ _
  constructor
  · intro h
    refine ⟨?_,linearIndepOn_of_finite I ?_⟩
    · intro e he
      exact (h {e} (by simpa using he)).1 (by simp)
    · intro J hJI hJ
      simpa only [Set.Finite.coe_toFinset] using
        (h hJ.toFinset (by simpa only [Set.Finite.coe_toFinset] using hJI)).2
  · rintro ⟨hIE,hli⟩ J hJI
    exact ⟨hJI.trans hIE,hli.mono hJI⟩
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
end Presentation
end PalomarDeepMonotone

namespace PalomarDeepMonotone.Bridge
open scoped Matroid
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V}

theorem onSet_agrees {K α W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (v : α → W) (E : Set α) :
    VectorMatroid.onSet (K := K) v E = Unimodular.VectorMatroid.onSet (K := K) v E := by
  apply Matroid.ext_indep rfl
  intro I hI
  exact (VectorMatroid.onSet_indep v E I).trans
    (Unimodular.VectorMatroid.onSet_indep v E I).symm

theorem normalMatroid_agrees (P : Presentation n ι) :
    P.normalMatroid = (sourcePresentation P).normalMatroid := by
  unfold Presentation.normalMatroid Unimodular.OriginalSmoothReflexivePresentation.normalMatroid
  rw [facet_normals_agree, character_agrees]
  exact onSet_agrees _ _

theorem groundSeriesParallel_agrees {α : Type*} (M : Matroid α) :
    GroundSeriesParallel M ↔ Unimodular.SeriesParallel.GroundSeriesParallel M := by
  constructor
  · intro h
    induction h with
    | empty M hE => exact .empty M hE
    | addLoop _ he ih => exact .addLoop ih he
    | addColoop _ he ih => exact .addColoop ih he
    | parallel _ hne hc ih => exact .parallel ih hne hc
    | series _ hne hc ih => exact .series ih hne hc
  · intro h
    induction h with
    | empty M hE => exact .empty M hE
    | addLoop _ he ih => exact .addLoop ih he
    | addColoop _ he ih => exact .addColoop ih he
    | parallel _ hne hc ih => exact .parallel ih hne hc
    | series _ hne hc ih => exact .series ih hne hc
end PalomarDeepMonotone.Bridge

namespace PalomarDeepMonotone.Presentation
open scoped Matroid
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V} (P : Presentation n ι)
/-- Theorem1.2, original-lattice necessity and all ordinary minors. Every
primitive geometric normal label is retained, with no coordinate basis or finite
ambient-label premise. The explicit connected-component network presentation
is a separate source conclusion, not assumed by this statement. -/
theorem necessity_and_all_minors (hn : 1 ≤ n) (hP : P.DeeplyMonotone) :
    GroundSeriesParallel P.normalMatroid ∧
      ∀ M : Matroid (N →+ ℤ), M ≤m P.normalMatroid → GroundSeriesParallel M := by
  have h := (Bridge.sourcePresentation P).theorem_1_2_original_lattice hn
    ((Bridge.deeplyMonotone_agrees P).mp hP)
  refine ⟨(Bridge.groundSeriesParallel_agrees _).mpr ?_,?_⟩
  · rw [Bridge.normalMatroid_agrees]
    exact h.1
  · intro M hM
    apply (Bridge.groundSeriesParallel_agrees M).mpr
    exact h.2 M (by rwa [← Bridge.normalMatroid_agrees])
end PalomarDeepMonotone.Presentation

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
    Pairwise (fun C D : Block M => Disjoint (matroid M C).E (matroid M D).E) := by
  exact Unimodular.SeriesParallel.NetworkComponents.pairwise_disjoint M
/-- Literal connectivity of a nonempty matroid through actual circuits. -/
def Connected (M : Matroid α) : Prop :=
  M.E.Nonempty ∧ ∀ e f, e ∈ M.E → f ∈ M.E → ConnectedTo M e f
end Components
namespace Presentation
universe u v
variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℝ V]
  {n : ℕ} {ι : N →+ V} (P : Presentation n ι)
end Presentation
end PalomarDeepMonotone

/- Actual rooted-network incidence and eligibility transports; unelaborated. -/
namespace PalomarDeepMonotone.Bridge
/-- Preserve both actual endpoint functions and every original edge label. -/
def sourceNetwork {n m : ℕ} (G : RootedNetwork n m) :
    Unimodular.SeriesParallel.RootedNetwork n m := ⟨G.source,G.target⟩
/-- The inverse literal endpoint conversion. -/
def freshNetwork {n m : ℕ} (G : Unimodular.SeriesParallel.RootedNetwork n m) :
    RootedNetwork n m := ⟨G.source,G.target⟩
/-- Real incidence vectors agree coordinatewise with the actual integral-basis
incidence representation, hence their whole ordinary cycle matroids agree. -/
theorem cycleMatroid_agrees {n m : ℕ} (G : RootedNetwork n m) :
    G.cycleMatroid = (sourceNetwork G).cycleMatroid := by
  unfold RootedNetwork.cycleMatroid
    Unimodular.SeriesParallel.RootedNetwork.cycleMatroid
    Unimodular.VectorMatroid.ofFamily
  rw [onSet_agrees]
  apply congrArg (fun f : Fin m → (Fin n → ℝ) =>
    Unimodular.VectorMatroid.onSet (K := ℝ) f Set.univ)
  funext e j
  cases hs : G.source e <;> cases ht : G.target e <;>
    simp [RootedNetwork.vertex,sourceNetwork,Unimodular.embed,
      Unimodular.Graphic.vertex,Pi.basisFun_apply,Pi.single_apply,hs,ht]

theorem eligible_to_source {m : ℕ} {G : RootedNetwork m m}
    (h : G.HasEligibleConstruction) : (sourceNetwork G).HasEligibleConstruction := by
  induction h with
  | empty => exact .empty
  | addLoop h ih => exact .addLoop ih
  | addBridge h ih => exact .addBridge ih
  | @parallel m G h e he ih =>
    exact .parallel ih e (by rwa [← cycleMatroid_agrees])
  | @subdivide m G h e he ih =>
    exact .subdivide ih e (by rwa [← cycleMatroid_agrees])
  | relabel h e ih => exact .relabel ih e

theorem eligible_from_source {m : ℕ} {G : Unimodular.SeriesParallel.RootedNetwork m m}
    (h : G.HasEligibleConstruction) : (freshNetwork G).HasEligibleConstruction := by
  induction h with
  | empty => exact .empty
  | addLoop h ih => exact .addLoop ih
  | addBridge h ih => exact .addBridge ih
  | @parallel m G h e he ih =>
    exact .parallel ih e (by rwa [cycleMatroid_agrees])
  | @subdivide m G h e he ih =>
    exact .subdivide ih e (by rwa [cycleMatroid_agrees])
  | relabel h e ih => exact .relabel ih e
end PalomarDeepMonotone.Bridge

namespace PalomarDeepMonotone.Presentation
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
          (Components.matroid P.normalMatroid C).E).mapEquiv e.symm = G.cycleMatroid := by
  have h := (Bridge.sourcePresentation P).theorem_1_2_original_lattice_direct_sum_networks
    hn ((Bridge.deeplyMonotone_agrees P).mp hP)
  rw [← Bridge.normalMatroid_agrees] at h
  refine ⟨h.1,h.2.1,?_⟩
  intro C
  obtain ⟨hconn,hloop,m,e,G,helig,heq⟩ := h.2.2 C
  have connected : Components.Connected (Components.matroid P.normalMatroid C) := by
    obtain ⟨z,hz⟩ := hconn.nonempty
    refine ⟨⟨z,hz⟩,?_⟩
    intro x y hx hy
    exact hconn.forall_connectedTo hx hy
  refine ⟨connected,hloop,m,e,Bridge.freshNetwork G,
    Bridge.eligible_from_source helig,?_⟩
  rw [Bridge.cycleMatroid_agrees]
  exact heq
end PalomarDeepMonotone.Presentation

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
end Presentation
end Coordinates
end PalomarDeepMonotone
/- Exact coordinate realization witness and full geometric matroid transport.
Unelaborated source work, separate from the frozen151/246 candidates. -/
namespace PalomarDeepMonotone.Bridge
/-- Copy every actual coordinate vertex, normal, active integral basis and
real convex-hull equality into the retained smooth-reflexive presentation. -/
def sourceCoordinate {n : ℕ} (P : Coordinates.Presentation n) :
    Unimodular.SmoothReflexivePresentation n where
  vertices := P.vertices
  normals := P.normals
  vertices_nonempty := P.vertices_nonempty
  basis := P.basis
  basis_mem := P.basis_mem
  basis_active := P.basis_active
  active_subset := P.active_subset
  normals_occur := P.normals_occur
  hull_eq := P.hull_eq
/-- An actual source coordinate polytope supplies exactly the same literal
geometric data; no realization or cohomology certificate is added as a field. -/
def freshCoordinate {n : ℕ} (P : Unimodular.SmoothReflexivePresentation n) :
    Coordinates.Presentation n where
  vertices := P.vertices
  normals := P.normals
  vertices_nonempty := P.vertices_nonempty
  basis := P.basis
  basis_mem := P.basis_mem
  basis_active := P.basis_active
  active_subset := P.active_subset
  normals_occur := P.normals_occur
  hull_eq := P.hull_eq

theorem source_fresh_coordinate {n : ℕ} (P : Unimodular.SmoothReflexivePresentation n) :
    sourceCoordinate (freshCoordinate P) = P := by
  cases P
  rfl

theorem coordinate_carrier_agrees {n : ℕ} (P : Coordinates.Presentation n) :
    P.carrier = (sourceCoordinate P).carrier := by rfl

theorem coordinate_edges_agree {n : ℕ} (P : Coordinates.Presentation n)
    (w : {w // w ∈ P.vertices}) :
    P.primitiveEdgeDirections w = (sourceCoordinate P).primitiveEdgeDirections w := by
  ext d
  simp only [Coordinates.Presentation.primitiveEdgeDirections,
    Unimodular.SmoothReflexivePresentation.primitiveEdgeDirections,
    Unimodular.primitiveLatticeVector_iff_isPrimitive, TauCeti.isPrimitive_def,
    IsPrimitive, Set.mem_setOf_eq, coordinate_carrier_agrees]
  rfl

end PalomarDeepMonotone.Bridge
namespace PalomarDeepMonotone
namespace Coordinates
namespace Presentation
variable {n : ℕ} (P : Presentation n)
/-- The whole actual edge set is finite by smoothness, not sampled or assumed. -/
theorem primitiveEdgeDirections_finite (w : {w // w ∈ P.vertices}) :
    (P.primitiveEdgeDirections w).Finite := by
  rw [Bridge.coordinate_edges_agree]
  exact (Bridge.sourceCoordinate P).primitiveEdgeDirections_finite w
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
end PalomarDeepMonotone
namespace PalomarDeepMonotone.Bridge
theorem coordinate_finsets_agree {n : ℕ} (P : Coordinates.Presentation n)
    (w : {w // w ∈ P.vertices}) :
    P.primitiveEdgeFinset w = (sourceCoordinate P).primitiveEdgeFinset w := by
  apply Finset.coe_injective
  simp only [Coordinates.Presentation.primitiveEdgeFinset,
    Unimodular.SmoothReflexivePresentation.primitiveEdgeFinset, Set.Finite.coe_toFinset]
  exact coordinate_edges_agree P w

theorem coordinate_corners_agree {n : ℕ} (P : Coordinates.Presentation n)
    (w : {w // w ∈ P.vertices}) :
    P.geometricUnitCorner w = (sourceCoordinate P).geometricUnitCorner w := by
  unfold Coordinates.Presentation.geometricUnitCorner
    Unimodular.SmoothReflexivePresentation.geometricUnitCorner
  rw [coordinate_finsets_agree]
  rfl

theorem coordinate_deeplyMonotone_agrees {n : ℕ} (P : Coordinates.Presentation n) :
    P.DeeplyMonotone ↔ (sourceCoordinate P).DeeplyMonotone := by
  simp only [Coordinates.Presentation.DeeplyMonotone,
    Unimodular.SmoothReflexivePresentation.DeeplyMonotone,
    coordinate_corners_agree, coordinate_carrier_agrees]
  rfl

theorem coordinate_facet_normals_agree {n : ℕ} (P : Coordinates.Presentation n) :
    P.geometricFacetNormals = (sourceCoordinate P).geometricFacetNormals := by
  ext m
  simp only [Coordinates.Presentation.geometricFacetNormals,
    Unimodular.SmoothReflexivePresentation.geometricFacetNormals,
    Coordinates.Presentation.normalFace, Unimodular.SmoothReflexivePresentation.normalFace,
    IsGeometricFacet, Unimodular.SmoothReflexivePresentation.IsFacet,
    IsPrimitive, Unimodular.primitiveLatticeVector_iff_isPrimitive,
    TauCeti.isPrimitive_def, Set.mem_setOf_eq, coordinate_carrier_agrees]
  rfl

/-- The actual geometric normal matroid equals the source's listed-normal
presentation only after the genuine facet-exhaustiveness theorem is used. -/
theorem coordinate_normalMatroid_agrees {n : ℕ} (P : Coordinates.Presentation n) :
    P.normalMatroid = Unimodular.VectorMatroid.onSet (K := ℝ)
      (Unimodular.embed : Unimodular.Lattice n → Unimodular.Ambient n)
      ((sourceCoordinate P).normals : Set (Unimodular.Lattice n)) := by
  unfold Coordinates.Presentation.normalMatroid
  rw [coordinate_facet_normals_agree,
    (sourceCoordinate P).geometricFacetNormals_eq_normals, onSet_agrees]
  rfl
end PalomarDeepMonotone.Bridge

namespace PalomarDeepMonotone
open scoped Matroid
/-- Theorem1.2 exact minor class, including realization: every actual matroid
on its full genuine ground is constructively series-parallel exactly when its
ground restriction embeds as an ordinary minor in the actual primitive-normal
matroid of some positive-dimensional deeply monotone polytope. The ambient
label type may be infinite and all loops/ground elements are retained. -/
theorem exact_minor_class {E : Type*} (M : Matroid E) :
    GroundSeriesParallel M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ (P : Coordinates.Presentation n)
        (f : M.E ↪ Coordinates.Lattice n), P.DeeplyMonotone ∧
        (M.restrictSubtype M.E).mapEmbedding f ≤m P.normalMatroid := by
  constructor
  · intro hM
    obtain ⟨n,hn,Q,f,hQ,hminor⟩ :=
      (Unimodular.SeriesParallel.groundSeriesParallel_iff_normalMatroid_minor M).mp
        ((Bridge.groundSeriesParallel_agrees M).mp hM)
    refine ⟨n,hn,Bridge.freshCoordinate Q,f,?_,?_⟩
    · apply (Bridge.coordinate_deeplyMonotone_agrees _).mpr
      simpa only [Bridge.source_fresh_coordinate] using hQ
    · rw [Bridge.coordinate_normalMatroid_agrees, Bridge.source_fresh_coordinate]
      exact hminor
  · rintro ⟨n,hn,P,f,hP,hminor⟩
    apply (Bridge.groundSeriesParallel_agrees M).mpr
    apply (Unimodular.SeriesParallel.groundSeriesParallel_iff_normalMatroid_minor M).mpr
    refine ⟨n,hn,Bridge.sourceCoordinate P,f,
      (Bridge.coordinate_deeplyMonotone_agrees P).mp hP,?_⟩
    rwa [← Bridge.coordinate_normalMatroid_agrees]
end PalomarDeepMonotone

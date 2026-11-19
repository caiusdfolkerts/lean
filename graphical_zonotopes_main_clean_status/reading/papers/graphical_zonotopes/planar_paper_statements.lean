module

public import Papers.GraphicalZonotopes.PlanarApexSeparation
public import Papers.GraphicalZonotopes.PlanarK33
public import Papers.GraphicalZonotopes.PlanarComponentDimension
public import Papers.GraphicalZonotopes.StackedTriangulation
public import Papers.GraphicalZonotopes.PolytopalDimension
public import Papers.GraphicalZonotopes.SeparatorPaperStatements

/-! # The planar classification and complete dimension spectrum

Planarity means an injective placement in the Euclidean plane with arbitrary
simple continuous edge arcs meeting only at shared endpoints. The geometric
obstructions are proved from that definition. No Euler inequality, forbidden
minor characterization, or straight-line realization is a premise here.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- On distinct actual four-cliques, the formal overlap threshold is
exactly the paper's adjacency relation of sharing a triangle. -/
theorem TetrahedronComponents.adj_iff_shared_triangle (G : SimpleGraph V)
    (C D : {C : Finset V // C ∈ tetrahedra G}) :
    (tetrahedronGraph (tetrahedra G)).Adj C D ↔ (C.1 ∩ D.1).card = 3 := by
  have hC : C.1.card = 4 := (Finset.mem_filter.mp C.2).2.1
  have hD : D.1.card = 4 := (Finset.mem_filter.mp D.2).2.1
  constructor
  · intro h
    have hle := Finset.card_le_card (Finset.inter_subset_left : C.1 ∩ D.1 ⊆ C.1)
    have hne : (C.1 ∩ D.1).card ≠ 4 := by
      intro he
      have hleft : C.1 ∩ D.1 = C.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      have hright : C.1 ∩ D.1 = D.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by omega)
      exact h.1 (Subtype.ext (hleft.symm.trans hright))
    have hlo := h.2
    omega
  · intro h
    refine ⟨?_,by omega⟩
    intro he
    have hv := congrArg Subtype.val he
    rw [hv,Finset.inter_self,hD] at h
    omega

theorem HasPlaneDrawing.maximum_dimension {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) :
    maximumIndecomposableDimension G = planarComponentDimension G := by
  have hs := hG.triangle_apex_separated
  exact hs.piecewise_maximum.trans
    (planarComponentDimension_eq_partialThreeTreeDimension hs hG.admissible).symm

theorem HasPlaneDrawing.full_polytopal_iff_threeTree {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (hn : 4 ≤ Fintype.card V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G := by
  rw [← supportsFullIndecomposable_iff_polytopal_weak]
  exact hG.triangle_apex_separated.supports_full_iff_threeTree hn hG.admissible

theorem HasPlaneDrawing.isStackedTriangulation_iff_threeTree {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : IsStackedTriangulation G ↔ IsThreeTree G := by
  rw [isStackedTriangulation_iff]
  exact ⟨fun h => h.1,fun h => ⟨h,hG.triangleMultiplicity_le_two⟩⟩

theorem HasPlaneDrawing.lattice_full_witness {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (ht : IsThreeTree G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by
  obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_witness_fintype ht hG.admissible
  have hQ := hfi.basePolytope hf.1.1 hf.2.1
  have hw := (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hfg
  exact ⟨basePolytope f,hQ,
    (weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp
      hf.minkowskiIndecomposable,hfd,hw,hfa⟩

theorem HasPlaneDrawing.full_lattice_spectrum {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ planarComponentDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  obtain ⟨Q,hQ,hi,hw,hD⟩ := hG.triangle_apex_separated.full_dimension_spectrum
    d hd (by rwa [hG.maximum_dimension])
  exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hD⟩

/-- Corollary 6.4 for every finite simple planar graph on at least four
vertices. The chosen vertex order is internal coordinate infrastructure,
not an additional assumption on the graph or its drawing. -/
theorem paper_corollary_6_4 {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G) := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  exact fun G hG hn => hG.full_polytopal_iff_threeTree hn

/-- The same classification with the paper's explicit stacked-triangulation
formulation: tetrahedral boundary faces are built by repeated one-to-three
face replacements, as certified by the independent boundary dictionary. -/
theorem paper_corollary_6_4_stacked {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsStackedTriangulation G) := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  intro G hG hn
  exact (hG.full_polytopal_iff_threeTree hn).trans hG.isStackedTriangulation_iff_threeTree.symm

/-- The lattice witness in the converse of the planar classification has
exactly the original graph as its actual exposed-edge direction graph. -/
theorem planar_threeTree_lattice_witness_finite {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → IsThreeTree G →
      ∃ Q : Set (W → ℝ),LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  exact fun G hG ht => hG.lattice_full_witness ht

/-- Corollary 6.5 with the literal maximum over the connected components of
the graph of all tetrahedra, and every positive dimension through that maximum.
The fallback values are exactly two for triangles, one for edges, and zero
for edgeless graphs. Both the supremum and witnesses use ordinary polytopal
Minkowski indecomposability. -/
theorem paper_corollary_6_5 {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G →
      (sSup {d : ℕ | ∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d}) = planarComponentDimension G ∧
      ∀ d : ℕ,1 ≤ d → d ≤ planarComponentDimension G →
        ∃ Q : Set (W → ℝ),LatticePolytope Q ∧
          PolytopalMinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  intro G hG
  refine ⟨?_,fun d hd hm => hG.full_lattice_spectrum d hd hm⟩
  rw [← maximumIndecomposableDimension_eq_polytopal_supremum]
  exact hG.maximum_dimension

end GraphicalZonotopes

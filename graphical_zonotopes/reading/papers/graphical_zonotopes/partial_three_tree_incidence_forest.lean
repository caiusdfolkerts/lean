module

public import Papers.GraphicalZonotopes.PartialThreeTreeGraph
public import Papers.GraphicalZonotopes.ThreeTreeIncidenceTree
public import Papers.GraphicalZonotopes.ThreeTreeSharedEdges

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangles_mono_graph {G H : SimpleGraph V} (h : G ≤ H) :
    triangles G ⊆ triangles H := by
  intro T hT
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  exact mem_triangles.mpr ⟨hc,fun u hu v hv huv => h (hcl hu hv huv)⟩

/-- The inclusion of a graph into a supergraph induces an actual injective
map of all its tetrahedron and triangle incidence nodes. -/
def incidenceHomOfLE {G H : SimpleGraph V} (h : G ≤ H) :
    cliqueTriangleIncidence G →g cliqueTriangleIncidence H where
  toFun := Sum.map (fun C => ⟨C.1,tetrahedra_mono h C.2⟩)
    (fun T => ⟨T.1,triangles_mono_graph h T.2⟩)
  map_rel' := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy

theorem incidenceHomOfLE_injective {G H : SimpleGraph V} (h : G ≤ H) :
    Function.Injective (incidenceHomOfLE h) := by
  apply Sum.map_injective.mpr
  constructor
  · intro C D he
    exact Subtype.ext (congrArg (fun E : {E : Finset V // E ∈ tetrahedra H} => E.1) he)
  · intro C D he
    exact Subtype.ext (congrArg (fun E : {E : Finset V // E ∈ triangles H} => E.1) he)

/-- The structural assertion in Corollary 6.8: the intrinsic incidence graph
of every partial three-tree is a forest, including all small-vertex cases.
No tree completion is part of the resulting graph or of its definition. -/
theorem IsPartialThreeTree.incidence_isAcyclic {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) : (cliqueTriangleIncidence G).IsAcyclic := by
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hno : ∀ C : {C : Finset V // C ∈ tetrahedra G},False := by
      intro C
      have hfour : C.1.card = 4 := (mem_filter.mp C.2).2.1
      have hle := card_le_card (subset_univ C.1)
      rw [card_univ,hfour] at hle
      omega
    have hbot : cliqueTriangleIncidence G = ⊥ := by
      ext x y
      cases x with
      | inl C => exact (hno C).elim
      | inr T =>
        cases y with
        | inl C => exact (hno C).elim
        | inr U => rfl
    rw [hbot]
    exact SimpleGraph.isAcyclic_bot
  · exact hH.incidence_isTree.isAcyclic.comap
      (incidenceHomOfLE hGH) (incidenceHomOfLE_injective hGH)

end GraphicalZonotopes

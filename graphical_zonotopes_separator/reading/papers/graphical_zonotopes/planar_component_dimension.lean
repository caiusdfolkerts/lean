module

public import Papers.GraphicalZonotopes.PlanarAnalyticSpectrum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

namespace TetrahedronComponents

/-- The actual connected components of the graph of all tetrahedra, with
adjacency given by sharing a triangle. -/
abbrev Component (G : SimpleGraph V) :=
  (tetrahedronGraph (tetrahedra G)).ConnectedComponent

def family (G : SimpleGraph V) (c : Component G) : Finset (Finset V) :=
  (tetrahedra G).filter (fun C => ∃ hC : C ∈ tetrahedra G,
    (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c)

@[simp] theorem mem_family (G : SimpleGraph V) (c : Component G) (C : Finset V) :
    C ∈ family G c ↔ ∃ hC : C ∈ tetrahedra G,
      (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c := by
  simp only [family,mem_filter]
  exact ⟨fun h => h.2,fun ⟨hC,h⟩ => ⟨hC,hC,h⟩⟩

theorem family_subset (G : SimpleGraph V) (c : Component G) :
    family G c ⊆ tetrahedra G := filter_subset _ _

theorem family_nonempty (G : SimpleGraph V) (c : Component G) : (family G c).Nonempty := by
  obtain ⟨C,hC⟩ := c.exists_rep
  exact ⟨C.1,(mem_family G c C.1).mpr ⟨C.2,hC⟩⟩

theorem family_connected (G : SimpleGraph V) (c : Component G) :
    (tetrahedronGraph (family G c)).Preconnected := by
  let f : c.toSimpleGraph →g tetrahedronGraph (family G c) :=
    { toFun := fun C => ⟨C.1.1,(mem_family G c C.1.1).mpr ⟨C.1.2,C.2⟩⟩
      map_rel' := by
        intro C D hCD
        change (tetrahedronGraph (tetrahedra G)).Adj C.1 D.1 at hCD
        refine ⟨?_,hCD.2⟩
        intro he
        have heval : C.1.1 = D.1.1 := congrArg
          (fun E : {E : Finset V // E ∈ family G c} => E.1) he
        exact hCD.1 (Subtype.ext heval) }
  intro A B
  obtain ⟨hA,hAc⟩ := (mem_family G c A.1).mp A.2
  obtain ⟨hB,hBc⟩ := (mem_family G c B.1).mp B.2
  exact ((c.connected_toSimpleGraph).preconnected
    ⟨⟨A.1,hA⟩,hAc⟩ ⟨⟨B.1,hB⟩,hBc⟩).map f

/-- Every nonempty connected collection is contained in one actual component
of the graph of all tetrahedra, rather than an arbitrary chosen enlargement. -/
theorem connected_family_subset_component (G : SimpleGraph V) (F : Finset (Finset V))
    (hne : F.Nonempty) (hsub : F ⊆ tetrahedra G)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ∃ c : Component G,F ⊆ family G c := by
  obtain ⟨A,hA⟩ := hne
  let f : tetrahedronGraph F →g tetrahedronGraph (tetrahedra G) :=
    { toFun := fun C => ⟨C.1,hsub C.2⟩
      map_rel' := by
        intro C D hCD
        refine ⟨?_,hCD.2⟩
        intro he
        have heval : C.1 = D.1 := congrArg
          (fun E : {E : Finset V // E ∈ tetrahedra G} => E.1) he
        exact hCD.1 (Subtype.ext heval) }
  let c : Component G := (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨A,hsub hA⟩
  refine ⟨c,?_⟩
  intro C hC
  apply (mem_family G c C).mpr
  refine ⟨hsub hC,?_⟩
  exact SimpleGraph.ConnectedComponent.sound ((hconn ⟨C,hC⟩ ⟨A,hA⟩).map f)

theorem family_admissible {G : SimpleGraph V} (hA : Admissible G) (c : Component G) :
    IsAdmissibleCliqueCollection G (family G c) := by
  refine ⟨family_nonempty G c,family_subset G c,family_connected G c,?_⟩
  intro T hT
  by_cases hcT : G.IsClique T
  · exact (card_le_card (filter_subset_filter _ (family_subset G c))).trans (hA T hT hcT)
  · have hempty : (family G c).filter (fun C => T ⊆ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hCF,hTC⟩ := mem_filter.mp hC
      have hcl := (mem_filter.mp (family_subset G c hCF)).2.2
      exact hcT (fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv)
    rw [hempty,card_empty]
    omega

/-- The exact vertex set denoted V(C) in Corollary 6.5. -/
def vertices (G : SimpleGraph V) (c : Component G) : Finset V := (family G c).biUnion id

theorem vertices_card {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    (hA : Admissible G) (c : Component G) :
    (vertices G c).card = (family G c).card + 3 :=
  ((family_admissible hA c).induced_structure_of_apex_separated hG).2.2.2

/-- Maximum of |V(C)|−1 over the actual triangle-adjacency components of
all four-cliques. The empty maximum is zero. -/
def maximumDimension (G : SimpleGraph V) : ℕ :=
  (univ : Finset (Component G)).sup (fun c => (vertices G c).card - 1)

/-- The component formula in the planar corollary is exactly equal to the
admissible-collection formula, with equivalence proved rather than stipulated. -/
theorem maximumDimension_eq {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    (hA : Admissible G) (hK : (tetrahedra G).Nonempty) :
    maximumDimension G = maximumAdmissibleCliqueCount G + 2 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro c _
    have hc := vertices_card hG hA c
    have hm := admissibleClique_count_le_maximum (family_admissible hA c)
    omega
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨c,hFc⟩ := connected_family_subset_component G F hF.nonempty hF.included hF.connected
    have hcard := card_le_card hFc
    have hc := vertices_card hG hA c
    have hm : (vertices G c).card - 1 ≤ maximumDimension G := by
      unfold maximumDimension
      exact Finset.le_sup (f := fun c : Component G => (vertices G c).card - 1) (mem_univ c)
    omega

end TetrahedronComponents

/-- The literal piecewise formula of Corollary 6.5, using actual connected
components of the tetrahedron graph, followed by triangles, edges, and zero. -/
def planarComponentDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then TetrahedronComponents.maximumDimension G
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0

theorem planarComponentDimension_eq_partialThreeTreeDimension {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hA : Admissible G) :
    planarComponentDimension G = partialThreeTreeDimension G := by
  unfold planarComponentDimension partialThreeTreeDimension
  split_ifs with hK hT hE
  · exact TetrahedronComponents.maximumDimension_eq hG hA hK
  all_goals rfl

end GraphicalZonotopes

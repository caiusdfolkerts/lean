module

public import Papers.GraphicalZonotopes.ThreeTreeKernelColumns

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem adjacent_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    {C D : Finset V} (hCD : (TriangleComponents.cliqueGraph G).Adj C D) :
    mobius f C=mobius f D := by
  obtain ⟨T,hTsub,hTcard⟩:=exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C:=hTsub.trans inter_subset_left
  have hTD : T⊆D:=hTsub.trans inter_subset_right
  have hC : C∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hCD.1,hCD.2.2.1⟩
  have hD : D∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hCD.2.1,hCD.2.2.2.1⟩
  have hT:=internal_triangle_of_shared hC hD hCD.2.2.2.2.1 hTcard hTC hTD
  exact incident_clique_scales_equal h s hn hf ⟨T,hT⟩ ⟨⟨C,hC⟩,hTC⟩ ⟨⟨D,hD⟩,hTD⟩

/-- Every actual tetrahedral coefficient of a tight variation is a common
real scalar. Propagation uses paths in the graph of all actual tetrahedra,
not a selected subfamily. -/
theorem all_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f) :
    ∃ a : ℝ,∀ C∈tetrahedra G,mobius f C=a := by
  obtain ⟨C₀,hC₀⟩:=h.tetrahedra_nonempty
  refine ⟨mobius f C₀,?_⟩
  intro C hC
  have hp:=h.tetrahedra_reachable hC hC₀
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  induction hp with
  | refl => rfl
  | @tail D E hD hDE ih =>
    have hmD : D ∈ tetrahedra G := mem_filter.mpr ⟨mem_univ _,hDE.1,hDE.2.2.1⟩
    exact (ih hmD).trans (adjacent_clique_scales_equal h s hn hf hDE)

theorem triangle_coefficient_of_good_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a)
    (T : ↥(triangles G)) (j : ↥T.1) (hg : GoodPair G (T.1.erase j.1)) :
    mobius f T.1=a*coefficients h s T.1 := by
  classical
  let E:=T.1.erase j.1
  have hEcard : E.card=2 := by
    dsimp only [E]
    rw [card_erase_of_mem j.2,(mem_triangles.mp T.2).1]
  have hE : E∈edgeFamily G:= (mem_edgeFamily G E).mpr ⟨hEcard,
    fun u hu v hv huv => (mem_triangles.mp T.2).2
      (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv⟩
  have hjE : j.1∉E:=notMem_erase _ _
  have he : T.1=insert j.1 E := (insert_erase j.2).symm
  have hlin:=good_pair_linear_relation h s hn hf E hE hg j.1 hjE
  rw [← he] at hlin
  have hcol:=weighted_column_eq_sum_pairLinear G s (fun C => mobius f C.1)
    E hEcard j.1 hjE T.1 T.2 he j.2
  rw [← hcol] at hlin
  have hweights : ∀ C : AllIncidentClique G T,mobius f C.1.1=a:=fun C => ha C.1.1 C.1.2
  simp_rw [hweights] at hlin
  rw [← mul_sum] at hlin
  change mobius f T.1= -(a*columnValue G s T j) at hlin
  rw [column_eq_triangleWeight h s T j] at hlin
  rw [coefficients_triangle h s T.2,hlin]
  ring

/-- If the 3-tree has at least two tetrahedra, every triangle contains a
good edge. For a leaf triangle, use its intersection with an internal face
of its unique incident tetrahedron. -/
theorem triangle_has_good_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hm : 2≤(tetrahedra G).card) (T : ↥(triangles G)) :
    ∃ j : ↥T.1,GoodPair G (T.1.erase j.1) := by
  classical
  by_cases hT : T.1∈internalTriangles G
  · obtain ⟨w,hw⟩:=card_pos.mp (by rw [(mem_triangles.mp T.2).1]; decide)
    exact ⟨⟨w,hw⟩,goodPair_of_internalTriangle G ⟨T.1,hT⟩ _ (erase_subset _ _)⟩
  · obtain ⟨C,hC,hTC⟩:=h.triangle_extends (mem_triangles.mp T.2).1 (mem_triangles.mp T.2).2
    obtain ⟨D,hD,hDC⟩:=exists_mem_ne (show 1<(tetrahedra G).card by omega) C
    obtain ⟨F,hF,hEF,hFC⟩:=h.shared_face_containing hC hD hDC.symm
      (E:=∅) (empty_subset _) (empty_subset _)
    have hFcard:=(mem_triangles.mp (mem_internalTriangles.mp hF).1).1
    obtain ⟨r,hr⟩:=exists_opposite (mem_filter.mp hC).2.1 hFcard hFC
    have hrT : r.1∈T.1 := by
      by_contra hrT
      have hTF : T.1⊆F := by
        rw [← hr]
        intro w hw
        exact mem_erase.mpr ⟨fun he => hrT (he ▸ hw),hTC hw⟩
      have he : T.1=F:=eq_of_subset_of_card_le hTF (by
        rw [(mem_triangles.mp T.2).1,hFcard])
      exact hT (he.symm ▸ hF)
    refine ⟨⟨r.1,hrT⟩,goodPair_of_internalTriangle G ⟨F,hF⟩ _ ?_⟩
    simpa only [← hr] using erase_subset_erase r.1 hTC

theorem all_triangle_coefficients_scaled {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    {f : SetFunction V} (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a) :
    ∀ T∈triangles G,mobius f T=a*coefficients h s T := by
  intro T hT
  obtain ⟨j,hj⟩:=triangle_has_good_pair h hm ⟨T,hT⟩
  exact triangle_coefficient_of_good_pair h s hn hf a ha ⟨T,hT⟩ j hj

end ThreeTreeStates
end GraphicalZonotopes

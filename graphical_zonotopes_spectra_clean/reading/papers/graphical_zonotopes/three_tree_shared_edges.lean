module

public import Papers.GraphicalZonotopes.PrunedIncidence

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tetrahedra_mono {G H : SimpleGraph V} (h : G≤H) :
    tetrahedra G⊆tetrahedra H := by
  classical
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  exact mem_filter.mpr ⟨mem_univ _,hc,fun u hu v hv huv => h (hcl hu hv huv)⟩

theorem triangleMultiplicity_mono {G H : SimpleGraph V} (h : G≤H) (T : Finset V) :
    triangleMultiplicity G T≤triangleMultiplicity H T := by
  classical
  apply card_le_card
  intro C hC
  obtain ⟨hC,hTC⟩ := mem_filter.mp hC
  exact mem_filter.mpr ⟨tetrahedra_mono h hC,hTC⟩

theorem internalTriangles_mono {G H : SimpleGraph V} (h : G≤H) :
    internalTriangles G⊆internalTriangles H := by
  intro T hT
  obtain ⟨hT,hcount⟩ := mem_internalTriangles.mp hT
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  exact mem_internalTriangles.mpr
    ⟨mem_triangles.mpr ⟨hc,fun u hu v hv huv => h (hcl hu hv huv)⟩,
      hcount.trans (triangleMultiplicity_mono h T)⟩

/-- A running-intersection consequence for all actual tetrahedra: if two
distinct cliques contain a set E, the first clique has a shared triangular
face containing E. In particular, an edge contained in several tetrahedra
meets an internal face at every tetrahedron containing it. -/
theorem ThreeTreeOn.shared_face_containing {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C D E : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) (hCD : C≠D)
    (hEC : E⊆C) (hED : E⊆D) :
    ∃ T∈internalTriangles G,E⊆T ∧ T⊆C := by
  classical
  induction h generalizing C D E with
  | tetrahedron A hA =>
    rw [tetrahedra_cliqueGraph hA,mem_singleton] at hC hD
    exact False.elim (hCD (hC.trans hD.symm))
  | @attach S G h u hu A hA hAS hcA ih =>
    let H := G⊔attachmentStar u A
    have hmono : G≤H := le_sup_left
    obtain ⟨K,hK,hAK⟩ := h.triangle_extends hA hcA
    have hnew : insert u A∈tetrahedra H := by
      rw [tetrahedra_after_attachment h hu hA hAS hcA]
      exact mem_insert_self _ _
    have hnewK : insert u A≠K := by
      intro he
      apply attached_tetrahedron_not_old h hu (T := A)
      simpa only [he] using hK
    have hshared : A∈internalTriangles H := internal_triangle_of_shared hnew
      (tetrahedra_mono hmono hK) hnewK hA (subset_insert _ _) hAK
    have hav : ∀ L∈tetrahedra G,u∉L := by
      intro L hL hum
      have hc := (mem_filter.mp hL).2
      exact hu (h.clique_subset_active (by omega) hc.2 hum)
    have hsubsetA : ∀ L∈tetrahedra G,E⊆L → E⊆insert u A → E⊆A := by
      intro L hL hEL hEN v hv
      rcases mem_insert.mp (hEN hv) with he | hvA
      · exact False.elim (hav L hL (he ▸ hEL hv))
      · exact hvA
    rw [tetrahedra_after_attachment h hu hA hAS hcA] at hC hD
    rcases mem_insert.mp hC with hC | hC
    · subst C
      rcases mem_insert.mp hD with hD | hD
      · exact False.elim (hCD hD.symm)
      · exact ⟨A,hshared,hsubsetA D hD hED hEC,subset_insert _ _⟩
    · rcases mem_insert.mp hD with hD | hD
      · subst D
        have hEA : E⊆A := hsubsetA C hC hEC hED
        by_cases hCK : C=K
        · exact ⟨A,hshared,hEA,by simpa only [hCK] using hAK⟩
        · obtain ⟨T,hT,hET,hTC⟩ := ih hC hK hCK hEC (hEA.trans hAK)
          exact ⟨T,internalTriangles_mono hmono hT,hET,hTC⟩
      · obtain ⟨T,hT,hET,hTC⟩ := ih hC hD hCD hEC hED
        exact ⟨T,internalTriangles_mono hmono hT,hET,hTC⟩

end GraphicalZonotopes

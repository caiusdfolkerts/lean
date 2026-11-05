import bier.inverse_stellar
import bier.isolated_data
import bier.nonpolytopal_examples

/-! The exact all-labels-present nonpolytopal example, using actual inverse stacking. -/
noncomputable section
namespace Bier
namespace Complex
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isolated_bier_nonpolytopal (K : Complex V) (hK : K.Proper)
    (hc : 2 ≤ Fintype.card V) (hv : ∃ w, K.face {w})
    (hn : ¬ Polytopal (K.ghost.bier K.ghost_proper)) :
    ¬ Polytopal (K.isolatedExtension.bier (K.isolatedExtension_proper hK)) := by
  apply (K.isolated_stellarData hK hc).not_polytopal_stellar ?_ hn
  obtain ⟨w, hw⟩ := hv
  refine ⟨Sum.inl (some w), K.ghost_bier_x_vertex hw, ?_⟩
  simp [ghostTopFace]

end Complex

theorem allLabelsSphere_nonpolytopal : ¬ Polytopal allLabelsSphere := by
  apply Complex.isolated_bier_nonpolytopal principalCore principalCore_proper
    (by simp [Fintype.card_sum]) ?_ principalSphere_nonpolytopal
  have hn : Nonempty (Fin 20 ⊕ Fin 145162) := inferInstance
  obtain ⟨w⟩ := hn
  refine ⟨w, ?_⟩
  rw [← Complex.mem_vertices, principalCore_vertices]
  exact Finset.mem_univ _

theorem all_labels_example :
    allLabelsInput.vertices = Finset.univ ∧ allLabelsInput.dimension = 9 ∧
    allLabelsSphere.vertices = Finset.univ ∧ allLabelsSphere.vertices.card = 290366 ∧
    allLabelsSphere.dimension = 145181 ∧ allLabelsSphere.IsSphere 145181 ∧
    ¬ Polytopal allLabelsSphere :=
  ⟨allLabelsInput_all_vertices, allLabelsInput_dimension, allLabelsSphere_all_vertices,
    allLabelsSphere_vertex_count, allLabelsSphere_dimension, allLabelsSphere_isSphere,
    allLabelsSphere_nonpolytopal⟩

end Bier

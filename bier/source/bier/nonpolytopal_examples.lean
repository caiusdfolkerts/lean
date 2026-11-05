import bier.obstruction
import bier.construction_data
import bier.spectral_example
import bier.self_dual_nonpolytopal
import bier.self_dual_dimension

/-! # The explicit nonpolytopal Bier spheres and the universal all-sign construction -/

noncomputable section

namespace Bier

variable {U R C : Type*} [Fintype U] [Fintype R] [Fintype C]
  [DecidableEq U] [DecidableEq R] [DecidableEq C]

theorem signComplex_bier_nonpolytopal (k : ℕ) (hk : 0 < k)
    (hkm : k < Fintype.card U) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (hinj : Function.Injective S)
    (H : Matrix R C ℝ) (hH : IsSignMatrix H)
    (hrank : Fintype.card U ^ 2 - Fintype.card U + 1 < signRank H) :
    ¬ Polytopal (ghostBier (signComplex k S hS H)) := by
  intro hP
  have hv : ∀ v, (signComplex k S hS H).face {v} := by
    intro v
    rw [← Complex.mem_vertices, signComplex_all_vertices k hk S hS H]
    exact Finset.mem_univ _
  have hbound := ghost_signRank_bound_fixedCard (signComplex k S hS H)
    (signComplex_proper k hkm S hS H) hv S k hk hS
    (fun r => signComplex_core k S hS H (S r) (by rw [hS])) H hH
    (fun r c => (signComplex_selected k S hS hinj H r c).symm) hP
  exact (not_le_of_gt hrank) hbound

theorem principalSphere_nonpolytopal : ¬ Polytopal principalSphere := by
  apply signComplex_bier_nonpolytopal 9 (by norm_num) (by norm_num)
    principalRows principalRows_card principalRows_injective principalSigns principalSigns_sign
  simpa using principalSigns_signRank_gt

theorem principal_example :
    principalInput.dimension = 9 ∧ principalSphere.IsSphere 145181 ∧
      principalSphere.dimension = 145181 ∧ principalSphere.vertices.card = 290365 ∧
        ¬ Polytopal principalSphere :=
  ⟨principalInput_dimension, principalSphere_isSphere, principalSphere_dimension,
    principalSphere_vertex_count, principalSphere_nonpolytopal⟩

theorem patternSphere_nonpolytopal (m k r : ℕ) (h : r + 1 ≤ m.choose k)
    (hk : 0 < k) (hkm : k < m) (hr : m ^ 2 - m + 1 < r + 1) :
    ¬ Polytopal (patternSphere m k r h) := by
  apply signComplex_bier_nonpolytopal k hk (by simpa using hkm)
    (patternRows m k r h) (patternRows_card m k r h) (patternRows_injective m k r h)
    (allColumnSigns (Fin r)) (allColumnSigns_sign (Fin r))
  simpa [allColumnSigns_signRank] using hr

theorem threeDimensionalSphere_nonpolytopal : ¬ Polytopal threeDimensionalSphere :=
  patternSphere_nonpolytopal 9 3 73 enough_triples (by norm_num) (by norm_num) (by norm_num)

theorem three_dimensional_example :
    threeDimensionalInput.dimension = 3 ∧
      threeDimensionalSphere.IsSphere (2 ^ 73 + 8) ∧
      threeDimensionalSphere.dimension = 2 ^ 73 + 8 ∧
      threeDimensionalSphere.vertices.card = 2 ^ 74 + 19 ∧
      ¬ Polytopal threeDimensionalSphere :=
  ⟨threeDimensionalInput_dimension, threeDimensionalSphere_isSphere,
    threeDimensionalSphere_dimension, threeDimensionalSphere_vertex_count,
    threeDimensionalSphere_nonpolytopal⟩

/-- The final paragraph of Section 4.3, with the complete parameter range. -/
theorem general_allSign_construction (m k : ℕ) (hk : 1 ≤ k) (hkm : k < m)
    (hchoose : m ^ 2 - m + 2 ≤ m.choose k) :
    ∃ h : (m ^ 2 - m + 1) + 1 ≤ m.choose k,
      (patternInput m k (m ^ 2 - m + 1) h).dimension = k ∧
      (patternSphere m k (m ^ 2 - m + 1) h).IsSphere
        (m + 2 ^ (m ^ 2 - m + 1) - 1) ∧
      (patternSphere m k (m ^ 2 - m + 1) h).vertices.card =
        2 * (m + 2 ^ (m ^ 2 - m + 1)) + 1 ∧
      ¬ Polytopal (patternSphere m k (m ^ 2 - m + 1) h) := by
  have h : (m ^ 2 - m + 1) + 1 ≤ m.choose k := by omega
  exact ⟨h, patternInput_dimension _ _ _ _, patternSphere_isSphere _ _ _ _,
    patternSphere_vertex_count _ _ _ _ hk hkm,
    patternSphere_nonpolytopal _ _ _ _ hk hkm (by omega)⟩

def selfDualInput := principalCore.selfDualSuspension

def selfDualSphere := selfDualInput.bier principalCore.selfDualSuspension_proper

theorem selfDualInput_dual (F : Finset ((Fin 20 ⊕ Fin 145162) ⊕ Bool)) :
    (selfDualInput.dual principalCore.selfDualSuspension_proper).face F ↔
      selfDualInput.face F := principalCore.selfDualSuspension_dual F

theorem selfDualSphere_vertex_count : selfDualSphere.vertices.card = 290368 := by
  simpa [selfDualSphere, selfDualInput, Fintype.card_sum] using
    principalCore.selfDualSuspension_bier_vertices_card principalCore_proper

theorem selfDualSphere_isSphere : selfDualSphere.IsSphere 145182 := by
  simpa [selfDualSphere, selfDualInput, Fintype.card_sum] using
    principalCore.selfDualSuspension_bier_isSphere

theorem selfDualSphere_dimension : selfDualSphere.dimension = 145182 := by
  simpa [selfDualSphere, selfDualInput, Fintype.card_sum] using
    principalCore.selfDualSuspension_bier_dimension

theorem selfDualSphere_centrallySymmetric : selfDualSphere.IsCentrallySymmetric :=
  principalCore.selfDualSuspension_bier_centrallySymmetric

theorem selfDualSphere_nonpolytopal : ¬ Polytopal selfDualSphere := by
  exact principalCore.selfDualSuspension_nonpolytopal principalCore_proper
    (by simp [Fintype.card_sum]) principalSphere_nonpolytopal

theorem self_dual_example :
    (∀ F, (selfDualInput.dual principalCore.selfDualSuspension_proper).face F ↔
      selfDualInput.face F) ∧
      selfDualSphere.IsSphere 145182 ∧ selfDualSphere.dimension = 145182 ∧
      selfDualSphere.vertices.card = 290368 ∧ selfDualSphere.IsCentrallySymmetric ∧
      ¬ Polytopal selfDualSphere :=
  ⟨selfDualInput_dual, selfDualSphere_isSphere, selfDualSphere_dimension,
    selfDualSphere_vertex_count, selfDualSphere_centrallySymmetric, selfDualSphere_nonpolytopal⟩

end Bier

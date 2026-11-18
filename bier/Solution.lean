module
public import bier
@[expose] public section
noncomputable section
open scoped Classical
namespace PalomarBier
open Bier
/-- Theorem 1 principal example, including the original ghost label. The Solution
supplies the concrete principalInput from the manuscript's explicit matrices. -/
theorem principal_example :
    ∃ I : Complex (Option (Fin 20 ⊕ Fin 145162)), ∃ hI : I.Proper,
      ¬ I.face {none} ∧ I.dimension = 9 ∧ (I.bier hI).IsSphere 145181 ∧
      (I.bier hI).dimension = 145181 ∧ (I.bier hI).vertices.card = 290365 ∧
      ¬ Polytopal (I.bier hI) := by
  refine ⟨Bier.principalInput, Bier.principalCore.ghost_proper, ?_, Bier.principal_example⟩
  simp [Bier.principalInput, Bier.Complex.ghost]
/-- Theorem 1 with all labels actual vertices of both input and Bier sphere. -/
theorem all_labels_example :
    ∃ I : Complex (Option (Fin 20 ⊕ Fin 145162)), ∃ hI : I.Proper,
      I.vertices = Finset.univ ∧ I.dimension = 9 ∧
      (I.bier hI).vertices = Finset.univ ∧ (I.bier hI).vertices.card = 290366 ∧
      (I.bier hI).dimension = 145181 ∧ (I.bier hI).IsSphere 145181 ∧
      ¬ Polytopal (I.bier hI) := by
  exact ⟨Bier.allLabelsInput,
    Bier.principalCore.isolatedExtension_proper Bier.principalCore_proper,
    Bier.all_labels_example⟩
/-- Theorem 1 with a self-dual input and centrally symmetric Bier sphere. -/
theorem self_dual_example :
    ∃ I : Complex ((Fin 20 ⊕ Fin 145162) ⊕ Bool), ∃ hI : I.Proper,
      (∀ F, (I.dual hI).face F ↔ I.face F) ∧
      (I.bier hI).IsSphere 145182 ∧ (I.bier hI).dimension = 145182 ∧
      (I.bier hI).vertices.card = 290368 ∧ (I.bier hI).IsCentrallySymmetric ∧
      ¬ Polytopal (I.bier hI) := by
  exact ⟨Bier.selfDualInput, Bier.principalCore.selfDualSuspension_proper,
    Bier.self_dual_example⟩
/-- Theorem 1 with input dimension three and the exact stated output counts. -/
theorem three_dimensional_example :
    ∃ I : Complex (Option (Fin 9 ⊕ (Fin 73 → Fin 2))), ∃ hI : I.Proper,
      I.dimension = 3 ∧ (I.bier hI).IsSphere (2 ^ 73 + 8) ∧
      (I.bier hI).dimension = 2 ^ 73 + 8 ∧ (I.bier hI).vertices.card = 2 ^ 74 + 19 ∧
      ¬ Polytopal (I.bier hI) := by
  exact ⟨Bier.threeDimensionalInput,
    (Bier.patternCore 9 3 73 Bier.enough_triples).ghost_proper,
    Bier.three_dimensional_example⟩
/-- The final construction for the full binomial-inequality parameter range. -/
theorem general_allSign_construction_unrestricted (m k : ℕ)
    (hchoose : m ^ 2 - m + 2 ≤ m.choose k) :
    ∃ I : Complex (Option (Fin m ⊕ (Fin (m ^ 2 - m + 1) → Fin 2))), ∃ hI : I.Proper,
      I.dimension = k ∧ (I.bier hI).IsSphere (m + 2 ^ (m ^ 2 - m + 1) - 1) ∧
      (I.bier hI).vertices.card = 2 * (m + 2 ^ (m ^ 2 - m + 1)) + 1 ∧
      ¬ Polytopal (I.bier hI) := by
  obtain ⟨h, hdim, hsphere, hvertices, hnon⟩ :=
    Bier.general_allSign_construction_unrestricted m k hchoose
  exact ⟨Bier.patternInput m k (m ^ 2 - m + 1) h,
    (Bier.patternCore m k (m ^ 2 - m + 1) h).ghost_proper,
    hdim, hsphere, hvertices, hnon⟩
end PalomarBier

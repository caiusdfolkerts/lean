import bier.self_dual
import bier.facets

/-! The dimension of the self-dual Bier construction as an actual face maximum. -/
noncomputable section
namespace Bier.Complex
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem selfDualSuspension_bier_dimension (K : Complex V) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).dimension = Fintype.card V := by
  let A : Finset (V ⊕ Bool) := Finset.univ.disjSum ∅
  let B : Finset (V ⊕ Bool) := {Sum.inr false}
  have hA : K.selfDualSuspension.face A := by simp [selfDualSuspension, A]
  have hB : K.selfDualSuspension.face B := by
    simpa [selfDualSuspension, B] using K.empty
  have hface : (K.selfDualSuspension.bier K.selfDualSuspension_proper).face (A.disjSum B) := by
    rw [bier_face_iff]
    simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
    refine ⟨hA, (K.selfDualSuspension_dual B).mpr hB, ?_⟩
    simp [A, B]
  have hcard : (A.disjSum B).card = Fintype.card V + 1 := by simp [A, B]
  have hlo := (K.selfDualSuspension.bier K.selfDualSuspension_proper).card_le_maxFaceCard hface
  rw [hcard] at hlo
  have hhi : (K.selfDualSuspension.bier K.selfDualSuspension_proper).maxFaceCard ≤
      Fintype.card V + 1 := by
    apply maxFaceCard_le
    intro s hs
    have h := K.selfDualSuspension.bier_card_lt K.selfDualSuspension_proper hs
    simp only [Fintype.card_sum, Fintype.card_bool] at h
    omega
  have heq := Nat.le_antisymm hhi hlo
  simp [dimension, heq]

end Bier.Complex

import bier.explicit_ordering
import bier.forster.hadamard

/-! # The strict numerical sign-rank obstruction in the principal example -/

noncomputable section

namespace Bier

theorem principalSigns_signRank_square : 145162 ≤ (signRank principalSigns) ^ 2 := by
  let e : Fin 145162 ↪ Fin 147456 := {
    toFun := Fin.castLE (by norm_num)
    inj' := by
      intro i j h
      exact Fin.ext (congrArg (fun z : Fin 147456 => z.val) h) }
  have h := Forster.hadamard_columnRestriction_signRank
    orderedHadamard orderedHadamard_hadamard e
  have he : orderedHadamard.submatrix id e = principalSigns := by rfl
  rw [he, Fintype.card_fin] at h
  exact h

theorem principalSigns_signRank_gt : 381 < signRank principalSigns := by
  have h := principalSigns_signRank_square
  nlinarith

end Bier

import CommAlg.Polymatroid.IdealBridge
import CommAlg.Polymatroid.ShiftMultiplication

/-! # Multiplication and containment for genuine homological shifts of ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

theorem homologicalShiftIdeal_le (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : homologicalShiftIdeal I hI i ≤ I := by
  rcases hI.eq_bot_or_rank with h0 | ⟨g, hg⟩
  · subst I
    simp
  · rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g hg i, hg]
    exact rankShiftIdeal_le_rankIdeal g i

/-- Lemma 3.4 for actual polynomial ideals, including both zero ideals. -/
theorem homologicalShiftIdeal_mul_le (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) (i : ℕ) :
    I * homologicalShiftIdeal J hJ i ≤ homologicalShiftIdeal (I * J) (hI.mul hJ) i := by
  rcases hI.eq_bot_or_rank with h0 | ⟨g, hg⟩
  · subst I
    simp
  rcases hJ.eq_bot_or_rank with h0 | ⟨f, hf⟩
  · subst J
    simp
  have hp : I * J = rankIdeal k (g.add f) := by rw [hg, hf, rankIdeal_add]
  rw [homologicalShiftIdeal_eq_rankShiftIdeal J hJ f hf i,
    homologicalShiftIdeal_eq_rankShiftIdeal (I * J) (hI.mul hJ) (g.add f) hp i, hg]
  exact rankIdeal_mul_rankShiftIdeal_le g f i

end CommAlg.Polymatroid

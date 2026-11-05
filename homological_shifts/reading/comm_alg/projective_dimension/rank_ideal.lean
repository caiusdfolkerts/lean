import CommAlg.ProjectiveDimension.RankIdealUpper
import CommAlg.KoszulComplex.CoefficientProjectiveDimension
import CommAlg.KoszulComplex.TorGrading
import CommAlg.Polymatroid.HomologicalMain
import CommAlg.Polymatroid.IdealBridge

/-!
# The actual projective dimension of a polymatroidal ideal

The upper bound is obtained from actual linear-quotient exact sequences.
The lower bound uses a nonzero multigraded component of Mathlib's derived
tensor functor and the proved coefficient-complex dimension-shift theorem.
Neither projective dimension nor Tor nonvanishing is defined by the rank formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rankShiftFamily_nonempty_iff_le_shiftLength (g : RankFunction V) (i : ℕ) :
    (rankShiftFamily g i).Nonempty ↔ i ≤ shiftLength g := by
  rw [rankShiftFamily_nonempty_iff]
  have hd := shiftLength_add_degree g
  by_cases hE : (univ : Finset V).Nonempty
  · rw [universalHomologicalRank_apply g i hE]
    omega
  · have he : (univ : Finset V) = ∅ := not_nonempty_iff_eq_empty.mp hE
    simp only [he, RankFunction.map_empty] at hd ⊢
    omega

theorem top_rankShiftFamily_nonempty (g : RankFunction V) :
    (rankShiftFamily g (shiftLength g)).Nonempty :=
  (rankShiftFamily_nonempty_iff_le_shiftLength g _).mpr le_rfl

end CommAlg.Polymatroid

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CategoryTheory.Limits CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The exact categorical projective dimension, including the unit ideal and loops. -/
theorem rankIdeal_projectiveDimension (g : RankFunction V) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (rankIdeal k g)) =
      (shiftLength g : WithBot ℕ∞) := by
  apply le_antisymm (rankIdeal_projectiveDimension_le g)
  obtain ⟨a, ha⟩ := top_rankShiftFamily_nonempty g
  have hβ := (gradedBettiNonzero_rankBases_iff (k := k) g a (shiftLength g)).mpr ha
  exact Koszul.finitePolynomialTor_nonzero_le_projectiveDimension _ _
    (Koszul.derivedTor_nonzero_of_graded _ _ _ hβ)

/-- The same statement for an actual polynomial ideal with its proved rank presentation. -/
theorem polymatroidalIdeal_projectiveDimension (I : Ideal (MvPolynomial V k))
    (g : RankFunction V) (hI : I = rankIdeal k g) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
      (shiftLength g : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_projectiveDimension g

end CommAlg.ProjectiveDimension

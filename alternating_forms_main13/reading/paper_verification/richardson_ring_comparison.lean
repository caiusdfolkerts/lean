module

public import PaperVerification.RichardsonChartIdeals
public import PaperVerification.SchubertRankMeaning

/-!
# The original interval ring and the independent opposite-flag ring

The flag ideal is defined by the actual projection-column conditions.
Its maximal-minor generators agree with the restricted rank minors on
every normalized Grassmannian chart.  The finite counting comparison
identifies this entire homogeneous ideal with the printed interval ideal,
so the ring comparison retains all polynomials and all homogeneous pieces.
It does not infer equality of graded rings merely from equality of Proj.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}

/-- Homogeneous equations for the two opposite coordinate-flag projections. -/
def flagRankPluckerIdeal (α β : Fin s → Fin n) :
    Ideal (MvPolynomial (PluckerIndex s n) K) :=
  matrixPluckerIdeal ⊔ ⨆ j : Fin s,
    selectedPluckerIdeal (K := K) (s := s) (s - j.val) {c | β j < c} ⊔
      selectedPluckerIdeal (K := K) (s := s) (j.val + 1) {c | c < α j}

/-- Equality of the entire ideals, before forming any projective spectrum. -/
theorem intervalPluckerIdeal_eq_flagRankPluckerIdeal (α β : Fin s → Fin n) :
    intervalPluckerIdeal (K := K) α β = flagRankPluckerIdeal α β :=
  intervalPluckerIdeal_eq_flag_coordinates α β

/-- The flag-rank homogeneous coordinate ring with the original Plücker variables. -/
abbrev FlagRankPluckerRing (α β : Fin s → Fin n) :=
  MvPolynomial (PluckerIndex s n) K ⧸ flagRankPluckerIdeal α β

/-- The original interval quotient is the independently defined opposite-flag ring. -/
def richardsonFlagRingEquiv (α β : Fin s → Fin n) :
    (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) ≃ₐ[K]
      FlagRankPluckerRing (K := K) α β :=
  Ideal.quotientEquivAlgOfEq K (intervalPluckerIdeal_eq_flagRankPluckerIdeal α β)

/-- Every original polynomial is retained by the comparison. -/
theorem richardsonFlagRingEquiv_mk (α β : Fin s → Fin n)
    (a : MvPolynomial (PluckerIndex s n) K) :
    richardsonFlagRingEquiv α β (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
  Ideal.quotientEquivAlgOfEq_mk K (intervalPluckerIdeal_eq_flagRankPluckerIdeal α β) a

/-- Exact preservation of every homogeneous piece, not merely of degree one. -/
theorem richardsonFlagRingEquiv_piece (α β : Fin s → Fin n) (d : ℕ) :
    (HomogeneousIdealPieces.piece (intervalPluckerIdeal (K := K) α β) d).map
        (richardsonFlagRingEquiv α β).toLinearMap =
      HomogeneousIdealPieces.piece (flagRankPluckerIdeal (K := K) α β) d := by
  apply le_antisymm
  · rintro y ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (richardsonFlagRingEquiv_mk α β a).symm⟩
  · rintro y ⟨a, ha, rfl⟩
    exact ⟨Ideal.Quotient.mk _ a, ⟨a, ha, rfl⟩, richardsonFlagRingEquiv_mk α β a⟩

end PaperVerification.AlternatingForms

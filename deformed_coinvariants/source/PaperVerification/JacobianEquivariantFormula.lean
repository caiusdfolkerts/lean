module

public import PaperVerification.JacobianEquivariantTowers
public import PaperVerification.JacobianEquivariantDefect
public import PaperVerification.JacobianHilbertFormula

/-!
# The actual exceptional defect as a finite-group representation

The source of the decomposition contains every nonnegative tower exponent.
Its summand at `j` is the degree `d-j*h` piece of the actual Milnor quotient;
the integer grading proves that this summand is zero when `j*h>d`.
The action on each summand is the restriction of the given linear coordinate
action. The isomorphism is constructed from the canonical defect map and an
averaged homogeneous section; no equivariant splitting is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped DirectSum BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ

theorem milnorRepresentation_preserves_negativeGrading
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) :
    ∀ g p x, x ∈ (milnorNegativeGrading F w h hF).piece p →
      JacobianLinearAction.milnorRepresentation ρ F hFix g x ∈
        (milnorNegativeGrading F w h hF).piece p := by
  intro g p x hx
  change x ∈ (NegativeWeightedGrading.quotientGrading w (jacobianSubmodule F)
    (homogeneousComponent_mem_jacobian F w h hF)).piece p at hx
  change JacobianLinearAction.milnorRepresentation ρ F hFix g x ∈
    (NegativeWeightedGrading.quotientGrading w (jacobianSubmodule F)
      (homogeneousComponent_mem_jacobian F w h hF)).piece p
  rw [NegativeWeightedGrading.quotientGrading_piece] at hx ⊢
  exact JacobianLinearAction.milnorRepresentation_preserves_pieces ρ F hFix
    (NegativeWeightedGrading.negativeWeights w)
    (fun a => JacobianLinearAction.respectsWeights_comp w (fun z : ℕ => -(z : ℤ))
      (ρ a : Matrix ι ι K) (hW a)) g p x hx

theorem brieskornRepresentation_preserves_grading
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) :
    ∀ g p x, x ∈ (brieskornGrading F w h hF).piece p →
      JacobianLinearAction.brieskornRepresentation ρ F hFix g x ∈
        (brieskornGrading F w h hF).piece p := by
  intro g p x hx
  rw [brieskornGrading_piece] at hx ⊢
  exact JacobianLinearAction.brieskornRepresentation_preserves_pieces ρ F hFix
    (NegativeWeightedGrading.negativeWeights w)
    (fun a => JacobianLinearAction.respectsWeights_comp w (fun z : ℕ => -(z : ℤ))
      (ρ a : Matrix ι ι K) (hW a)) g p x hx

/-- The summands in the integer-graded presentation agree with the printed
ordinary-degree components, including every vanishing negative degree. -/
theorem milnor_tower_piece (F : P) (w : ι → ℕ) (h d j : ℕ)
    (hF : F.IsWeightedHomogeneous w h) :
    (milnorNegativeGrading F w h hF).piece (-(d : ℤ) + (j : ℤ) * h) =
      if j*h ≤ d then EulerResonance.quotientComponent w (d-j*h) (jacobianSubmodule F)
      else ⊥ := by
  by_cases hj : j*h ≤ d
  · rw [if_pos hj]
    have he : -(d : ℤ) + (j : ℤ) * h = -((d-j*h : ℕ) : ℤ) := by
      rw [← Nat.cast_mul]
      omega
    rw [he, milnorNegativeGrading_piece]
  · rw [if_neg hj]
    apply milnorNegativeGrading_positive
    have hlt : (d : ℤ) < ((j*h : ℕ) : ℤ) := by exact_mod_cast Nat.lt_of_not_ge hj
    rw [Nat.cast_mul] at hlt
    omega

def milnorTowerRepresentation
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) :
    Representation K G
      (⨁ j : ℕ, (milnorNegativeGrading F w h hF).piece (-(d : ℤ) + (j : ℤ) * h)) :=
  GradedTowers.shiftedPiecesRepresentation (milnorNegativeGrading F w h hF)
    (JacobianLinearAction.milnorRepresentation ρ F hFix)
    (milnorRepresentation_preserves_negativeGrading ρ F w h hF hFix hW) h (-(d : ℤ))

/-- Formula (6.2) for the actual isolated complex hypersurface and its actual
finite linear symmetry group. There is no supplied regular sequence, basis,
equivariant section, invariant relation space, or bound on the tower index. -/
theorem hypersurface_exceptional_defect_representation [Fintype G]
    {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h d : ℕ) (t : ℂ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (hres : (h : ℂ) + t * ((∑ i, w i : ℕ) + d : ℂ) = 0)
    (ρ : G →* (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) ℂ) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ e : DefectQuotient F t ≃ₗ[ℂ]
      (⨁ j : ℕ, (milnorNegativeGrading F w h hF).piece (-(d : ℤ) + (j : ℤ) * h)),
      ∀ g x, e (JacobianLinearAction.defectQuotientRepresentation ρ F t hFix g x) =
        milnorTowerRepresentation ρ F w h d hF hFix hW g (e x) := by
  obtain ⟨s, e, hsq, hsgrade, hesingle, hegrade, heG⟩ :=
    hypersurface_equivariant_milnor_towers hn F w h hne hw hh hF hiso ρ hFix hW
  let GW := milnorNegativeGrading F w h hF
  let GV := brieskornGrading F w h hF
  let ec := GradedTowers.componentEquiv GW GV h e hegrade (-(d : ℤ))
  let ed := exceptionalDefectComponentEquiv F w h d t hh hF hres
  refine ⟨ed.trans ec.symm, ?_⟩
  intro g x
  apply ec.injective
  change ec (ec.symm (ed (JacobianLinearAction.defectQuotientRepresentation
      ρ F t hFix g x))) =
    ec (milnorTowerRepresentation ρ F w h d hF hFix hW g (ec.symm (ed x)))
  rw [LinearEquiv.apply_symm_apply]
  have hc := GradedTowers.componentEquiv_intertwines GW GV h e hegrade
    (JacobianLinearAction.milnorRepresentation ρ F hFix)
    (JacobianLinearAction.brieskornRepresentation ρ F hFix)
    (milnorRepresentation_preserves_negativeGrading ρ F w h hF hFix hW)
    (brieskornRepresentation_preserves_grading ρ F w h hF hFix hW)
    heG (-(d : ℤ)) g (ec.symm (ed x))
  change ec (milnorTowerRepresentation ρ F w h d hF hFix hW g (ec.symm (ed x))) =
    JacobianLinearAction.brieskornComponentRepresentation ρ F w h d hF hFix hW g
      (ec (ec.symm (ed x))) at hc
  rw [hc, LinearEquiv.apply_symm_apply]
  exact JacobianLinearAction.exceptionalDefectComponentEquiv_intertwines
    ρ F w h d t hh hF hres hFix hW g x

/-- The same representation formula with the paper's literal exceptional
parameter and its occurring-degree hypothesis. -/
theorem paper_formula_6_2 [Fintype G]
    {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h d : ℕ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (hd : d ∈ EulerJacobian.occurringDegrees (K := ℂ) w)
    (ρ : G →* (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) ℂ) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ e : DefectQuotient F (-(h : ℂ) / ((∑ i, w i : ℕ) + d : ℂ)) ≃ₗ[ℂ]
      (⨁ j : ℕ, (milnorNegativeGrading F w h hF).piece (-(d : ℤ) + (j : ℤ) * h)),
      ∀ g x, e (JacobianLinearAction.defectQuotientRepresentation ρ F
          (-(h : ℂ) / ((∑ i, w i : ℕ) + d : ℂ)) hFix g x) =
        milnorTowerRepresentation ρ F w h d hF hFix hW g (e x) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply hypersurface_exceptional_defect_representation hn F w h d _ hne hw hh hF hiso
    ((EulerJacobian.eigenvalue_zero_iff w hw h d _).mpr rfl) ρ hFix hW

end PaperVerification.JacobianDivergence

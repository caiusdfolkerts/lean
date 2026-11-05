module

public import PaperVerification.HomogeneousSection
public import PaperVerification.QuotientLinearAction
public import PaperVerification.HomogeneousQuotientBasis
public import PaperVerification.HypersurfaceFreeness

/-!
# Homogeneous equivariant lifts of the Milnor quotient

The section is constructed from homogeneous polynomial representatives and
finite-group averaging. The action on the Milnor quotient is the actual
quotient action. The separate linear-substitution argument supplies the two
stability hypotheses from a linear group preserving the weights and potential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module

namespace PaperVerification.JacobianDivergence

variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι]
variable [Group G] [Fintype G]
local notation "P" => MvPolynomial ι K

def milnorAction (F : P) (ρ : G →* Module.End K P)
    (hJ : ∀ g p, p ∈ jacobianSubmodule F → ρ g p ∈ jacobianSubmodule F) :
    G →* Module.End K (MilnorQuotient F) :=
  QuotientLinearAction.action ρ (jacobianSubmodule F) hJ

theorem exists_equivariant_homogeneous_milnor_section
    (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h)
    (ρ : G →* Module.End K P)
    (hJ : ∀ g p, p ∈ jacobianSubmodule F → ρ g p ∈ jacobianSubmodule F)
    (hw : ∀ g d p, p.IsWeightedHomogeneous w d → (ρ g p).IsWeightedHomogeneous w d) :
    ∃ s : MilnorQuotient F →ₗ[K] P,
      (∀ x, (jacobianSubmodule F).mkQ (s x) = x) ∧
      (∀ g x, s (milnorAction F ρ hJ g x) = ρ g (s x)) ∧
      ∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
        (s x).IsWeightedHomogeneous w d := by
  classical
  obtain ⟨I, b, B, hb, hrep⟩ := exists_homogeneous_milnor_basis F w
  choose degree hdegree using hb
  let GQ := EulerResonance.quotientGrading w (jacobianSubmodule F)
    (homogeneousComponent_mem_jacobian F w h hF)
  have hpiece (d : ℕ) : GQ.piece d =
      EulerResonance.quotientComponent w d (jacobianSubmodule F) :=
    EulerResonance.quotientGrading_piece w (jacobianSubmodule F)
      (homogeneousComponent_mem_jacobian F w h hF) d
  have hB : ∀ i, B i ∈ GQ.piece (degree i) := by
    intro i
    rw [hpiece, EulerResonance.quotientComponent_eq_map]
    exact ⟨b i, hdegree i, hrep i⟩
  have hq : ∀ g p, (jacobianSubmodule F).mkQ (ρ g p) =
      milnorAction F ρ hJ g ((jacobianSubmodule F).mkQ p) := by
    intro g p
    exact (QuotientLinearAction.action_mkQ ρ _ hJ g p).symm
  have hσ : ∀ g d x, x ∈ GQ.piece d → milnorAction F ρ hJ g x ∈ GQ.piece d := by
    intro g d x hx
    rw [hpiece, EulerResonance.quotientComponent_eq_map] at hx ⊢
    exact QuotientLinearAction.action_preserves_image_piece ρ _ hJ
      (weightedHomogeneousSubmodule K w) hw g d x hx
  obtain ⟨s, hsq, hsG, hsgrade⟩ := HomogeneousSection.exists_equivariant_section
    ρ (milnorAction F ρ hJ) (jacobianSubmodule F).mkQ GQ
    (weightedHomogeneousSubmodule K w) B degree b hB hdegree hrep hq hw hσ
  refine ⟨s, hsq, hsG, ?_⟩
  intro d x hx
  apply hsgrade d x
  rwa [hpiece]

end PaperVerification.JacobianDivergence

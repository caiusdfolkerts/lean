module

public import PaperVerification.JacobianLinearAction
public import PaperVerification.JacobianHilbertBasis

/-!
# Equivariance of the canonical exceptional defect

Every action is induced by the given invertible linear coordinate substitutions.
The exceptional isomorphism is the previously constructed canonical map: an
actual class of `F * p` is sent to the degree-`d` component of `p` in the actual
Brieskorn quotient. Its equivariance follows from the proved multiplication and
homogeneous-projection identities. No invariant relation space is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.JacobianLinearAction

open MvPolynomial JacobianDivergence
open scoped BigOperators

variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ

/-- The actual Jacobian ideal, regarded as a subrepresentation of polynomials. -/
def jacobianRepresentation (ρ : G →* GL) (F : P)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (jacobianSubmodule F) :=
  (polynomialRepresentation ρ).subrepresentation (jacobianSubmodule F)
    (fun g p hp => linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hFix g⁻¹) p hp)

/-- The action on the literal quotient `J(F)/H_t(F)` is induced from the
coordinate action on the actual ideal and actual hit space. -/
def defectQuotientRepresentation (ρ : G →* GL) (F : P) (t : K)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (DefectQuotient F t) :=
  (jacobianRepresentation ρ F hFix).quotient
    ((EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype)
    (fun g p hp => linearSubst_mem_hit (ρ g⁻¹) F t (hFix g⁻¹) p hp)

/-- The elementary first-isomorphism identification of `J/H` with its image
inside `P/H` respects the actual coordinate actions. -/
theorem defectQuotientEquivImage_intertwines (ρ : G →* GL) (F : P) (t : K)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (g : G) (x : DefectQuotient F t) :
    defectQuotientEquivImage F t (defectQuotientRepresentation ρ F t hFix g x) =
      defectRepresentation ρ F t hFix g (defectQuotientEquivImage F t x) := by
  obtain ⟨p, rfl⟩ :=
    ((EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype).mkQ_surjective x
  apply Subtype.ext
  rfl

/-- The actual degree-`d` part of the raw Brieskorn quotient is invariant. -/
theorem brieskornQuotientRepresentation_preserves_component
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (d : ℕ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (x : BrieskornQuotient F)
    (hx : x ∈ EulerResonance.quotientComponent w d (divergenceSpace F)) :
    brieskornQuotientRepresentation ρ F hFix g x ∈
      EulerResonance.quotientComponent w d (divergenceSpace F) := by
  rw [EulerResonance.quotientComponent_eq_map] at hx ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨polynomialRepresentation ρ g p,
    polynomialRepresentation_preserves_weights ρ w hW g hp, rfl⟩

def rawBrieskornComponentRepresentation
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (d : ℕ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K)) :
    Representation K G (EulerResonance.quotientComponent w d (divergenceSpace F)) :=
  (brieskornQuotientRepresentation ρ F hFix).subrepresentation
    (EulerResonance.quotientComponent w d (divergenceSpace F))
    (fun g x hx => brieskornQuotientRepresentation_preserves_component
      ρ F w d hFix hW g x hx)

/-- This computation identifies the canonical defect map on every polynomial
representative, including representatives with several homogeneous components. -/
theorem exceptionalDefectEquiv_apply_potential
    (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (p : P) (hp : potentialToHitQuotient F t p ∈ defectImage F t) :
    (exceptionalDefectEquiv F w h d t hh hF hres
      ⟨potentialToHitQuotient F t p, hp⟩ : BrieskornQuotient F) =
        (divergenceSpace F).mkQ (weightedHomogeneousComponent w d p) := by
  let hr := normalized_resonance w h d t hh hres
  have hrange : potentialToHitQuotient F t p ∈ LinearMap.range
      (potentialToHitQuotient F t) := ⟨p, rfl⟩
  change
    (EulerResonance.resonantQuotientEquiv w
      (1 + (t / h) * (∑ i, w i : ℕ)) (t / h) d hr.2.1 hr.2.2
      (divergenceSpace F)
      (fun f hf => homogeneousComponent_mem_divergenceSpace F w h hF f hf d)
      ((Submodule.quotEquivOfEq _ _
        (potentialToHitQuotient_kernel F w h t hh hF hr.1))
        ((potentialToHitQuotient F t).quotKerEquivRange.symm
          ⟨potentialToHitQuotient F t p, hrange⟩)) : BrieskornQuotient F) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- Naturality of the actual canonical exceptional-defect isomorphism. -/
theorem exceptionalDefectEquiv_intertwines
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (x : defectImage F t) :
    exceptionalDefectEquiv F w h d t hh hF hres
        (defectRepresentation ρ F t hFix g x) =
      rawBrieskornComponentRepresentation ρ F w d hFix hW g
        (exceptionalDefectEquiv F w h d t hh hF hres x) := by
  have hmem (p : P) : potentialToHitQuotient F t p ∈ defectImage F t := by
    rw [← potentialToHitQuotient_range F w h t hh hF]
    exact ⟨p, rfl⟩
  have hxrange : x.val ∈ LinearMap.range (potentialToHitQuotient F t) := by
    rw [potentialToHitQuotient_range F w h t hh hF]
    exact x.property
  obtain ⟨p, hp⟩ := hxrange
  have hx : x = ⟨potentialToHitQuotient F t p, hmem p⟩ := Subtype.ext hp.symm
  subst x
  have hg :
      defectRepresentation ρ F t hFix g ⟨potentialToHitQuotient F t p, hmem p⟩ =
        ⟨potentialToHitQuotient F t (polynomialRepresentation ρ g p),
          hmem (polynomialRepresentation ρ g p)⟩ := by
    apply Subtype.ext
    exact (potentialToHitQuotient_intertwines ρ F t hFix g p).symm
  rw [hg]
  apply Subtype.ext
  change
    (exceptionalDefectEquiv F w h d t hh hF hres
      ⟨potentialToHitQuotient F t (polynomialRepresentation ρ g p),
        hmem (polynomialRepresentation ρ g p)⟩ : BrieskornQuotient F) =
      brieskornQuotientRepresentation ρ F hFix g
        (exceptionalDefectEquiv F w h d t hh hF hres
          ⟨potentialToHitQuotient F t p, hmem p⟩ : BrieskornQuotient F)
  rw [exceptionalDefectEquiv_apply_potential, exceptionalDefectEquiv_apply_potential]
  change (divergenceSpace F).mkQ
      (weightedHomogeneousComponent w d (linearSubst (ρ g⁻¹ : Matrix ι ι K) p)) =
    (divergenceSpace F).mkQ
      (linearSubst (ρ g⁻¹ : Matrix ι ι K) (weightedHomogeneousComponent w d p))
  rw [linearSubst_weightedHomogeneousComponent _ w (hW g⁻¹)]

theorem exceptionalDefectQuotientEquiv_intertwines
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (x : DefectQuotient F t) :
    exceptionalDefectQuotientEquiv F w h d t hh hF hres
        (defectQuotientRepresentation ρ F t hFix g x) =
      rawBrieskornComponentRepresentation ρ F w d hFix hW g
        (exceptionalDefectQuotientEquiv F w h d t hh hF hres x) := by
  change exceptionalDefectEquiv F w h d t hh hF hres
      (defectQuotientEquivImage F t (defectQuotientRepresentation ρ F t hFix g x)) =
    rawBrieskornComponentRepresentation ρ F w d hFix hW g
      (exceptionalDefectEquiv F w h d t hh hF hres (defectQuotientEquivImage F t x))
  rw [defectQuotientEquivImage_intertwines,
    exceptionalDefectEquiv_intertwines ρ F w h d t hh hF hres hFix hW]

/-- The action on the actual graded Brieskorn module component. The negative
index is the existing grading convention, representing ordinary weight `d`. -/
def brieskornComponentRepresentation
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K)) :
    Representation K G ((brieskornGrading F w h hF).piece (-(d : ℤ))) :=
  (brieskornRepresentation ρ F hFix).subrepresentation
    ((brieskornGrading F w h hF).piece (-(d : ℤ))) (by
      intro g x hx
      rw [brieskornGrading_piece] at hx ⊢
      exact brieskornRepresentation_preserves_pieces ρ F hFix
        (NegativeWeightedGrading.negativeWeights w)
        (fun a i j hij => congrArg (fun z : ℕ => -(z : ℤ)) (hW a i j hij))
        g (-(d : ℤ)) x hx)

/-- The raw-quotient and polynomial-module component presentations use the
same natural action, transported through the actual AEval equivalence. -/
theorem rawBrieskornComponentEquiv_intertwines
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (x : EulerResonance.quotientComponent w d (divergenceSpace F)) :
    rawBrieskornComponentEquiv F w h d hF
        (rawBrieskornComponentRepresentation ρ F w d hFix hW g x) =
      brieskornComponentRepresentation ρ F w h d hF hFix hW g
        (rawBrieskornComponentEquiv F w h d hF x) := by
  apply Subtype.ext
  let e := Module.AEval'.of (potentialAction F)
  change e (brieskornQuotientRepresentation ρ F hFix g x.val) =
    e (brieskornQuotientRepresentation ρ F hFix g (e.symm (e x.val)))
  rw [LinearEquiv.symm_apply_apply]

/-- The canonical isomorphism from the paper's literal `J/H` to `V_F[d]`
is equivariant for every actual weight-preserving linear group action. -/
theorem exceptionalDefectComponentEquiv_intertwines
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K))
    (g : G) (x : DefectQuotient F t) :
    exceptionalDefectComponentEquiv F w h d t hh hF hres
        (defectQuotientRepresentation ρ F t hFix g x) =
      brieskornComponentRepresentation ρ F w h d hF hFix hW g
        (exceptionalDefectComponentEquiv F w h d t hh hF hres x) := by
  change rawBrieskornComponentEquiv F w h d hF
      (exceptionalDefectQuotientEquiv F w h d t hh hF hres
        (defectQuotientRepresentation ρ F t hFix g x)) =
    brieskornComponentRepresentation ρ F w h d hF hFix hW g
      (rawBrieskornComponentEquiv F w h d hF
        (exceptionalDefectQuotientEquiv F w h d t hh hF hres x))
  rw [exceptionalDefectQuotientEquiv_intertwines ρ F w h d t hh hF hres hFix hW,
    rawBrieskornComponentEquiv_intertwines ρ F w h d hF hFix hW]

end PaperVerification.JacobianLinearAction

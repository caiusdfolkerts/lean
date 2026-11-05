module

public import PaperVerification.SymmetricProjectiveTotalChowRank
public import PaperVerification.SymmetricFreeProjectiveIso
public import PaperVerification.OnePlaneProjectiveComparison

/-!
# The original one-plane boundary of the Chow rank theorem

Every alternating form vanishes on a line, so the original one-plane common
isotropic scheme is the full original Plücker projective space. The comparison
below uses its literal quotient ring and the genuine symmetric projective
hyperplane calculation, retaining the scalar morphism throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory
open AlternatingForms
open OAI.AlgebraicGeometry.Divisors.LineBundles
open SymmetricProjective.Scheme.BundleCycles

/-- The actual original one-plane Chow group has total rank at most the
ambient vector-space dimension. -/
theorem onePlane_total_chow_rank (n : ℕ) (hn : 0 < n) :
    letI := (onePlaneOriginalProjectivePresentation n hn).isNoetherian
    Module.Finite ℚ (TotalChowQ (onePlaneOriginalStructureMap (K := ℂ) n)) ∧
      Module.finrank ℚ (TotalChowQ (onePlaneOriginalStructureMap (K := ℂ) n)) ≤ n := by
  letI := (onePlaneOriginalProjectivePresentation n hn).isNoetherian
  letI := (onePlaneOriginalProjectivePresentation n hn).finiteType.1
  let b := Pi.basisFun ℂ (Fin n)
  let E := onePlaneOriginalProjIsoPolynomial (K := ℂ) n ≪≫
    SymmetricFreeProjectiveIso.projectiveIso b
  have hover : E.hom ≫ symmetricProjectiveToBase ℂ (Fin n → ℂ) =
      onePlaneOriginalStructureMap (K := ℂ) n := by
    change (_ ≫ _) ≫ _ = _
    rw [Category.assoc, SymmetricFreeProjectiveIso.projectiveIso_hom_over,
      onePlaneOriginalProjIsoPolynomial_hom_over]
  let C := totalChowEquiv E _ _ hover
  have h := coordinateProjective_total_rank n
  letI := h.1
  exact ⟨Module.Finite.equiv C.symm, C.finrank_eq.trans_le h.2⟩

end PaperVerification.TotalChow

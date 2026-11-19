module

public import PaperVerification.BarDiagonalHomology
public import PaperVerification.HomogeneousQuadraticDual

/-!
# Actual positive diagonal homology equals the intrinsic quadratic-dual degree

This comparison is basis independent on its quadratic-dual side. It uses
the actual bar differential, actual categorical homology, original algebra
multiplication, and the canonical tensor annihilator. Koszulness is not a
hypothesis. All positive degrees and every finite homogeneous basis are
included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.HomogeneousDiagonalDuality

open AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ) (ε : A →ₐ[K] K)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i)) (hpos : ∀ i,0<δ i)
  (hε : ∀ i,ε (B (some i))=0)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hzero hhom hpos in
theorem diagonal_finrank_eq_intrinsic (r : ℕ) :
    Module.finrank K
      ((WeightedBar.internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1))=
      Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul (r+1)) :=
  (BarDiagonalHomology.diagonal_finrank_eq_quotient_finrank
    ε B hunit hε δ hpos hδ r).trans
      (HomogeneousQuadraticDual.degree_finrank_eq G B δ hzero hunit hhom hmul (r+1)).symm

end PaperVerification.HomogeneousDiagonalDuality

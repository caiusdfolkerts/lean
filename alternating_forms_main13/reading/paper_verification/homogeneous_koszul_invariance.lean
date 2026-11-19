module

public import PaperVerification.HomogeneousDiagonalDuality
public import PaperVerification.WeightedBarTorOrthogonality
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Independence of diagonal ordinary Tor from a homogeneous basis

For every finite homogeneous augmented basis, positive diagonal homology
has the dimension of the same intrinsic quadratic-dual piece. If one
basis gives diagonal concentration, its diagonal image exhausts ordinary
Tor. Finite dimension then forces the other basis's diagonal image to be
all of that same Tor module. Orthogonality kills its off-diagonal pieces.
The zeroth homological degree is treated directly by the empty bar word.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.HomogeneousKoszulInvariance

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AugmentedAlgebraBasis WeightedBar

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

/-- An actual internal bar homology group is finite-dimensional because
its cycles embed in a finite word space and its homology is their quotient. -/
theorem internalHomology_finite (r N : ℕ) :
    Module.Finite K ((internalComplex ε B hunit hε δ hδ N).homology r) := by
  let C := internalComplex ε B hunit hε δ hδ N
  haveI : Module.Finite K (C.X r) := by
    change Module.Finite K (piece (K := K) δ r N)
    infer_instance
  haveI : Module.Finite K (C.cycles r) :=
    Module.Finite.of_injective (C.iCycles r).hom
      ((ModuleCat.mono_iff_injective (C.iCycles r)).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ r).hom
    ((ModuleCat.epi_iff_surjective (C.homologyπ r)).mp inferInstance)

variable (G : TauCeti.InternalGrading K A ℕ)
  (hzero : G.piece 0=(1 : Submodule K A))
  (hhom : ∀ i,B (some i)∈G.piece (δ i)) (hpos : ∀ i,0<δ i)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))
  {J : Type u} [Fintype J]
  (B' : Module.Basis (Option J) K A)
  (hunit' : B' none=1) (hε' : ∀ i,ε (B' (some i))=0)
  (δ' : J → ℕ)
  (hδ' : ∀ a b c,productCoefficients B' a b c≠0 → δ' c=δ' a+δ' b)
  (hhom' : ∀ i,B' (some i)∈G.piece (δ' i)) (hpos' : ∀ i,0<δ' i)

include hzero hhom hpos hmul hhom' hpos' in
/-- Diagonal ordinary Tor concentration transfers to every other actual
finite homogeneous augmented basis for the same original grading. -/
theorem hasDiagonalTor_transfer
    (h : HasDiagonalTor ε B hunit hε δ hδ) :
    HasDiagonalTor ε B' hunit' hε' δ' hδ' := by
  intro r N hne
  rcases r with _ | r
  · exact torPiece_zero_off_diagonal ε B' hunit' hε' δ' hδ' N hne
  · have htop := diagonal_top_of_hasDiagonalTor ε B hunit hε δ hδ h (r+1)
    let e : (internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1) ≃ₗ[K]
        AugmentationCoinvariants.augmentationTor ε (r+1) :=
      (internalTorEquiv ε B hunit hε δ hδ (r+1) (r+1)).trans
        ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)
    haveI : Module.Finite K
        ((internalComplex ε B hunit hε δ hδ (r+1)).homology (r+1)) :=
      internalHomology_finite ε B hunit hε δ hδ (r+1) (r+1)
    haveI : Module.Finite K (AugmentationCoinvariants.augmentationTor ε (r+1)) :=
      Module.Finite.equiv e
    have hdim : Module.finrank K (AugmentationCoinvariants.augmentationTor ε (r+1))=
        Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul (r+1)) :=
      e.finrank_eq.symm.trans
        (HomogeneousDiagonalDuality.diagonal_finrank_eq_intrinsic
          G ε B δ hzero hunit hhom hpos hε hδ hmul r)
    have hdim' : Module.finrank K (torPiece ε B' hunit' hε' δ' hδ' (r+1) (r+1))=
        Module.finrank K (HomogeneousQuadraticDual.wordPiece G hmul (r+1)) :=
      (internalTorEquiv ε B' hunit' hε' δ' hδ' (r+1) (r+1)).finrank_eq.symm.trans
        (HomogeneousDiagonalDuality.diagonal_finrank_eq_intrinsic
          G ε B' δ' hzero hunit' hhom' hpos' hε' hδ' hmul r)
    have htop' : torPiece ε B' hunit' hε' δ' hδ' (r+1) (r+1)=⊤ :=
      Submodule.eq_top_of_finrank_eq (hdim'.trans hdim.symm)
    have hd := torPiece_disjoint ε B' hunit' hε' δ' hδ' (r+1) N (r+1) (Ne.symm hne)
    rw [htop'] at hd
    exact disjoint_top.mp hd

include hzero hhom hpos hmul hhom' hpos' in
/-- The concentration property is independent of every compatible finite
homogeneous basis, without assuming Koszulness or a Hilbert formula. -/
theorem hasDiagonalTor_iff :
    HasDiagonalTor ε B hunit hε δ hδ ↔ HasDiagonalTor ε B' hunit' hε' δ' hδ' := by
  constructor
  · exact hasDiagonalTor_transfer ε B hunit hε δ hδ G hzero hhom hpos hmul
      B' hunit' hε' δ' hδ' hhom' hpos'
  · exact hasDiagonalTor_transfer ε B' hunit' hε' δ' hδ' G hzero hhom' hpos' hmul
      B hunit hε δ hδ hhom hpos

end PaperVerification.HomogeneousKoszulInvariance

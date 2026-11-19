module

public import PaperVerification.AlternatingFormsOnePlaneTorGrading
public import PaperVerification.AlternatingFormsPolynomialDegreeCompatibility
public import PaperVerification.ModuleCatRingEquivTorElementary

/-!
# The actual one-plane resolution preserves internal degree

The degree-one variables are the classes of the original Plucker
coordinates.  Their monomials are identified through the explicit
ring isomorphism, and each actual contraction term adds one variable
while removing one exterior basis factor.  Thus the ordinary
one-plane Tor grading defined by images of these homogeneous pieces
is the internal grading of the original homogeneous resolution.

This is an uncompiled proof candidate, not a completion certificate.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial CategoryTheory TauCeti

universe u
variable (K : Type u) [Field K] (n : ℕ)
local notation "P" => Ring K n

theorem functional_basis (i : Fin n) :
    functional K n (Pi.basisFun P (Fin n) i)=generator K n i := by
  rw [Pi.basisFun_apply]
  exact (Fintype.linearCombination_apply_single P (generator K n) i 1).trans
    (one_smul _ _)

def differentialOverK (r : ℕ) : freeTermOverK K n (r+1) →ₗ[K] freeTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map ((complex K n).d (r+1) r)).hom

set_option backward.isDefEq.respectTransparency false in
theorem differentialOverK_apply (r : ℕ) (z : freeTermOverK K n (r+1)) :
    differentialOverK K n r z=koszulDifferential (functional K n) r z := by
  change ((TauCeti.koszulComplex (functional K n)).d (r+1) r).hom z=_
  rw [TauCeti.koszulComplex_d_apply]

theorem differentialOverK_monomial_mem (r N : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) (r+1)) (hdeg : d.degree+(r+1)=N) :
    differentialOverK K n r (freeMonomialBasis K n (r+1) (d,I))∈
      (freeGrading K n r).piece N := by
  rw [freeMonomialBasis_apply,differentialOverK_apply]
  change koszulDifferential (functional K n) r
    (coordinateMonomial K n d • (Pi.basisFun P (Fin n)).exteriorPower (r+1) I)∈(freeGrading K n r).piece N
  rw [map_smul,PolynomialKoszul.differential_eq_coordinate_sum (Pi.basisFun P (Fin n))]
  simp only [functional_basis,Finset.smul_sum]
  apply Submodule.sum_mem
  intro i hi
  by_cases hI : i∈I.val
  · rw [PolynomialKoszul.coordinate_contraction_mem _ hI]
    have hm : coordinateMonomial K n d*generator K n i=
        coordinateMonomial K n (d+Finsupp.single i 1) := by
      apply (polynomialEquiv K n).injective
      simp only [map_mul,coordinateMonomial,AlgEquiv.apply_symm_apply,
        polynomialEquiv_generator,X,monomial_mul_monomial,mul_one]
    let I' : Set.powersetCard (Fin n) r :=
      Set.powersetCard.ofCard (s := I.val.erase i)
        (by simp [Finset.card_erase_of_mem hI,Set.powersetCard.card_eq])
    have hd' : (d+Finsupp.single i 1).degree+r=N := by
      rw [map_add,Finsupp.degree_single]
      omega
    have hmem := BasisDegree.basis_mem_piece (freeMonomialBasis K n r)
      (fun a ↦ a.1.degree+r) (d+Finsupp.single i 1,I')
    change freeMonomialBasis K n r (d+Finsupp.single i 1,I')∈
      (freeGrading K n r).piece ((d+Finsupp.single i 1).degree+r) at hmem
    rw [hd',freeMonomialBasis_apply] at hmem
    have hsign := ((freeGrading K n r).piece N).toAddSubgroup.zsmul_mem hmem
      (ExteriorAlgebra.basisEraseSign i I.val : ℤ)
    change coordinateMonomial K n d • generator K n i •
        ((ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
          (Pi.basisFun P (Fin n)).exteriorPower r I') ∈ (freeGrading K n r).piece N
    have heq : coordinateMonomial K n d • generator K n i •
        ((ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
          (Pi.basisFun P (Fin n)).exteriorPower r I') =
      (ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
        (coordinateMonomial K n (d+Finsupp.single i 1) •
          (Pi.basisFun P (Fin n)).exteriorPower r I') := by
      calc
        _ = (ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
            ((coordinateMonomial K n d*generator K n i) •
              (Pi.basisFun P (Fin n)).exteriorPower r I') :=
          ModuleCatRingEquivTor.associate_integer_smul
            (coordinateMonomial K n d) (generator K n i)
            (ExteriorAlgebra.basisEraseSign i I.val : ℤ)
            ((Pi.basisFun P (Fin n)).exteriorPower r I')
        _ = _ := congrArg
          (fun a : P => (ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
            (a • (Pi.basisFun P (Fin n)).exteriorPower r I')) hm
    rw [heq]
    exact hsign
  · rw [PolynomialKoszul.coordinate_contraction_not_mem _ hI,smul_zero,smul_zero]
    exact Submodule.zero_mem _

/-- The genuine differential of the full polynomial free resolution
preserves the original internal degree in every homological degree. -/
theorem differentialOverK_homogeneous (r N : ℕ) (z : freeTermOverK K n (r+1))
    (hz : z∈(freeGrading K n (r+1)).piece N) :
    differentialOverK K n r z∈(freeGrading K n r).piece N := by
  change z∈BasisDegree.piece (freeMonomialBasis K n (r+1))
    (fun a ↦ a.1.degree+(r+1)) N at hz
  rw [BasisDegree.piece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨d,I⟩,hd,rfl⟩ := hz
    exact differentialOverK_monomial_mem K n r N d I hd
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

end PaperVerification.AlternatingForms.OnePlaneKoszul

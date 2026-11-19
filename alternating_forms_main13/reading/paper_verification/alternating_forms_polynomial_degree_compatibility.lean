module

public import PaperVerification.AlternatingFormsPolynomialTorGrading

/-!
# Compatibility of the actual polynomial differential with internal degree

This proves preservation of the monomial-plus-exterior degree by the
original contraction differential.  The coordinate-contraction identities
are proved from the actual exterior-basis formula.  Their short proofs
follow the corresponding identities in TauCeti's KoszulComplex/Basis
development (commit 8428d6217f74afa72531df0bc85d7b57ab72810f); the present
file imports only the already vendored pinned contraction infrastructure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.PolynomialKoszul

open MvPolynomial CategoryTheory TauCeti

section CoordinateContraction

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I] (b : Module.Basis I R M)

theorem differential_eq_coordinate_sum [Fintype I] (φ : Module.Dual R M)
    (r : ℕ) (z : ⋀[R]^(r+1) M) :
    koszulDifferential φ r z=∑ i,φ (b i) • koszulDifferential (b.coord i) r z := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply,Submodule.coe_sum]
  conv_lhs => rw [←b.sum_dual_apply_smul_coord φ]
  rw [map_sum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul,LinearMap.smul_apply,Submodule.coe_smul,coe_koszulDifferential_apply]

theorem coordinate_contraction_mem {r : ℕ} {i : I}
    {s : Set.powersetCard I (r+1)} (hi : i∈s.val) :
    koszulDifferential (b.coord i) r (b.exteriorPower (r+1) s)=
      ExteriorAlgebra.basisEraseSign i s.val • b.exteriorPower r
        (Set.powersetCard.ofCard (s := s.val.erase i)
          (by simp [Finset.card_erase_of_mem hi,Set.powersetCard.card_eq])) := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply,←ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp only [hi,if_true,Submodule.coe_smul_of_tower]
  rw [←ExteriorAlgebra.basis_eq_coe_basis,Set.powersetCard.val_ofCard]

theorem coordinate_contraction_not_mem {r : ℕ} {i : I}
    {s : Set.powersetCard I (r+1)} (hi : i∉s.val) :
    koszulDifferential (b.coord i) r (b.exteriorPower (r+1) s)=0 := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply,←ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp [hi]

end CoordinateContraction

universe u
variable (K : Type u) [Field K] (n : ℕ)
local notation "P" => PolynomialRing K n

theorem variableFunctional_basis (i : Fin n) :
    variableFunctional K n (Pi.basisFun P (Fin n) i)=X i := by
  rw [Pi.basisFun_apply]
  exact (Fintype.linearCombination_apply_single P (fun i : Fin n ↦ X (R := K) i) i 1).trans
    (one_smul _ _)

def differentialOverK (r : ℕ) : freeTermOverK K n (r+1) →ₗ[K] freeTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map ((complex K n).d (r+1) r)).hom

set_option backward.isDefEq.respectTransparency false in
theorem differentialOverK_apply (r : ℕ) (z : freeTermOverK K n (r+1)) :
    differentialOverK K n r z=koszulDifferential (variableFunctional K n) r z := by
  change ((TauCeti.koszulComplex (variableFunctional K n)).d (r+1) r).hom z=_
  rw [TauCeti.koszulComplex_d_apply]

theorem differentialOverK_monomial_mem (r N : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) (r+1)) (hdeg : d.degree+(r+1)=N) :
    differentialOverK K n r (freeMonomialBasis K n (r+1) (d,I))∈
      (freeGrading K n r).piece N := by
  rw [freeMonomialBasis_apply,differentialOverK_apply]
  change koszulDifferential (variableFunctional K n) r
    (monomial d (1 : K) • (Pi.basisFun P (Fin n)).exteriorPower (r+1) I)∈(freeGrading K n r).piece N
  rw [map_smul,differential_eq_coordinate_sum (Pi.basisFun P (Fin n))]
  simp only [variableFunctional_basis,Finset.smul_sum]
  apply Submodule.sum_mem
  intro i hi
  by_cases hI : i∈I.val
  · rw [coordinate_contraction_mem _ hI,←mul_smul,smul_comm]
    have hm : (monomial d (1 : K) : P)*X i=monomial (d+Finsupp.single i 1) 1 := by
      rw [X,monomial_mul_monomial,mul_one]
    rw [hm]
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
    rw [Units.smul_def]
    exact ((freeGrading K n r).piece N).toAddSubgroup.zsmul_mem hmem _
  · rw [coordinate_contraction_not_mem _ hI,smul_zero,smul_zero]
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

end PaperVerification.AlternatingForms.PolynomialKoszul

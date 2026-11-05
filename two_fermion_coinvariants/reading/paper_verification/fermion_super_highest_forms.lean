module

public import PaperVerification.FermionHighestForms
public import PaperVerification.FermionSuperMonomialBasics
public import PaperVerification.FermionFilteredModuleSpanning
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Algebra.Module.NatInt

/-!
# Highest forms in the literal polynomial/exterior tensor product

The filtration is defined by the actual monomial/exterior basis. Multiplying
by arbitrary basis words on both sides is handled using the true exterior
shuffle formula, including its zero cases. Thus the later filtered spanning
argument uses the original two-sided moment ideal.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial
open scoped BigOperators TensorProduct

variable {K : Type*} [CommRing K] {n : ℕ} [LinearOrder (OddIndex n)]

def wordPolynomialWeight (ν : OddIndex n → ℕ) (T : Finset (OddIndex n)) : ℕ := ∑ j ∈ T, ν j

def superMonomialWeight (w : Fin n → ℕ) (ν : OddIndex n → ℕ) (z : SuperMonomialIndex n) : ℕ :=
  Finsupp.weight w z.1 + wordPolynomialWeight ν z.2

theorem superMonomialBasis_repr_tmul (p : PolynomialRing K n) (T : Finset (OddIndex n))
    (z : SuperMonomialIndex n) :
    (superMonomialBasis (K := K)).repr
      (p ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T) z =
      if T=z.2 then p.coeff z.1 else 0 := by
  classical
  have hc (p : PolynomialRing K n) (a : Fin n →₀ ℕ) :
      (basisMonomials (Fin n) K).repr p a = p.coeff a := rfl
  rcases z with ⟨a,U⟩
  simp [superMonomialBasis,Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,hc]

theorem hasTop_tmul_word (w : Fin n → ℕ) (ν : OddIndex n → ℕ)
    (p p₀ : PolynomialRing K n) (d : ℕ) (hp : Filtered.HasTop w d p p₀)
    (T : Finset (OddIndex n)) :
    BasisFiltered.HasTop (superMonomialBasis (K := K)) (superMonomialWeight w ν)
      (d+wordPolynomialWeight ν T)
      (p ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T)
      (p₀ ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T) := by
  classical
  constructor
  · intro z hz
    rw [superMonomialBasis_repr_tmul] at hz
    split_ifs at hz with hT
    · unfold superMonomialWeight
      rw [← hT]
      exact Nat.add_le_add_right (hp.1 z.1 hz) _
    · exact (hz rfl).elim
  · apply (superMonomialBasis (K := K)).repr.injective
    ext z
    rw [BasisFiltered.repr_component,superMonomialBasis_repr_tmul,superMonomialBasis_repr_tmul]
    by_cases hT : T=z.2
    · rw [if_pos hT,if_pos hT]
      simp only [superMonomialWeight,← hT,Nat.add_right_cancel_iff]
      have h := congrArg (fun q : PolynomialRing K n ↦ q.coeff z.1) hp.2
      simpa only [coeff_weightedHomogeneousComponent] using h
    · simp only [if_neg hT,ite_self]

/-- Every product of two exterior basis words is an actual scalar multiple
of one basis word, with the additive weight when it is nonzero. -/
theorem exterior_basis_mul_weight (ν : OddIndex n → ℕ) (S T : Finset (OddIndex n)) :
    ∃ (a : K) (U : Finset (OddIndex n)),
      (Pi.basisFun K (OddIndex n)).ExteriorAlgebra S *
        (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T =
          a • (Pi.basisFun K (OddIndex n)).ExteriorAlgebra U ∧
      (a ≠ 0 → wordPolynomialWeight ν U = wordPolynomialWeight ν S + wordPolynomialWeight ν T) := by
  classical
  by_cases h : Disjoint S T
  · let S' : Set.powersetCard (OddIndex n) S.card := ⟨S,rfl⟩
    let T' : Set.powersetCard (OddIndex n) T.card := ⟨T,rfl⟩
    let a : K := ((Set.powersetCard.permOfDisjoint (s := S') (t := T') h).sign : ℤ)
    refine ⟨a,S.disjUnion T h,?_,?_⟩
    · simpa only [a,Units.smul_def,Int.cast_smul_eq_zsmul,Set.powersetCard.coe_disjUnion] using
        ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun K (OddIndex n)) S' T' h
    · intro ha
      exact Finset.sum_disjUnion h
  · refine ⟨0,∅,?_,fun h0 ↦ (h0 rfl).elim⟩
    rw [zero_smul]
    exact ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun K (OddIndex n))
      (⟨S,rfl⟩ : Set.powersetCard (OddIndex n) S.card)
      (⟨T,rfl⟩ : Set.powersetCard (OddIndex n) T.card) h

theorem exterior_basis_triple_weight (ν : OddIndex n → ℕ) (L T R : Finset (OddIndex n)) :
    ∃ (a : K) (U : Finset (OddIndex n)),
      ((Pi.basisFun K (OddIndex n)).ExteriorAlgebra L *
        (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T) *
          (Pi.basisFun K (OddIndex n)).ExteriorAlgebra R =
        a • (Pi.basisFun K (OddIndex n)).ExteriorAlgebra U ∧
      (a ≠ 0 → wordPolynomialWeight ν U =
        wordPolynomialWeight ν L+wordPolynomialWeight ν T+wordPolynomialWeight ν R) := by
  obtain ⟨a,U,hU,hwU⟩ := exterior_basis_mul_weight (K := K) ν L T
  obtain ⟨b,V,hV,hwV⟩ := exterior_basis_mul_weight (K := K) ν U R
  refine ⟨a*b,V,?_,?_⟩
  · rw [hU,smul_mul_assoc,hV,smul_smul]
  · intro hab
    rw [hwV (right_ne_zero_of_mul hab),hwU (left_ne_zero_of_mul hab)]

/-- Multiplication by both actual basis words preserves the prescribed
highest form, including products that vanish by repeated odd variables. -/
theorem hasTop_basis_multiples (w : Fin n → ℕ) (ν : OddIndex n → ℕ)
    (p p₀ : PolynomialRing K n) (d : ℕ) (hp : Filtered.HasTop w d p p₀)
    (T : Finset (OddIndex n)) (L R : SuperMonomialIndex n) :
    BasisFiltered.HasTop (superMonomialBasis (K := K)) (superMonomialWeight w ν)
      (superMonomialWeight w ν L+(d+wordPolynomialWeight ν T)+superMonomialWeight w ν R)
      (superMonomialBasis L * (p ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T) *
        superMonomialBasis R)
      (superMonomialBasis L * (p₀ ⊗ₜ[K] (Pi.basisFun K (OddIndex n)).ExteriorAlgebra T) *
        superMonomialBasis R) := by
  classical
  rw [superMonomialBasis_apply,superMonomialBasis_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  obtain ⟨a,U,hU,hwU⟩ := exterior_basis_triple_weight (K := K) ν L.2 T R.2
  rw [hU]
  by_cases ha : a=0
  · simp only [ha,zero_smul,TensorProduct.tmul_zero]
    exact BasisFiltered.HasTop.zero _ _ _
  · have hpL := Filtered.HasTop.of_homogeneous w
      (isWeightedHomogeneous_monomial w L.1 (1 : K) rfl)
    have hpR := Filtered.HasTop.of_homogeneous w
      (isWeightedHomogeneous_monomial w R.1 (1 : K) rfl)
    have h := hasTop_tmul_word w ν _ _ _
      (Filtered.HasTop.mul w (Filtered.HasTop.mul w hpL hp) hpR) U
    have he : Finsupp.weight w L.1+d+Finsupp.weight w R.1+wordPolynomialWeight ν U =
        superMonomialWeight w ν L+(d+wordPolynomialWeight ν T)+superMonomialWeight w ν R := by
      rw [hwU ha]
      simp only [superMonomialWeight]
      omega
    rw [he] at h
    simpa only [TensorProduct.tmul_smul] using BasisFiltered.HasTop.smul _ _ h a

end PaperVerification.Fermion

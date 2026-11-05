module

public import PaperVerification.AlternatingFormsBooleanQuotient
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact duality for the homogeneous Boolean quotient

The dual of the actual polynomial ideal quotient in degree `q` is identified
with the homogeneous multiaffine polynomials annihilated by both actual
directional derivations.  The square-free coefficient pairing has no factorial
denominators, and the argument works in every characteristic and in degree zero.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanQuotient

open scoped BigOperators
open MvPolynomial BooleanCoefficients EvenDeterminants

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K

/-- The standard coefficient pairing, with every square-free basis vector of norm one. -/
def coefficientDual (q : ℕ) :
    (FixedSubsets ι q → K) →ₗ[K] Module.Dual K (FixedSubsets ι q → K) where
  toFun v :=
    { toFun := fun w => ∑ U, v U * w U
      map_add' := by intro w z; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a w; simp [Finset.mul_sum, mul_left_comm] }
  map_add' v w := by ext z; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a v := by ext w; simp [Finset.mul_sum, mul_assoc]

def coefficientDualEquiv (q : ℕ) :
    (FixedSubsets ι q → K) ≃ₗ[K] Module.Dual K (FixedSubsets ι q → K) where
  __ := coefficientDual q
  invFun φ U := φ (Pi.single U 1)
  left_inv v := by
    ext U
    simp [coefficientDual, Pi.single_apply, eq_comm]
  right_inv φ := by
    apply LinearMap.ext
    intro w
    change (∑ U, φ (Pi.single U 1) * w U) = φ w
    conv_rhs => rw [pi_eq_sum_univ' w]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro U hU
    exact mul_comm _ _

def coefficientFunctional (q : ℕ) (v : FixedSubsets ι q → K) : Module.Dual K P :=
  (coefficientDual q v).comp (coefficients q)

theorem coefficientFunctional_monomial (q : ℕ) (v : FixedSubsets ι q → K)
    (d : ι →₀ ℕ) (a : K) :
    coefficientFunctional q v (monomial d a) = a * (evaluation q v).coeff d := by
  change (∑ U : FixedSubsets ι q, v U * (monomial d a).coeff (subsetExponent U.val)) =
    a * (∑ U : FixedSubsets ι q, v U • subsetMonomial U.val).coeff d
  rw [coeff_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  by_cases he : subsetExponent U.val = d
  · simp only [coeff_monomial, he, if_true, coeff_smul, subsetMonomial, smul_eq_mul,
      mul_one]
    exact mul_comm _ _
  · simp only [coeff_monomial, if_neg he, if_neg (Ne.symm he), coeff_smul,
      subsetMonomial, smul_zero, mul_zero]

/-- The integer multiplier in the derivative coefficient disappears precisely
because every exponent in the polynomial is at most one. -/
theorem directionalDerivative_coeff_multiaffine (b : ι → K) (f : P)
    (hf : ∀ i, f.degreeOf i ≤ 1) (d : ι →₀ ℕ) :
    (directionalDerivative b f).coeff d = ∑ i, b i * f.coeff (d + Finsupp.single i 1) := by
  rw [directionalDerivative_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : d i = 0
  · simp only [hd, Nat.cast_zero, zero_add, mul_one]
  · have hz : f.coeff (d + Finsupp.single i 1) = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      apply MvPolynomial.notMem_support_of_degreeOf_lt i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      have := hf i
      omega
    rw [hz, zero_mul]

/-- Multiplication by a linear form and directional differentiation are adjoint
on the square-free coefficient pairing, verified on every ordinary monomial. -/
theorem coefficientFunctional_linearForm_mul_monomial (b : ι → K) (q : ℕ)
    (v : FixedSubsets ι q → K) (d : ι →₀ ℕ) (a : K) :
    coefficientFunctional q v (linearForm b * monomial d a) =
      a * (directionalDerivative b (evaluation q v)).coeff d := by
  simp only [linearForm, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul,
    MvPolynomial.X, monomial_mul_monomial, one_mul]
  simp_rw [coefficientFunctional_monomial]
  rw [directionalDerivative_coeff_multiaffine b _ (evaluation_multiaffine q v),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_comm (Finsupp.single i 1) d]
  ring

theorem annihilates_relationMap_iff (b : ι → K) (q : ℕ) (v : FixedSubsets ι q → K) :
    (∀ p : P, coefficientDual q v (relationMap b q p) = 0) ↔
      directionalDerivative b (evaluation q v) = 0 := by
  constructor
  · intro h
    apply MvPolynomial.ext
    intro d
    have hd := h (monomial d 1)
    change coefficientFunctional q v (linearForm b * monomial d 1) = 0 at hd
    rw [coefficientFunctional_linearForm_mul_monomial, one_mul] at hd
    simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hd
  · intro h p
    let F : P →ₗ[K] K := (coefficientFunctional q v).comp (LinearMap.mulLeft K (linearForm b))
    change F p = 0
    rw [p.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    change coefficientFunctional q v (linearForm b * monomial d (p.coeff d)) = 0
    rw [coefficientFunctional_linearForm_mul_monomial, h]
    simp

def jointCoefficientKernel (b c : ι → K) (q : ℕ) : Submodule K (FixedSubsets ι q → K) :=
  ((directionalDerivative b).toLinearMap.comp (evaluation q)).ker ⊓
    ((directionalDerivative c).toLinearMap.comp (evaluation q)).ker

@[simp] theorem mem_jointCoefficientKernel (b c : ι → K) (q : ℕ)
    (v : FixedSubsets ι q → K) :
    v ∈ jointCoefficientKernel b c q ↔
      directionalDerivative b (evaluation q v) = 0 ∧
      directionalDerivative c (evaluation q v) = 0 := Iff.rfl

theorem coefficientDual_mem_annihilator_iff (b c : ι → K) (q : ℕ)
    (v : FixedSubsets ι q → K) :
    coefficientDual q v ∈ (relations b c q).dualAnnihilator ↔
      v ∈ jointCoefficientKernel b c q := by
  rw [relations, Submodule.dualAnnihilator_sup_eq, Submodule.mem_inf,
    Submodule.mem_dualAnnihilator, Submodule.mem_dualAnnihilator,
    mem_jointCoefficientKernel]
  have hr (a : ι → K) :
      (∀ w ∈ (relationMap a q).range, coefficientDual q v w = 0) ↔
        directionalDerivative a (evaluation q v) = 0 := by
    rw [← annihilates_relationMap_iff]
    constructor
    · intro h p
      exact h _ (LinearMap.mem_range_self _ p)
    · intro h w hw
      obtain ⟨p, rfl⟩ := hw
      exact h p
  exact and_congr (hr b) (hr c)

theorem coefficientDual_map_jointKernel (b c : ι → K) (q : ℕ) :
    (jointCoefficientKernel b c q).map (coefficientDualEquiv q).toLinearMap =
      (relations b c q).dualAnnihilator := by
  ext φ
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (coefficientDual_mem_annihilator_iff b c q v).mpr hv
  · intro hφ
    refine ⟨(coefficientDualEquiv q).symm φ, ?_, (coefficientDualEquiv q).apply_symm_apply φ⟩
    apply (coefficientDual_mem_annihilator_iff b c q _).mp
    change coefficientDualEquiv q ((coefficientDualEquiv q).symm φ) ∈ _
    rwa [LinearEquiv.apply_symm_apply]

def jointCoefficientEquivAnnihilator (b c : ι → K) (q : ℕ) :
    jointCoefficientKernel b c q ≃ₗ[K] (relations b c q).dualAnnihilator :=
  (coefficientDualEquiv q).ofSubmodules _ _ (coefficientDual_map_jointKernel b c q)

/-- A concrete subspace of the original polynomial ring, not an abstract matrix kernel. -/
def jointDerivativeKernel (b c : ι → K) (q : ℕ) : Submodule K P :=
  (evaluation q).range ⊓
    ((directionalDerivative b).toLinearMap.ker ⊓ (directionalDerivative c).toLinearMap.ker)

/-- Exact mathematical meaning of membership in the polynomial kernel. -/
theorem mem_jointDerivativeKernel_iff (b c : ι → K) (q : ℕ) (f : P) :
    f ∈ jointDerivativeKernel b c q ↔
      f.IsHomogeneous q ∧ (∀ i, f.degreeOf i ≤ 1) ∧
        directionalDerivative b f = 0 ∧ directionalDerivative c f = 0 := by
  constructor
  · rintro ⟨⟨v, rfl⟩, hb, hc⟩
    exact ⟨evaluation_isHomogeneous q v, evaluation_multiaffine q v, hb, hc⟩
  · rintro ⟨hh, hm, hb, hc⟩
    refine ⟨⟨coefficients q f, ?_⟩, hb, hc⟩
    exact evaluation_coefficients_eq q f hh hm

def jointEvaluation (b c : ι → K) (q : ℕ) :
    jointCoefficientKernel b c q →ₗ[K] jointDerivativeKernel b c q :=
  ((evaluation q).comp (jointCoefficientKernel b c q).subtype).codRestrict _
    (fun v => ⟨LinearMap.mem_range_self _ v.val, v.property⟩)

theorem jointEvaluation_bijective (b c : ι → K) (q : ℕ) :
    Function.Bijective (jointEvaluation b c q) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply evaluation_injective q
    exact congrArg Subtype.val huv
  · intro f
    obtain ⟨v, hv⟩ := f.property.1
    have hker : v ∈ jointCoefficientKernel b c q := by
      change directionalDerivative b (evaluation q v) = 0 ∧
        directionalDerivative c (evaluation q v) = 0
      rw [hv]
      exact f.property.2
    refine ⟨⟨v, hker⟩, ?_⟩
    exact Subtype.ext hv

def jointCoefficientEquivPolynomial (b c : ι → K) (q : ℕ) :
    jointCoefficientKernel b c q ≃ₗ[K] jointDerivativeKernel b c q :=
  LinearEquiv.ofBijective (jointEvaluation b c q) (jointEvaluation_bijective b c q)

/-- Full duality with the literal homogeneous component of the ordinary
polynomial quotient by all coordinate squares and the two linear forms. -/
def pieceDualEquivJointDerivativeKernel (b c : ι → K) (q : ℕ) :
    Module.Dual K (piece b c q) ≃ₗ[K] jointDerivativeKernel b c q :=
  (cokernelEquivPiece b c q).dualMap |>.trans
    ((relations b c q).dualQuotEquivDualAnnihilator |>.trans
      ((jointCoefficientEquivAnnihilator b c q).symm.trans
        (jointCoefficientEquivPolynomial b c q)))

instance finiteDimensional_piece (b c : ι → K) (q : ℕ) :
    FiniteDimensional K (piece b c q) :=
  Module.Finite.of_surjective (toPiece b c q) (toPiece_surjective b c q)

theorem finrank_piece_eq_jointDerivativeKernel (b c : ι → K) (q : ℕ) :
    Module.finrank K (piece b c q) = Module.finrank K (jointDerivativeKernel b c q) := by
  simpa only [Subspace.dual_finrank_eq] using
    (pieceDualEquivJointDerivativeKernel b c q).finrank_eq

instance finiteDimensional_jointDerivativeKernel (b c : ι → K) (q : ℕ) :
    FiniteDimensional K (jointDerivativeKernel b c q) :=
  Module.Finite.of_surjective (jointCoefficientEquivPolynomial b c q).toLinearMap
    (jointCoefficientEquivPolynomial b c q).surjective

/-- An independent family of actual joint-kernel polynomials gives a lower
bound for the ordinary Boolean quotient, through the proved duality. -/
theorem card_le_finrank_piece_of_linearIndependent {η : Type*} [Fintype η]
    (b c : ι → K) (q : ℕ) (f : η → P)
    (hf : ∀ a, f a ∈ jointDerivativeKernel b c q)
    (hli : LinearIndependent K f) :
    Fintype.card η ≤ Module.finrank K (piece b c q) := by
  let g : η → jointDerivativeKernel b c q := fun a => ⟨f a, hf a⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp (jointDerivativeKernel b c q).subtype
    exact hli
  have h := hg.fintype_card_le_finrank
  rwa [← finrank_piece_eq_jointDerivativeKernel b c q] at h

end PaperVerification.AlternatingForms.BooleanQuotient

module
public import graph_results.grading_foundations

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialMultigradedTensor -/
section

/-!
# Fine degrees of polynomial tensor modules

The degree is the complete exponent vector. A homogeneous matrix entry
is consequently a scalar multiple of its uniquely determined monomial.
The zero statement for incomparable shifts is included, so truncated
subtraction never disguises an impossible degree.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers
open Classical CommAlg MvPolynomial
open scoped TensorProduct

variable {k V M N I J : Type*} [CommRing k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

def polynomialTensorFineDegree (degree : I → V →₀ ℕ)
    (a : (V →₀ ℕ) × I) : V →₀ ℕ := a.1 + degree a.2

theorem polynomialTensor_monomial_finePiece (b : Module.Basis I k M)
    (degree : I → V →₀ ℕ) (a q : V →₀ ℕ) {x : M}
    (hx : x ∈ Grading.Piece b degree q) :
    monomial a 1 ⊗ₜ[k] x ∈ Grading.Piece (polynomialTensorBasis b)
      (polynomialTensorFineDegree degree) (a + q) := by
  let L := Grading.Piece (polynomialTensorBasis (V := V) b)
    (polynomialTensorFineDegree degree) (a + q)
  let f := TensorProduct.mk k (MvPolynomial V k) M (monomial a 1)
  have hle : Grading.Piece b degree q ≤ L.comap f := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    have hi' : degree i = q := hi
    change monomial a 1 ⊗ₜ[k] b i ∈ L
    rw [← polynomialTensorBasis_apply]
    have hb := Grading.basis_mem_piece (polynomialTensorBasis (V := V) b)
      (polynomialTensorFineDegree degree) (a, i)
    simpa only [L, polynomialTensorFineDegree, hi'] using hb
  exact hle hx

theorem polynomialTensor_baseChange_finePiece (b : Module.Basis I k M)
    (c : Module.Basis J k N) (degree : I → V →₀ ℕ) (degree' : J → V →₀ ℕ)
    (f : M →ₗ[k] N) (hf : ∀ i, f (b i) ∈ Grading.Piece c degree' (degree i))
    (a : (V →₀ ℕ) × I) :
    (f.baseChange (MvPolynomial V k)).restrictScalars k (polynomialTensorBasis b a) ∈
      Grading.Piece (polynomialTensorBasis c) (polynomialTensorFineDegree degree')
        (polynomialTensorFineDegree degree a) := by
  rw [LinearMap.restrictScalars_apply, polynomialTensorBasis_apply,
    LinearMap.baseChange_tmul]
  exact polynomialTensor_monomial_finePiece c degree' a.1 (degree a.2) (hf a.2)

theorem polynomialTensor_coefficient_fineDegree (b : Module.Basis I k M)
    (degree : I → V →₀ ℕ) (q : V →₀ ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b)
      (polynomialTensorFineDegree degree) q)
    (a : V →₀ ℕ) (i : I)
    (ha : (((b.baseChange (MvPolynomial V k)).repr x) i).coeff a ≠ 0) :
    a + degree i = q := by
  have hc : (polynomialTensorBasis b).repr x (a, i) ≠ 0 := by
    rw [polynomialTensorBasis_repr]
    exact ha
  exact (Grading.mem_piece (polynomialTensorBasis b)
    (polynomialTensorFineDegree degree) q x).mp hx (a, i) hc

/-- Applying any nonnegative variable weights to the exact fine-degree
equation gives the corresponding weighted homogeneous matrix entry. -/
theorem polynomialTensor_coefficient_weighted (b : Module.Basis I k M)
    (degree : I → V →₀ ℕ) (q : V →₀ ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b)
      (polynomialTensorFineDegree degree) q) (w : V → ℕ) (i : I) :
    (((b.baseChange (MvPolynomial V k)).repr x) i).IsWeightedHomogeneous w
      (Finsupp.weight w q - Finsupp.weight w (degree i)) := by
  intro a ha
  have he := congrArg (Finsupp.weight w)
    (polynomialTensor_coefficient_fineDegree b degree q hx a i ha)
  rw [map_add] at he
  omega

/-- Every actual matrix entry has precisely the fine shift dictated by
its source and target basis vectors, with no possible extra monomials. -/
theorem polynomialTensor_coefficient_eq_monomial (b : Module.Basis I k M)
    (degree : I → V →₀ ℕ) (q : V →₀ ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b)
      (polynomialTensorFineDegree degree) q) (i : I) :
    ((b.baseChange (MvPolynomial V k)).repr x) i =
      monomial (q - degree i)
        ((((b.baseChange (MvPolynomial V k)).repr x) i).coeff (q - degree i)) := by
  ext a
  by_cases ha : a = q - degree i
  · subst a
    simp only [coeff_monomial, ite_true]
  · have hz : (((b.baseChange (MvPolynomial V k)).repr x) i).coeff a = 0 := by
      by_contra hn
      have he := polynomialTensor_coefficient_fineDegree b degree q hx a i hn
      apply ha
      ext v
      have hv := DFunLike.congr_fun he v
      simp only [Finsupp.add_apply] at hv
      simp only [Finsupp.tsub_apply]
      omega
    rw [hz, coeff_monomial, if_neg (Ne.symm ha)]

/-- If a target shift is not coordinatewise below the source shift,
the corresponding polynomial coefficient is zero. -/
theorem polynomialTensor_coefficient_zero_of_not_le (b : Module.Basis I k M)
    (degree : I → V →₀ ℕ) (q : V →₀ ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b)
      (polynomialTensorFineDegree degree) q) (i : I) (hi : ¬degree i ≤ q) :
    ((b.baseChange (MvPolynomial V k)).repr x) i = 0 := by
  ext a
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hn
  have he := polynomialTensor_coefficient_fineDegree b degree q hx a i hn
  apply hi
  rw [← he]
  exact le_add_of_nonneg_left (show (0 : V →₀ ℕ) ≤ a from zero_le)

end FourPapers

#print axioms FourPapers.polynomialTensor_baseChange_finePiece
#print axioms FourPapers.polynomialTensor_coefficient_weighted
#print axioms FourPapers.polynomialTensor_coefficient_eq_monomial
#print axioms FourPapers.polynomialTensor_coefficient_zero_of_not_le

end
end
end

end

module
public import shared_results.part002
public import graph_foundation.part011
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.InternalGradedPerturbation -/
section

/-! # Preservation of ordinary internal degree by finite perturbation -/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.HomologicalPerturbation

section Restriction

variable {K R M : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]

/-- Restriction retains the same actual inverse operators. -/
def restrictScalarsUnit (u : (Module.End R M)ˣ) : (Module.End K M)ˣ where
  val := (u : Module.End R M).restrictScalars K
  inv := (↑(u⁻¹) : Module.End R M).restrictScalars K
  val_inv := by
    ext x
    exact LinearMap.congr_fun u.val_inv x
  inv_val := by
    ext x
    exact LinearMap.congr_fun u.inv_val x

end Restriction

namespace LinearContraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))
  (P : Module.End R M) (Q : Module.End R H)
  (δ : Module.End R M) (u : (Module.End R M)ˣ)
  (hu : (u : Module.End R M) = 1 + δ * C.h)
  (hh : C.h * P = P * C.h) (hδ : δ * P = P * δ)
  (hi : C.inclusion.comp Q = P.comp C.inclusion)
  (hp : C.projection.comp P = Q.comp C.projection)

include hu hh hδ in
theorem internalPerturbationUnit_commutes : Commute (u : Module.End R M) P := by
  change (u : Module.End R M) * P = P * (u : Module.End R M)
  rw [hu, add_mul, mul_add, one_mul, mul_one]
  congr 1
  rw [mul_assoc, hh, ← mul_assoc, hδ, mul_assoc]

include hu hh hδ in
theorem internalCorrection_commutes : correction u δ * P = P * correction u δ := by
  have hc := (C.internalPerturbationUnit_commutes P δ u hu hh hδ).units_inv_left
  rw [correction, mul_assoc, hδ, ← mul_assoc, hc.eq, mul_assoc]

include hu hh hδ hi hp in
/-- The actual transferred differential has ordinary internal degree zero. -/
theorem transferredDifferential_preserves_internal :
    (C.transferredDifferential δ u).comp Q = Q.comp (C.transferredDifferential δ u) := by
  ext x
  change C.projection (correction u δ (C.inclusion (Q x))) =
    Q (C.projection (correction u δ (C.inclusion x)))
  have hi' := LinearMap.congr_fun hi x
  have ha' := LinearMap.congr_fun (C.internalCorrection_commutes P δ u hu hh hδ) (C.inclusion x)
  have hp' := LinearMap.congr_fun hp (correction u δ (C.inclusion x))
  change C.inclusion (Q x) = P (C.inclusion x) at hi'
  change correction u δ (P (C.inclusion x)) = P (correction u δ (C.inclusion x)) at ha'
  change C.projection (P (correction u δ (C.inclusion x))) =
    Q (C.projection (correction u δ (C.inclusion x))) at hp'
  rw [hi', ha', hp']

include hu hh hδ hi in
theorem transferredInclusion_preserves_internal :
    (C.transferredInclusion δ u).comp Q = P.comp (C.transferredInclusion δ u) := by
  ext x
  have hi' := LinearMap.congr_fun hi x
  have ha' := LinearMap.congr_fun (C.internalCorrection_commutes P δ u hu hh hδ) (C.inclusion x)
  have hh' := LinearMap.congr_fun hh (correction u δ (C.inclusion x))
  change C.inclusion (Q x) = P (C.inclusion x) at hi'
  change correction u δ (P (C.inclusion x)) = P (correction u δ (C.inclusion x)) at ha'
  change C.h (P (correction u δ (C.inclusion x))) = P (C.h (correction u δ (C.inclusion x))) at hh'
  change C.inclusion (Q x) - C.h (correction u δ (C.inclusion (Q x))) =
    P (C.inclusion x - C.h (correction u δ (C.inclusion x)))
  rw [hi', ha', hh', map_sub]

end LinearContraction
end FourPapers.HomologicalPerturbation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialGradedTensor -/
section

/-! # Actual polynomial tensor gradings and homogeneous matrix entries -/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical CommAlg MvPolynomial
open scoped TensorProduct

variable {k V M N I J : Type*} [CommRing k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

def polynomialTensorBasis (b : Module.Basis I k M) :
    Module.Basis ((V →₀ ℕ) × I) k (MvPolynomial V k ⊗[k] M) :=
  (MvPolynomial.basisMonomials V k).tensorProduct b

def polynomialTensorDegree (degree : I → ℕ) (a : (V →₀ ℕ) × I) : ℕ :=
  a.1.degree + degree a.2

@[simp] theorem polynomialTensorBasis_apply (b : Module.Basis I k M)
    (a : V →₀ ℕ) (i : I) :
    polynomialTensorBasis b (a,i) = monomial a 1 ⊗ₜ[k] b i := by
  simp only [polynomialTensorBasis, Module.Basis.tensorProduct_apply,
    MvPolynomial.coe_basisMonomials]

/-- The grading of the polynomial factor is added to the genuine original
coefficient degree, rather than replacing that degree by a chosen weight. -/
theorem polynomialTensor_monomial_piece (b : Module.Basis I k M) (degree : I → ℕ)
    (a : V →₀ ℕ) (q : ℕ) {x : M} (hx : x ∈ Grading.Piece b degree q) :
    monomial a 1 ⊗ₜ[k] x ∈
      Grading.Piece (polynomialTensorBasis b) (polynomialTensorDegree degree) (a.degree+q) := by
  let L := Grading.Piece (polynomialTensorBasis (V := V) b)
    (polynomialTensorDegree degree) (a.degree+q)
  let f := TensorProduct.mk k (MvPolynomial V k) M (monomial a 1)
  have hle : Grading.Piece b degree q ≤ L.comap f := by
    apply Submodule.span_le.mpr
    rintro y ⟨i,hi,rfl⟩
    have hi' : degree i = q := hi
    change monomial a 1 ⊗ₜ[k] b i ∈ L
    rw [← polynomialTensorBasis_apply]
    have hb := Grading.basis_mem_piece (polynomialTensorBasis (V := V) b)
      (polynomialTensorDegree degree) (a,i)
    simpa only [L,polynomialTensorDegree,hi'] using hb
  exact hle hx

/-- Scalar extension of a genuinely degree-preserving coefficient map
preserves the total ordinary polynomial degree. -/
theorem polynomialTensor_baseChange_piece (b : Module.Basis I k M) (c : Module.Basis J k N)
    (degree : I → ℕ) (degree' : J → ℕ) (f : M →ₗ[k] N)
    (hf : ∀ i, f (b i) ∈ Grading.Piece c degree' (degree i))
    (a : (V →₀ ℕ) × I) :
    (f.baseChange (MvPolynomial V k)).restrictScalars k (polynomialTensorBasis b a) ∈
      Grading.Piece (polynomialTensorBasis c) (polynomialTensorDegree degree')
        (polynomialTensorDegree degree a) := by
  rw [LinearMap.restrictScalars_apply, polynomialTensorBasis_apply,
    LinearMap.baseChange_tmul]
  exact polynomialTensor_monomial_piece c degree' a.1 (degree a.2) (hf a.2)

/-- The coefficient of the actual polynomial matrix is exactly the
corresponding scalar coefficient in the expanded monomial tensor basis. -/
theorem polynomialTensorBasis_repr (b : Module.Basis I k M)
    (x : MvPolynomial V k ⊗[k] M) (a : V →₀ ℕ) (i : I) :
    (polynomialTensorBasis b).repr x (a,i) =
      (((b.baseChange (MvPolynomial V k)).repr x) i).coeff a := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply, AddMonoidAlgebra.coeff_zero]
  | tmul f x =>
      rw [polynomialTensorBasis, Module.Basis.tensorProduct_repr_tmul_apply,
        Module.Basis.baseChange_repr_tmul]
      change b.repr x i • f.coeff a = (b.repr x i • f).coeff a
      exact (MvPolynomial.coeff_smul a (b.repr x i) f).symm
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add]
      rw [hx,hy]

theorem polynomialTensor_coefficient_degree (b : Module.Basis I k M) (degree : I → ℕ)
    (q : ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b) (polynomialTensorDegree degree) q)
    (a : V →₀ ℕ) (i : I)
    (ha : (((b.baseChange (MvPolynomial V k)).repr x) i).coeff a ≠ 0) :
    a.degree + degree i = q := by
  have hc : (polynomialTensorBasis b).repr x (a,i) ≠ 0 := by
    rw [polynomialTensorBasis_repr]
    exact ha
  exact (Grading.mem_piece (polynomialTensorBasis b) (polynomialTensorDegree degree) q x).mp
    hx (a,i) hc

/-- Homogeneity in the shifted free module gives actual homogeneous
polynomial coefficients of the expected difference of shifts. -/
theorem polynomialTensor_coefficient_homogeneous (b : Module.Basis I k M) (degree : I → ℕ)
    (q : ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b) (polynomialTensorDegree degree) q)
    (i : I) :
    IsWeightedHomogeneous (fun _ : V => (1 : ℕ))
      (((b.baseChange (MvPolynomial V k)).repr x) i) (q-degree i) := by
  intro a ha
  have he := polynomialTensor_coefficient_degree b degree q hx a i ha
  rw [← Finsupp.degree_eq_weight_one]
  omega

theorem polynomialTensor_coefficient_zero_of_shift_gt (b : Module.Basis I k M) (degree : I → ℕ)
    (q : ℕ) {x : MvPolynomial V k ⊗[k] M}
    (hx : x ∈ Grading.Piece (polynomialTensorBasis b) (polynomialTensorDegree degree) q)
    (i : I) (hi : q < degree i) :
    ((b.baseChange (MvPolynomial V k)).repr x) i = 0 := by
  ext a
  by_contra ha
  have hne : (((b.baseChange (MvPolynomial V k)).repr x) i).coeff a ≠ 0 := by
    simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using ha
  have he := polynomialTensor_coefficient_degree b degree q hx a i hne
  omega

end FourPapers

end
end
end


end

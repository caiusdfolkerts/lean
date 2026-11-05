module

public import PaperVerification.FermionCreatorTriangularity
public import PaperVerification.FermionSpecialization

/-!
# Strict-height creators use positive ordinary moments

The strict quotient has the zeroth odd contractions but no zeroth ordinary
moment. Both creator colors therefore carry an additional parameter factor.
The proofs here retain that distinction explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
variable (b : Module.Basis (Fin n ⊕ Fin n) R V) (φ β : Fin n → R)

/-- Multiplication by the parameter in the polynomial index needs only positive
ordinary moments. -/
theorem strict_polynomial_moment_zero
    (h : ∀ k, moment φ (fun i ↦ β i * φ i) k = 0) (p : Polynomial R) :
    ordinaryPolynomialMoment φ β (fun _ ↦ 1) (fun _ ↦ 1) (Polynomial.X * p) = 0 := by
  have hh := polynomial_moment_zero φ (fun i ↦ β i * φ i) h p
  simpa only [ordinaryPolynomialMoment, one_mul, mul_one, Polynomial.eval_mul,
    Polynomial.eval_X, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hh

 theorem strict_thetaCreator_preserves_harmonics
    (h : ∀ k, moment φ (fun i ↦ β i * φ i) k = 0)
    (p : Polynomial R) (w : ExteriorAlgebra R V)
    (hw : IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1) w) :
    IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1)
      (thetaCreator b φ β (fun _ ↦ 1) (Polynomial.X * p) w) := by
  apply thetaCreator_preserves_harmonics_of_moments b φ β (fun _ ↦ 1) (fun _ ↦ 1)
    (Polynomial.X * p) _ w hw
  intro q
  rw [show q * (Polynomial.X * p) = Polynomial.X * (q * p) by ring]
  exact strict_polynomial_moment_zero φ β h (q * p)

 theorem strict_xiCreator_preserves_harmonics
    (h : ∀ k, moment φ (fun i ↦ β i * φ i) k = 0)
    (p : Polynomial R) (w : ExteriorAlgebra R V)
    (hw : IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1) w) :
    IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1)
      (xiCreator b φ (fun _ ↦ 1) (Polynomial.X * p) w) := by
  apply xiCreator_preserves_harmonics_of_moments b φ β (fun _ ↦ 1) (fun _ ↦ 1)
    (Polynomial.X * p) _ w hw
  intro q
  rw [show q * (Polynomial.X * p) = Polynomial.X * (q * p) by ring]
  exact strict_polynomial_moment_zero φ β h (q * p)

 theorem strict_thetaCreatorVector (p : Polynomial R) :
    thetaCreatorVector b φ β φ p =
      thetaCreatorVector b φ β (fun _ ↦ 1) (Polynomial.X * p) := by
  simp only [thetaCreatorVector, mul_one, Polynomial.eval_mul, Polynomial.eval_X, mul_assoc]

 theorem strict_xiCreatorVector (p : Polynomial R) :
    xiCreatorVector b φ φ p = xiCreatorVector b φ (fun _ ↦ 1) (Polynomial.X * p) := by
  simp only [xiCreatorVector, one_mul, Polynomial.eval_mul, Polynomial.eval_X]

/-- Every ordered product of the strict creators is a literal strict harmonic. -/
theorem strict_prefixCreator_product_isHarmonic
    (h : ∀ k, moment φ (fun i ↦ β i * φ i) k = 0) (L : List (Fin n ⊕ Fin n)) :
    IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1)
      ((L.map fun j ↦ ExteriorAlgebra.ι R (prefixCreatorVector b φ β φ φ j)).prod) := by
  induction L with
  | nil => exact isHarmonic_one b φ β (fun _ => 1) (fun _ ↦ 1)
  | cons j L ih =>
      cases j with
      | inl j =>
          change IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1)
            (ExteriorAlgebra.ι R (thetaCreatorVector b φ β φ (suffixPolynomial φ j)) * _)
          rw [strict_thetaCreatorVector]
          exact strict_thetaCreator_preserves_harmonics b φ β h _ _ ih
      | inr j =>
          change IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1)
            (ExteriorAlgebra.ι R (xiCreatorVector b φ φ (suffixPolynomial φ j)) * _)
          rw [strict_xiCreatorVector]
          exact strict_xiCreator_preserves_harmonics b φ β h _ _ ih

local instance FermionStrictCreators_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The same actual triangular wedge, with both prefactors equal to the
parameter, is harmonic for the strict currents. -/
theorem strict_prefixCreatorWedge_isHarmonic
    (h : ∀ k, moment φ (fun i ↦ β i * φ i) k = 0)
    (k : ℕ) (s : Set.powersetCard (Fin n ⊕ Fin n) k) :
    IsHarmonic b φ β (fun _ ↦ 1) (fun _ ↦ 1)
      (prefixCreatorWedge b φ β φ φ k s : ExteriorAlgebra R V) := by
  have hp := strict_prefixCreator_product_isHarmonic b φ β h
    (List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm s))
  simpa only [Function.comp_def,prefixCreatorWedge, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family_apply_coe,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    List.map_ofFn, Function.comp_apply, prefixCreatorMap_basis] using hp

end PaperVerification.Fermion.Exterior

namespace PaperVerification.Fermion

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}

/-- Strict relations map to the harmonic orthogonal using positive ordinary
moments. In particular, no nonexistent zeroth ordinary relation is assumed. -/
theorem strictIdeal_le_harmonic_comap [LinearOrder (OddIndex n)]
    (f : PolynomialRing K n →ₐ[K] A) (β : Fin n → K) (φ : Fin n → PolynomialRing K n)
    (hordinary : ∀ k, moment (fun i ↦ f (φ i))
      (fun i ↦ algebraMap K A (β i) * f (φ i)) k = 0) :
    strictIdeal β φ ≤
      (Exterior.harmonicOrthogonalIdeal (Pi.basisFun A (OddIndex n))
        (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
        (fun _ ↦ 1) (fun _ ↦ 1)).comap (superSpecialization f).toRingHom := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨⟨kind, k⟩, rfl⟩
  change superSpecialization f (moment φ (strictCoefficients β φ kind) k) ∈
    Exterior.harmonicOrthogonalIdeal (Pi.basisFun A (OddIndex n))
      (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
      (fun _ ↦ 1) (fun _ ↦ 1)
  have h := Exterior.relations_mem_harmonicOrthogonal (Pi.basisFun A (OddIndex n))
    (fun i ↦ f (φ i)) (fun i ↦ algebraMap K A (β i))
    (fun _ ↦ 1) (fun _ ↦ 1) (Polynomial.X ^ k)
  cases kind with
  | polynomial =>
      have heq : moment φ (strictCoefficients β φ .polynomial) k =
          moment φ (pairedCoefficients β φ (fun _ ↦ 1) .polynomial) k := by
        simp only [moment, strictCoefficients, pairedCoefficients, mul_one]
      rw [heq, superSpecialization_paired_polynomial]
      simp only [map_one, mul_one, hordinary, map_zero]
      exact TwoSidedIdeal.zero_mem _
  | theta =>
      have heq : moment φ (strictCoefficients β φ .theta) k =
          moment φ (pairedCoefficients β (fun _ ↦ 1) (fun _ ↦ 1) .theta) k := by
        simp only [moment, strictCoefficients, pairedCoefficients, one_smul]
      rw [heq, superSpecialization_paired_theta]
      simpa only [map_one] using h.1
  | xi =>
      have heq : moment φ (strictCoefficients β φ .xi) k =
          moment φ (pairedCoefficients β (fun _ ↦ 1) (fun _ ↦ 1) .xi) k := by
        simp only [moment, strictCoefficients, pairedCoefficients, mul_one]
      rw [heq, superSpecialization_paired_xi]
      simpa only [map_one] using h.2.1
  | mixed =>
      change superSpecialization f
        (moment φ (pairedCoefficients β (fun _ ↦ 1) (fun _ ↦ 1) .mixed) k) ∈ _
      rw [superSpecialization_paired_mixed]
      exact h.2.2

end PaperVerification.Fermion

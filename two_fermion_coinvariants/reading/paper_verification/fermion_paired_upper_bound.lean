module

public import PaperVerification.FermionPowerHarmonicBound
public import PaperVerification.FermionQuotientDual

/-!
# The full homogeneous paired quotient upper bound

This theorem concerns the paper's literal two-sided quotient. The ordinary
relations give the exact scalar quotient factor map; Frobenius duality
embeds its dual in the actual harmonic space, whose complete path-box
dimension bound was proved from prefix identities and endpoint lengths.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct BigOperators
open MvPolynomial Exterior Endpoint

variable {K : Type*} [Field K] {n : ℕ}

local instance FermionPairedUpperBound_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m

theorem includeLeft_module_moment
    (φ v : Fin n → PolynomialRing K n) (k : ℕ) :
    (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n)
        (moment φ v k) = moment φ (fun i ↦ v i • (1 : SuperRing K n)) k := by
  simp only [moment, map_sum, smul_eq_mul, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', mul_one]

theorem includeLeft_powerMoment_mem_pairedIdeal
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (huv : ∀ i, u i + v i = r i * s) (k : ℕ) :
    (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n)
      (powerMoment r β s k) ∈
      pairedIdeal β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) := by
  have hcoeff (i : Fin n) :
      (C (β i) * Polynomial.aeval ((X i : PolynomialRing K n) ^ r i)
        ((Polynomial.X : Polynomial K) ^ s) : PolynomialRing K n) =
        C (β i) * X i ^ u i * X i ^ v i := by
    rw [Polynomial.aeval_X_pow, ← pow_mul, ← huv i, pow_add]
    ring
  rw [powerMoment_eq_moment, includeLeft_module_moment]
  simp only [hcoeff]
  exact TwoSidedIdeal.subset_span ⟨(.polynomial, k), rfl⟩

theorem includeLeft_powerMomentIdeal_le_pairedIdeal
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (huv : ∀ i, u i + v i = r i * s) :
    ∀ p ∈ powerMomentIdeal r β s,
      (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n) p ∈
        pairedIdeal β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i) := by
  let I := pairedIdeal β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)
  let incl : PolynomialRing K n →ₐ[K] SuperRing K n := Algebra.TensorProduct.includeLeft
  have hle : powerMomentIdeal r β s ≤ (I.comap incl.toRingHom).asIdeal := by
    apply Ideal.span_le.mpr
    rintro p ⟨k, rfl⟩
    change powerMoment r β s k ∈ (I.comap incl.toRingHom).asIdeal
    rw [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_comap]
    exact includeLeft_powerMoment_mem_pairedIdeal r u v β s huv k
  intro p hp
  have hh := hle hp
  rw [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_comap] at hh
  exact hh

/-- Finiteness of the literal homogeneous paired quotient follows from its
actual ordinary scalar relations. -/
theorem pairedPower_quotient_finite
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ)
    (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Module.Finite K
      (PairedQuotient β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)) := by
  let A := ordinaryPowerRing r β s
  let E := ordinaryPowerExterior r β s
  let I := pairedIdeal β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)
  letI : Module.Finite K A := powerMoment_quotient_finite r β s hβ
  letI : Module.Finite A E := Module.Finite.of_basis (Pi.basisFun A (OddIndex n)).ExteriorAlgebra
  letI : Module.Finite K E := Module.Finite.trans A E
  exact Module.Finite.of_surjective
    (superQuotientFactor I (powerMomentIdeal r β s)
      (includeLeft_powerMomentIdeal_le_pairedIdeal r u v β s huv)).toLinearMap
    (superQuotientFactor_surjective I (powerMomentIdeal r β s)
      (includeLeft_powerMomentIdeal_le_pairedIdeal r u v β s huv))

/-- The full Section 4.3 upper bound for the paper's actual homogeneous
paired quotient. There is no supplied harmonic dimension, endpoint colength,
Frobenius pairing, finite-dimensionality, or quotient-realization hypothesis.
-/
theorem pairedPower_quotient_finrank_le_box_count
    (r u v : Fin n → ℕ) (β : Fin n → K) (s : ℕ) (hs : 0 < s)
    (hr : ∀ i, 0 < r i) (huv : ∀ i, u i + v i = r i * s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hfac : IsUnit (n.factorial : K)) :
    Module.finrank K
      (PairedQuotient β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)) ≤
      ∑ T : Finset (Fin n ⊕ Fin n), pairedWordBoxCard r u v s T := by
  letI := powerMoment_quotient_finite r β s hβ
  obtain ⟨ε, hε⟩ := powerMoment_quotient_frobenius r β s hr hs hβ
  have hquot := pairedQuotient_finrank_le_harmonics β
    (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)
    (powerMomentIdeal r β s) (includeLeft_powerMomentIdeal_le_pairedIdeal r u v β s huv)
    ε hε.separatingLeft
  have hquot' : Module.finrank K
      (PairedQuotient β (fun i ↦ X i ^ r i) (fun i ↦ X i ^ u i) (fun i ↦ X i ^ v i)) ≤
      Module.finrank K (pairedPowerHarmonics r u v β s) := by
    simpa only [pairedPowerHarmonics, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap] using hquot
  exact hquot'.trans (pairedPowerHarmonics_finrank_le_box_count r u v β s hs hr huv hβ hfac)

end PaperVerification.Fermion

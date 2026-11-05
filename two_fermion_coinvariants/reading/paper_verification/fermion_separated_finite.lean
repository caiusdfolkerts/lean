module

public import PaperVerification.FermionDefinitions
public import PaperVerification.FermionNecessary
public import PaperVerification.FermionTensorFinite
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The exact finiteness criterion for the actual super quotients

This file uses the ordinary criterion and the exterior augmentation to establish
Proposition 7.1 for the paired and strict separated-cover families. The exterior
factor remains the actual exterior algebra, with two-sided moment ideals.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators TensorProduct

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The exterior augmentation kills every odd generator. -/
def oddAugmentation (K : Type*) [CommRing K] (n : ℕ) :
    ExteriorAlgebra K (OddModule K n) →ₐ[K] K :=
  ExteriorAlgebra.lift K ⟨0, fun _ ↦ by simp⟩

@[simp]
theorem oddAugmentation_ι (v : OddModule K n) :
    oddAugmentation K n (ExteriorAlgebra.ι K v) = 0 := by
  rw [oddAugmentation, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- The exterior-degree-zero projection of the actual ambient algebra. -/
def scalarProjection : SuperRing K n →ₐ[K] PolynomialRing K n :=
  tensorScalarProjection (oddAugmentation K n)

@[simp]
theorem scalarProjection_theta (i : Fin n) : scalarProjection (theta K n i) = 0 := by
  simp [scalarProjection, theta, tensorScalarProjection]

@[simp]
theorem scalarProjection_xi (i : Fin n) : scalarProjection (xi K n i) = 0 := by
  simp [scalarProjection, xi, tensorScalarProjection]

@[simp]
theorem scalarProjection_smul (a : PolynomialRing K n) (z : SuperRing K n) :
    scalarProjection (a • z) = a * scalarProjection z :=
  tensorScalarProjection_smul _ _ _

theorem scalarProjection_moment (φ : Fin n → PolynomialRing K n)
    (v : Fin n → SuperRing K n) (k : ℕ) :
    scalarProjection (moment φ v k) =
      moment φ (fun i ↦ scalarProjection (v i)) k := by
  simp only [moment, map_sum, scalarProjection_smul, smul_eq_mul]

theorem includeLeft_scalar_moment (φ v : Fin n → PolynomialRing K n) (k : ℕ) :
    (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n)
        (moment φ v k) = moment φ (fun i ↦ v i • (1 : SuperRing K n)) k := by
  simp only [moment, map_sum, smul_eq_mul, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', mul_one]

/-- Finiteness of a four-family moment quotient is exactly finiteness of its ordinary part
when the remaining three families have zero exterior augmentation. -/
theorem finite_moment_quotient_iff_ordinary
    (φ : Fin n → PolynomialRing K n) (β : Fin n → K) (G : Polynomial K)
    (v : MomentKind → Fin n → SuperRing K n)
    (hpoly : ∀ i, v .polynomial i =
      (MvPolynomial.C (β i) * Polynomial.aeval (φ i) G) • (1 : SuperRing K n))
    (hodd : ∀ kind : MomentKind, kind ≠ .polynomial →
      ∀ i, scalarProjection (v kind i) = 0) :
    Module.Finite K (momentIdeal φ v).ringCon.Quotient ↔
      Module.Finite K (PolynomialRing K n ⧸ ordinaryMomentIdeal φ β G) := by
  classical
  letI : LinearOrder (OddIndex n) :=
    LinearOrder.lift' (Fintype.equivFin (OddIndex n)) (Fintype.equivFin (OddIndex n)).injective
  letI : Module.Finite K (ExteriorAlgebra K (OddModule K n)) :=
    Module.Finite.of_basis (Pi.basisFun K (OddIndex n)).ExteriorAlgebra
  let I := momentIdeal φ v
  let J := ordinaryMomentIdeal φ β G
  let incl : PolynomialRing K n →ₐ[K] SuperRing K n := Algebra.TensorProduct.includeLeft
  have hJ' : J ≤ (I.comap incl.toRingHom).asIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change moment φ
      (fun i ↦ (algebraMap K (PolynomialRing K n)) (β i) * Polynomial.aeval (φ i) G) k ∈
      (I.comap incl.toRingHom).asIdeal
    rw [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_comap]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.algebraMap_eq]
    change (Algebra.TensorProduct.includeLeft : PolynomialRing K n →ₐ[K] SuperRing K n)
      (moment φ (fun i ↦ MvPolynomial.C (β i) * Polynomial.aeval (φ i) G) k) ∈ I
    rw [includeLeft_scalar_moment]
    have hv : (fun i ↦ (MvPolynomial.C (β i) * Polynomial.aeval (φ i) G) •
        (1 : SuperRing K n)) = v .polynomial := by
      funext i
      exact (hpoly i).symm
    rw [hv]
    exact TwoSidedIdeal.subset_span ⟨(.polynomial, (k : ℕ)), rfl⟩
  have hJ : ∀ a : PolynomialRing K n, a ∈ J → incl a ∈ I := by
    intro a ha
    simpa only [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_comap,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hJ' ha
  have hI' : I ≤ J.toTwoSided.comap (scalarProjection (K := K) (n := n)).toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨⟨kind, k⟩, rfl⟩
    change moment φ (v kind) k ∈
      J.toTwoSided.comap (scalarProjection (K := K) (n := n)).toRingHom
    rw [TwoSidedIdeal.mem_comap, Ideal.mem_toTwoSided]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [scalarProjection_moment]
    cases kind with
    | polynomial =>
      have hv : (fun i ↦ scalarProjection (v .polynomial i)) =
          fun i ↦ MvPolynomial.C (β i) * Polynomial.aeval (φ i) G := by
        funext i
        rw [hpoly, scalarProjection_smul, map_one, mul_one]
      rw [hv]
      exact ordinaryMoment_mem φ β G k
    | theta => simpa [moment, hodd .theta (by decide)] using J.zero_mem
    | xi => simpa [moment, hodd .xi (by decide)] using J.zero_mem
    | mixed => simpa [moment, hodd .mixed (by decide)] using J.zero_mem
  have hI : ∀ z : SuperRing K n, z ∈ I → scalarProjection z ∈ J := by
    intro z hz
    simpa only [TwoSidedIdeal.mem_comap, Ideal.mem_toTwoSided,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hI' hz
  exact finite_tensor_quotient_iff_scalar_quotient (oddAugmentation K n) I J hJ hI

/-- Exterior augmentation identifies the exact ordinary quotient of the paired family. -/
theorem paired_finite_iff_ordinary
    (β : Fin n → K) (φ a b : Fin n → PolynomialRing K n) (G : Polynomial K)
    (hab : ∀ i, a i * b i = Polynomial.aeval (φ i) G) :
    Module.Finite K (PairedQuotient β φ a b) ↔
      Module.Finite K (PolynomialRing K n ⧸ ordinaryMomentIdeal φ β G) := by
  apply finite_moment_quotient_iff_ordinary φ β G (pairedCoefficients β a b)
  · intro i
    simp only [pairedCoefficients, mul_assoc, hab]
  · intro kind hkind i
    cases kind with
    | polynomial => exact (hkind rfl).elim
    | theta => simp [pairedCoefficients]
    | xi => simp [pairedCoefficients]
    | mixed => simp [pairedCoefficients]

/-- Exterior augmentation identifies the exact ordinary quotient of the strict family. -/
theorem strict_finite_iff_ordinary (β : Fin n → K) (φ : Fin n → PolynomialRing K n) :
    Module.Finite K (StrictQuotient β φ) ↔
      Module.Finite K (PolynomialRing K n ⧸ ordinaryMomentIdeal φ β Polynomial.X) := by
  apply finite_moment_quotient_iff_ordinary φ β Polynomial.X (strictCoefficients β φ)
  · intro i
    simp only [strictCoefficients, Polynomial.aeval_X]
  · intro kind hkind i
    cases kind with
    | polynomial => exact (hkind rfl).elim
    | theta => simp [strictCoefficients]
    | xi => simp [strictCoefficients]
    | mixed => simp [strictCoefficients]

/-- Proposition 7.1, paired case: the exact finiteness criterion for separated monic covers.

No invertibility of `n!` is needed for this finiteness assertion. The polynomials
`aᵢ,bᵢ` may be any factors with the specified common product.
-/
theorem paired_separated_finite_iff
    (β : Fin n → K) (G : Polynomial K) (φ : Fin n → Polynomial K)
    (a b : Fin n → PolynomialRing K n)
    (hG : G.Monic) (hGpos : 0 < G.natDegree)
    (hφ : ∀ i, (φ i).Monic) (hφpos : ∀ i, 0 < (φ i).natDegree)
    (hab : ∀ i, a i * b i =
      Polynomial.aeval (Polynomial.aeval (MvPolynomial.X i) (φ i)) G) :
    Module.Finite K
      (PairedQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)) a b) ↔
      ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i) := by
  rw [paired_finite_iff_ordinary _ _ _ _ G hab]
  exact separated_ordinary_finite_iff β G φ hG hGpos hφ hφpos

/-- Proposition 7.1, strict case, with arbitrary separated monic positive-degree covers. -/
theorem strict_separated_finite_iff
    (β : Fin n → K) (φ : Fin n → Polynomial K)
    (hφ : ∀ i, (φ i).Monic) (hφpos : ∀ i, 0 < (φ i).natDegree) :
    Module.Finite K
      (StrictQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i))) ↔
      ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i) := by
  cases subsingleton_or_nontrivial K with
  | inl hK =>
    letI := hK
    letI := Algebra.subsingleton K
      (StrictQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)))
    constructor
    · intro _ U _
      exact isUnit_of_subsingleton _
    · intro _
      infer_instance
  | inr hK =>
    letI := hK
    rw [strict_finite_iff_ordinary]
    exact separated_ordinary_finite_iff β Polynomial.X φ Polynomial.monic_X (by simp) hφ hφpos

/-- A monic polynomial of prescribed formal degree, phrased so that the zero ring is allowed.

Over a nonzero ring this says exactly that `p` is monic and has natural degree `d`.
Over the zero ring, the coefficient condition `p.coeff d = 1` remains meaningful,
as it does for a monic polynomial specified by its coefficients over an arbitrary base.
-/
def MonicAtDegree (p : Polynomial K) (d : ℕ) : Prop :=
  p.natDegree ≤ d ∧ p.coeff d = 1

theorem MonicAtDegree.monic {p : Polynomial K} {d : ℕ}
    (hp : MonicAtDegree p d) : p.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hp.1 hp.2

theorem MonicAtDegree.natDegree_eq [Nontrivial K] {p : Polynomial K} {d : ℕ}
    (hp : MonicAtDegree p d) : p.natDegree = d :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hp.1 (by rw [hp.2]; exact one_ne_zero)

theorem monicAtDegree_iff [Nontrivial K] (p : Polynomial K) (d : ℕ) :
    MonicAtDegree p d ↔ p.Monic ∧ p.natDegree = d := by
  constructor
  · intro hp
    exact ⟨hp.monic, hp.natDegree_eq⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hd.le, hd ▸ hp.coeff_natDegree⟩

/-- The paired finiteness criterion over every commutative coefficient ring, including
the zero ring. The prescribed degrees are positive and the factors have their literal
common product; there are no restrictions on the subset sums in the hypotheses. -/
theorem paired_separated_finite_iff_over_any_ring
    (β : Fin n → K) (G : Polynomial K) (φ : Fin n → Polynomial K)
    (a b : Fin n → PolynomialRing K n) (s : ℕ) (r : Fin n → ℕ)
    (hs : 0 < s) (hr : ∀ i, 0 < r i)
    (hG : MonicAtDegree G s) (hφ : ∀ i, MonicAtDegree (φ i) (r i))
    (hab : ∀ i, a i * b i =
      Polynomial.aeval (Polynomial.aeval (MvPolynomial.X i) (φ i)) G) :
    Module.Finite K
      (PairedQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)) a b) ↔
      ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i) := by
  cases subsingleton_or_nontrivial K with
  | inl hK =>
    letI := hK
    letI := Algebra.subsingleton K
      (PairedQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)) a b)
    constructor
    · intro _ U _
      exact isUnit_of_subsingleton _
    · intro _
      infer_instance
  | inr hK =>
    letI := hK
    apply paired_separated_finite_iff β G φ a b hG.monic
      (hG.natDegree_eq.symm ▸ hs) (fun i ↦ (hφ i).monic)
      (fun i ↦ (hφ i).natDegree_eq.symm ▸ hr i) hab

/-- The strict finiteness criterion with prescribed positive monic degrees, valid over
every commutative coefficient ring, including the zero ring. -/
theorem strict_separated_finite_iff_over_any_ring
    (β : Fin n → K) (φ : Fin n → Polynomial K) (r : Fin n → ℕ)
    (hr : ∀ i, 0 < r i) (hφ : ∀ i, MonicAtDegree (φ i) (r i)) :
    Module.Finite K
      (StrictQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i))) ↔
      ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i) := by
  cases subsingleton_or_nontrivial K with
  | inl hK =>
    letI := hK
    letI := Algebra.subsingleton K
      (StrictQuotient β (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)))
    constructor
    · intro _ U _
      exact isUnit_of_subsingleton _
    · intro _
      infer_instance
  | inr hK =>
    letI := hK
    exact strict_separated_finite_iff β φ (fun i ↦ (hφ i).monic)
      (fun i ↦ (hφ i).natDegree_eq.symm ▸ hr i)

end PaperVerification.Fermion

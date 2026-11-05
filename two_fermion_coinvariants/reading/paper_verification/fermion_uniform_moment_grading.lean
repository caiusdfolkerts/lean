module

public import PaperVerification.FermionSuperTrigrading
public import PaperVerification.FermionStrictHighestForms
public import PaperVerification.FermionSharedGrading

/-!
# Physical three-gradings of the uniform paired and strict moment quotients

Each defining current is checked in the
original polynomial tensor exterior algebra. The quotient components are
the images of those physical components, and their directness follows from
the proved homogeneous-ideal construction. No character comparison or
choice of quotient basis enters these definitions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

open MvPolynomial Exterior
variable {R : Type*} [CommRing R] {n : ℕ}
local instance uniformMomentOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance uniformMomentDecidableEq : DecidableEq (OddIndex n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq

def physicalMomentBidegree : MomentKind → ℕ×ℕ
  | .polynomial => (0,0)
  | .theta => (1,0)
  | .xi => (0,1)
  | .mixed => (1,1)

theorem pairedMomentWord_physical_degree (kind : MomentKind) (i : Fin n) :
    exteriorWordDegree physicalOddBidegree (pairedMomentWord kind i)=
      physicalMomentBidegree kind := by
  cases kind <;> simp [pairedMomentWord,physicalMomentBidegree,
    exteriorWordDegree,physicalOddBidegree] <;> rfl

def uniformPairedCoefficientDegree (u v : ℕ) : MomentKind → ℕ
  | .polynomial => u+v
  | .theta => v
  | .xi => u
  | .mixed => 0

def uniformStrictCoefficientDegree (r : ℕ) : MomentKind → ℕ
  | .polynomial => r
  | .theta => 0
  | .xi => 0
  | .mixed => 0

theorem physical_X_pow_homogeneous (i : Fin n) (r : ℕ) :
    (X i^r : PolynomialRing R n).IsWeightedHomogeneous (fun _ ↦ 1) r := by
  simpa only [nsmul_eq_mul,Nat.cast_id,mul_one] using
    (isWeightedHomogeneous_X (R := R) (fun _ : Fin n ↦ (1 : ℕ)) i).pow r

theorem uniformPairedCoefficient_homogeneous (beta : Fin n → R) (u v : ℕ)
    (kind : MomentKind) (i : Fin n) :
    (pairedPolynomialCoefficient beta (fun i ↦ X i^u) (fun i ↦ X i^v) kind i).IsWeightedHomogeneous (fun _ ↦ 1) (uniformPairedCoefficientDegree u v kind) := by
  cases kind with
  | polynomial =>
      simpa only [pairedPolynomialCoefficient,uniformPairedCoefficientDegree,zero_add] using
        ((isWeightedHomogeneous_C (fun _ : Fin n ↦ (1 : ℕ)) (beta i)).mul
          (physical_X_pow_homogeneous i u)).mul (physical_X_pow_homogeneous i v)
  | theta => exact physical_X_pow_homogeneous i v
  | xi =>
      simpa only [pairedPolynomialCoefficient,uniformPairedCoefficientDegree,zero_add] using
        (isWeightedHomogeneous_C (fun _ : Fin n ↦ (1 : ℕ)) (beta i)).mul
          (physical_X_pow_homogeneous i u)
  | mixed => exact isWeightedHomogeneous_one R _

theorem uniformStrictCoefficient_homogeneous (beta : Fin n → R) (r : ℕ)
    (kind : MomentKind) (i : Fin n) :
    (strictPolynomialCoefficient beta (fun i ↦ X i^r) kind i).IsWeightedHomogeneous (fun _ ↦ 1) (uniformStrictCoefficientDegree r kind) := by
  cases kind with
  | polynomial =>
      simpa only [strictPolynomialCoefficient,uniformStrictCoefficientDegree,zero_add] using
        (isWeightedHomogeneous_C (fun _ : Fin n ↦ (1 : ℕ)) (beta i)).mul
          (physical_X_pow_homogeneous i r)
  | theta => exact isWeightedHomogeneous_one R _
  | xi => exact isWeightedHomogeneous_C _ _
  | mixed => exact isWeightedHomogeneous_one R _

theorem uniformPairedMoment_physical_mem (beta : Fin n → R) (r u v : ℕ)
    (kind : MomentKind) (k : ℕ) :
    moment (R := PolynomialRing R n) (M := SuperRing R n) (fun i ↦ X i^r)
      (pairedCoefficients beta (fun i ↦ X i^u) (fun i ↦ X i^v) kind) k∈
      physicalSuperPart (R := R) (n := n) (r*k+uniformPairedCoefficientDegree u v kind,
        physicalMomentBidegree kind) := by
  rw [pairedMoment_eq_tensor_sum]
  apply Submodule.sum_mem
  intro i hi
  have hx : ((X i^r)^k : PolynomialRing R n).IsWeightedHomogeneous (fun _ ↦ 1) (r*k) := by
    simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm k r] using
      (physical_X_pow_homogeneous (R := R) i r).pow k
  have hm := polynomialExteriorPart_tmul_word (fun _ : Fin n ↦ 1)
    physicalOddBidegree
    ((X i^r)^k*pairedPolynomialCoefficient beta (fun i ↦ X i^u)
      (fun i ↦ X i^v) kind i) _
    (hx.mul (uniformPairedCoefficient_homogeneous beta u v kind i))
    (pairedMomentWord kind i)
  simpa only [physicalSuperPart,pairedMomentWord_physical_degree] using hm

theorem uniformStrictMoment_physical_mem (beta : Fin n → R) (r : ℕ)
    (kind : MomentKind) (k : ℕ) :
    moment (R := PolynomialRing R n) (M := SuperRing R n) (fun i ↦ X i^r) (strictCoefficients beta (fun i ↦ X i^r) kind) k∈
      physicalSuperPart (R := R) (n := n) (r*k+uniformStrictCoefficientDegree r kind,
        physicalMomentBidegree kind) := by
  rw [strictMoment_eq_tensor_sum]
  apply Submodule.sum_mem
  intro i hi
  have hx : ((X i^r)^k : PolynomialRing R n).IsWeightedHomogeneous (fun _ ↦ 1) (r*k) := by
    simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm k r] using
      (physical_X_pow_homogeneous (R := R) i r).pow k
  have hm := polynomialExteriorPart_tmul_word (fun _ : Fin n ↦ 1)
    physicalOddBidegree
    ((X i^r)^k*strictPolynomialCoefficient beta (fun i ↦ X i^r) kind i) _
    (hx.mul (uniformStrictCoefficient_homogeneous beta r kind i))
    (pairedMomentWord kind i)
  simpa only [physicalSuperPart,pairedMomentWord_physical_degree] using hm

def uniformPairedPhysicalPart (beta : Fin n → R) (r u v : ℕ)
    (g : ℕ×(ℕ×ℕ)) :
    Submodule R (PairedQuotient beta (fun i ↦ X i^r) (fun i ↦ X i^u) (fun i ↦ X i^v)) :=
  gradedImagePart (R := R) (A := SuperRing R n)
    (B := PairedQuotient beta (fun i ↦ X i^r) (fun i ↦ X i^u) (fun i ↦ X i^v))
    (physicalSuperPart (R := R) (n := n))
    ((pairedIdeal beta (fun i ↦ X i^r) (fun i ↦ X i^u) (fun i ↦ X i^v)).ringCon.mkₐ R) g

def uniformPairedPhysicalGrading (beta : Fin n → R) (r u v : ℕ) :
    GradedAlgebra (R := R)
      (A := PairedQuotient beta (fun i ↦ X i^r) (fun i ↦ X i^u) (fun i ↦ X i^v))
      (uniformPairedPhysicalPart beta r u v) := by
  letI := physicalSuperGrading (R := R) (n := n)
  exact multihomogeneousTwoSidedQuotientGrading (R := R) (A := SuperRing R n)
    (Γ := ℕ×(ℕ×ℕ)) (physicalSuperPart (R := R) (n := n))
    (Set.range (fun p : MomentKind×ℕ ↦ moment (R := PolynomialRing R n) (M := SuperRing R n) (fun i ↦ X i^r)
      (pairedCoefficients beta (fun i ↦ X i^u) (fun i ↦ X i^v) p.1) p.2)) (by
      rintro x ⟨⟨kind,k⟩,rfl⟩
      exact ⟨_,uniformPairedMoment_physical_mem beta r u v kind k⟩)

def uniformStrictPhysicalPart (beta : Fin n → R) (r : ℕ)
    (g : ℕ×(ℕ×ℕ)) : Submodule R (StrictQuotient beta (fun i ↦ X i^r)) :=
  gradedImagePart (R := R) (A := SuperRing R n)
    (B := StrictQuotient beta (fun i ↦ X i^r))
    (physicalSuperPart (R := R) (n := n))
    ((strictIdeal beta (fun i ↦ X i^r)).ringCon.mkₐ R) g

def uniformStrictPhysicalGrading (beta : Fin n → R) (r : ℕ) :
    GradedAlgebra (R := R) (A := StrictQuotient beta (fun i ↦ X i^r))
      (uniformStrictPhysicalPart beta r) := by
  letI := physicalSuperGrading (R := R) (n := n)
  exact multihomogeneousTwoSidedQuotientGrading (R := R) (A := SuperRing R n)
    (Γ := ℕ×(ℕ×ℕ)) (physicalSuperPart (R := R) (n := n))
    (Set.range (fun p : MomentKind×ℕ ↦ moment (R := PolynomialRing R n) (M := SuperRing R n) (fun i ↦ X i^r)
      (strictCoefficients beta (fun i ↦ X i^r) p.1) p.2)) (by
      rintro x ⟨⟨kind,k⟩,rfl⟩
      exact ⟨_,uniformStrictMoment_physical_mem beta r kind k⟩)

end PaperVerification.Fermion

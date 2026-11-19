module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.Algebra.Equiv

/-!
# An actual unit-plus-augmentation basis

These are coefficient identities for a genuine augmented algebra and a
basis whose distinguished vector is the unit. They are the algebraic
inputs for the normalized free bar resolution: positive multiplication,
its associativity, and the splitting used by the contracting homotopy.
No bar exactness or homological claim is assumed in these data.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AugmentedAlgebraBasis

open scoped BigOperators

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def positiveVector (i : I) : A := B (some i)

def positiveCoordinates : A →ₗ[K] (I →₀ K) :=
  (Finsupp.lcomapDomain (R := K) (M := K) Option.some (Option.some_injective I)).comp
    B.repr.toLinearMap

@[simp] theorem positiveCoordinates_apply (x : A) (i : I) :
    positiveCoordinates B x i=B.repr x (some i) := rfl

def positiveCombination : (I →₀ K) →ₗ[K] A :=
  Finsupp.linearCombination K (positiveVector B)

@[simp] theorem positiveCombination_apply (c : I →₀ K) :
    positiveCombination B c=c.sum (fun i z => z • positiveVector B i) := rfl

include hunit hε in
theorem augmentation_eq_coordinate (x : A) : ε x=B.repr x none := by
  have he : ε.toLinearMap=B.coord none := by
    apply B.ext
    intro i
    cases i with
    | none =>
        change ε (B none)=B.repr (B none) none
        rw [Module.Basis.repr_self,Finsupp.single_eq_same,hunit,map_one]
    | some i =>
        change ε (B (some i))=B.repr (B (some i)) none
        rw [hε,Module.Basis.repr_self,Finsupp.single_eq_of_ne (by simp)]
  exact LinearMap.congr_fun he x

@[simp] theorem positiveCoordinates_vector (i : I) :
    positiveCoordinates B (positiveVector B i)=Finsupp.single i 1 := by
  classical
  ext j
  simp [positiveCoordinates_apply,positiveVector,Module.Basis.repr_self,
    Finsupp.single_apply]

include hunit in
@[simp] theorem positiveCoordinates_one : positiveCoordinates B (1 : A)=0 := by
  rw [←hunit]
  ext i
  simp only [positiveCoordinates_apply,Module.Basis.repr_self,Finsupp.single_apply,
    reduceCtorEq,ite_false,Finsupp.zero_apply]

include hunit hε in
/-- The literal splitting of every algebra element into its scalar and
augmentation parts. -/
theorem scalar_add_positive (x : A) :
    ε x • (1 : A)+positiveCombination B (positiveCoordinates B x)=x := by
  have h := B.linearCombination_repr x
  rw [Finsupp.linearCombination_apply,Finsupp.sum_option_index_smul,hunit,
    ←augmentation_eq_coordinate ε B hunit hε x] at h
  exact h

include hunit hε in
theorem positiveCombination_coordinates (x : A) (hx : ε x=0) :
    positiveCombination B (positiveCoordinates B x)=x := by
  have h := scalar_add_positive ε B hunit hε x
  simpa only [hx,zero_smul,zero_add] using h

@[simp] theorem positiveCoordinates_combination (c : I →₀ K) :
    positiveCoordinates B (positiveCombination B c)=c := by
  rw [positiveCombination_apply]
  simp only [Finsupp.sum,map_sum,map_smul,positiveCoordinates_vector,
    Finsupp.smul_single,smul_eq_mul,mul_one]
  exact Finsupp.sum_single c

theorem positiveCombination_injective : Function.Injective (positiveCombination B) :=
  Function.LeftInverse.injective (positiveCoordinates_combination B)

def productCoefficients (i j : I) : I →₀ K :=
  positiveCoordinates B (positiveVector B i*positiveVector B j)

include hunit hε in
theorem product_expansion (i j : I) :
    positiveCombination B (productCoefficients B i j)=positiveVector B i*positiveVector B j := by
  apply positiveCombination_coordinates ε B hunit hε
  simp only [positiveVector,map_mul,hε,mul_zero]

include hunit hε in
theorem productCoefficients_associative (i j k : I) :
    (productCoefficients B i j).sum (fun a c => c • productCoefficients B a k)=
      (productCoefficients B j k).sum (fun a c => c • productCoefficients B i a) := by
  apply positiveCombination_injective B
  simp only [Finsupp.sum,map_sum,map_smul,product_expansion ε B hunit hε]
  have hl := congrArg (fun z : A => z*positiveVector B k)
    (product_expansion ε B hunit hε i j)
  have hr := congrArg (fun z : A => positiveVector B i*z)
    (product_expansion ε B hunit hε j k)
  simp only [positiveCombination_apply,Finsupp.sum,Finset.sum_mul,smul_mul_assoc] at hl
  simp only [positiveCombination_apply,Finsupp.sum,Finset.mul_sum,mul_smul_comm] at hr
  exact hl.trans ((mul_assoc _ _ _).trans hr.symm)

include hunit hε in
/-- This is the identity that cancels the first multiplication term
against the positive-prefix part of the normalized bar homotopy. -/
theorem positiveCoordinates_mul_vector (x : A) (j : I) :
    positiveCoordinates B (x*positiveVector B j)=
      ε x • Finsupp.single j 1+
        (positiveCoordinates B x).sum (fun i c => c • productCoefficients B i j) := by
  have h := congrArg (fun z : A => positiveCoordinates B (z*positiveVector B j))
    (scalar_add_positive ε B hunit hε x)
  rw [add_mul,smul_mul_assoc,one_mul,map_add,map_smul,positiveCoordinates_vector] at h
  rw [positiveCombination_apply] at h
  simp only [Finsupp.sum,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul] at h
  exact h.symm

end PaperVerification.AugmentedAlgebraBasis

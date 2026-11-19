module

public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A dimension gained when rehomogenizing an actual polynomial quotient

For a homogeneous ideal, setting one degree-one coordinate equal to one
quotients by a nonzero divisor. The proof checks every homogeneous component;
it does not assume the quotient is a domain or that the coordinate is regular.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped nonZeroDivisors

namespace PaperVerification.GradedDehomogenization

variable {K ι : Type*} [Field K]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.gradedAlgebra

theorem component_of_mem_homogeneous (I : Ideal P)
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K))
    (f : P) (hf : f∈I) (d : ℕ) : homogeneousComponent d f∈I := by
  exact homogeneousComponent_mem_of_mem hI hf d

theorem mem_of_components_mem (I : Ideal P) (f : P)
    (hf : ∀ d, homogeneousComponent d f∈I) : f∈I := by
  classical
  rw [←sum_homogeneousComponent f]
  exact I.sum_mem fun d hd => hf d

/-- The actual element `X_i-1` is regular modulo every homogeneous ideal. -/
theorem variable_sub_one_mem_nonZeroDivisors (I : Ideal P)
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K)) (i : ι) :
    Ideal.Quotient.mk I (X i-1) ∈ (P⧸I)⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro q hq
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hf : (X i-1)*f∈I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hq
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply mem_of_components_mem I f
  intro d
  induction d with
  | zero =>
    have h := component_of_mem_homogeneous I hI _ hf 0
    rw [show (X i-1)*f=f*X i-f by ring,map_sub,
      (isHomogeneous_X K i).homogeneousComponent_mul_right] at h
    simpa only [show ¬(1 : ℕ) ≤ 0 by omega,ite_false,zero_sub,neg_mem_iff] using h
  | succ d ih =>
    have h := component_of_mem_homogeneous I hI _ hf (d+1)
    rw [show (X i-1)*f=f*X i-f by ring,map_sub,
      (isHomogeneous_X K i).homogeneousComponent_mul_right,
      if_pos (Nat.succ_le_succ (Nat.zero_le d)),Nat.add_sub_cancel] at h
    have hmul := I.mul_mem_right (X i) ih
    simpa only [sub_sub_cancel] using I.sub_mem hmul h

/-- Any actual dehomogenized quotient has dimension at least one less than
the homogeneous cone. Surjectivity and the coordinate value are the only
map-specific conditions. -/
theorem dimension_succ_le_of_dehomogenized_surjection
    (I : Ideal P) (hI : I.IsHomogeneous (homogeneousSubmodule ι K)) (i : ι)
    {R : Type*} [CommRing R] (φ : (P⧸I) →+* R)
    (hφ : Function.Surjective φ) (hi : φ (Ideal.Quotient.mk I (X i))=1) :
    ringKrullDim R+1 ≤ ringKrullDim (P⧸I) := by
  apply ringKrullDim_succ_le_of_surjective φ hφ (variable_sub_one_mem_nonZeroDivisors I hI i)
  simp only [map_sub,map_one,hi,sub_self]

end PaperVerification.GradedDehomogenization
